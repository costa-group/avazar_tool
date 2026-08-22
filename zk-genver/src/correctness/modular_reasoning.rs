use solvers_interface::{CorrectnessVerification, PossibleResult, PossibleSolver, cvc5_interface, ffsol_interface, nia_z3_interface, parallel_interface, yices_interface, z3_interface};
type Constraint = circuits_constraints_and_algebra::r1cs::R1CSConstraint<usize>;
use circuits_constraints_and_algebra::num_bigint::BigInt;
use std::collections::LinkedList;
use std::time::{Instant, Duration};
use utils::structure::NodeInfo;
use std::collections::{HashSet,HashMap};
use crate::correctness::correctness_check::ResultInfoCorrectness;
use crate::equivalence::equivalence_check::ResultInfoEquivalence;
use indexmap::IndexMap;
use utils::read_specification::MacroDef;
use crate::correctness::processing_correctness_utils::{
    get_all_signals_macro,
    get_input_signals_macro,
    get_equivalent_signal_in_macro,
    build_macros,
    get_equivalent_subcomponent_signal_in_macro,
    build_call_macro
    
};
use std::collections::BTreeMap;


pub type CorrectnessImplication = (Vec<(usize, String)>, Vec<(usize, String)>);




    pub fn check_node(
        node_info: &NodeInfo,
        field: &BigInt,
        verification_timeout: u64,
        node_list: &Vec<NodeInfo>,
        nodeid2pos: &HashMap<usize, usize>,
        constraint_list: &Vec<Constraint>,
        macros: &IndexMap<String, MacroDef>,
        correspondence_nodeid_macros: &HashMap<usize, String>,
        signal_to_name: &BTreeMap<usize, String>,
        solver: PossibleSolver,
        apply_deduction_assigned: bool,
        include_niaz3_in_all: bool,
        apply_predecessors:bool,
        apply_bidirectional: bool,
        no_abstract_fails:bool,
        results:&ResultInfoCorrectness,
        extra_rounds: usize,
        verbose: bool,
        original_file: &str,
    ) 
    -> (PossibleResult, f64, usize, bool, Vec<String>, HashSet<usize>){

        let node_name = node_info.node_name.clone();
        let node_id = node_info.node_id;
        println!("Considering {}", node_id);
        println!("{:?}", correspondence_nodeid_macros);
        let macro_name = correspondence_nodeid_macros.get(&node_id).unwrap();
        let macro_spec = macros.get(macro_name).unwrap();


        let signals_1: LinkedList<usize> = node_info.signals.clone().into_iter().collect(); 
        let signals_2: Vec<String> = get_all_signals_macro(macro_spec); 

        let inputs_1 = node_info.input_signals.clone();
        let inputs_2 = get_input_signals_macro( inputs_1.len(), macro_spec);

        let outputs_1 = node_info.output_signals.clone();
        let mut outputs_2 = Vec::new();
        for out in &outputs_1 {
            outputs_2.push(get_equivalent_signal_in_macro(*out, macro_spec, signal_to_name));
        }

        let mut constraints_1 = Vec::new();
        for c in &node_info.constraints{
            constraints_1.push(constraint_list[*c].clone());
        }
        let constraints_2 = vec![macro_spec.formula.clone()];
        

        let mut macros_to_include = HashSet::new();
        macros_to_include.insert(macro_name.clone());
        let checked_by_some_node: HashSet<&String> =
            correspondence_nodeid_macros.values().collect();
        for name in macros.keys() {
            if !checked_by_some_node.contains(name) {
                macros_to_include.insert(name.clone());
            }
        }
        let unpacked_macros = build_macros(macros, &macros_to_include);

        let mut logs =  Vec::new();
        let mut n_rounds = 0;
        let mut unknown_rounds = 0;
        let implications_safety: Vec<CorrectnessImplication> = Vec::new();


        let node_name = if node_info.node_name.is_empty() {
            format!("node_{}", node_info.node_id)
        } else {
            node_info.node_name.clone()
        };



        let mut verification = CorrectnessVerification::new(
            &node_name,
            &original_file.to_string(),
            signals_1,
            signals_2,
            inputs_1,
            inputs_2,
            outputs_1,
            outputs_2,
            constraints_1,
            constraints_2,
            implications_safety,
            field,
            verification_timeout,
            verbose,
            unpacked_macros
        );

        let mut to_check_next=Vec::new();
        if !apply_predecessors || apply_bidirectional{
            let mut to_check = generate_and_add_node_info(&node_info.successors, &mut verification, node_list, nodeid2pos, constraint_list, macro_spec, macros,correspondence_nodeid_macros, signal_to_name, results, apply_bidirectional, no_abstract_fails);
            to_check_next.append(&mut to_check);
        } 
        if apply_predecessors || apply_bidirectional{
            let mut to_check = generate_and_add_node_info(&node_info.predecessors, &mut verification, node_list, nodeid2pos, constraint_list, macro_spec, macros,correspondence_nodeid_macros,signal_to_name, results, apply_bidirectional, false);
            to_check_next.append(&mut to_check);
        }

        
        logs.push(format!("Checking template {}\n", node_info.node_id));
        logs.push(format!("Number of signals in the first version (i,int,o): {}\n", node_info.signals.len()));      

        logs.push(format!("Number of constraints in the first template: {}\n", node_info.constraints.len()));

        let inicio = Instant::now();

        let (mut result_safety, mut logs_round) = prove_equivalence(&verification, solver);

        let mut used_extra_rounds = false;
        let mut finished_verification = match result_safety{
            PossibleResult::UNKNOWN =>{
                unknown_rounds += 1;
                if unknown_rounds <= extra_rounds {
                    used_extra_rounds = true;
                }
                unknown_rounds > extra_rounds
            },
            PossibleResult::FAILED =>{
                false
            },
            _ => true
        };
        logs.append(&mut logs_round);
        
        while !finished_verification && !to_check_next.is_empty(){
            n_rounds += 1;

            let new_components = std::mem::take(&mut to_check_next);
            for node_id in &new_components{
                if *node_id != node_info.node_id && !verification.added_nodes.contains(node_id) { 

                    let pos = nodeid2pos[node_id];
                    let node = &node_list[pos];
                    let result_add_components = add_info_component(node, &mut verification, node_list, nodeid2pos, constraint_list, macro_spec, macros, correspondence_nodeid_macros, signal_to_name, results, apply_predecessors, apply_bidirectional, no_abstract_fails);                    
                    if result_add_components.is_some(){
                        to_check_next.append(&mut result_add_components.unwrap());
                    }
                    verification.added_nodes.insert(*node_id);
                }
            }
 

            logs.push(format!("### Trying to verify adding constraints of the children\n"));
            (result_safety, logs_round) = prove_equivalence(&verification, solver);
            finished_verification = match result_safety{
                PossibleResult::UNKNOWN =>{
                    unknown_rounds += 1;
                    if unknown_rounds <= extra_rounds {
                        used_extra_rounds = true;
                    }
                    unknown_rounds > extra_rounds
                },
                PossibleResult::FAILED =>{
                    false
                },
                _ => true
            };
            logs.append(&mut logs_round);

        } 
        let duration = inicio.elapsed();  
        pretty_print_result(&mut logs, duration, n_rounds, &result_safety);
        let extra_rounds_helped = used_extra_rounds && result_safety == PossibleResult::VERIFIED;
        (
            result_safety,
            duration.as_secs_f64(),
            n_rounds,
            extra_rounds_helped,
            logs,
            verification.added_nodes,
        )
        
    }

    fn add_info_component(
        info: &NodeInfo, 
        verification: &mut CorrectnessVerification, 
        node_list: &Vec<NodeInfo>, 
        nodeid2pos: &HashMap<usize, usize>, 
        constraint_list_1: &Vec<Constraint>,
        father_macro: &MacroDef,
        macros: &IndexMap<String, MacroDef>,
        correspondence_nodeid_macros: &HashMap<usize, String>,
        signal_to_name: &BTreeMap<usize, String>,
        results:&ResultInfoCorrectness,
        apply_predecessors: bool,
        apply_bidirectional: bool,
        no_abstract_fails: bool
    )-> Option<Vec<usize>>{

            for c in &info.constraints{
                verification.constraints_1.push(constraint_list_1[*c].clone());
            }

            // add the macro
            let node_id = &info.node_id;
            let macro_child_name = correspondence_nodeid_macros.get(node_id).unwrap();
            let macro_info = macros.get(macro_child_name).unwrap();
            let macro_formula = build_call_macro(macro_child_name, &macro_info.params, macro_info.formula.clone());
            verification.macros.insert(macro_child_name.clone(), macro_formula);

            for s in &info.signals{
                verification.signals_1.push_back(*s);
            }
            let mut to_check_next: Vec<usize> = Vec::new();
            if !apply_predecessors || apply_bidirectional{
                let mut to_check = generate_and_add_node_info(&info.successors, verification, node_list, nodeid2pos, constraint_list_1, father_macro, macros, correspondence_nodeid_macros, signal_to_name,  results, apply_bidirectional, no_abstract_fails);
                to_check_next.append(&mut to_check);
            } 
            if apply_predecessors || apply_bidirectional{
                            //println!("Entra pred");

                let mut to_check = generate_and_add_node_info(&info.predecessors, verification, node_list, nodeid2pos, constraint_list_1, father_macro, macros, correspondence_nodeid_macros, signal_to_name, results, apply_bidirectional, false);
                to_check_next.append(&mut to_check);
            }

            if to_check_next.len() > 0 {Some(to_check_next)} else {None}
    }

    fn generate_and_add_node_info(
        node_ids: &[usize], 
        verification: &mut CorrectnessVerification, 
        node_list: &Vec<NodeInfo>, 
        nodeid2pos: &HashMap<usize, usize>, 
        constraint_list_1: &Vec<Constraint>,
        father_macro: &MacroDef,
        macros: &IndexMap<String, MacroDef>,
        correspondence_nodeid_macros: &HashMap<usize, String>,
        signal_to_name: &BTreeMap<usize, String>,        
        results:&ResultInfoCorrectness, 
        apply_bidirectional: bool,
        no_abstract_fails: bool,
    ) -> Vec<usize> {
        let mut to_check_next = Vec::new();
        for node_id in node_ids {
            let pos = nodeid2pos[node_id];
            let subtree_child: &NodeInfo = &node_list[pos];
            
            let (mut new_signals_1, new_implications_safety) = generate_info_subtree(subtree_child, father_macro, signal_to_name);
            verification.signals_1.append(&mut new_signals_1);

            if no_abstract_fails && results.studied_nodes.contains_key(node_id){
                    let result = results.studied_nodes.get(node_id).unwrap();
                    match result{
                        PossibleResult::VERIFIED => {
                            verification.implications_equivalence.push(new_implications_safety);
                            to_check_next.push(*node_id);
                        }
                        _ =>{
                            if !verification.added_nodes.contains(node_id) { 
                                let pos = nodeid2pos[node_id];
                                let node = &node_list[pos];
                                let result_add_components = add_info_component(node, verification, node_list, nodeid2pos, constraint_list_1, father_macro, macros,correspondence_nodeid_macros,signal_to_name, results,  false, false, no_abstract_fails);                    
                                if result_add_components.is_some(){
                                    for aux in result_add_components.unwrap(){
                                        to_check_next.push(aux);
                                    }
                                }
                                verification.added_nodes.insert(*node_id);
                            }
                        }
                    }
            }else{
                verification.implications_equivalence.push(new_implications_safety);
                to_check_next.push(*node_id);
            }            
            
        }
        to_check_next
    }

    fn generate_info_subtree(
        info: &NodeInfo,
        macro_info: &MacroDef,
        signal_to_name: &BTreeMap<usize, String>,     
    )-> (LinkedList<usize>, CorrectnessImplication){
        let io_signals_1 = generate_io_signals(info);
        ( 
            io_signals_1,
            generate_implications_safety(info, macro_info, signal_to_name)
        )
    }

    fn generate_io_signals(info: &NodeInfo)->  LinkedList<usize>{
        let mut signals_1 = LinkedList::new();
        for s in &info.input_signals{
            signals_1.push_back(*s);
        }
        for s in &info.output_signals{
            signals_1.push_back(*s);
        }
        signals_1
    }
    
    fn generate_implications_safety(
        info: &NodeInfo,
        macro_info: &MacroDef,
        signal_to_name: &BTreeMap<usize, String>,     
    )-> CorrectnessImplication{
        let mut list_inputs = Vec::new();
        let mut list_outputs = Vec::new();

        for out in &info.output_signals{
            let out_name: String = get_equivalent_subcomponent_signal_in_macro(*out, macro_info, signal_to_name);
            list_outputs.push((*out, out_name));
        }
        for inp in &info.input_signals{
            let inp_name: String = get_equivalent_subcomponent_signal_in_macro(*inp, macro_info, signal_to_name);
            list_inputs.push((*inp, inp_name));
        }
        (list_inputs, list_outputs)
    }

    fn pretty_print_result(logs: &mut Vec<String>, duration: Duration, n_rounds: usize, result: &PossibleResult){
        logs.push(format!("Verification time per template: {}\n", duration.as_secs_f64()));    
        logs.push(format!("     NUMBER OF ROUNDS: {}\n\n ", n_rounds));
        logs.push(format!("******** VERIFICATION RESULTS ********\n"));

        logs.push(format!("-----> WEAK SAFETY: "));
        logs.push(result.result_to_str());

        logs.push(format!("\n\n"));
    }



    fn prove_equivalence(
        problem: &CorrectnessVerification,
        solver: PossibleSolver,
    )-> (PossibleResult, Vec<String>) {
        match solver{
            PossibleSolver::FFSOL=>{
                ffsol_interface::study_correctness(
                    problem,
                    &ffsol_interface::FfsolConfig::default(problem.verification_timeout, problem.verbose),
                )
            },
            PossibleSolver::CVC5=>{
                cvc5_interface::study_correctness(problem)
            },
            PossibleSolver::YICES=>{
                yices_interface::study_correctness(problem)
            },
            PossibleSolver::NIAZ3=>{
                nia_z3_interface::study_correctness(problem)
            },
            /* 
            PossibleSolver::Z3=>{
                z3_interface::study_correctness(problem)
            },
            */
            PossibleSolver::ALL=>{
                parallel_interface::study_correctness(problem)
            },
            _ => unreachable!()
        }
    }


