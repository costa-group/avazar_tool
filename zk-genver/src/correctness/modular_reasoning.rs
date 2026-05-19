use solvers_interface::{EquivalenceVerification, PossibleResult, PossibleSolver, cvc5_interface, ffsol_interface, nia_z3_interface, parallel_interface, yices_interface, z3_interface};
type Constraint = circom_algebra::algebra::Constraint<usize>;
use circom_algebra::num_bigint::BigInt;
use utils::read_specification::SpecificationInfo;
use std::collections::LinkedList;
use std::time::{Instant, Duration};
use utils::structure::NodeInfo;
use std::collections::{HashSet,HashMap};
use crate::equivalence::equivalence_check::ResultInfoEquivalence;


pub type EquivalenceImplication = (Vec<(usize, usize)>, Vec<(usize, usize)>);

    pub fn check_node(
        node_info: &NodeInfo, 
        field: &BigInt, 
        verification_timeout: u64,
        node_list: &Vec<NodeInfo>,
        nodeid2pos: &HashMap<usize, usize>,
        constraint_list: &Vec<Constraint>,
        specification: &SpecificationInfo,
        solver: PossibleSolver,
        apply_deduction_assigned: bool,
        include_niaz3_in_all: bool,
        apply_predecessors:bool,
        apply_bidirectional: bool,
        no_abstract_fails:bool,
        results:&ResultInfoEquivalence,
        extra_rounds: usize,
        verbose: bool
    ) 
    -> (PossibleResult, f64, usize, bool, Vec<String>, HashSet<usize>){

        let node_name = node_info.node_name;
        let node_specification_info = specification.get(&node_name).unwrap();
        
        let signals_1: LinkedList<usize> = node_info.signals.clone().into_iter().collect(); 
        let signals_2: LinkedList<String> = node_specification_info.signals.clone().into_iter().collect(); 

        let mut constraints = Vec::new();
        for c in &node_info.constraints{
            constraints.push(constraint_list[*c].clone());
        }

        let mut logs =  Vec::new();
        let mut n_rounds = 0;
        let mut unknown_rounds = 0;
        let implications_safety: Vec<EquivalenceImplication> = Vec::new();


        let mut verification = CorrectnessVerification::new(
            &node_info.node_name.to_string(), 
            signals_1,
            signals_2, 
            node_info.input_signals.clone(),
            node_specification_info.input_signals.clone(),
            node_info.output_signals.clone(),
            node_specification_info.output_signals.clone(),
            constraints_1.clone(), 
            constraints_2.clone(),
            implications_safety,
            field,
            verification_timeout,
            apply_deduction_assigned,
            verbose
        );

        let mut to_check_next=Vec::new();
        if !apply_predecessors || apply_bidirectional{
            let mut to_check = generate_and_add_node_info(&node_info.successors, &mut verification, node_list, nodeid2pos, constraint_list_1, constraint_list_2, results, apply_bidirectional, no_abstract_fails);
            to_check_next.append(&mut to_check);
        } 
        if apply_predecessors || apply_bidirectional{
            let mut to_check = generate_and_add_node_info(&node_info.predecessors, &mut verification, node_list, nodeid2pos, constraint_list_1, constraint_list_2, results, apply_bidirectional, false);
            to_check_next.append(&mut to_check);
        }

        
        logs.push(format!("Checking template {}\n", node_info.node_id));
        logs.push(format!("Number of signals in the first version (i,int,o): {}\n", node_info.signals_1.len()));      
        logs.push(format!("Number of signals in the second version (i,int,o): {}\n", node_info.signals_2.len()));      

        logs.push(format!("Number of constraints in the first template: {}\n", node_info.constraints_1.len()));
        logs.push(format!("Number of constraints in the second template: {}\n", node_info.constraints_2.len()));

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
                    let result_add_components = add_info_component(node, &mut verification, node_list, nodeid2pos, constraint_list_1, constraint_list_2, results, apply_predecessors, apply_bidirectional, no_abstract_fails);                    
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
        verification: &mut EquivalenceVerification, 
        node_list: &Vec<NodeInfo>, 
        nodeid2pos: &HashMap<usize, usize>, 
        constraint_list_1: &Vec<Constraint>,
        constraint_list_2: &Vec<Constraint>,
        results:&ResultInfoEquivalence,
        apply_predecessors: bool,
        apply_bidirectional: bool,
        no_abstract_fails: bool
    )-> Option<Vec<usize>>{

            for c in &info.constraints_1{
                verification.constraints_1.push(constraint_list_1[*c].clone());
            }
            for s in &info.signals_1{
                verification.signals_1.push_back(*s);
            }
            for c in &info.constraints_2{
                verification.constraints_2.push(constraint_list_2[*c].clone());
            }
            for s in &info.signals_2{
                verification.signals_2.push_back(*s);
            }
            let mut to_check_next: Vec<usize> = Vec::new();
            if !apply_predecessors || apply_bidirectional{
                let mut to_check = generate_and_add_node_info(&info.successors, verification, node_list, nodeid2pos, constraint_list_1, constraint_list_2,  results, apply_bidirectional, no_abstract_fails);
                to_check_next.append(&mut to_check);
            } 
            if apply_predecessors || apply_bidirectional{
                            //println!("Entra pred");

                let mut to_check = generate_and_add_node_info(&info.predecessors, verification, node_list, nodeid2pos, constraint_list_1, constraint_list_2, results, apply_bidirectional, false);
                to_check_next.append(&mut to_check);
            }

            if to_check_next.len() > 0 {Some(to_check_next)} else {None}
    }

    fn generate_and_add_node_info(
        node_ids: &[usize], 
        verification: &mut EquivalenceVerification, 
        node_list: &Vec<NodeInfo>, 
        nodeid2pos: &HashMap<usize, usize>, 
        constraint_list_1: &Vec<Constraint>,
        constraint_list_2: &Vec<Constraint>,
        results:&ResultInfoEquivalence, 
        apply_bidirectional: bool,
        no_abstract_fails: bool,
    ) -> Vec<usize> {
        let mut to_check_next = Vec::new();
        for node_id in node_ids {
            println!("node_id {}", node_id);
            let pos = nodeid2pos[node_id];
            let subtree_child = &node_list[pos];
            let (mut new_signals_1, mut new_signals_2, new_implications_safety) = generate_info_subtree(subtree_child);
            verification.signals_1.append(&mut new_signals_1);
            verification.signals_2.append(&mut new_signals_2);

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
                                let result_add_components = add_info_component(node, verification, node_list, nodeid2pos, constraint_list_1, constraint_list_2, results,  false, false, no_abstract_fails);                    
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

    fn generate_info_subtree(info: &NodeInfo)-> (LinkedList<usize>, LinkedList<usize>, EquivalenceImplication){
        let (io_signals_1, io_signals_2) = generate_io_signals(info);
        ( 
            io_signals_1,
            io_signals_2,
            generate_implications_safety(info)
        )
    }

    fn generate_io_signals(info: &NodeInfo)-> (LinkedList<usize>, LinkedList<usize>){
        let mut signals_1 = LinkedList::new();
        for s in &info.input_signals_1{
            signals_1.push_back(*s);
        }
        for s in &info.output_signals_1{
            signals_1.push_back(*s);
        }  
        let mut signals_2 = LinkedList::new();
        for s in &info.input_signals_2{
            signals_2.push_back(*s);
        }
        for s in &info.output_signals_2{
            signals_2.push_back(*s);
        }  
        (signals_1, signals_2)
    }
    
    fn generate_implications_safety(info: &NodeInfo)-> EquivalenceImplication{
        let mut list_inputs = Vec::new();
        let mut list_outputs = Vec::new();

        for i in 0..info.output_signals_1.len(){
            list_outputs.push((info.output_signals_1[i], info.output_signals_2[i]));
        }
        for i in 0..info.input_signals_1.len(){
            list_inputs.push((info.input_signals_1[i], info.input_signals_2[i]));
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
        problem: &EquivalenceVerification,
        solver: PossibleSolver,
    )-> (PossibleResult, Vec<String>) {
        match solver{
            PossibleSolver::FFSOL=>{
                ffsol_interface::study_equivalence(
                    problem,
                    &ffsol_interface::FfsolConfig::default(problem.verification_timeout, problem.verbose),
                )
            },
            PossibleSolver::CVC5=>{
                cvc5_interface::study_equivalence(problem)
            },
            PossibleSolver::YICES=>{
                yices_interface::study_equivalence(problem)
            },
            PossibleSolver::NIAZ3=>{
                nia_z3_interface::study_equivalence(problem)
            },
            PossibleSolver::Z3=>{
                z3_interface::study_equivalence(problem)
            },
            PossibleSolver::ALL=>{
                parallel_interface::study_equivalence(problem)
            },
            _ => unreachable!()
        }
    }


