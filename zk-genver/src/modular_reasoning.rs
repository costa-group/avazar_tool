use civer::tags_checking::TemplateVerification;
use solvers_interface::{SafetyVerification, PossibleResult, PossibleSolver, picus_interface};
type Constraint = circom_algebra::algebra::Constraint<usize>;
use circom_algebra::num_bigint::BigInt;
use std::collections::LinkedList;
use std::time::{Instant, Duration};
use utils::structure::NodeInfo;
use std::collections::HashMap;

pub type SafetyImplication = (Vec<usize>, Vec<usize>);


    pub fn check_tags(
        node_info: &NodeInfo, 
        field: &BigInt, 
        verification_timeout: u64,
        node_list: &Vec<NodeInfo>,
        nodeid2pos: &HashMap<usize, usize>,
        constraint_list: &Vec<Constraint>,
        solver: PossibleSolver
    ) 
    -> (PossibleResult, f64, usize, Vec<String>){
        
        let mut signals: LinkedList<usize> = node_info.signals.clone().into_iter().collect(); 
        
        let mut constraints = Vec::new();
        for c in &node_info.constraints{
            constraints.push(constraint_list[*c].clone());
        }

        let mut implications_safety: Vec<SafetyImplication> = Vec::new();
        for node_id in &node_info.successors{
            let pos = nodeid2pos[node_id];
            let subtree_child = &node_list[pos];
            let (mut new_signals, new_implications_safety) = generate_info_subtree(subtree_child);
            signals.append(&mut new_signals);
            implications_safety.push(new_implications_safety)
        }
        let mut to_check_next = node_info.successors.clone();

        
        let mut logs =  Vec::new();
        let mut n_rounds = 0;


        let mut verification = SafetyVerification::new(
            &node_info.node_id.to_string(), 
            signals.clone(), 
            node_info.input_signals.clone(),
            node_info.output_signals.clone(),
            constraints.clone(), 
            implications_safety.clone(),
            field,
            verification_timeout,
        );
        logs.push(format!("Checking template {}\n", node_info.node_id));
        logs.push(format!("Number of signals (i,int,o): {}\n", node_info.signals.len()));      
        logs.push(format!("Number of constraints in template: {}\n", node_info.constraints.len()));
        let inicio = Instant::now();

        let (mut result_safety, mut logs_round) = prove_safety(&verification, solver);

        let mut finished_verification = result_safety.finished_verification();
        logs.append(&mut logs_round);
        
        while !finished_verification && !to_check_next.is_empty(){
            n_rounds += 1;

            let new_components = std::mem::take(&mut to_check_next);
            for node_id in &new_components{
                if !verification.added_nodes.contains(node_id) { 

                    let pos = nodeid2pos[node_id];
                    let node = &node_list[pos];
                    let result_add_components = add_info_component(node, &mut verification, node_list, nodeid2pos, constraint_list);                    
                    if result_add_components.is_some(){
                        for aux in result_add_components.unwrap(){
                            to_check_next.push(aux);
                        }
                    }
                    verification.added_nodes.insert(*node_id);
                } else{
                    unreachable!();
                }
            }
 

            logs.push(format!("### Trying to verify adding constraints of the children\n"));
            (result_safety, logs_round) = prove_safety(&verification, solver);
            finished_verification = result_safety.finished_verification();
            logs.append(&mut logs_round);

        } 
        let duration = inicio.elapsed();  
        pretty_print_result(&mut logs, duration, n_rounds, &result_safety);
        (result_safety, duration.as_secs_f64(), n_rounds, logs)
        
    }

  
    

    fn add_info_component(info: &NodeInfo, verification: &mut SafetyVerification, node_list: &Vec<NodeInfo>, nodeid2pos: &HashMap<usize, usize>, constraint_list: &Vec<Constraint>)-> Option<Vec<usize>>{

            for c in &info.constraints{
                verification.constraints.push(constraint_list[*c].clone());
            }
            for s in &info.signals{
                verification.signals.push_back(*s);
            }
            for node_id in &info.successors{
                let pos = nodeid2pos[node_id];
                let subtree_child = &node_list[pos];
                let (new_signals, new_safety_implication) = generate_info_subtree(subtree_child);
                for s in new_signals{
                    verification.signals.push_back(s);
                }
                verification.implications_safety.push(new_safety_implication);
            }
            Some(info.successors.clone())

    }

    fn generate_info_subtree(info: &NodeInfo)-> (LinkedList<usize>, SafetyImplication){
        (   generate_io_signals(info),
            generate_implications_safety(info)
        )
    }

    fn generate_io_signals(info: &NodeInfo)-> LinkedList<usize>{
        let mut signals = LinkedList::new();
        for s in &info.input_signals{
            signals.push_back(*s);
        }
        for s in &info.output_signals{
            signals.push_back(*s);
        }  
        signals
    }
    
    fn generate_implications_safety(info: &NodeInfo)-> SafetyImplication{
        let mut list_inputs = Vec::new();
        let mut list_outputs = Vec::new();
        for s in &info.output_signals{
            list_outputs.push(*s);
        }
        for s in &info.input_signals{
            list_inputs.push(*s);
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



    fn prove_safety(
        problem: &SafetyVerification,
        solver: PossibleSolver
    )-> (PossibleResult, Vec<String>) {
        match solver{
            PossibleSolver::CIVER =>{
                let mut civer_template_verification = TemplateVerification::new(problem);
                civer_template_verification.deduce()
            },
            PossibleSolver::PICUS =>{
                picus_interface::deduce(problem)
            }
        }
    }


