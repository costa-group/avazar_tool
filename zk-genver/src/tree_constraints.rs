

use civer::tags_checking::{TemplateVerification, PossibleResult};
type Constraint = circom_algebra::algebra::Constraint<usize>;
use circom_algebra::num_bigint::BigInt;
use std::collections::LinkedList;
use std::hash::Hash;
use std::time::{Instant, Duration};
use utils::structure::NodeInfo;
use std::collections::{HashMap, HashSet};

pub type SafetyImplication = (Vec<usize>, Vec<usize>);

#[derive(Default, Debug)]
pub struct TreeConstraints {
    pub constraints: Vec<usize>,
    _node_id: usize,
    template_name: String,
    pub inputs: Vec<usize>, 
    outputs: Vec<usize>,
    pub signals: Vec<usize>,
    pub subcomponents: Vec<usize>,
}

impl TreeConstraints {
    pub fn new(info: &NodeInfo) -> TreeConstraints {
        TreeConstraints{
            constraints: info.constraints.clone(),
            inputs: info.input_signals.clone(),
            outputs: info.output_signals.clone(),
            signals: info.signals.clone(),
            _node_id: info.node_id,
            template_name: format!("node_{}", info.node_id),
            subcomponents: info.successors.clone(),
        }
    }

    pub fn _template_name(&self)-> &String{
        &self.template_name
    }

    pub fn _subcomponents(&self)-> &Vec<usize>{
        &self.subcomponents
    }

    pub fn constraints(&self)-> &Vec<usize>{
        &self.constraints
    }

    

    fn add_info_component(info: &NodeInfo, verification: &mut TemplateVerification, node_list: &Vec<NodeInfo>, nodeid2pos: &HashMap<usize, usize>, constraint_list: &Vec<Constraint>)-> Option<Vec<usize>>{
        //if self.constraints.len() <= 150{
            for c in &info.constraints{
                verification.constraints.push(constraint_list[*c].clone());
            }
            for s in &info.signals{
                verification.signals.push_back(*s);
            }
            for node_id in &info.successors{
                let pos = nodeid2pos[node_id];
                let subtree_child = &node_list[pos];
                let (new_signals, new_safety_implication) = TreeConstraints::generate_info_subtree(subtree_child);
                for s in new_signals{
                    verification.signals.push_back(s);
                }
                verification.implications_safety.push(new_safety_implication);
            }
            Some(info.successors.clone())
        /* } else{
            println!("Subcomponent has not been considered since it has {} constraints", self.constraints.len());
            None
        }*/
    }

    pub fn check_tags(&self, 
        field: &BigInt, 
        verification_timeout: u64,
        node_list: &Vec<NodeInfo>,
        nodeid2pos: &HashMap<usize, usize>,
        constraint_list: &Vec<Constraint>
    ) 
    -> (PossibleResult, f64, usize, Vec<String>){

        let mut implications_safety: Vec<SafetyImplication> = Vec::new();

        let mut signals: LinkedList<usize> = LinkedList::new(); 

        let mut logs =  Vec::new();
        
        for s in &self.signals{
            signals.push_back(*s);
        }
        
        let mut constraints = Vec::new();

        for node_id in &self.subcomponents{
            let pos = nodeid2pos[node_id];
            let subtree_child = &node_list[pos];
            let (mut new_signals, new_implications_safety) = TreeConstraints::generate_info_subtree(subtree_child);
            signals.append(&mut new_signals);
            implications_safety.push(new_implications_safety)
        }

        for c in &self.constraints{
            constraints.push(constraint_list[*c].clone());
        }

        let mut verification = TemplateVerification::new(
            &self.template_name, 
            signals.clone(), 
            self.inputs.clone(),
            self.outputs.clone(),
            constraints.clone(), 
            implications_safety.clone(),
            field,
            verification_timeout,
        );
        logs.push(format!("Checking template {}\n", self.template_name));
        logs.push(format!("Number of signals (i,int,o): {}\n", self.signals.len()));      
        logs.push(format!("Number of constraints in template: {}\n", self.constraints().len()));
        let inicio = Instant::now();

        let (mut result_safety, mut logs_round) = verification.deduce();

        let mut finished_verification = result_safety.finished_verification();
        logs.append(&mut logs_round);
        if finished_verification{
            logs.push(format!("### Finished verification of the template: {} \n", result_safety.result_to_str()));
            let duration = inicio.elapsed();    
            TreeConstraints::pretty_print_result(&mut logs, duration, 0, &result_safety);
            (result_safety, duration.as_secs_f64(), 0, logs)
        } else if !self.subcomponents.is_empty(){
            let mut to_check_next = Vec::new();
            let mut n_rounds = 1;
            let mut suc_number = 0;
            for node_id in &self.subcomponents{
                if !verification.added_nodes.contains(node_id)  {
                    let pos = nodeid2pos[node_id];
                    let node = &node_list[pos];
                    let result_add_components = TreeConstraints::add_info_component(node, &mut verification, node_list, nodeid2pos, constraint_list);
                    if result_add_components.is_some(){
                        for aux in result_add_components.unwrap(){
                            to_check_next.push(aux);
                        }
                    }
                    verification.added_nodes.insert(*node_id);
                }
                suc_number += 1;
            }

            logs.push(format!("### Trying to verify adding constraints of the children\n"));
            
            (result_safety, logs_round) = verification.deduce();
            finished_verification = result_safety.finished_verification();
            logs.append(&mut logs_round);
            while !finished_verification && !to_check_next.is_empty(){
                let new_components = std::mem::take(&mut to_check_next);
                n_rounds = n_rounds + 1;
                
                for node_id in &new_components{
                    if !verification.added_nodes.contains(node_id){

                        let pos = nodeid2pos[node_id];
                        let node = &node_list[pos];
                        let result_add_components = TreeConstraints::add_info_component(node, &mut verification, node_list, nodeid2pos, constraint_list);                    
                        if result_add_components.is_some(){
                            for aux in result_add_components.unwrap(){
                                to_check_next.push(aux);
                            }
                        }
                        verification.added_nodes.insert(*node_id);
                    }
                }
 

                logs.push(format!("### Trying to verify adding constraints of the children\n"));
                (result_safety, logs_round) = verification.deduce();
                finished_verification = result_safety.finished_verification();
                logs.append(&mut logs_round);
            }
            let duration = inicio.elapsed();    
            TreeConstraints::pretty_print_result(&mut logs, duration, n_rounds, &result_safety);
            (result_safety, duration.as_secs_f64(), n_rounds, logs)
        } else{
            let duration = inicio.elapsed();  
            TreeConstraints::pretty_print_result(&mut logs, duration, 0, &result_safety);
            (result_safety, duration.as_secs_f64(), 0, logs)
        }
    }

    fn generate_info_subtree(info: &NodeInfo)-> (LinkedList<usize>, SafetyImplication){
        (   TreeConstraints::generate_io_signals(info),
            TreeConstraints::generate_implications_safety(info)
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


}
