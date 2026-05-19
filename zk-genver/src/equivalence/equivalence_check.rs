use std::collections::HashSet;
use solvers_interface::{EquivalenceVerification, PossibleResult, PossibleSolver};
use crate::Input;
use crate::processing_utils::*;
use utils::equivalence_structure::*;
use num_bigint_dig::BigInt;
use std::collections::{HashMap, BTreeMap};
use circom_algebra::algebra::Constraint;
use crate::equivalence::modular_reasoning::check_node;
use solvers_interface::ffsol_interface;
use solvers_interface::cvc5_interface;
use solvers_interface::nia_z3_interface;
use solvers_interface::yices_interface;
use solvers_interface::z3_interface;

use utils::small_utilities::{GraphBackend, EquivalenceMode, ClusteringPreprocessing};


#[derive(Default)]
pub struct ResultInfoEquivalence{
    verified_nodes: HashSet<usize>,
    failed_nodes: HashSet<usize>,
    unknown_nodes: HashSet<usize>,
    // unknown_undivisible_nodes: HashSet<usize>,
    pub studied_nodes: HashMap<usize, PossibleResult>,
    // total_constraints: usize,
    // verified_constraints: usize,
    // fails_original_templates: Option<HashSet<String>>,// include which constraints fail in each component or not?
    // number_unverified_orig_constraints: Option<usize>, // the number of constraints included in the unverified templates
    // number_unverified_orig_constraints_noreps: Option<usize>, // the number of constraints included in the unverified templates
    // unverified_nodes_to_templates: Option<HashMap<usize, HashSet<String>>>,
    // unverified_nodes_to_nodes: Option<HashMap<usize, HashSet<usize>>>,

}

pub fn prove_equivalence(user_input: Input) -> Result<(), ()> {    
    let (constraints,
        signals,
        n_outputs,
        n_inputs)
        = process_constraints(&user_input.input_r1cs);

    let (constraints_aux,
        signals_aux,
        n_outputs_aux,
        n_inputs_aux)
        = process_constraints(&user_input.check_equivalence.unwrap());

    // Read the structure
    let structure  = if user_input.input_structure.is_some(){
        let input_str = &format!("{}", user_input.input_structure.as_ref().unwrap().display());
        read_equivalence_structure(input_str).unwrap()
    } else{
        generate_empty_equivalence_structure(constraints.len(), constraints_aux.len(), signals.len(), signals_aux.len(), n_outputs, n_outputs_aux, n_inputs, n_inputs_aux)
    }; 
        
    let timeout: u64 = user_input.timeout;
    let apply_deduction_assigned: bool = user_input.apply_deduction_assigned;
    let include_niaz3_in_all: bool = user_input.include_niaz3_in_all;
    let apply_predecessors: bool = user_input.apply_predecessors;
    let apply_bidirectional: bool = user_input.apply_bidirectional;


    let field = user_input.prime;

    let equivalence_mode = match user_input.equivalence_mode{
        0 => EquivalenceMode::None,
        1 => EquivalenceMode::Local,
        2 => EquivalenceMode::Total,
        _ => unreachable!()
    };

    let (
        nodeid2pos, 
        local_equivalence_classes, 
        structural_equivalence_classes,
        mut max_node_id
    ) = process_equivalence_structure(&structure);


    let clustering_size = user_input.clustering_size;
    let target_size = user_input.target_size;

    
    let mut results = ResultInfoEquivalence{
        verified_nodes: HashSet::new(),
        failed_nodes: HashSet::new(),
        unknown_nodes: HashSet::new(),
        studied_nodes: HashMap::new()
    };

    for node in structure.nodes.iter().rev(){
        process_node(&node, 
            &structure, 
            &constraints, 
            &constraints_aux,
            &local_equivalence_classes,
            &structural_equivalence_classes,
            &nodeid2pos, 
            &field, 
            timeout, 
            user_input.solver_option,
            apply_deduction_assigned,
            include_niaz3_in_all,
            apply_predecessors,
            apply_bidirectional,
            &mut results,
            user_input.extra_rounds,
            user_input.limit_size,
            user_input.flag_verbose
        );
    }
    /* 
    let mut to_study_again = if clustering_size != 0{
        reconsider_big_nodes(&structure, &nodeid2pos, &mut results, clustering_size)
    } else{
        Vec::new()
    };

    while !to_study_again.is_empty(){
        for node_id in to_study_again{
            decompose_and_study(
                node_id,
                &mut structure,
                &constraints,
                &mut nodeid2pos,
                &mut max_node_id,
                &field, 
                timeout, 
                user_input.solver_option,
                equivalence_mode,
                target_size,
                apply_deduction_assigned,
                include_niaz3_in_all,
                apply_predecessors,
                apply_bidirectional,
                &mut results,
                user_input.extra_rounds,
                user_input.limit_size,
                user_input.flag_verbose
            );
        }
        to_study_again = reconsider_big_nodes(&structure, &nodeid2pos, &mut results, clustering_size);
    }
    */

    // print the results    
    print_pretty_results(&results, &structure, nodeid2pos);
    Result::Ok(())
}

fn process_node(
    node: &NodeInfo,
    structure: &EquivalenceStructureInfo,
    constraints_1: &Vec<Constraint<usize>>,
    constraints_2: &Vec<Constraint<usize>>,
    local_equivalence_classes: &HashMap<usize, usize>,
    structural_equivalence_classes: &HashMap<usize, usize>,
    //studied_eq_classes: &mut HashMap<usize, PossibleResult>,
    nodeid2pos: &HashMap<usize, usize>,
    field: &BigInt,
    timeout: u64,
    solver: PossibleSolver,
    apply_deduction_assigned: bool,
    include_niaz3_in_all: bool,
    apply_predecessors: bool,
    apply_bidirectional: bool,
    results: &mut ResultInfoEquivalence,
    extra_rounds: usize,
    limit_size: usize,
    verbose: bool
) {

    // To not study the custom templates
    if node.is_custom{
        results.studied_nodes.insert(node.node_id, PossibleResult::NOTHING);
        return;
    }

    if results.studied_nodes.contains_key(&node.node_id) {
        // If the node has already been studied, we skip it.
        return;
    }

    if node.constraints_1.len() > limit_size || node.constraints_2.len() > limit_size{
        println!("Not considering node {} because it is too big", node.node_id);
        results.studied_nodes.insert(node.node_id, PossibleResult::UNKNOWN);
        results.unknown_nodes.insert(node.node_id);
    }

    println!("LOG: Considering node {} with {} and {} constraints", node.node_id, node.constraints_1.len(), node.constraints_2.len());
    let no_abstract_fails = false;
            
    // If the equivalence class of the node has not been studied, we process it.
    let (result, _, n_rounds, _extra_rounds_helped, logs, included_nodes) = check_node(
        node,
        &field,
        timeout,
        &structure.nodes,
        &nodeid2pos, 
        &constraints_1,
        &constraints_2,
        solver,
        apply_deduction_assigned,
        include_niaz3_in_all,
        apply_predecessors,
        apply_bidirectional,
        no_abstract_fails,
        results,
        extra_rounds,
        verbose
    );
        
        for log in logs{
            println!("{}", log);
        }

    // check if one of the children is verified using the parent. If so, do not generalize to any class
    let mut verified_child = false;
    if result == PossibleResult::VERIFIED && no_abstract_fails{
        for id_included in included_nodes{

            if results.studied_nodes.contains_key(&id_included){

                let prev_result = results.studied_nodes.get_mut(&id_included).unwrap();
                match prev_result{
                    PossibleResult::VERIFIED =>{
                    },
                    PossibleResult::NOTHING =>{
                    },
                    PossibleResult::FAILED =>{
                    	println!("Child node {} becomes safe when considering father constraints", id_included);
                        results.failed_nodes.remove(&id_included);
                        results.verified_nodes.insert(id_included);

                        *prev_result = PossibleResult::VERIFIED; 
                        verified_child = true;
                    },
                    PossibleResult::UNKNOWN =>{
                        println!("Child node {} becomes safe when considering father constraints", id_included);
                        results.unknown_nodes.remove(&id_included);
                        results.failed_nodes.remove(&id_included);
                        results.verified_nodes.insert(id_included);

                        *prev_result = PossibleResult::VERIFIED;
                        verified_child = true;
                    },
                    _ => unreachable!(),
                }	
            }
        }
    }

        
    if n_rounds == 0{
    	// No need to study children, can generalize to all the local equivalence class
    	 let id_class = local_equivalence_classes.get(&node.node_id).unwrap();
         let local_eq_class = &structure.local_equivalency[*id_class];
         update_result_for_class(&result, local_eq_class, results);
    } else if !verified_child{
        // Considering children, only generalize to the structural equivalence class
         let id_class = structural_equivalence_classes.get(&node.node_id).unwrap();
         let structural_eq_class = &structure.structural_equivalency[*id_class];
        update_result_for_class(&result, structural_eq_class, results);
    } else{
        update_result_for_class(&result, &vec![node.node_id], results);
    }

}

/* 
fn decompose_and_study(
    node_id: usize,
    structure: &mut EquivalenceStructureInfo,
    constraints_1: &Vec<Constraint<usize>>,
    constraints_2: &Vec<Constraint<usize>>,
    nodeid2pos: &mut HashMap<usize, usize>,
    max_node_id: &mut usize,
    field: &BigInt,
    timeout: u64,
    solver: PossibleSolver,
    equivalence_mode: EquivalenceMode,
    target_size: usize,
    apply_deduction_assigned: bool,
    include_niaz3_in_all: bool,
    apply_predecessors: bool,
    apply_bidirectional: bool,
    results: &mut ResultInfoEquivalence,
    extra_rounds: usize,
    limit_size: usize,
    verbose: bool
) {
    println!("LOG: Reconsidering again node {}", node_id);
    let node_info = structure.nodes.get(*nodeid2pos.get(&node_id).unwrap()).unwrap();

    //print_node_info(node_info, constraints);
    let mut constraints_original_index = Vec::new();
    let mut constraints_copy = Vec::new();
    for c_id in &node_info.constraints_1{
        let c = &constraints_1[*c_id];
        let interface_aux_constraint = (
            c.a().clone(),
            c.b().clone(),
            c.c().clone()
        );
        constraints_original_index.push(*c_id);
        constraints_copy.push(
            interface_aux_constraint
        );
    }

    let mut constraints_2_original_index = Vec::new();
    let mut constraints_2_copy = Vec::new();
    for c_id in &node_info.constraints_2{
        let c = &constraints_2[*c_id];
        let interface_aux_constraint = (
            c.a().clone(),
            c.b().clone(),
            c.c().clone()
        );
        constraints_2_original_index.push(*c_id);
        constraints_2_copy.push(
            interface_aux_constraint
        );
    }

    let decompose_options = DecomposeOptions {
        target_size: Some(target_size as f64),
        equivalence_mode: equivalence_mode,
        inverse_coni_mapping: Some(&constraints_original_index),
        ..Default::default()
    };

    let structure_reader = decompose_node(
        field, 
        &constraints_copy, 
        &node_info.input_signals, 
        &node_info.output_signals,
        decompose_options
    );  


    let mut new_structure = transform_structure_reader(structure_reader);
    let (new_nodeid2pos, 
        local_equivalence_classes, 
        structural_equivalence_classes,
        new_max_node_id
    ) = process_structure(&new_structure);

    println!("LOG: node decomposed in {} new nodes", new_nodeid2pos.len());

    let mut new_results = ResultInfoDeterminism{
        verified_nodes: HashSet::new(),
        failed_nodes: HashSet::new(),
        unknown_nodes: HashSet::new(),
        unknown_undivisible_nodes: HashSet::new(),
        studied_nodes: HashMap::new(),
        total_constraints: 0,
        verified_constraints: 0,
        fails_original_templates: None,
        number_unverified_orig_constraints: None,
        number_unverified_orig_constraints_noreps: None,
        unverified_nodes_to_templates:None,
        unverified_nodes_to_nodes:None,

    };

    if new_structure.nodes.len() == 1{
        // in this case the clustering is not performing any changes -> add as unknown and do not divide
		println!("LOG: case node not divided, no studying again");
        results.studied_nodes.insert(node_id, PossibleResult::UNKNOWN);
		results.unknown_undivisible_nodes.insert(node_id);
        return;
    }

    for node in &new_structure.nodes{
        if node.constraints.len() == 0{
            //println!("LOG: printing info node with 0 constraints");
            //print_node_info(node, constraints);
        }

        process_node(node, 
            &new_structure, 
            &constraints, 
            &local_equivalence_classes,
            &structural_equivalence_classes,
            &new_nodeid2pos, 
            &field, 
            timeout, 
            solver,
            apply_deduction_assigned,
            include_niaz3_in_all,
            apply_predecessors,
            apply_bidirectional,
            &mut new_results,
            extra_rounds,
            limit_size,
            verbose
        );
    }

    println!("LOG: studied the new nodes -> verified {}", new_results.verified_nodes.len());

    let mut index = 0;
    for (node_id, result) in new_results.studied_nodes{
        // add the new nodes to the initial structure
        let pos_id = *new_nodeid2pos.get(&node_id).unwrap();

        let node_info = new_structure.nodes.get_mut(pos_id).unwrap();
        let new_node_id = node_info.node_id + *max_node_id;  // to get a unique node id
        node_info.node_id = new_node_id;
        nodeid2pos.insert(new_node_id, structure.nodes.len() + index);
        index += 1;

        // add the new results to the previous ones
        results.studied_nodes.insert(new_node_id, result.clone());
		match result{
			PossibleResult::VERIFIED =>{
				results.verified_nodes.insert(new_node_id);
			},
			PossibleResult::FAILED =>{
				results.failed_nodes.insert(new_node_id);
			},
			PossibleResult::UNKNOWN =>{
				results.unknown_nodes.insert(new_node_id);
			},
			_ => unreachable!(),
		}	
    }   
    structure.nodes.append(&mut new_structure.nodes);


    *max_node_id += new_max_node_id;

    //println!("Added the info to the results");

}

// To get the nodes that were too big and need to be studied again
fn reconsider_big_nodes(
    structure: &StructureInfo,
    nodeid2pos: &HashMap<usize, usize>,
    results: &mut ResultInfoDeterminism,
    clustering_size: usize
) -> Vec<usize>{

    // TODO: only insert one for the equivalent ones
    println!("Reconsidering again searching big nodes");
    let mut to_study_again = Vec::new();
    for node_id in &results.unknown_nodes{
        let node_info = &structure.nodes[nodeid2pos[node_id]];
        let number_constraints = node_info.constraints.len();
        //println!("Studying node {} of {} constraints", node_id, number_constraints);
        if number_constraints > clustering_size {
            to_study_again.push(*node_id);
        }
    }

    // Remove from the studied nodes as we will consider again
    for node_id in &to_study_again{
        results.studied_nodes.remove(node_id);
        results.unknown_nodes.remove(node_id);
    }

    to_study_again
}
*/

fn update_result_for_class(node_result: &PossibleResult, equiv_class: &Vec<usize>, results: &mut ResultInfoEquivalence){
	for node in equiv_class{
		results.studied_nodes.insert(*node, node_result.clone());
		match node_result{
			PossibleResult::VERIFIED =>{
				results.verified_nodes.insert(*node);
			},
			PossibleResult::FAILED =>{
				results.failed_nodes.insert(*node);
			},
			PossibleResult::UNKNOWN =>{
				results.unknown_nodes.insert(*node);
			},
			_ => unreachable!(),
		}	
	}
}



fn print_pretty_results(
    results: &ResultInfoEquivalence,
    structure: &EquivalenceStructureInfo,
    node_id_to_pos: HashMap<usize, usize>,


){


    println!();

    println!("--------------------------------------------");
    println!("--------------------------------------------");
    println!("------ ZK-GENVER VERIFICATION RESULTS ------");
    println!("--------------------------------------------");
    println!("--------------------------------------------\n");

    if results.failed_nodes.is_empty() && results.unknown_nodes.is_empty(){
        println!("-> All nodes are equivalent :)");
    } else{
    	println!("-> ZK-GENVER could not verify the equivalence of all components");
    	if !results.failed_nodes.is_empty(){
        	println!("Nodes that are not equivalent: ");
        	for c in &results.failed_nodes{
                let pos = node_id_to_pos.get(c).unwrap();
                let node_name = &structure.nodes[*pos].node_name;
    			println!("    - Node {}: {}, ", c,  node_name);
    		}
        }
    	if !results.unknown_nodes.is_empty() {
        	println!("Nodes that timeout when checking equivalence: ");
        	for c in &results.unknown_nodes{
    			let pos = node_id_to_pos.get(c).unwrap();
                let node_name = &structure.nodes[*pos].node_name;
    			println!("    - Node {}: {}, ", c, node_name);
    		}
        }
    }
    println!("  * Number of verified nodes (equivalence): {}",  results.verified_nodes.len());
    println!("  * Number of failed nodes (equivalence): {}",  results.failed_nodes.len());        
    println!("  * Number of timeout nodes (equivalence): {}",  results.unknown_nodes.len());

}
