mod modular_reasoning;
mod input_user;
use num_bigint_dig::BigInt;
use std::collections::{HashMap, HashSet, BTreeMap};
use circom_algebra::algebra::Constraint;
use utils::read_r1cs::read_r1cs;
use utils::read_original_structure::read_original_structure;
use utils::structure::*;
use solvers_interface::{PossibleResult, PossibleSolver};
use input_user::Input;
use std::path::PathBuf;
use crate::modular_reasoning::check_tags;
use clustering::decompose_circuit::decompose_node;
use utils::small_utilities::{GraphBackend, EquivalenceMode};


use ansi_term::Colour;

struct ResultInfo{
    verified_nodes: HashSet<usize>,
    failed_nodes: HashSet<usize>,
    unknown_nodes: HashSet<usize>,
    unknown_undivisible_nodes: HashSet<usize>,
    studied_nodes: HashMap<usize, PossibleResult>,
    total_constraints: usize,
    verified_constraints: usize,
    fails_original_templates: Option<HashSet<String>>,// include which constraints fail in each component or not?
    number_unverified_orig_constraints: Option<usize>, // the number of constraints included in the unverified templates
    number_unverified_orig_constraints_noreps: Option<usize> // the number of constraints included in the unverified templates

}


fn process_constraints(input: &PathBuf) -> (
    Vec<Constraint<usize>>,
    Vec<usize>,
    usize,
    usize
 ) {
    let input = &format!("{}", input.display());
    let result = read_r1cs(input).unwrap();
    let constraint_list = result.constraints;
    let mut formatted_list = Vec::new();
    for (a, b, c) in constraint_list{
        formatted_list.push(Constraint::new(a,b,c));
    }
    (
        formatted_list,
        result.signals,
        result.header_data.public_outputs,
        result.header_data.public_inputs + result.header_data.private_inputs,
    )
}

fn process_structure(structure: &StructureInfo) -> (HashMap<usize, usize>, HashMap<usize, usize>, HashMap<usize, usize>, usize){
    
    // Process the structure and return maps:
    // Map nodeid -> position in structure.nodes
    // Map node_id -> id_local_equiv_class (position in the array of local equiv classes)
    // Map node_id -> id_structural_equiv_class (position in the array of structural equiv classes)
    // Usize fresh node_id

    let mut local_equivalence_classes = HashMap::new();
    let mut structural_equivalence_classes = HashMap::new();
    let mut id_equiv_class = 0;
    let mut max_node_id = 0;

    let mut nodeid2pos = HashMap::new(); // node id to position in vector
    let mut pos = 0;
    for node in &structure.nodes {
        nodeid2pos.insert(node.node_id, pos);
        pos += 1;
        max_node_id = std::cmp::max(max_node_id, node.node_id);
    }


    for eq_class in &structure.local_equivalency{
        for node_id in eq_class{
            local_equivalence_classes.insert(*node_id, id_equiv_class);
        }
        id_equiv_class += 1;
    }

    id_equiv_class = 0;
    for eq_class in &structure.structural_equivalency{
        for node_id in eq_class{
            structural_equivalence_classes.insert(*node_id, id_equiv_class);
        }
        id_equiv_class += 1;
    }

    (nodeid2pos, local_equivalence_classes, structural_equivalence_classes, max_node_id + 1)
}


fn get_constraint_info_component(info: &BTreeMap<usize, String>, c: usize) -> (usize, String,usize){
    let mut previous_c = 0;
    let mut previous_comp = "";
    for (init, comp) in info{
        if *init > c{
            return (previous_c, previous_comp.to_string(), *init);
        } else{
            previous_c = *init;
            previous_comp = comp;
        }
    }
    (previous_c, previous_comp.to_string(), 0)

}

fn main() {
    let result = start();
    if result.is_err() {
        eprintln!("{}", Colour::Red.paint("previous errors were found"));
        std::process::exit(1);
    } else {
        println!("{}", Colour::Green.paint("Everything went okay"));
        //std::process::exit(0);
    }
}

fn start() -> Result<(), ()> {
    let user_input = Input::new()?;
    
    let (constraints,
        signals,
        n_outputs,
        n_inputs)
        = process_constraints(&user_input.input_r1cs);
    
    // Read the structure
    let mut structure  = if user_input.input_structure.is_some(){
        let input_str = &format!("{}", user_input.input_structure.as_ref().unwrap().display());
        read_structure(input_str).unwrap()
    } else{
        generate_empty_structure(constraints.len(), signals.len(), n_outputs, n_inputs)
    };

    let (
        mut nodeid2pos, 
        local_equivalence_classes, 
        structural_equivalence_classes,
        mut max_node_id
    ) = process_structure(&structure);

    let timeout: u64 = user_input.timeout;
    let apply_deduction_assigned: bool = user_input.apply_deduction_assigned;


    let starting_constraints = if user_input.original_structure.is_some(){
        let init_constraints = read_original_structure(user_input.original_structure.as_ref().unwrap()).unwrap();
        Some(init_constraints)
    } else{
        None
    };

    let field = user_input.prime;

    let solver = if user_input.use_civer{
        PossibleSolver::CIVER
    } else if user_input.use_picus{
        PossibleSolver::PICUS
    } else{
        unreachable!()
    };

    let equivalence_mode = match user_input.equivalence_mode{
        0 => EquivalenceMode::None,
        1 => EquivalenceMode::Local,
        2 => EquivalenceMode::Total,
        _ => unreachable!()
    };
    

    let clustering_size = user_input.clustering_size;
    let target_size = user_input.target_size;

    
    let mut results = ResultInfo{
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

    };

    for node in &structure.nodes{
        process_node(node, 
            &structure, 
            &constraints, 
            &local_equivalence_classes,
            &structural_equivalence_classes,
            &nodeid2pos, 
            &field, 
            timeout, 
            solver,
            apply_deduction_assigned,
            &mut results
        );
    }

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
                solver,
                equivalence_mode,
                target_size,
                apply_deduction_assigned,
                &mut results,
            );
        }
        to_study_again = reconsider_big_nodes(&structure, &nodeid2pos, &mut results, clustering_size);
    }
    


    // Just to compute extra info (constraints and original structure)
    compute_info_constraints(&mut results, &structure, &nodeid2pos);

    if starting_constraints.is_some(){
        compute_info_fails_original_template(
            &mut results, 
            &structure, 
            &nodeid2pos, 
            starting_constraints.as_ref().unwrap());
    }

    // print the results    
    print_pretty_results(&results);
    Result::Ok(())
}

fn process_node(
    node: &NodeInfo,
    structure: &StructureInfo,
    constraints: &Vec<Constraint<usize>>,
    local_equivalence_classes: &HashMap<usize, usize>,
    structural_equivalence_classes: &HashMap<usize, usize>,
    //studied_eq_classes: &mut HashMap<usize, PossibleResult>,
    nodeid2pos: &HashMap<usize, usize>,
    field: &BigInt,
    timeout: u64,
    solver: PossibleSolver,
    apply_deduction_assigned: bool,
    results: &mut ResultInfo,
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

        println!("LOG: Considering node {} with {} constraints", node.node_id, node.constraints.len());

            
    // If the equivalence class of the node has not been studied, we process it.
    let (result, _, n_rounds, _logs) = check_tags(
        node,
        &field,
        timeout,
        &structure.nodes,
        &nodeid2pos, 
        &constraints ,
        solver,
        apply_deduction_assigned
    );
        
        //for log in logs{
        //    println!("{}", log);
        //}
        
    if n_rounds == 0{
    	// No need to study children, can generalize to all the local equivalence class
    	 let id_class = local_equivalence_classes.get(&node.node_id).unwrap();
         let local_eq_class = &structure.local_equivalency[*id_class];
         update_result_for_class(&result, local_eq_class, results);
    } else{
        // Considering children, only generalize to the structural equivalence class
         let id_class = structural_equivalence_classes.get(&node.node_id).unwrap();
         let structural_eq_class = &structure.structural_equivalency[*id_class];
        update_result_for_class(&result, structural_eq_class, results);
    }

}


fn decompose_and_study(
    node_id: usize,
    structure: &mut StructureInfo,
    constraints: &Vec<Constraint<usize>>,
    nodeid2pos: &mut HashMap<usize, usize>,
    max_node_id: &mut usize,
    field: &BigInt,
    timeout: u64,
    solver: PossibleSolver,
    equivalence_mode: EquivalenceMode,
    target_size: usize,
    apply_deduction_assigned: bool,
    results: &mut ResultInfo,
) {
    println!("LOG: Reconsidering again node {}", node_id);
    let node_info = structure.nodes.get(*nodeid2pos.get(&node_id).unwrap()).unwrap();

    //print_node_info(node_info, constraints);
    let mut constraints_original_index = Vec::new();
    let mut constraints_copy = Vec::new();
    for c_id in &node_info.constraints{
        let c = &constraints[*c_id];
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
    

    let structure_reader = decompose_node(
        field, 
        &constraints_copy, 
        &node_info.input_signals, 
        &node_info.output_signals,
        None,
        Some(target_size as f64),
        equivalence_mode,
        GraphBackend::GraphRS,
        Some(&constraints_original_index),
        None,
        None, // minimum_equivalence_size: Option<usize> -- flag for minimum size to try equivalence
        None, // equivalence_comparison_budget: Option<usize> -- flag for maximum number of comparisons made -- use only one
        false
    );  


    let mut new_structure = transform_structure_reader(structure_reader);
    let (new_nodeid2pos, 
        local_equivalence_classes, 
        structural_equivalence_classes,
        new_max_node_id
    ) = process_structure(&new_structure);

    println!("LOG: node decomposed in {} new nodes", new_nodeid2pos.len());

    let mut new_results = ResultInfo{
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
            println!("LOG: printing info node with 0 constraints");
            print_node_info(node, constraints);
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
            &mut new_results
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

    println!("Added the info to the results");

}
// To get the nodes that were too big and need to be studied again
fn reconsider_big_nodes(
    structure: &StructureInfo,
    nodeid2pos: &HashMap<usize, usize>,
    results: &mut ResultInfo,
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


fn update_result_for_class(node_result: &PossibleResult, equiv_class: &Vec<usize>, results: &mut ResultInfo){
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

// Returns the total number of constraints and the total number of constraints in verified components
fn compute_info_constraints(
    results: &mut ResultInfo, 
    structure: &StructureInfo,
    nodeid2pos: &HashMap<usize, usize>,
){
    let mut number_of_constraints = 0;
    let mut number_of_constraints_verified = 0;
    for (node_id, result) in &results.studied_nodes{
        let node_info = &structure.nodes[nodeid2pos[node_id]];
        number_of_constraints += node_info.constraints.len();
        if *result == PossibleResult::VERIFIED {
            number_of_constraints_verified += node_info.constraints.len();
        }
    }
    results.total_constraints = number_of_constraints;
    results.verified_constraints = number_of_constraints_verified;
}

fn compute_info_fails_original_template(
    results: &mut ResultInfo, 
    structure: &StructureInfo,
    nodeid2pos: &HashMap<usize, usize>,
    original_structure: &BTreeMap<usize, String>
){
    let mut original_unverified_templates = HashSet::new();
    let mut number_unverified_orig_constraints = 0;
    let mut number_unverified_orig_constraints_noreps = 0;

    for node_id in &results.failed_nodes{
        let node_info = &structure.nodes[nodeid2pos[node_id]];
        for c in &node_info.constraints{
            let (prev_c, component, mut last_c) = 
                get_constraint_info_component(original_structure, *c);
            if last_c == 0{
                last_c = results.total_constraints;
            }
            //number_unverified_orig_constraints += last_c - prev_c;
            if !original_unverified_templates.contains(&component){
                number_unverified_orig_constraints_noreps += last_c - prev_c;
            }
            original_unverified_templates.insert(component.clone());
        }       
    }
    for node_id in &results.unknown_nodes{
        let node_info = &structure.nodes[nodeid2pos[node_id]];
        for c in &node_info.constraints{
            let (prev_c, component, mut last_c) = 
                get_constraint_info_component(original_structure, *c);
            if last_c == 0{
                last_c = results.total_constraints;
            }
            //number_unverified_orig_constraints += last_c - prev_c;
            if !original_unverified_templates.contains(&component){
                number_unverified_orig_constraints_noreps += last_c - prev_c;
            }
            original_unverified_templates.insert(component.clone());
        }       
    }

    for node_id in &results.unknown_undivisible_nodes{
        let node_info = &structure.nodes[nodeid2pos[node_id]];
        for c in &node_info.constraints{
            let (prev_c, component, mut last_c) = 
                get_constraint_info_component(original_structure, *c);
            if last_c == 0{
                last_c = results.total_constraints;
            }
            //number_unverified_orig_constraints += last_c - prev_c;
            if !original_unverified_templates.contains(&component){
                number_unverified_orig_constraints_noreps += last_c - prev_c;
            }
            original_unverified_templates.insert(component.clone());
        }       
    }

    //results.number_unverified_orig_constraints = Some(number_unverified_orig_constraints);
    results.number_unverified_orig_constraints_noreps = Some(number_unverified_orig_constraints_noreps);    
    results.fails_original_templates = Some(original_unverified_templates);
}

fn print_pretty_results(results: &ResultInfo){

    println!();

    println!("--------------------------------------------");
    println!("--------------------------------------------");
    println!("------ ZK-GENVER VERIFICATION RESULTS ------");
    println!("--------------------------------------------");
    println!("--------------------------------------------\n");

    if results.failed_nodes.is_empty() && results.unknown_nodes.is_empty(){
        println!("-> All nodes satisfy weak safety :)");
    } else{
    	println!("-> ZK-GENVER could not verify weak safety of all components");
    	if !results.failed_nodes.is_empty(){
        	println!("Nodes that do not satisfy weak safety: ");
        	for c in &results.failed_nodes{
    			println!("    - Node {}, ", c);
    		}
        }
    	if !results.unknown_nodes.is_empty() || !results.unknown_undivisible_nodes.is_empty(){
        	println!("Nodes that timeout when checking weak-safety: ");
        	for c in &results.unknown_nodes{
    			println!("    - Node {}, ", c);
    		}
            for c in &results.unknown_undivisible_nodes{
    			println!("    - Node {}, ", c);
    		}
        }
    }
    println!("  * Number of verified nodes (weak-safety): {}",  results.verified_nodes.len());
    println!("  * Number of failed nodes (weak-safety): {}",  results.failed_nodes.len());        
    println!("  * Number of timeout nodes (weak-safety): {}",  results.unknown_nodes.len()+results.unknown_undivisible_nodes.len());
    println!("  * Percentage of constraints that are in verified nodes : {}%", (results.verified_constraints as f64 / results.total_constraints as f64) * 100.0);
    println!("\n\n\n");
    if results.fails_original_templates.is_some(){
        let original_fails = results.fails_original_templates.as_ref().unwrap();
        //let number_unverified_orig_constraints = results.number_unverified_orig_constraints.unwrap();
        let number_unverified_orig_constraints_noreps = results.number_unverified_orig_constraints_noreps.unwrap();
  
        if !original_fails.is_empty(){
            println!("The constraints that are not verified are in the following original components of the circuit: ");
            for c in original_fails{
                println!("    - {}, ", c);
            }
            //println!("The total number of constraints in these templates is: {} ({}%)", number_unverified_orig_constraints, (number_unverified_orig_constraints as f64 / results.total_constraints as f64) * 100.0);
            println!("The number of constraints in these templates is: {}", number_unverified_orig_constraints_noreps);
            println!("\n\n\n");

        }

    }
}
