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



use ansi_term::Colour;

struct ResultInfo{
    verified_nodes: HashSet<usize>,
    failed_nodes: HashSet<usize>,
    unknown_nodes: HashSet<usize>,
    studied_nodes: HashMap<usize, PossibleResult>,
    total_constraints: usize,
    verified_constraints: usize,
    fails_original_templates: Option<HashSet<String>>,// include which constraints fail in each component or not?
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

fn process_structure(
    input: &Option<PathBuf>,
    n_constraints: usize,
    n_signals: usize,
    n_outputs: usize,
    n_inputs: usize,
) -> 
(StructureInfo, HashMap<usize, usize>, HashMap<usize, usize>, HashMap<usize, usize>){
    // Read the structure
    let structure  = if input.is_some(){
        let input_str = &format!("{}", input.as_ref().unwrap().display());
        read_structure(input_str).unwrap()
    } else{
        generate_empty_structure(n_constraints, n_signals, n_outputs, n_inputs)
    };
    
    // Process the structure and return maps:
    // Map nodeid -> position in structure.nodes
    // Map node_id -> id_local_equiv_class (position in the array of local equiv classes)
    // Map node_id -> id_structural_equiv_class (position in the array of structural equiv classes)

    let mut local_equivalence_classes = HashMap::new();
    let mut structural_equivalence_classes = HashMap::new();
    let mut id_equiv_class = 0;

    let mut nodeid2pos = HashMap::new(); // node id to position in vector
    let mut pos = 0;
    for node in &structure.nodes {
        nodeid2pos.insert(node.node_id, pos);
        pos += 1;
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

    (structure, nodeid2pos, local_equivalence_classes, structural_equivalence_classes)
}


fn get_constraint_info_component(info: &BTreeMap<usize, String>, c: usize) -> (usize, String){
    let mut previous_c = 0;
    let mut previous_comp = "";
    for (init, comp) in info{
        if *init > c{
            return (previous_c, previous_comp.to_string());
        } else{
            previous_c = *init;
            previous_comp = comp;
        }
    }
    (previous_c, previous_comp.to_string())

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
    
    let (
        structure,
        nodeid2pos, 
        local_equivalence_classes, 
        structural_equivalence_classes
    ) = process_structure(&user_input.input_structure,
        constraints.len(),
        signals.len(),
        n_outputs,
        n_inputs
    );

    let timeout: u64 = user_input.timeout;
    
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

    
    let mut results = ResultInfo{
        verified_nodes: HashSet::new(),
        failed_nodes: HashSet::new(),
        unknown_nodes: HashSet::new(),
        studied_nodes: HashMap::new(),
        total_constraints: 0,
        verified_constraints: 0,
        fails_original_templates: None,
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
            &mut results
        );
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
    results: &mut ResultInfo,
) {

    if results.studied_nodes.contains_key(&node.node_id) {
        // If the node has already been studied, we skip it.
        return;
    }
            
    // If the equivalence class of the node has not been studied, we process it.
    let (result, _, n_rounds, _logs) = check_tags(
        node,
        &field,
        timeout,
        &structure.nodes,
        &nodeid2pos, 
        &constraints ,
        solver
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
    for node_id in &results.failed_nodes{
        let node_info = &structure.nodes[nodeid2pos[node_id]];
        for c in &node_info.constraints{
            let (_, component) = 
                get_constraint_info_component(original_structure, *c);
            original_unverified_templates.insert(component.clone());
        }       
    }
    for node_id in &results.unknown_nodes{
        let node_info = &structure.nodes[nodeid2pos[node_id]];
        for c in &node_info.constraints{
            let (_, component) = 
                get_constraint_info_component(original_structure, *c);
            original_unverified_templates.insert(component.clone());
        }       
    }

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
    	if !results.unknown_nodes.is_empty(){
        	println!("Nodes that timeout when checking weak-safety: ");
        	for c in &results.unknown_nodes{
    			println!("    - Node {}, ", c);
    		}
        }
    }
    println!("  * Number of verified nodes (weak-safety): {}",  results.verified_nodes.len());
    println!("  * Number of failed nodes (weak-safety): {}",  results.failed_nodes.len());        
    println!("  * Number of timeout nodes (weak-safety): {}",  results.unknown_nodes.len());
    println!("  * Percentage of constraints that are in verified nodes : {}%", (results.verified_constraints as f64 / results.total_constraints as f64) * 100.0);
    println!("\n\n\n");
    if results.fails_original_templates.is_some(){
        let original_fails = results.fails_original_templates.as_ref().unwrap();
        if !original_fails.is_empty(){
            println!("The constraints that are not verified are in the following original components of the circuit: ");
            for c in original_fails{
                println!("    - {}, ", c);
            }
            println!("\n\n\n");

        }

    }
}
