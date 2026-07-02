use std::collections::BTreeMap;
use std::collections::{HashSet, HashMap};
use solvers_interface::{CorrectnessVerification, PossibleResult, PossibleSolver};
use utils::read_specification::MacroDef;
use crate::Input;
use crate::processing_utils::*;
use utils::read_correspondence::read_signal_correspondence;
use utils::structure::*;
use regex::Regex;
use circom_algebra::algebra::Constraint;
use num_bigint_dig::BigInt;

use indexmap::IndexMap;


use crate::correctness::processing_correctness_utils::{process_correspondence_node_macro, build_macros, get_all_signals_macro, get_equivalent_signal_in_macro, get_equivalent_subcomponent_signal_in_macro, get_input_signals_macro};

use crate::report;
use crate::correctness::modular_reasoning::check_node;


#[derive(Default)]
pub struct ResultInfoCorrectness{
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




pub fn prove_correctness(user_input: Input) -> Result<(), ()> {    
    
    let (constraints,
        signals,
        n_outputs,
        n_inputs)
        = process_constraints(&user_input.input_r1cs);

    let outputs: Vec<usize> = (1..n_outputs+1).collect();
    let inputs: Vec<usize> = (n_outputs+1..n_outputs+n_inputs+1).collect();
        

    // Read the structure
    let structure  = if user_input.input_structure.is_some(){
        let input_str = &format!("{}", user_input.input_structure.as_ref().unwrap().display());
        read_structure(input_str).unwrap()
    } else{
        generate_empty_structure(constraints.len(), signals.len(), n_outputs, n_inputs)
    };
    let (
        nodeid2pos, 
        local_equivalence_classes, 
        structural_equivalence_classes,
        mut max_node_id
    ) = process_structure(&structure);


    // Read the signal names
    let input_correspondence_str = &format!("{}", user_input.input_correspondence.as_ref().unwrap().display());
    let (pos_to_signal_name, signal_name_to_pos) = read_signal_correspondence(input_correspondence_str).unwrap();

    let (macros, main_section) = process_smt_formula(user_input.check_correctness.as_ref().unwrap());
    let main_macro = macros.get("main").expect("specification has no 'main' macro");


    let formula_str: &str = &main_macro.formula.to_string();

    let main_template = if let Some(idx) = formula_str.find('@') {
        let till_end = &formula_str[idx..];
        
        let first_split = till_end.split_whitespace().next().unwrap_or("");
        first_split.trim_matches(|c| c == ')' || c == '(' || c == ' ').to_string()
    } else {
        unreachable!()
    };



    let mut correspondence_nodeid_macro: HashMap<usize, String> = HashMap::new();
    correspondence_nodeid_macro.insert(0, main_template.to_string());

    process_correspondence_node_macro(&structure, &nodeid2pos, &macros,0,&main_template.to_string(), &mut correspondence_nodeid_macro);
    
    /* 
    let signals_aux: Vec<String> = get_all_signals_macro(main_macro);
    let mut outputs_aux = Vec::new();
    for out in &outputs{
        let equiv_out = get_equivalent_signal_in_macro(*out, main_macro, &pos_to_signal_name);
        outputs_aux.push(equiv_out);
    }
    
    let inputs_aux  = get_input_signals_macro(inputs.len(), main_macro);
    let formula_aux: Vec<String> = vec![main_macro.formula.clone()];

    let to_include: HashSet<String> = macros.keys().cloned().collect();
    let macros: Vec<String> = build_macros(&macros, &to_include);
    */

    let field = user_input.prime.clone();

    if !(user_input.solver_option==PossibleSolver::FFSOL||user_input.solver_option==PossibleSolver::CVC5||user_input.solver_option==PossibleSolver::YICES||user_input.solver_option==PossibleSolver::NIAZ3){
        println!("Z3, CIVER and PICUS cannot be used to check correctness. Use FFSOL, CVC5, YICES or NIAZ3 instead");
        return Err(());
    };

        
    let timeout: u64 = user_input.timeout;
    let apply_deduction_assigned: bool = user_input.apply_deduction_assigned;
    let include_niaz3_in_all: bool = user_input.include_niaz3_in_all;
    let apply_predecessors: bool = user_input.apply_predecessors;
    let apply_bidirectional: bool = user_input.apply_bidirectional;




    
    let mut results = ResultInfoCorrectness{
        verified_nodes: HashSet::new(),
        failed_nodes: HashSet::new(),
        unknown_nodes: HashSet::new(),
        studied_nodes: HashMap::new()
    };

    for node in structure.nodes.iter().rev(){
        process_node(&node,
            &structure,
            &constraints,
            &macros,
            &correspondence_nodeid_macro,
            &pos_to_signal_name,
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
            user_input.flag_verbose,
            "main",
        );
    }

    // print the results
    print_pretty_results(&results, &structure, &nodeid2pos);

    if let Some(report_path) = &user_input.report_output {
        let rep = build_equivalence_report(&user_input, &results, &structure, &nodeid2pos);
        report::write_report(&rep, report_path);
    }

    Result::Ok(())
}


fn process_node(
    node: &NodeInfo,
    structure: &StructureInfo,
    constraints: &Vec<Constraint<usize>>,
    macros: &IndexMap<String, MacroDef>,
    correspondence_nodeid_macros: &HashMap<usize, String>,
    signal_to_name: &BTreeMap<usize, String>,
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
    results: &mut ResultInfoCorrectness,
    extra_rounds: usize,
    limit_size: usize,
    verbose: bool,
    original_file: &str,
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

    if node.constraints.len() > limit_size {
        println!("Not considering node {} because it is too big", node.node_id);
        results.studied_nodes.insert(node.node_id, PossibleResult::UNKNOWN);
        results.unknown_nodes.insert(node.node_id);
    }

    println!("LOG: Considering node {} with {} constraints", node.node_name, node.constraints.len());
    let no_abstract_fails = false;
            
    // If the equivalence class of the node has not been studied, we process it.
    let (result, _, n_rounds, _extra_rounds_helped, logs, included_nodes) = check_node(
        node,
        &field,
        timeout,
        &structure.nodes,
        &nodeid2pos,
        &constraints,
        &macros,
        &correspondence_nodeid_macros,
        &signal_to_name,
        solver,
        apply_deduction_assigned,
        include_niaz3_in_all,
        apply_predecessors,
        apply_bidirectional,
        no_abstract_fails,
        results,
        extra_rounds,
        verbose,
        original_file,
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


fn update_result_for_class(node_result: &PossibleResult, equiv_class: &Vec<usize>, results: &mut ResultInfoCorrectness){
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



fn build_equivalence_report(
    input: &crate::Input,
    results: &ResultInfoCorrectness,
    structure: &StructureInfo,
    nodeid2pos: &HashMap<usize, usize>,
) -> report::VerificationReport {
    let overall = report::compute_overall(
        results.failed_nodes.is_empty(),
        results.unknown_nodes.is_empty(),
    );

    let summary = report::ReportSummary {
        total_nodes: results.studied_nodes.len(),
        verified_nodes: results.verified_nodes.len(),
        previously_verified_nodes: None,
        failed_nodes: results.failed_nodes.len(),
        timeout_nodes: results.unknown_nodes.len(),
        total_constraints: None,
        verified_constraints: None,
        verified_constraints_pct: None,
    };

    let mut nodes: Vec<report::NodeResult> = results.studied_nodes.iter().map(|(node_id, result)| {
        let node_name = nodeid2pos.get(node_id)
            .and_then(|&pos| structure.nodes.get(pos))
            .map(|n| n.node_name.clone())
            .unwrap_or_default();
        report::NodeResult {
            node_id: *node_id,
            node_name,
            result: report::possible_result_str(result).to_string(),
            num_constraints: None,
            previously_verified: None,
        }
    }).collect();
    nodes.sort_by_key(|n| n.node_id);

    let second_circuit = input.check_equivalence.as_ref()
        .map(|p| p.display().to_string());

    report::VerificationReport {
        check_type: report::CheckType::Equivalence,
        input_circuit: input.input_r1cs.display().to_string(),
        second_circuit,
        solver: report::solver_to_str(input.solver_option).to_string(),
        timeout_ms: input.timeout,
        overall_result: overall,
        summary,
        nodes,
        failed_templates: None,
    }
}



fn print_pretty_results(
    results: &ResultInfoCorrectness,
    structure: &StructureInfo,
    node_id_to_pos: &HashMap<usize, usize>,
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
