use std::collections::{HashSet, HashMap};
use solvers_interface::{CorrectnessVerification, PossibleResult, PossibleSolver};
use crate::Input;
use crate::processing_utils::*;
use utils::read_correspondence::read_signal_correspondence;
use utils::structure::*;
use utils::read_specification::*;
use std::collections::BTreeMap;
use indexmap::IndexMap;




use solvers_interface::ffsol_interface;
use solvers_interface::cvc5_interface;
use solvers_interface::nia_z3_interface;
use solvers_interface::yices_interface;

#[derive(Default)]
pub struct ResultInfoCorrectness{
    verified_nodes: HashSet<usize>,
    failed_nodes: HashSet<usize>,
    unknown_nodes: HashSet<usize>,
    // unknown_undivisible_nodes: HashSet<usize>,
    // pub studied_nodes: HashMap<usize, PossibleResult>,
    // total_constraints: usize,
    // verified_constraints: usize,
    // fails_original_templates: Option<HashSet<String>>,// include which constraints fail in each component or not?
    // number_unverified_orig_constraints: Option<usize>, // the number of constraints included in the unverified templates
    // number_unverified_orig_constraints_noreps: Option<usize>, // the number of constraints included in the unverified templates
    // unverified_nodes_to_templates: Option<HashMap<usize, HashSet<String>>>,
    // unverified_nodes_to_nodes: Option<HashMap<usize, HashSet<usize>>>,

}


pub fn get_equivalent_subcomponent_signal_in_macro(signal: usize, studied_macro: &MacroDef, signal_to_name: &BTreeMap<usize, String>)->String{

    let complete_signal_name = signal_to_name.get(&signal).unwrap();

    // 1. Look for the LAST '[' from the right side of the string
    let (possible_array_access, remaining) = if complete_signal_name.ends_with(']') {
        if let Some(bracket_idx) = complete_signal_name.rfind('[') {
            // Extract the number inside the final brackets
            let number_str = complete_signal_name[bracket_idx + 1..complete_signal_name.len() - 1].to_string();
            let number = number_str.parse::<usize>().unwrap();
            // Cut off the trailing bracket part for the dot analysis
            let left_side = complete_signal_name[..bracket_idx].to_string();
            (Some(number), left_side)

        } else{
            unreachable!()
        }
    } else{
        (None, complete_signal_name.clone())
    };

    // 2. Get the last two dot-separated segments from what remains
    let last_access: Vec<&str> = remaining.rsplit('.').take(2).collect();
    let signal_name: String = format!("{}.{}", last_access[1], last_access[0]);

    let signal_info_macro = studied_macro.vars_info.get(&signal_name).unwrap();
    if signal_info_macro.is_array(){
        assert!(possible_array_access.is_some());
        signal_info_macro.as_array().unwrap()[possible_array_access.unwrap()].to_string()
    } else{
        signal_info_macro.to_string()
    }

}

pub fn get_equivalent_signal_in_macro(signal: usize, studied_macro: &MacroDef, signal_to_name: &BTreeMap<usize, String>)->String{

    let complete_signal_name = signal_to_name.get(&signal).unwrap();

    // 1. Look for the LAST '[' from the right side of the string
    let (possible_array_access, remaining) = if complete_signal_name.ends_with(']') {
        if let Some(bracket_idx) = complete_signal_name.rfind('[') {
            // Extract the number inside the final brackets
            let number_str = complete_signal_name[bracket_idx + 1..complete_signal_name.len() - 1].to_string();
            let number = number_str.parse::<usize>().unwrap();
            // Cut off the trailing bracket part for the dot analysis
            let left_side = complete_signal_name[..bracket_idx].to_string();
            (Some(number), left_side)

        } else{
            unreachable!()
        }
    } else{
        (None, complete_signal_name.clone())
    };

    // 2. Get the last dot-separated segments from what remains
    let last_access: Vec<&str> = remaining.rsplit('.').take(1).collect();
    let signal_name: String = last_access[0].to_string();

    let signal_info_macro = studied_macro.vars_info.get(&signal_name).unwrap();
    if signal_info_macro.is_array(){
        assert!(possible_array_access.is_some());
        let acc = &signal_info_macro.as_array().unwrap()[possible_array_access.unwrap()];
        acc.as_str().unwrap_or_default().to_string()
    } else{
        signal_info_macro.as_str().unwrap_or_default().to_string()
    }

}

pub fn get_input_signals_macro(number_inputs: usize, studied_macro: &MacroDef) -> Vec<String>{
    let mut inputs = Vec::new();
    let mut input_var_index = 0;
    while inputs.len() < number_inputs{
        let arg_name = format!("%arg{}", input_var_index);
        let signal_info_macro = studied_macro.vars_info.get(&arg_name).unwrap();
        if signal_info_macro.is_array(){
            if let Some(array) = signal_info_macro.as_array() {
                for s in array {
                    let s_str: String = s.as_str().unwrap_or_default().to_string();
                    inputs.push(s_str);
                }
            }
        } else{
            let s_str: String = signal_info_macro.as_str().unwrap_or_default().to_string();
            inputs.push(s_str);
        }

        input_var_index += 1;
    }

    inputs
}

pub fn get_all_signals_macro(studied_macro: &MacroDef)-> Vec<String>{
    let mut signals = Vec::new();
    for v in &studied_macro.params{
        signals.push(v.name.clone());
    }
    signals
}



pub fn build_macros(macro_defs: &IndexMap<String, MacroDef>, to_include: &HashSet<String>)-> Vec<String>{
    pub fn build_call_macro(name: &String, params: &Vec<VarInfo>, mut content: String)-> String{
        //(define-fun @IsZero_0 ((v_0 FFp) (v_7 FFp) (v_1 FFp) (v_2 FFp) (v_3 FFp) (v_4 FFp) (v_5 FFp) (v_6 FFp)) Bool

        
        let mut macro_to_build = format!("(define-fun {} (", name);
        for par in params{
            macro_to_build.push_str(&format!("(macro_{} FF0) ", par.name));
        }
        macro_to_build.push_str(") Bool\n");


       use regex::{Regex, escape};

        for target in params {
            let regex_pattern = format!(r"\b{}\b", escape(&target.name));
            let re = Regex::new(&regex_pattern).unwrap();
    
            let replacement = format!("macro_{}", target.name);
            content = re.replace_all(&content, replacement.as_str()).into_owned();
    
        }
        macro_to_build.push_str(&content);
        macro_to_build.push_str(")\n");
        macro_to_build

    }
    
    let mut macro_formulas = Vec::new();

    for (name_macro, def) in macro_defs{
        if to_include.contains(name_macro){
            let new_macro = build_call_macro(&name_macro, &def.params, def.formula.clone());
            macro_formulas.push(new_macro);

        } else{
            let empty_formula = "";
            let new_macro = build_call_macro(&name_macro, &def.params, empty_formula.to_string());
            macro_formulas.push(new_macro);
        }
    }

    macro_formulas

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

    // Read the signal names
    let input_correspondence_str = &format!("{}", user_input.input_correspondence.as_ref().unwrap().display());
    let (pos_to_signal_name, signal_name_to_pos) = read_signal_correspondence(input_correspondence_str).unwrap();

    let (macros, main_section) = process_smt_formula(&user_input.check_correctness.unwrap());
    let main_macro = macros.get("main").expect("specification has no 'main' macro");
    
    

    
    let signals_aux: Vec<String> = get_all_signals_macro(main_macro);
    let mut outputs_aux = Vec::new();
    for out in &outputs{
        let equiv_out = get_equivalent_signal_in_macro(*out, main_macro, &pos_to_signal_name);
        outputs_aux.push(equiv_out);
    }
    
    let inputs_aux  = get_input_signals_macro(inputs.len(), main_macro);
    let formula_aux: Vec<String> = vec![main_macro.formula.clone()];

    let to_include: HashSet<String> = macros.keys().cloned().collect();
    let macros = build_macros(&macros, &to_include);

    let field = user_input.prime;

    if !(user_input.solver_option==PossibleSolver::FFSOL||user_input.solver_option==PossibleSolver::CVC5||user_input.solver_option==PossibleSolver::YICES||user_input.solver_option==PossibleSolver::NIAZ3){
        println!("Z3, CIVER and PICUS cannot be used to check correctness. Use FFSOL, CVC5, YICES or NIAZ3 instead");
        return Err(());
    };

    let result= if false{
        PossibleResult::FAILED
    } else{

        let to_study = CorrectnessVerification::new(
            &"main".to_string(),
                    &"main".to_string(),

            signals,
            signals_aux,
            inputs,
            inputs_aux,
            outputs.clone(),
            outputs_aux,
            constraints,
            formula_aux,
            Vec::new(),
            &field,
            user_input.timeout,
            user_input.flag_verbose,
            macros,
        );

        let (result,logs) = call_prove_correctness(&to_study, user_input.solver_option);
        result
    };

    let mut results=ResultInfoCorrectness::default();
    
    
    match result{
        PossibleResult::FAILED=>{
            results.failed_nodes.insert(0);
        },
        PossibleResult::UNKNOWN=>{
            results.unknown_nodes.insert(0);
        },
        _=>{
            results.verified_nodes.insert(0);
        },
    }
    

    // print the results    
    print_pretty_results(&results);
    Result::Ok(())
}

fn call_prove_correctness(
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
            }
            _ => unreachable!()
        }
    }



fn print_pretty_results(results: &ResultInfoCorrectness){


    println!();

    println!("--------------------------------------------");
    println!("--------------------------------------------");
    println!("------ ZK-GENVER VERIFICATION RESULTS ------");
    println!("--------------------------------------------");
    println!("--------------------------------------------\n");

    if results.failed_nodes.is_empty() && results.unknown_nodes.is_empty(){
        println!("-> All nodes are correct :)");
    } else{
    	println!("-> ZK-GENVER could not verify the correctness of all components");
    	if !results.failed_nodes.is_empty(){
        	println!("Nodes that are not correct: ");
        	for c in &results.failed_nodes{
    			println!("    - Node {}, ", c);
    		}
        }
    	if !results.unknown_nodes.is_empty() {
        	println!("Nodes that timeout when checking correctness: ");
        	for c in &results.unknown_nodes{
    			println!("    - Node {}, ", c);
    		}
        }
    }
    println!("  * Number of verified nodes (correctness): {}",  results.verified_nodes.len());
    println!("  * Number of failed nodes (correctness): {}",  results.failed_nodes.len());        
    println!("  * Number of timeout nodes (correctness): {}",  results.unknown_nodes.len());

}
