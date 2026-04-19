use std::collections::{HashMap, HashSet, BTreeMap};
use solvers_interface::{CorrectnessVerification, PossibleResult, PossibleSolver};
use crate::Input;
use crate::processing_utils::*;


use solvers_interface::ffsol_interface;
use solvers_interface::cvc5_interface;

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

pub fn prove_correctness(user_input: Input) -> Result<(), ()> {    
    
    let (constraints,
        signals,
        n_outputs,
        n_inputs)
        = process_constraints(&user_input.input_r1cs);

    let (formula_aux,
        signals_aux,
        outputs_aux,
        inputs_aux)
        = process_smt_formula(&user_input.check_correctness.unwrap());
    
    let mut light_check = false;
    let mut outputs = Vec::new();
    let mut inputs = Vec::new();
        
    if n_outputs != outputs_aux.len(){
        light_check = true;
    } else{
        outputs= (1..n_outputs+1).collect();
    }
    if n_inputs != inputs_aux.len(){
        light_check = true;
    } else{
        inputs = (n_outputs+1..n_outputs+n_inputs+1).collect();
    }


    let field = user_input.prime;

    if !(user_input.solver_option==PossibleSolver::FFSOL||user_input.solver_option==PossibleSolver::CVC5){
        println!("Z3, CIVER and PICUS cannot be used to check correctness. Use FFSOL or CVC5 instead");
        return Err(());
    };

    let result= if light_check{
        PossibleResult::FAILED
    } else{

        let to_study = CorrectnessVerification::new(
            &"main".to_string(),
            signals,
            signals_aux,
            inputs.clone(),
            inputs_aux,
            outputs.clone(),
            outputs_aux,
            constraints,
            formula_aux,
            Vec::new(),
            &field,
            user_input.timeout,
            user_input.flag_verbose
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
