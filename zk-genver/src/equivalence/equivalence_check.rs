use std::collections::{HashMap, HashSet, BTreeMap};
use solvers_interface::{EquivalenceVerification, PossibleResult, PossibleSolver};
use crate::Input;
use crate::processing_utils::*;


use solvers_interface::ffsol_interface;
use solvers_interface::cvc5_interface;
use solvers_interface::z3_interface;


#[derive(Default)]
pub struct ResultInfoEquivalence{
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
    
    let mut light_check = false;
    let mut outputs = Vec::new();
    let mut inputs = Vec::new();
        
    if n_outputs != n_outputs_aux{
        light_check = true;
    } else{
        outputs= (1..n_outputs+1).collect();
    }
    if n_inputs != n_inputs_aux{
        light_check = true;
    } else{
        inputs = (n_outputs+1..n_outputs+n_inputs+1).collect();
    }


    let field = user_input.prime;

    if user_input.solver_option==PossibleSolver::CIVER||user_input.solver_option==PossibleSolver::PICUS{
        println!("CIVER and PICUS cannot be used to check equivalence. Use Z3,FFSOL or CVC5 instead");
        return Err(());
    };

    let result= if light_check{
        PossibleResult::FAILED
    } else{

        let to_study = EquivalenceVerification::new(
            &"main".to_string(),
            signals,
            signals_aux,
            inputs.clone(),
            inputs,
            outputs.clone(),
            outputs,
            constraints,
            constraints_aux,
            Vec::new(),
            &field,
            user_input.timeout,
            user_input.apply_deduction_assigned,
            user_input.flag_verbose
        );

        let (result,logs) = call_prove_equivalence(&to_study, user_input.solver_option);
        result
    };

    let mut results=ResultInfoEquivalence::default();
    
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

fn call_prove_equivalence(
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
            PossibleSolver::Z3=>{
                z3_interface::study_equivalence(problem)
            },
            _ => unreachable!()
        }
    }



fn print_pretty_results(results: &ResultInfoEquivalence){


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
    			println!("    - Node {}, ", c);
    		}
        }
    	if !results.unknown_nodes.is_empty() {
        	println!("Nodes that timeout when checking equivalence: ");
        	for c in &results.unknown_nodes{
    			println!("    - Node {}, ", c);
    		}
        }
    }
    println!("  * Number of verified nodes (equivalence): {}",  results.verified_nodes.len());
    println!("  * Number of failed nodes (equivalence): {}",  results.failed_nodes.len());        
    println!("  * Number of timeout nodes (equivalence): {}",  results.unknown_nodes.len());

}
