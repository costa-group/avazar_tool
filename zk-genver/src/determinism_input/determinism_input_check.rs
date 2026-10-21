
use num_bigint_dig::BigInt;
use std::collections::{HashMap, HashSet, BTreeMap};
use std::hash::Hash;
use circom_algebra::algebra::Constraint;
use utils::read_witness::read_witness;
use utils::structure::*;
use utils::small_utilities::DecomposeOptions;
use crate::Input;
use utils::small_utilities::{GraphBackend, EquivalenceMode, ClusteringPreprocessing};
use crate::processing_utils::*;
use crate::report;
use utils::read_correspondence::read_signal_correspondence;
use solvers_interface::PossibleResult::VERIFIED;

use solvers_interface::{WitnessVerification, PossibleResult, PossibleSolver, cvc5_interface, ffsol_interface, nia_z3_interface, parallel_interface, yices_interface, z3_interface};


pub fn prove_input_determinism(user_input: Input) -> Result<(), ()> {
    let original_file = user_input.input_r1cs
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("")
        .to_string();

    let (constraints,
        signals,
        n_outputs,
        n_inputs,
        field
    ) = process_constraints(&user_input.input_r1cs);

    let timeout: u64 = user_input.timeout;

    let witness = read_witness(&user_input.check_determinism_input.unwrap()).unwrap();


    let problem = WitnessVerification {
        original_file: original_file.clone(),
        template_name: "main".to_string(),
        constraints,
        signals: signals.into_iter().collect(),
        outputs: (1.. n_outputs + 1).collect(),
        inputs: (n_outputs + 1..n_outputs + n_inputs + 1).collect(),
        field,
        witness,
        verification_timeout: timeout,
        verbose: user_input.flag_verbose
    };

    let (result, logs) = prove_witness(&problem, PossibleSolver::FFSOL);

    for l in logs{
        println!("{}", l);
    }
    // print the results
    //print_pretty_results(&results, &structure, &nodeid2pos);



    Result::Ok(())
}



fn prove_witness(
        problem: &WitnessVerification,
        solver: PossibleSolver
)-> (PossibleResult, Vec<String>) {
        match solver{
            PossibleSolver::FFSOL=>{
                ffsol_interface::study_witness(
                    problem,
                    None,
                    &mut ffsol_interface::FfsolConfig::default(problem.verification_timeout, problem.verbose)                )
            },
            /* 
            PossibleSolver::CVC5=>{
                cvc5_interface::study_witness(problem)
            },
            PossibleSolver::YICES=>{
                yices_interface::study_witness(problem)
            },
            PossibleSolver::NIAZ3=>{
                nia_z3_interface::study_witness(problem)
            },
            /* 
            PossibleSolver::Z3=>{
                z3_interface::study_correctness(problem)
            },
            */
            PossibleSolver::ALL=>{
                parallel_interface::study_witness(problem)
            },
            */
            _ => unreachable!()
        }
    }