mod input_user;
mod determinism;
mod processing_utils;
mod equivalence;
mod correctness;

use num_bigint_dig::BigInt;
use input_user::Input;
use determinism::determinism_check::prove_safety;
use crate::equivalence::equivalence_check::prove_equivalence;
use crate::correctness::correctness_check::prove_correctness;



use ansi_term::Colour;


fn main() {
    let user_input = Input::new();

    if user_input.is_err(){
        eprintln!("{}", Colour::Red.paint("previous errors were found"));
        std::process::exit(1);
    }

    let user_input = user_input.unwrap();

    let result: Result<(), ()> = if user_input.check_equivalence.is_some(){

        prove_equivalence(user_input)
    } else if user_input.check_correctness.is_some(){
        prove_correctness(user_input)
    } else{
        prove_safety(user_input)
    };

    if result.is_err() {
        eprintln!("{}", Colour::Red.paint("previous errors were found"));
        std::process::exit(1);
    } else {
        println!("{}", Colour::Green.paint("Everything went okay"));
        //std::process::exit(0);
    }
}
