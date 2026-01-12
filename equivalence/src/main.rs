use clap::Parser;
use std::time::{Instant};

use utils::read_r1cs::{R1CSData};
use circuits_and_constraints::circuit::{Circuit};
use circuits_and_constraints::utils::{circuit_shuffle};

mod argument_parsing;
mod encoding;
pub mod fingerprinting;
pub mod compare_circuits;

use argument_parsing::Args;
use compare_circuits::{compare_circuits};

fn main() {
    let args = Args::parse();
    if args.test {
        println!("{} {:?}", args.file1path, args.file2path);

        let parsing_shuffling_timer = Instant::now();
        let (r1cs, r1cs_shuffled): (R1CSData, R1CSData) = circuit_shuffle(&args.file1path, 25565, true, true, true, !args.dont_shuffle_internals).ok().unwrap();
        println!("shuffled, {:?}", parsing_shuffling_timer.elapsed());
        // dummy test expand later

        println!("{:?}", compare_circuits(&[&r1cs, &r1cs_shuffled], args.debug))
    } else {
        println!("{} {:?}", args.file1path, args.file2path);

        let  (r1cs1, r1cs2) = (R1CSData::parse_file(&args.file1path).ok().unwrap(), R1CSData::parse_file(&args.file2path.unwrap()).ok().unwrap());

        println!("{:?}", compare_circuits(&[&r1cs1, &r1cs2], args.debug))
    }
}