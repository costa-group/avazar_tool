mod circuit_implementation;
mod constraint_implementation;

use circom_algebra::num_bigint::BigInt;
use std::collections::{HashSet, HashMap};

pub struct ACIRConstraint {
    mult: HashMap<(usize, usize), BigInt>,
    linear: HashMap<usize, BigInt>,
    constant: Option<BigInt>
}

pub struct ACIRCircuit {
    prime: BigInt,
    constraints: Vec<ACIRConstraint>,
    input_signals: HashSet<usize>,
    output_signals: HashSet<usize>,
    signals: HashSet<usize>
}