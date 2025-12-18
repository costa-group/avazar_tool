
use utils::read_r1cs::{R1CSData, Constraint as ConstraintPart, HeaderData};

mod circuit_implementation;
mod constraint_implementation;

//This struct contained all the sections

pub type R1CSConstraint = (ConstraintPart, ConstraintPart, ConstraintPart);