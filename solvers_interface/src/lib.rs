pub mod picus_interface;
pub mod ffsol_interface;
pub mod cvc5_interface;
mod smt2_utils;

use std::collections::{HashSet, LinkedList};
use num_bigint_dig::BigInt;

use circom_algebra::algebra::Constraint;

#[derive(PartialEq, Eq, Clone, Copy)] 
pub enum PossibleSolver{
    PICUS, CIVER, FFSOL, CVC5
}


#[derive(PartialEq, Eq, Clone, Copy, Debug)] 
pub enum PossibleResult{
    VERIFIED, UNKNOWN, FAILED, NOSTUDIED, NOTHING
} impl PossibleResult {
    pub fn finished_verification(&self) -> bool{
        self == &PossibleResult::VERIFIED || 
        self == &PossibleResult::NOSTUDIED || 
        self == &PossibleResult::NOTHING || 
        self == &PossibleResult::UNKNOWN
    }
    pub fn result_to_str(&self)-> String{
        match self{
            &PossibleResult::FAILED => {format!("FAILED -> FOUND COUNTEREXAMPLE\n")}
            &PossibleResult::UNKNOWN => {format!("UNKNOWN -> VERIFICATION TIMEOUT\n")}
            &PossibleResult::NOTHING => {format!("NOTHING TO VERIFY\n")}
            _ => {format!("VERIFIED\n")}
        }            
    }
}


pub struct SafetyVerification {
    pub template_name: String,
    pub signals: LinkedList<usize>,
    pub inputs: Vec<usize>,
    pub outputs: Vec<usize>,
    pub constraints: Vec<Constraint<usize>>,
    pub implications_safety: Vec<(Vec<usize>, Vec<usize>)>,
    pub field: BigInt,
    pub verification_timeout: u64,
    pub added_nodes: HashSet<usize>,
    pub apply_deduction_assigned: bool,
}

impl SafetyVerification{

    pub fn new(
        template_name: &String,
        signals: LinkedList<usize>,
        inputs: Vec<usize>,
        outputs: Vec<usize>,
        constraints: Vec<Constraint<usize>>,
        implications_safety: Vec<(Vec<usize>, Vec<usize>)>,
        field: &BigInt,
        verification_timeout: u64, 
        apply_deduction_assigned: bool,
    ) -> SafetyVerification {
        let mut fixed_constraints = Vec::new();
        for mut c in constraints{
            Constraint::fix_constraint(&mut c, field);
            fixed_constraints.push(c);
        }

        SafetyVerification {
            template_name: template_name.clone(),
            signals,
            inputs,
            outputs, 
            implications_safety,
            constraints: fixed_constraints,
            field: field.clone(),
            verification_timeout, 
            added_nodes: HashSet::new(),
            apply_deduction_assigned,
        }
    }
    
}



pub struct EquivalenceVerification {
    pub template_name: String,
    pub signals_1: Vec<usize>,
    pub signals_2: Vec<usize>,
    pub inputs_1: Vec<usize>,
    pub outputs_1: Vec<usize>,
    pub inputs_2: Vec<usize>,
    pub outputs_2: Vec<usize>,
    pub constraints_1: Vec<Constraint<usize>>,
    pub constraints_2: Vec<Constraint<usize>>,
    pub implications_equivalence: Vec<(Vec<usize>, Vec<usize>)>,
    pub field: BigInt,
    pub verification_timeout: u64,
    pub added_nodes: HashSet<usize>,
    pub apply_deduction_assigned: bool,
}

impl EquivalenceVerification{

    pub fn new(
        template_name: &String,
        signals_1: Vec<usize>,
        signals_2: Vec<usize>,
        inputs_1: Vec<usize>,
        inputs_2:Vec<usize>,
        outputs_1: Vec<usize>,
        outputs_2:Vec<usize>,
        constraints_1: Vec<Constraint<usize>>,
        constraints_2: Vec<Constraint<usize>>,
        implications_equivalence: Vec<(Vec<usize>, Vec<usize>)>,
        field: &BigInt,
        verification_timeout: u64, 
        apply_deduction_assigned: bool,
    ) -> EquivalenceVerification {
        let mut fixed_constraints_1 = Vec::new();
        for mut c in constraints_1{
            Constraint::fix_constraint(&mut c, field);
            fixed_constraints_1.push(c);
        }
        let mut fixed_constraints_2 = Vec::new();
        for mut c in constraints_2{
            Constraint::fix_constraint(&mut c, field);
            fixed_constraints_2.push(c);
        }

        EquivalenceVerification {
            template_name: template_name.clone(),
            signals_1,
            signals_2,
            inputs_1,
            inputs_2,
            outputs_1,
            outputs_2, 
            implications_equivalence,
            constraints_1: fixed_constraints_1,
            constraints_2: fixed_constraints_2,
            field: field.clone(),
            verification_timeout, 
            added_nodes: HashSet::new(),
            apply_deduction_assigned,
        }
    }
    
}



