pub mod picus_interface;
use std::collections::{HashSet, LinkedList};
use num_bigint_dig::BigInt;

use circom_algebra::algebra::Constraint;

#[derive(PartialEq, Eq, Clone, Copy)] 
pub enum PossibleSolver{
    PICUS, CIVER
}


#[derive(PartialEq, Eq, Clone, Debug)] 
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
    pub internal_solver: String
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
        internal_solver: &str
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
            internal_solver: internal_solver.clone().to_string()
        }
    }
    
}
