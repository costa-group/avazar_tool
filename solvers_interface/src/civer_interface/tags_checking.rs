use std::{cmp::max, collections::{HashMap, LinkedList}};
use std::sync::atomic::AtomicBool;
use num_bigint_dig::BigInt;
use crate::{PossibleResult, SafetyVerification};
use circom_algebra::algebra::{EncodableConstraint};
use std::clone::Clone;

use circom_algebra::{modular_arithmetic, algebra::{
    Constraint, ExecutedInequation}};

use super::safety_z3::try_prove_safety_with_z3;
use super::safety_z3::try_prove_safety_with_z3_cancel;

pub type Signal2Bounds = HashMap<usize, ExecutedInequation<usize>>;

pub struct TemplateVerification<C: EncodableConstraint + Clone> {
    pub template_name: String,
    pub signals: LinkedList<usize>,
    pub inputs: Vec<usize>,
    pub outputs: Vec<usize>,
    pub constraints: Vec<C>,
    pub implications_safety: Vec<(Vec<usize>, Vec<usize>)>,
    pub deductions: Signal2Bounds,
    pub substitutions: HashMap<usize, usize>,
    pub field: BigInt,
    pub verbose: bool,
    pub verification_timeout: u64,
    pub apply_deduction_assigned: bool,
}

impl<C: EncodableConstraint + Clone + Sync> TemplateVerification<C>{

    pub fn new(
        problem: &SafetyVerification<C>,
    ) -> TemplateVerification<C> {

        let mut substitutions = HashMap::new();
        for s in &problem.signals{
            substitutions.insert(*s, *s);
        }

        TemplateVerification {
            template_name: problem.template_name.clone(),
            signals: problem.signals.clone(),
            inputs: problem.inputs.clone(),
            outputs: problem.outputs.clone(), 
            implications_safety: problem.implications_safety.clone(),
            deductions: HashMap::new(),
            substitutions,
            constraints: problem.constraints.clone(),
            field: problem.field.clone(),
            verbose: false,      
            verification_timeout: problem.verification_timeout, 
            apply_deduction_assigned: problem.apply_deduction_assigned,
        }
    }

    pub fn initialize_bounds_preconditions(&mut self){
        self.deductions.insert(0, ExecutedInequation{signal: 0, min: BigInt::from(1), max: BigInt::from(1)});

    }


    pub fn deduce(&mut self)-> (PossibleResult, Vec<String>) {        //self.print_pretty_template_verification();
        
        //self.deduce_round();
        //self.normalize();

        let mut logs = Vec::new();

        let result_safety = self.try_prove_safety(&mut logs);

        (result_safety, logs)
    }

    pub fn deduce_with_cancel(&mut self, cancel_flag: &AtomicBool)-> (PossibleResult, Vec<String>) {
        let mut logs = Vec::new();

        let result_safety = self.try_prove_safety_with_cancel(&mut logs, cancel_flag);

        (result_safety, logs)
    }

    // returns the signals where it was able to find new bounds
    pub fn deduce_round(&mut self)-> Vec<usize>{
        let mut new_signal_bounds:Vec<usize> = Vec::new();
        let mut new_signal_bounds_iteration = Vec::new();

        self.initialize_bounds_preconditions();

        let filter_const = std::mem::take(&mut self.constraints);

        for c in filter_const{
            let should_remove = c.deduction_rule_integrity_domain(&mut self.deductions, &self.field); 
            if !should_remove{ 
                self.constraints.push(c);
            }
        } 

        for c in &self.constraints{
            new_signal_bounds_iteration.append(&mut c.deduction_rule_apply_bounds_constraint(&mut self.deductions, &self.field, self.verbose));
        }

        while !new_signal_bounds_iteration.is_empty(){
            new_signal_bounds.append(&mut new_signal_bounds_iteration);
            for c in &self.constraints{
              
                new_signal_bounds_iteration.append(&mut c.deduction_rule_apply_bounds_constraint(&mut self.deductions, &self.field, self.verbose));
            }
        }
        new_signal_bounds
    }

    pub fn try_prove_safety(&mut self, logs: &mut Vec<String>) -> PossibleResult{
        let signals_vec = self.signals.iter().cloned().collect::<Vec<_>>();

        self.deduce_round();
        try_prove_safety_with_z3(
                &self.inputs,
                &self.outputs,
                &signals_vec,
                &self.constraints,
                &self.implications_safety,
                &self.deductions,
                &self.field,
                self.verification_timeout,
                self.apply_deduction_assigned,
                logs,
        )
    }

    pub fn try_prove_safety_with_cancel(&mut self, logs: &mut Vec<String>, cancel_flag: &AtomicBool) -> PossibleResult{
        let signals_vec = self.signals.iter().cloned().collect::<Vec<_>>();

        self.deduce_round();
        try_prove_safety_with_z3_cancel(
                &self.inputs,
                &self.outputs,
                &signals_vec,
                &self.constraints,
                &self.implications_safety,
                &self.deductions,
                &self.field,
                self.verification_timeout,
                self.apply_deduction_assigned,
                logs,
                cancel_flag,
        )
    }
}

// fn deduction_rule_implications_with_deduced_preconditions(
//     deductions: &mut Signal2Bounds, 
//     implication: &ExecutedImplication, 
//     field: &BigInt
// ) -> Vec<usize> {
//     let mut updated_signals = Vec::new();
//     let mut check_preconditions = true;
    
//     for precondition in &implication.left {
//         check_preconditions &= implies_bounds_signal(deductions, precondition.signal, &precondition.min, &precondition.max, field);
//     }
//     if check_preconditions {
//         for postcondition in &implication.right{
//             if update_bounds_signal(deductions, postcondition.signal, postcondition.min.clone(), postcondition.max.clone(), field){
//                 updated_signals.push(postcondition.signal.clone());
//             }
//         }
//     }
//     updated_signals
// }

// (x - a)*(x - b) = 0 ==> a <= x <= b

// pub fn compute_upper_lower_bounds(c: &Constraint<usize>, bounds: &HashMap<usize, ExecutedInequation<usize>>, field: &BigInt) -> (BigInt, BigInt) {
//     let a = c.a();
//     let b = c.b();
//     let c = c.c();
    
    
//     let (lower_limit_a, upper_limit_a) = compute_bounds_linear_expression_strict(bounds, &a, field);
//     let (lower_limit_b, upper_limit_b) = compute_bounds_linear_expression_strict(bounds, &b, field);

//     let (lower_limit_ab, upper_limit_ab) = compute_bounds_product(
//         &lower_limit_a, 
//         &upper_limit_a, 
//         &lower_limit_b, 
//         &upper_limit_b
//     );

 
//     let (lower_limit_c, upper_limit_c) = compute_bounds_linear_expression_strict(bounds, &c, field);
    
//     (&lower_limit_c - &upper_limit_ab, &upper_limit_c - &lower_limit_ab) // lower and upper bounds

// }