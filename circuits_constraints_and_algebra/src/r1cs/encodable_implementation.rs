use std::collections::{HashMap, HashSet};

use circom_algebra::{encodable_constraint_impl::Signal2Bounds, algebra::EncodableConstraint, num_bigint::BigInt};
use super::{R1CSConstraint};

impl EncodableConstraint for R1CSConstraint {

    fn constraint_to_smt2(&self, signal_to_name: &HashMap<usize, String>) -> String;
    fn take_signals(&self) -> HashSet<&usize>;
    fn take_only_linear_signals(&self) -> HashSet<&usize>;
    fn fix_constraint(&mut self, field: &BigInt) -> ();

    fn deduction_rule_apply_bounds_constraint(&self, deductions: &mut Signal2Bounds,field: &BigInt, _verbose: bool) -> Vec<usize>;
    fn deduction_rule_integrity_domain(&self, deductions: &mut Signal2Bounds, field: &BigInt) -> bool;

    fn declare_constraint_z3(&self, solver: &z3::Solver, signals_to_z3: &HashMap<usize, z3::ast::Int>, field: &BigInt) -> ();
    fn insert_constraint_in_smt_z3(&self, solver: &z3::Solver, signals_to_smt_symbols: &HashMap<usize, z3::ast::Int>, field: &BigInt, deductions: &Signal2Bounds, num_k: usize, p: &z3::ast::Int, _verbose: bool) -> ();
    fn constraint_to_mod0_assert(&self, signal_to_name: &HashMap<usize, String>, prime: &BigInt) -> String;

    fn apply_deduction_assigned(&self, solver: &z3::Solver, signals_to_smt_symbols_1: &HashMap<usize, z3::ast::Int>, signals_to_smt_symbols_2: &HashMap<usize, z3::ast::Int>) -> ();
    fn apply_deduction_rule_homologues(&self, solver: &z3::Solver, signals_to_smt_symbols_1: &HashMap<usize, z3::ast::Int>, signals_to_smt_symbols_2: &HashMap<usize, z3::ast::Int>, deductions: &Signal2Bounds, field: &BigInt, p: &z3::ast::Int) -> ();
}