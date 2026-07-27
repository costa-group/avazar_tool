#![allow(unused_variables)]
use crate::constraint::{Constraint};
use crate::num_bigint::BigInt;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash};
use std::cmp::{Eq};
use std::fmt::Debug;
use rustsat::instances::ObjectVarManager;
use rustsat::types::Clause;

use super::{FormulaAtom};

const EQUIV_ERR_MESSAGE: &str = "Equivalence is not supported for Formula Expressions";

impl Constraint for FormulaAtom {

    type Fingerprint<'a, T: Hash + Eq + Default + Copy + Ord + Debug>: = () where Self: 'a;

    fn normalise(&self, prime: &BigInt) -> Vec<Self> where Self: Sized {unimplemented!("{EQUIV_ERR_MESSAGE}");}
    fn signals(&self) -> HashSet<usize> {self.signals.iter().copied().collect()}
    fn fingerprint<'a, T: Hash + Eq + Default + Copy + Ord + Debug>(&'a self, fingerprint: &mut Option<Self::Fingerprint<'a, T>>, signal_to_fingerprint: &HashMap<usize, T>) -> () {unimplemented!("{EQUIV_ERR_MESSAGE}");}
    fn fingerprint_signal<'a, T: Hash + Eq + Default + Copy + Ord + Debug>(
        signal: &usize, 
        fingerprint: &mut Option<Self::Fingerprint<'a, T>>,
        normalised_constraints: &'a Vec<Self>, 
        normalised_constraint_to_fingerprints: &HashMap<usize, T>, 
        prev_signal_to_fingerprint: &HashMap<usize, T>, 
        signal_to_normi: &HashMap<usize, Vec<usize>>
    ) -> () where Self: 'a + Sized {unimplemented!("{EQUIV_ERR_MESSAGE}");}
    
    fn is_nonlinear(&self) -> bool {unimplemented!("{EQUIV_ERR_MESSAGE}");}
    fn is_ordered(&self) -> bool {false}
    fn is_bridge_constraint(&self, prime: &BigInt, strict: bool) -> bool {unimplemented!("{EQUIV_ERR_MESSAGE}");}
    fn singular_class_requires_additional_constraints() -> bool {true}

    fn encode_single_norm_pair(
        norms: &[&Self; 2],
        is_ordered: bool,
        signal_pair_encoder: &mut ObjectVarManager,
        fingerprint_to_signals: &[HashMap<usize, Vec<usize>>; 2],
        signal_to_fingerprint: &[HashMap<usize, usize>; 2],
        is_singular_class: bool
    ) -> Vec<Clause> {unimplemented!("{EQUIV_ERR_MESSAGE}");}
}

