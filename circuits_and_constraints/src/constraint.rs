use circom_algebra::num_bigint::BigInt;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash};
use std::cmp::{Eq};
use rand::Rng;
use std::fmt::Debug;
use rustsat::instances::ObjectVarManager;
use rustsat::types::Clause;

pub trait Constraint {

    type Fingerprint<'a, T: Hash + Eq + Default + Copy + Ord + Debug>: Hash + Eq + Clone + Debug where Self: 'a;

    fn normalise(&self, prime: &BigInt) -> Vec<Self> where Self: Sized;
    fn signals(&self) -> HashSet<usize>;
    fn fingerprint<'a, T: Hash + Eq + Default + Copy + Ord + Debug>(&'a self, fingerprint: &mut Option<Self::Fingerprint<'a, T>>, signal_to_fingerprint: &HashMap<usize, T>) -> ();
    fn fingerprint_signal<'a, T: Hash + Eq + Default + Copy + Ord + Debug>(
        signal: &usize, 
        fingerprint: &mut Option<Self::Fingerprint<'a, T>>,
        normalised_constraints: &'a Vec<Self>, 
        normalised_constraint_to_fingerprints: &HashMap<usize, T>, 
        prev_signal_to_fingerprint: &HashMap<usize, T>, 
        signal_to_normi: &HashMap<usize, Vec<usize>>
    ) -> () where Self: 'a + Sized;
    
    fn is_nonlinear(&self) -> bool;
    fn is_ordered(&self) -> bool;
    fn singular_class_requires_additional_constraints() -> bool;

    fn encode_single_norm_pair(
        norms: &[&Self; 2],
        is_ordered: bool,
        signal_pair_encoder: &mut ObjectVarManager,
        fingerprint_to_signals: &[HashMap<usize, Vec<usize>>; 2],
        signal_to_fingerprint: &[HashMap<usize, usize>; 2],
        is_singular_class: bool
    ) -> Vec<Clause>;
}

pub trait ShuffleConstraint {
    fn add_random_constant_factor(&mut self, rng: &mut impl Rng, field: &BigInt) -> ();
    fn shuffle_constraint_internals(&mut self, rng: &mut impl Rng) -> ();
}