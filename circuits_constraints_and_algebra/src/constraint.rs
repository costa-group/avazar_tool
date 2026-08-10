use crate::num_bigint::BigInt;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash};
use std::cmp::{Eq};
use rand::Rng;
use std::fmt::Debug;
use rustsat::instances::ObjectVarManager;
use rustsat::types::Clause;

pub trait Constraint {

    /// The type for the fingerprint used in equivalence
    type Fingerprint<'a, T: Hash + Eq + Default + Copy + Ord + Debug>: Hash + Eq + Clone + Debug where Self: 'a;

    /// Normalises self under the given prime
    fn normalise(&self, prime: &BigInt) -> Vec<Self> where Self: Sized;

    /// Returns the signals in self
    fn signals(&self) -> HashSet<usize>;

    /// Calculates fingerprint of self and places it in Options.
    ///
    /// If the fingerprint is in the Option already, then it modifies the signals in the fingerprint with the new signal_to_fingerprint
    fn fingerprint<'a, T: Hash + Eq + Default + Copy + Ord + Debug>(&'a self, fingerprint: &mut Option<Self::Fingerprint<'a, T>>, signal_to_fingerprint: &HashMap<usize, T>) -> ();

    /// Calculates a signal fingerprint based on the previous signal fingerprints and constraint structure.
    fn fingerprint_signal<'a, T: Hash + Eq + Default + Copy + Ord + Debug>(
        signal: &usize, 
        fingerprint: &mut Option<Self::Fingerprint<'a, T>>,
        normalised_constraints: &'a Vec<Self>, 
        normalised_constraint_to_fingerprints: &HashMap<usize, T>, 
        prev_signal_to_fingerprint: &HashMap<usize, T>, 
        signal_to_normi: &HashMap<usize, Vec<usize>>
    ) -> () where Self: 'a + Sized;
    
    /// Checks is self is nonlinear
    fn is_nonlinear(&self) -> bool;

    /// Checks if self, when normalised, has a singular order
    fn is_ordered(&self) -> bool;

    /// Checks if self is a bridge constraint, i.e. a constraint of the form x = y
    fn is_bridge_constraint(&self, prime: &BigInt, strict: bool) -> bool;

    /// Checks if self is a constraint type that requires additional constraints when encoded into equivalence
    fn singular_class_requires_additional_constraints() -> bool;

    /// Encodes, for a single norm pair, that the two are equivalent into SAT
    fn encode_single_norm_pair(
        norms: &[&Self; 2],
        is_ordered: bool,
        signal_pair_encoder: &mut ObjectVarManager,
        fingerprint_to_signals: &[HashMap<usize, Vec<usize>>; 2],
        signal_to_fingerprint: &[HashMap<usize, usize>; 2],
        is_singular_class: bool
    ) -> Vec<Clause>;
}

// Trait for testing equivalence by permuting circuits.
pub trait ShuffleConstraint {
    fn add_random_constant_factor(&mut self, rng: &mut impl Rng, field: &BigInt) -> ();
    fn shuffle_constraint_internals(&mut self, rng: &mut impl Rng) -> ();
}