use circom_algebra::num_bigint::BigInt;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash};
use std::cmp::{Eq};
use rand::Rng;
use std::fmt::Debug;

pub trait Constraint {

    type Fingerprint<'a, T: Hash + Eq + Default + Copy + Ord + Debug>: Hash + Eq + Clone + Debug where Self: 'a;

    fn normalise(&self, prime: &BigInt) -> Vec<Self> where Self: Sized;
    fn signals(&self) -> HashSet<usize>;
    fn fingerprint<'a, T: Hash + Eq + Default + Copy + Ord + Debug>(&'a self, fingerprint: &mut Option<Self::Fingerprint<'a, T>>, signal_to_fingerprint: &HashMap<usize, T>) -> ();
    fn is_nonlinear(&self) -> bool;
    fn get_coefficients(&self) -> impl Hash + Eq;
    fn add_random_constant_factor(&mut self, rng: &mut impl Rng, field: &BigInt) -> ();
    fn shuffle_constraint_internals(&mut self, rng: &mut impl Rng) -> ();
    fn is_ordered(&self) -> bool;
}