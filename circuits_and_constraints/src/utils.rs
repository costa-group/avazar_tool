use std::collections::HashMap;
use either::Either;
use std::fmt::Debug;
use std::cmp::{Eq, PartialEq, Ord, PartialOrd, Ordering};
use std::hash::{Hash, Hasher};

use crate::constraint::Constraint;
use crate::circuit::Circuit;

pub fn signals_to_constraints_with_them(
    cons: &Vec<impl Constraint>,
    names: Option<&Vec<usize>>,
    mut _signal_to_cons: Option<HashMap<usize, Vec<usize>>>
) -> HashMap<usize, Vec<usize>> {
    
    let mut signal_to_cons = _signal_to_cons.unwrap_or_else(HashMap::new);

    for (i, con) in names.map(|v| Either::Left(v.iter().copied())).unwrap_or_else(|| Either::Right(0..cons.len())).zip(cons.iter()) {
        for signal in con.signals().iter().copied() { // hmmm copied copied...
            signal_to_cons.entry(signal).or_insert_with(Vec::new).push(i)
        }
    }

    signal_to_cons
}

use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;
use rand::seq::SliceRandom;

pub fn circuit_shuffle<C: Constraint, S: Circuit<C>>(
    inputfile: &String, seed: u64, 
    add_constant_factor: bool,
    shuffle_constraint_order: bool,
    shuffle_signals: bool,
    shuffle_constraint_internals: bool
) -> (S, S) {

    let mut circ: S = S::new();
    circ.parse_file(inputfile);

    let mut circ_shuffled: S = S::new();
    circ_shuffled.parse_file(&inputfile);

    let mut rng = ChaCha20Rng::seed_from_u64(seed);
    let mut add_constant_factor_rng = ChaCha20Rng::seed_from_u64(rng.random::<u64>());
    let mut shuffle_constraint_order_rng = ChaCha20Rng::seed_from_u64(rng.random::<u64>());
    let mut shuffle_signals_rng = ChaCha20Rng::seed_from_u64(rng.random::<u64>());
    let mut shuffle_constraint_internals_rng = ChaCha20Rng::seed_from_u64(rng.random::<u64>());

    if add_constant_factor {
        let prime = &circ_shuffled.prime().clone();
        for constraint in circ_shuffled.get_mut_constraints().into_iter() {
            constraint.add_random_constant_factor(&mut add_constant_factor_rng, prime);
        }
    }

    if shuffle_constraint_order {
        circ_shuffled.get_mut_constraints().shuffle(&mut shuffle_constraint_order_rng);
    }

    if shuffle_signals {
        circ_shuffled = circ_shuffled.shuffle_signals(&mut shuffle_signals_rng);
    }

    if shuffle_constraint_internals {
        for constraint in circ_shuffled.get_mut_constraints().into_iter() {
            constraint.shuffle_constraint_internals(&mut shuffle_constraint_internals_rng);
        }
    }

    (circ, circ_shuffled)
}

/*
FingerprintIndex struct that stores the hash value for the index and uses it to compare, but otherwise 
*/
#[derive(Default, Copy, Debug, Clone)]
pub struct FingerprintIndex<H: Hash + Eq + Ord + Default + Copy + Debug> {
    pub fingerprint: H,
    pub index: usize
}

impl<H: Hash + Eq + Ord + Default + Copy + Debug> Hash for FingerprintIndex<H> {
    fn hash<T: Hasher>(&self, state: &mut T) {
        self.fingerprint.hash(state);
    }
}

impl<H: Hash + Eq + Ord + Default + Copy + Debug> PartialEq for FingerprintIndex<H> {
    fn eq(&self, other: &Self) -> bool {
        self.fingerprint == other.fingerprint
    }
}

impl<H: Hash + Eq + Ord + Default + Copy + Debug> Eq for FingerprintIndex<H> {}

impl<H: Hash + Eq + Ord + Default + Copy + Debug> PartialOrd for FingerprintIndex<H> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.fingerprint.cmp(&other.fingerprint))
    }
}

impl<H: Hash + Eq + Ord + Default + Copy + Debug> Ord for FingerprintIndex<H> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.fingerprint.cmp(&other.fingerprint)
    }
}