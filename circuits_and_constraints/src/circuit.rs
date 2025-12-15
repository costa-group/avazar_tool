use circom_algebra::num_bigint::BigInt;
use rustsat::instances::ObjectVarManager;
use rustsat::types::Clause;

use std::collections::{HashMap, HashSet};
use std::hash::{Hash};
use std::cmp::{Eq};
use rand::Rng;
use std::fmt::Debug;

use crate::constraint::{Constraint};

pub trait Circuit<C: Constraint> {

    type SignalFingerprint<'a, T: Hash + Eq + Default + Copy + Ord + Debug>: Hash + Eq + Clone + Debug where C: 'a;

    fn new() -> Self;

    fn prime(&self) -> &BigInt;
    fn n_constraints(&self) -> usize;
    fn n_wires(&self) -> usize;
    
    fn get_constraints(&self) -> &Vec<C>;
    fn get_mut_constraints(&mut self) -> &mut Vec<C>;

    fn normalise_constraints(&self) -> Vec<C> {
        self.get_constraints().into_iter().flat_map(|cons| cons.normalise(self.prime()).into_iter()).collect()
    }

    fn normi_to_coni(&self) -> &Vec<usize>;
    fn n_inputs(&self) -> usize;
    fn n_outputs(&self) -> usize;
    fn signal_is_input(&self, signal: usize) -> bool;
    fn signal_is_output(&self, signal: usize) -> bool;
    fn get_signals(&self) -> impl Iterator<Item = usize>;
    fn get_input_signals(&self) -> impl Iterator<Item = usize>;
    fn get_output_signals(&self) -> impl Iterator<Item = usize>;
    fn parse_file(&mut self, file: &str) -> ();
    
    fn fingerprint_signal<'a, T: Hash + Eq + Default + Copy + Ord + Debug>(
        &self, 
        signal: &usize, 
        fingerprint: &mut Option<Self::SignalFingerprint<'a, T>>,
        normalised_constraints: &'a Vec<C>, 
        normalised_constraint_to_fingerprints: &HashMap<usize, T>, 
        prev_signal_to_fingerprint: &HashMap<usize, T>, 
        signal_to_normi: &HashMap<usize, Vec<usize>>
    ) -> () where C: 'a;
    
    fn take_subcircuit(
        &self, 
        constraint_subset: &Vec<usize>, 
        input_signals: Option<&HashSet<usize>>, 
        output_signals: Option<&HashSet<usize>>, 
        signal_map: Option<&HashMap<usize,usize>>, 
        return_signal_mapping: Option<bool>
    ) -> Self;
    
    fn singular_class_requires_additional_constraints() -> bool;

    fn encode_single_norm_pair(
        norms: &[&C; 2],
        is_ordered: bool,
        signal_pair_encoder: &mut ObjectVarManager,
        fingerprint_to_signals: &[HashMap<usize, Vec<usize>>; 2],
        signal_to_fingerprint: &[HashMap<usize, usize>; 2],
        is_singular_class: bool
    ) -> Vec<Clause>;

    // fn normalise_constraints(&self) -> None:

    //     if len(&self.normalised_constraints) != 0: 
    //         warnings.warn("Attempting to normalised already normalised constraints")
    //     else:

    //         fn _normalised_constraint_building_step(coni: int, cons: Constraint):
    //             norms = cons.normalise()
    //             &self.normalised_constraints.extend(norms)
    //             &self.normi_to_coni.extend(coni for _ in range(len(norms)))

    //         deque(
    //             maxlen=0,
    //             iterable = itertools.starmap(_normalised_constraint_building_step, enumerate(&self.constraints))
    //         )

    fn shuffle_signals(self, rng: &mut impl Rng) -> Self;
}