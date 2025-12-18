use circom_algebra::num_bigint::BigInt;
use std::collections::{HashMap, HashSet};
use std::borrow::Borrow;
use rand::Rng;

use crate::constraint::{Constraint};

pub trait Circuit<C: Constraint> {

    fn prime(&self) -> &BigInt;
    fn n_constraints(&self) -> usize;
    fn n_wires(&self) -> usize;
    
    fn get_constraints(&self) -> &Vec<impl Borrow<C>>;

    fn normalise_constraints(&self) -> Vec<C> {
        self.get_constraints().into_iter().flat_map(|cons| cons.borrow().normalise(self.prime()).into_iter()).collect()
    }

    fn normi_to_coni(&self) -> &Vec<usize>;
    fn n_inputs(&self) -> usize;
    fn n_outputs(&self) -> usize;
    fn signal_is_input(&self, signal: &usize) -> bool;
    fn signal_is_output(&self, signal: &usize) -> bool;
    fn get_signals(&self) -> impl Iterator<Item = usize>;
    fn get_input_signals(&self) -> impl Iterator<Item = usize>;
    fn get_output_signals(&self) -> impl Iterator<Item = usize>;
    fn parse_file(file: &str) -> Self;
    
    type SubCircuit<'a>: Circuit<C> where Self: 'a;
    fn take_subcircuit<'a>(
        &'a self, 
        constraint_subset: &Vec<usize>, 
        input_signals: Option<&HashSet<usize>>, 
        output_signals: Option<&HashSet<usize>>, 
        signal_map: Option<&HashMap<usize,usize>>, 
        return_signal_mapping: Option<bool>
    ) -> Self::SubCircuit<'a> where Self: 'a;
}

pub trait ShuffleCircuit<C> {

    fn get_mut_constraints(&mut self) -> &mut Vec<C>;
    fn shuffle_signals(self, rng: &mut impl Rng) -> Self;
}