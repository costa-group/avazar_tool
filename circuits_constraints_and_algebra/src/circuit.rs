use crate::num_bigint::BigInt;
use std::collections::{HashMap, HashSet};
use std::error::Error;
use rand::Rng;

use crate::constraint::{Constraint, ShuffleConstraint};

pub trait Circuit<C: Constraint> {

    /// Returns a reference to the internal prime
    fn prime(&self) -> &BigInt;

    /// Returns the number of constraints in the circuit
    fn n_constraints(&self) -> usize;

    /// Returns the number of wires in the circuit
    fn n_wires(&self) -> usize;
    
    /// Returns a Vector containing references to each constraint
    fn constraints(&self) -> Vec<&C>;
    
    /// Returns a reference to the constraint at index idx
    fn get_constraint(&self, idx: usize) -> &C;

    /// Normalises each constraint and returns them in a Vec, idx i in the returned vector is the normalised constraint for coni i.
    fn normalise_constraints(&self) -> Vec<C> {
        self.constraints().into_iter().flat_map(|cons| cons.normalise(self.prime()).into_iter()).collect()
    }

    /// Returns number of inputs
    fn n_inputs(&self) -> usize;

    /// Returns number of outputs
    fn n_outputs(&self) -> usize;

    /// Checks if the given signal is an input signal in the circuit
    fn signal_is_input(&self, signal: &usize) -> bool;

    /// Checks if the given signal is an output signal in the circuit
    fn signal_is_output(&self, signal: &usize) -> bool;

    /// Returns an iterator for all signals in the circuit
    fn get_signals(&self) -> impl Iterator<Item = usize>;

    /// Returns an iterator for all input signals in the circuit
    fn get_input_signals(&self) -> impl Iterator<Item = usize>;

    /// Returns an iterator for all input signals in the circuit
    fn get_output_signals(&self) -> impl Iterator<Item = usize>;

    /// Parses an input file
    fn parse_file(filepath: &str) -> Result<Self, Box<dyn Error>> where Self: Sized;
    
    /// Returns a subcircuit of the circuit
    ///
    /// The constraints in the subcircuit are the constraint_subset, the inputs/outputs are as given.
    /// # Panics
    /// The method expects either Both input_signals and outputs_signals, with no signal_map. Or signal_map and no input_signals, output_signals.
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

/// Trait for testing equivalence by permutating an input Circuit
pub trait ShuffleCircuit<C: Constraint + ShuffleConstraint> {

    fn get_mut_constraints(&mut self) -> &mut Vec<C>;
    fn shuffle_signals(self, rng: &mut impl Rng) -> Self;
}