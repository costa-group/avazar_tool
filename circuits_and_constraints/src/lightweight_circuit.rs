use std::collections::{HashMap, HashSet};
use std::borrow::Borrow;

use circom_algebra::num_bigint::{BigInt};
use crate::circuit::Circuit;
use crate::constraint::Constraint;

pub struct LightweightCircuit<'a, C: Constraint> {
    prime: &'a BigInt,
    constraints: Vec<&'a C>,
    inputs: HashSet<usize>,
    outputs: HashSet<usize>,
    signals: HashSet<usize>,
}

impl<'a, C: Constraint> LightweightCircuit<'a, C> {

    pub fn from<'b>(prime: &'a BigInt, constraints: impl IntoIterator<Item = &'a C>, inputs: impl IntoIterator<Item = &'b usize>, outputs: impl IntoIterator<Item = &'b usize>) -> Self {

        let constraints: Vec<&'a C> = constraints.into_iter().collect();
        let signals: HashSet<usize> = constraints.iter().flat_map(|con| con.signals()).collect();

        Self {prime: prime, constraints: constraints, inputs: inputs.into_iter().copied().collect(), outputs: outputs.into_iter().copied().collect(), signals: signals}
    }
}

impl<'a, C: Constraint> Circuit<C> for LightweightCircuit<'a, C> {

    fn prime(&self) -> &BigInt {
        self.prime
    }
    fn n_constraints(&self) -> usize {
        self.constraints.len()
    }
    fn n_wires(&self) -> usize {self.signals.len()}
    
    fn get_constraints(&self) -> &Vec<impl Borrow<C>> {
        &self.constraints
    }

    fn n_inputs(&self) -> usize {self.inputs.len()}
    fn n_outputs(&self) -> usize {self.outputs.len()}
    fn signal_is_input(&self, signal: &usize) -> bool {self.inputs.contains(signal)}
    fn signal_is_output(&self, signal: &usize) -> bool {self.outputs.contains(signal)}
    fn get_signals(&self) -> impl Iterator<Item = usize> {self.signals.iter().copied()}
    fn get_input_signals(&self) -> impl Iterator<Item = usize> {self.inputs.iter().copied()}
    fn get_output_signals(&self) -> impl Iterator<Item = usize> {self.outputs.iter().copied()}
    fn parse_file(_file: &str) -> Self {unimplemented!("LightweightCircuit does not support file parsing")}
    
    type SubCircuit<'b> = LightweightCircuit<'b, C> where Self: 'b;
    fn take_subcircuit<'b>(
        &'b self, 
        constraint_subset: &Vec<usize>, 
        input_signals: Option<&HashSet<usize>>, 
        output_signals: Option<&HashSet<usize>>, 
        signal_map: Option<&HashMap<usize,usize>>, 
        _return_signal_mapping: Option<bool>
    ) -> Self::SubCircuit<'b> where Self: 'b{

        
        let input_signals_unwrapped: &HashSet<usize>;
        let output_signals_unwrapped: &HashSet<usize>;
        let inputs: HashSet<usize>;
        let outputs: HashSet<usize>;

        // Construct the mapping
        if signal_map.is_none() {
            // construct from input/output_signals
            (input_signals_unwrapped, output_signals_unwrapped) = (input_signals.unwrap(), output_signals.unwrap());
        } else {
            let signal_mapping = signal_map.unwrap();
            inputs = signal_mapping.keys().copied().filter(|sig| self.signal_is_input(sig)).collect();
            outputs = signal_mapping.keys().copied().filter(|sig| self.signal_is_output(sig)).collect();
            (input_signals_unwrapped, output_signals_unwrapped) = (&inputs, &outputs);
        }

        LightweightCircuit::from(
            self.prime,
            constraint_subset.into_iter().copied().map(|coni| self.constraints[coni]),
            input_signals_unwrapped,
            output_signals_unwrapped
        )
    }
}
