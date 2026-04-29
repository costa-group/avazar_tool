use circom_algebra::num_bigint::BigInt;
use std::collections::{HashMap, HashSet};
use std::borrow::Borrow;
use std::error::Error;
use rand::seq::SliceRandom;
use rand::Rng;

use utils::read_r1cs::read_r1cs;
use super::{R1CSConstraint, R1CSData, HeaderData};
use crate::circuit::{ShuffleCircuit, Circuit};
use crate::lightweight_circuit::LightweightCircuit;

impl Circuit<R1CSConstraint> for R1CSData {

    fn prime(&self) -> &BigInt {&self.header_data.field}
    fn n_constraints(&self) -> usize {self.header_data.number_of_constraints}
    fn n_wires(&self) -> usize {self.header_data.total_wires}
    
    
    fn get_constraints(&self) -> &Vec< impl Borrow<R1CSConstraint>> {&self.constraints}
    fn n_inputs(&self) -> usize {self.header_data.public_inputs + self.header_data.private_inputs}
    fn n_outputs(&self) -> usize {self.header_data.public_outputs}
    fn signal_is_input(&self, signal: &usize) -> bool {let sig = *signal; self.header_data.public_outputs < sig && sig <= self.header_data.public_inputs + self.header_data.private_inputs + self.header_data.public_outputs} 
    fn signal_is_output(&self, signal: &usize) -> bool {let sig = *signal; 0 < sig && sig <= self.header_data.public_outputs}
    fn get_signals(&self) -> impl Iterator<Item = usize> {1..self.header_data.total_wires}
    fn get_input_signals(&self) -> impl Iterator<Item = usize> {self.header_data.public_outputs+1..=self.header_data.public_inputs + self.header_data.private_inputs + self.header_data.public_outputs}
    fn get_output_signals(&self) -> impl Iterator<Item = usize> {1..=self.header_data.public_outputs}
    fn parse_file(filepath: &str) -> Result<Self, Box<dyn Error>> where Self: Sized {Ok(read_r1cs(filepath)?)}
    
    type SubCircuit<'a> = LightweightCircuit<'a, R1CSConstraint> where Self: 'a;
    fn take_subcircuit<'a>(
        &'a self, 
        constraint_subset: &Vec<usize>, 
        input_signals: Option<&HashSet<usize>>, 
        output_signals: Option<&HashSet<usize>>, 
        signal_map: Option<&HashMap<usize,usize>>, 
        _return_signal_mapping: Option<bool> // TODO: implement in the mapping overhaul
    ) -> LightweightCircuit<'a, R1CSConstraint> where Self: 'a {
        // Assumes correct inputs

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
        let self_constraints = self.get_constraints();

        LightweightCircuit::from(
            self.prime(),
            constraint_subset.into_iter().copied().map(|coni| self_constraints[coni].borrow()),
            input_signals_unwrapped,
            output_signals_unwrapped
        )
    }
}

impl ShuffleCircuit<R1CSConstraint> for R1CSData {

    fn get_mut_constraints(&mut self) -> &mut Vec<R1CSConstraint> {&mut self.constraints}

    fn shuffle_signals(self, rng: &mut impl Rng) -> Self {
        let mut outputs: Vec<usize> = self.get_output_signals().into_iter().collect();
        let mut inputs: Vec<usize> = self.get_input_signals().into_iter().collect();
        let mut remaining: Vec<usize> = (self.n_outputs() + self.n_inputs() + 1..self.n_wires()).into_iter().collect();
    
        outputs.shuffle(rng);
        inputs.shuffle(rng);
        remaining.shuffle(rng);
    
        let mapping: Vec<usize> = [0].into_iter().chain(outputs.into_iter()).chain(inputs.into_iter()).chain(remaining.into_iter()).collect();

        // constructing new constraint lists needs to consume the current one and for that we need to consume Self -- this avoids cloning a whole bunch of BigInts
        let Self {header_data, constraints, signals, ..} = self;
        let HeaderData {field, field_size, total_wires, public_outputs, public_inputs, private_inputs, number_of_labels, number_of_constraints } = header_data;

        let new_constraints = constraints.into_iter().map(|cons|
            (cons.0.into_iter().map(|(k, val)| (mapping[k], val)).collect::<HashMap<usize, BigInt>>(),
             cons.1.into_iter().map(|(k, val)| (mapping[k], val)).collect::<HashMap<usize, BigInt>>(),
             cons.2.into_iter().map(|(k, val)| (mapping[k], val)).collect::<HashMap<usize, BigInt>>())
        ).collect::<Vec<R1CSConstraint>>();

        R1CSData::from(
            field,
            field_size,
            total_wires,
            public_outputs,
            public_inputs,
            private_inputs,
            number_of_labels,
            number_of_constraints,
            new_constraints,
            signals,
            false,
            None,
            None
        )
    }
}