use std::collections::{HashMap, HashSet};

use circom_algebra::num_bigint::{BigInt};
use crate::circuit::Circuit;
use crate::constraint::Constraint;

pub struct LightweightCircuit<C: Constraint> {
    prime: BigInt,
    constraints: Vec<C>,
    inputs: HashSet<usize>,
    outputs: HashSet<usize>,
    signals: HashSet<usize>
}

impl<C: Constraint + Clone> LightweightCircuit<C> {

    pub fn from(prime: &BigInt, constraints: &Vec<C>, inputs: &[usize], outputs: &[usize]) -> Self {

        let cloned_constraints: Vec<C> = constraints.into_iter().cloned().collect();
        let signals: HashSet<usize> = constraints.iter().flat_map(|con| con.signals()).collect();

        Self {prime: prime.clone(), constraints: cloned_constraints, inputs: inputs.into_iter().copied().collect(), outputs: outputs.into_iter().copied().collect(), signals: signals}
    }
}

impl<C: Constraint> Circuit<C> for LightweightCircuit<C> {

    fn prime(&self) -> &BigInt {
        &self.prime
    }
    fn n_constraints(&self) -> usize {
        self.constraints.len()
    }
    fn n_wires(&self) -> usize {self.signals.len()}
    
    fn get_constraints(&self) -> &Vec<C> {
        &self.constraints
    }

    fn normi_to_coni(&self) -> &Vec<usize> {unimplemented!("This function is not implemented yet")}
    fn n_inputs(&self) -> usize {self.inputs.len()}
    fn n_outputs(&self) -> usize {self.outputs.len()}
    fn signal_is_input(&self, signal: usize) -> bool {self.inputs.contains(&signal)}
    fn signal_is_output(&self, signal: usize) -> bool {self.outputs.contains(&signal)}
    fn get_signals(&self) -> impl Iterator<Item = usize> {self.signals.iter().copied()}
    fn get_input_signals(&self) -> impl Iterator<Item = usize> {self.inputs.iter().copied()}
    fn get_output_signals(&self) -> impl Iterator<Item = usize> {self.outputs.iter().copied()}
    fn parse_file(_file: &str) -> Self {unimplemented!("LightweightCircuit does not support file parsing")}
    
    fn take_subcircuit(
        &self, 
        constraint_subset: &Vec<usize>, 
        input_signals: Option<&HashSet<usize>>, 
        output_signals: Option<&HashSet<usize>>, 
        signal_map: Option<&HashMap<usize,usize>>, 
        _return_signal_mapping: Option<bool>
    ) -> Self {

        let signal_mapping_: HashMap<usize, usize>;
        let signal_mapping: &HashMap<usize, usize>;

        // Construct the mapping
        if signal_map.is_none() {
            // construct from input/output_signals

            let (inputs, outputs) = (input_signals.unwrap(), output_signals.unwrap());

            if inputs.intersection(outputs).count() > 0 {panic!("Gave overlapping input/output to take_subcircuit");}

            signal_mapping_ = outputs.iter().copied().chain(inputs.iter().copied()).chain(
                constraint_subset.into_iter().flat_map(|cons| self.constraints[*cons].signals().into_iter()).collect::<HashSet<_>>().difference(&outputs.iter().chain(inputs.iter()).copied().collect::<HashSet<_>>()).copied()
            ).enumerate().map(|(idx, val)| (val, idx+1)).collect();

            signal_mapping = &signal_mapping_;
        } else {
            signal_mapping = signal_map.unwrap();
        }

        LightweightCircuit {
            prime: self.prime.clone(),
            constraints: constraint_subset.into_iter().copied().map(|coni| self.constraints[coni].substitute_signals(signal_mapping)).collect(),
            inputs: self.inputs.iter().map(|sig| signal_mapping[sig]).collect(),
            outputs: self.outputs.iter().map(|sig| signal_mapping[sig]).collect(),
            signals: self.signals.iter().map(|sig| signal_mapping[sig]).collect()
        }

    }
}
