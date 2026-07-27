#![allow(unused_variables)]
use crate::num_bigint::BigInt;

use itertools::Itertools;
use std::collections::{HashMap, HashSet};
use std::error::Error;

use crate::constraint::Constraint;
use crate::circuit::Circuit;
use crate::lightweight_circuit::LightweightCircuit;
use super::{Formula, FormulaAtom};

const EQUIV_ERR_MESSAGE: &str = "Equivalence is not supported for Formula Expressions";

impl Circuit<FormulaAtom> for Formula {

    fn prime(&self) -> &BigInt {unimplemented!("{EQUIV_ERR_MESSAGE}");}
    fn n_constraints(&self) -> usize {self.atoms.len()}
    fn n_wires(&self) -> usize {self.signals.len()}
    
    fn constraints(&self) -> Vec<&FormulaAtom> {self.atoms.iter().collect::<Vec<_>>()}
    fn get_constraint(&self, idx: usize) -> &FormulaAtom {&self.atoms[idx]}
    fn n_inputs(&self) -> usize {self.input_signals.len()}
    fn n_outputs(&self) -> usize {self.output_signals.len()}
    fn signal_is_input(&self, signal: &usize) -> bool {self.input_signals.contains(signal)}
    fn signal_is_output(&self, signal: &usize) -> bool {self.output_signals.contains(signal)}
    fn get_signals(&self) -> impl Iterator<Item = usize> {self.signals.iter().copied()}
    fn get_input_signals(&self) -> impl Iterator<Item = usize> {self.input_signals.iter().copied().sorted()}
    fn get_output_signals(&self) -> impl Iterator<Item = usize> {self.output_signals.iter().copied().sorted()}
    fn parse_file(filepath: &str) -> Result<Self, Box<dyn Error>> where Self: Sized {unimplemented!("Formula Expression cannot be parsed directly, they need to be tied to some other Circuit");}
    
    // TODO: code duplication with this same take_subcircuit implementation across 4 circuit types
    type SubCircuit<'a> = LightweightCircuit<'a, FormulaAtom> where Self: 'a;
    fn take_subcircuit<'a>(
        &'a self, 
        constraint_subset: &Vec<usize>, 
        input_signals: Option<&HashSet<usize>>, 
        output_signals: Option<&HashSet<usize>>, 
        signal_map: Option<&HashMap<usize,usize>>, 
        _return_signal_mapping: Option<bool> // TODO: implement in the mapping overhaul
    ) -> Self::SubCircuit<'a> where Self: 'a {

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
            self.prime(),
            constraint_subset.into_iter().copied().map(|coni| self.get_constraint(coni)),
            input_signals_unwrapped,
            output_signals_unwrapped
        )
    }
}