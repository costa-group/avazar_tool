#![allow(unused_variables)]
use circuits_constraints_and_algebra::num_bigint::BigInt;

use itertools::Itertools;
use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fs::File;
use std::io::BufReader;
use std::borrow::Borrow;

use crate::constraint::Constraint;
use crate::circuit::Circuit;
use crate::lightweight_circuit::LightweightCircuit;
use super::{AIRData, AIRDataWrapper, ExpressionWrapper, ExpressionData};

const EQUIV_ERR_MESSAGE: &str = "Equivalence is not supported for Generic Expressions";

pub fn wrap_airdata(airdata: AIRData) -> AIRDataWrapper {

    let AIRData {constraints, signals, inputs, outputs, lookups} = airdata;

    // convert ExpressionData to ExpressionWrapper (store signals seperately to speedup .signals())

    fn get_signals(con: &ExpressionData, signals: &mut HashSet<usize>) -> () {

        match con {
            ExpressionData::BinaryExpression(inner) => {get_signals(&inner.left, signals); get_signals(&inner.right, signals);}
            ExpressionData::UnaryExpression(inner) => {get_signals(&inner.value, signals);}
            ExpressionData::Range(inner) => {get_signals(&inner.expression, signals);}
            ExpressionData::Signal(sig) => {signals.insert(*sig);}
            _ => {}
        }
    }

    let constraints: Vec<ExpressionWrapper> = constraints.into_iter().map(
        |con| {let mut signals = HashSet::new(); get_signals(&con, &mut signals); ExpressionWrapper {expression: con, signals: signals.into_iter().collect()}}
    ).collect();

    // convert inputs, outputs to HashSet to speedup .contains calls
    let inputs = inputs.into_iter().collect();
    let outputs = outputs.into_iter().collect();

    AIRDataWrapper { constraints, signals, inputs, outputs, lookups }

}

impl Circuit<ExpressionWrapper> for AIRDataWrapper {

    fn prime(&self) -> &BigInt {unimplemented!("{EQUIV_ERR_MESSAGE}");}
    fn n_constraints(&self) -> usize {self.constraints.len()}
    fn n_wires(&self) -> usize {self.signals.len()}
    
    fn constraints(&self) -> Vec<&ExpressionWrapper> {self.constraints.iter().collect::<Vec<_>>()}
    fn get_constraint(&self, idx: usize) -> &ExpressionWrapper {&self.constraints[idx]}
    fn n_inputs(&self) -> usize {self.inputs.len()}
    fn n_outputs(&self) -> usize {self.outputs.len()}
    fn signal_is_input(&self, signal: &usize) -> bool {self.inputs.contains(signal)}
    fn signal_is_output(&self, signal: &usize) -> bool {self.outputs.contains(signal)}
    fn get_signals(&self) -> impl Iterator<Item = usize> {self.signals.iter().copied()}
    fn get_input_signals(&self) -> impl Iterator<Item = usize> {self.inputs.iter().copied().sorted()}
    fn get_output_signals(&self) -> impl Iterator<Item = usize> {self.outputs.iter().copied().sorted()}
    fn parse_file(filepath: &str) -> Result<Self, Box<dyn Error>> where Self: Sized {

        let file = File::open(filepath)?;
        let reader = BufReader::new(file);
        
        let airdata = serde_json::from_reader(reader)?;
        Ok(wrap_airdata(airdata))
    }
    
    // TODO: code duplication with this same take_subcircuit implementation across 4 circuit types
    type SubCircuit<'a> = LightweightCircuit<'a, ExpressionWrapper> where Self: 'a;
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