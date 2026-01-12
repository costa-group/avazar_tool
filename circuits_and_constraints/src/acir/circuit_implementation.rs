use circom_algebra::num_bigint::{BigInt, ParseBigIntError};
use std::collections::{HashMap, HashSet};
use serde::{Serialize,Deserialize};
use std::borrow::Borrow;
use std::error::Error;
use std::fs::File;
use std::io::BufReader;
use std::str::FromStr;

use super::{ACIRCircuit, ACIRConstraint};
use crate::circuit::Circuit;
use crate::constraint::Constraint;
use crate::lightweight_circuit::LightweightCircuit;

#[derive(Deserialize,Serialize, Debug)]
struct ACIRReader {
    prime: String,
    number_of_signals: usize,
    inputs: Vec<usize>,
    outputs: Vec<usize>,
    constraints: Vec<ACIRConstraintJSON>
}

#[derive(Deserialize,Serialize, Debug)]
struct ACIRConstraintJSON {
    constant: String,
    linear: Vec<LinearTerm>,
    mul: Vec<MultTerm>
}

#[derive(Deserialize,Serialize, Debug)]
struct LinearTerm {
    coeff: String,
    witness: usize,
}

#[derive(Deserialize,Serialize, Debug)]
struct MultTerm {
    coeff: String,
    witness1: usize,
    witness2: usize
}

impl Circuit<ACIRConstraint> for ACIRCircuit{

    fn prime(&self) -> &BigInt {&self.prime}
    fn n_constraints(&self) -> usize {self.constraints.len()}
    fn n_wires(&self) -> usize {self.signals.len()}
    fn get_constraints(&self) -> &Vec<impl Borrow<ACIRConstraint>> {&self.constraints}
    fn n_inputs(&self) -> usize {self.input_signals.len()}
    fn n_outputs(&self) -> usize {self.output_signals.len()}
    fn signal_is_input(&self, signal: &usize) -> bool {self.input_signals.contains(signal)}
    fn signal_is_output(&self, signal: &usize) -> bool {self.output_signals.contains(signal)}
    fn get_signals(&self) -> impl Iterator<Item = usize> {self.signals.iter().copied()}
    fn get_input_signals(&self) -> impl Iterator<Item = usize> {self.input_signals.iter().copied()}
    fn get_output_signals(&self) -> impl Iterator<Item = usize> {self.output_signals.iter().copied()}
    fn parse_file(filepath: &str) -> Result<Self, Box<dyn Error>> where Self: Sized {

        let file = File::open(filepath)?;
        let reader = BufReader::new(file);
        let ACIRReader {prime, inputs, outputs, constraints, ..} = serde_json::from_reader(reader)?;

        fn to_constraint(json: ACIRConstraintJSON) -> Result<ACIRConstraint, Box<dyn Error>>  {
            let ACIRConstraintJSON {constant, linear, mul} = json;
            let new_mult: HashMap<(usize, usize), BigInt> = mul.into_iter()
                .map(|mult_term| {let MultTerm {coeff, witness1, witness2} = mult_term; ((witness1, witness2), BigInt::from_str(coeff.as_str()))})
                .map(|(k, v)| v.map(|coeff| (k, coeff))).collect::<Result<HashMap<(usize, usize), BigInt>, ParseBigIntError>>()?;
            let new_linear: HashMap<usize, BigInt> = linear.into_iter().map(|linear_term| {let LinearTerm {coeff, witness} = linear_term; (witness, BigInt::from_str(coeff.as_str()))})
                .map(|(k, v)| v.map(|coeff| (k, coeff))).collect::<Result<HashMap<usize, BigInt>, ParseBigIntError>>()?;
            let new_const: BigInt = BigInt::from_str(constant.as_str())?;

            Ok(ACIRConstraint {
                mult: new_mult ,
                linear: new_linear,
                constant: new_const
            })
        }

        let new_constraints: Vec<ACIRConstraint> = constraints.into_iter().map(to_constraint).collect::<Result<Vec<ACIRConstraint>, Box<dyn Error>>>()?;
        let new_signals: HashSet<usize> = new_constraints.iter().flat_map(|cons| cons.signals()).collect();

        let input_signals: HashSet<usize> = inputs.into_iter().collect();
        let output_signals: HashSet<usize> = outputs.into_iter().collect();

        if !input_signals.is_subset(&new_signals) {return Err("input signals listed in file are not a subset of signals in constraints".into());}
        if !output_signals.is_subset(&new_signals) {return Err("output signals listed in file are not a subset of signals in constraints".into());}

        Ok(ACIRCircuit {
            prime: BigInt::from_str(prime.as_str())?,
            constraints: new_constraints,
            input_signals: input_signals,
            output_signals: output_signals,
            signals: new_signals
        })
    } 

    // def parse_file(self, file: str) -> None:
    //     fp = open(file, 'r')
    //     acir_json = json.load(fp)
    //     fp.close()

    //     self._prime = int(acir_json["prime"])
    //     self._nWires = int(acir_json["number_of_signals"])
    //     self.input_signals = acir_json["inputs"]
    //     self.output_signals = acir_json["outputs"]

    //     self._constraints = list(map(lambda cons : parse_acir_constraint(cons, self.prime), acir_json["constraints"]))

    //     ## fix any preprocessing bugs
    //     circ_signals = set(itertools.chain(self.input_signals, self.output_signals, itertools.chain.from_iterable(map(lambda con : con.signals(), self.constraints))))
    //     if len(circ_signals) != self._nWires: warnings.warn(f"Number of signals in file {self.nWires} does not match given value {len(circ_signals)}, fixing...")

    //     next_int = itertools.count().__next__
    //     sigmapp = {sig : next_int() for sig in sorted(circ_signals)}

    //     self._constraints = list(map(lambda con : con.signal_map(sigmapp), self._constraints))
    //     self._nWires = len(circ_signals)
    //     self.input_signals = list(map(sigmapp.__getitem__, self.input_signals))
    //     self.output_signals = list(map(sigmapp.__getitem__, self.output_signals))
    
    // TODO: code duplication with this same take_subcircuit implementation across 3 circuit types
    type SubCircuit<'a> = LightweightCircuit<'a, ACIRConstraint> where Self: 'a;
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
        let self_constraints = self.get_constraints();

        LightweightCircuit::from(
            self.prime(),
            constraint_subset.into_iter().copied().map(|coni| self_constraints[coni].borrow()),
            input_signals_unwrapped,
            output_signals_unwrapped
        )
    }
}