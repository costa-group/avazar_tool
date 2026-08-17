mod circuit_implementation;
mod constraint_implementation;

use itertools::Itertools;

use std::fs::File;
use std::io::BufReader;
use std::path::PathBuf;
use std::error::Error;

use crate::num_bigint::{BigInt};
use std::collections::{HashSet, HashMap};
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct FormulaAtom {
    pub name: String,
    pub signals: Vec<usize>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Formula {
    prime: BigInt,
    atoms: Vec<FormulaAtom>,
    signals: Vec<usize>,
    input_signals: HashSet<usize>,
    output_signals: HashSet<usize>,
    component_to_atomrange: HashMap<String, (usize, usize)>,
}

impl Formula {
    pub fn get_atomrange_for_component(&self, component_name: &String) -> Option<std::ops::Range<usize>> {
        self.component_to_atomrange.get(component_name).map(|&(l, r)| l..r)
    }
}

pub fn parse_formula(filepath: &PathBuf, prime: &BigInt, input_signals: HashSet<usize>, output_signals: HashSet<usize>, ignore_empty_atoms: Option<bool>) -> Result<Formula, Box<dyn Error>> {
    
    let ignore_empty_atoms = ignore_empty_atoms.unwrap_or(true);

    let file = File::open(filepath)?;
    let reader = BufReader::new(file);

    #[derive(Serialize, Deserialize, Debug, Clone)]
    #[serde(untagged)]
    enum OneOrMore {
        Single(usize),
        Many(Vec<usize>)
    }

    #[derive(Serialize, Deserialize, Debug, Clone)]
    #[serde(untagged)]
    enum NameOrSignalList {
        Name(String),
        SignalList(Vec<OneOrMore>)
    }

    let input_data: HashMap<String, Vec<HashMap<String, NameOrSignalList>>> = serde_json::from_reader(reader).unwrap();
    let mut instance_to_atoms: HashMap<String, Vec<(String, Vec<usize>)>> = HashMap::new();

    for macros in input_data.into_values() {for mut instance in macros {

        let instance_name = match instance.remove("instance").expect("Instance does not have a name") {NameOrSignalList::Name(s) => s, _ => panic!("Instance name is not string"),};

        // need to build HashMap first to ensure instances are contiguous -- previous error with multiple main instances
        instance_to_atoms.entry(instance_name).or_insert_with(|| Vec::new()).extend(instance.into_iter().map(
            |(name, value)| (name, match value {
                NameOrSignalList::SignalList(list) => list.into_iter().flat_map(|val: OneOrMore| match val {OneOrMore::Single(num) => vec![num].into_iter(), OneOrMore::Many(arr) => arr.into_iter()}).collect::<Vec<_>>(),
                _ => panic!("Non-instance entry is not SignalList")
            })
        ).filter(|(_, value)| !ignore_empty_atoms || value.len() > 0));
    }}

    let mut component_to_atomrange: HashMap<String, (usize, usize)> = HashMap::new();
    let mut atoms: Vec<(String, Vec<usize>)> = Vec::new();
    for (instance_name, atoms_in_instance) in instance_to_atoms.into_iter() {
        component_to_atomrange.insert(instance_name, (atoms.len(), atoms.len() + atoms_in_instance.len()));
        atoms.extend(atoms_in_instance.into_iter());
    }

    let signals: Vec<_> = atoms.iter().flat_map(|(_, signals)| signals.iter().copied()).collect::<HashSet<_>>().into_iter().sorted().collect();

    Ok(Formula {prime: prime.clone(),
        atoms: atoms.into_iter().map(|(name, signals)| FormulaAtom {name, signals} ).collect(), signals,
        input_signals, output_signals, component_to_atomrange
    })
}