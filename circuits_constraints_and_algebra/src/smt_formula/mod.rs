mod circuit_implementation;
mod constraint_implementation;

use serde_json::Value;
use itertools::Itertools;

use std::fs::File;
use std::io::BufReader;
use std::path::PathBuf;
use std::error::Error;

use std::collections::{HashSet, HashMap};
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct FormulaAtom {
    pub name: String,
    pub signals: Vec<usize>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Formula {
    atoms: Vec<FormulaAtom>,
    signals: Vec<usize>,
    input_signals: HashSet<usize>,
    output_signals: HashSet<usize>,
}

pub fn parse_formula(filepath: &PathBuf, input_signals: HashSet<usize>, output_signals: HashSet<usize>, ignore_empty_atoms: Option<bool>) -> Result<Formula, Box<dyn Error>> {
    
    let ignore_empty_atoms = ignore_empty_atoms.unwrap_or(true);

    let file = File::open(filepath)?;
    let reader = BufReader::new(file);

    #[derive(Serialize, Deserialize, Debug, Clone)]
    #[serde(untagged)]
    enum OneOrMore {
        Single(usize),
        Many(Vec<usize>)
    }

    let input_data: HashMap<String, HashMap<String, Vec<OneOrMore>>> = serde_json::from_reader(reader).unwrap();

    let atoms: Vec<_> = input_data.into_values().flat_map(|macro_| macro_.into_iter()).map(
        |(name, value)| (name, value.into_iter().flat_map(|val: OneOrMore| match val {OneOrMore::Single(num) => vec![num].into_iter(), OneOrMore::Many(arr) => arr.into_iter()}).collect::<Vec<_>>())
    ).filter(|(name, signals)| !ignore_empty_atoms || signals.len() > 0).collect();
    let signals: Vec<_> = atoms.iter().flat_map(|(_, signals)| signals.iter().copied()).collect::<HashSet<_>>().into_iter().sorted().collect();

    Ok(Formula {
        atoms: atoms.into_iter().map(|(name, signals)| FormulaAtom {name, signals} ).collect(), signals,
        input_signals, output_signals
    })
}