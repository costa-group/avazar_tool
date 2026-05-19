use serde::{Serialize,Deserialize};
use std::fs::File;
use std::io::BufReader;
use std::path::Path;
use std::error::Error;
use std::collections::HashMap;

#[derive(Deserialize,Serialize, Debug, Clone)]
pub struct NodeSpecificationInfo{
    pub call_name: String,
    pub body: Vec<String>,
    pub input_signals: Vec<String>,
    pub output_signals: Vec<String>,
    pub signals: Vec<String>, 
}

pub type SpecificationInfo = HashMap<String, NodeSpecificationInfo>;



pub fn read_smt_specification<P: AsRef<Path>>(path: P) -> Result<SpecificationInfo, Box<dyn Error>> {
    // Open the file in read-only mode with buffer.
    let file = File::open(path)?;
    let reader = BufReader::new(file);

    // Read the JSON contents of the file as an instance of `StructureInfo`.
    let u: SpecificationInfo = serde_json::from_reader(reader)?;

    Ok(u)
}