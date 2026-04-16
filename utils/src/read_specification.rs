use serde::{Serialize,Deserialize};
use std::fs::File;
use std::io::BufReader;
use std::path::Path;
use std::error::Error;


#[derive(Deserialize,Serialize, Debug, Clone)]
pub struct SpecificationInfo{
    pub node_id: usize,
    pub node_name:String,
    pub constraints: Vec<String>, //ids of the constraints
    pub input_signals: Vec<String>,
    pub output_signals: Vec<String>,
    pub signals: Vec<String>, 
}



pub fn read_smt_specification<P: AsRef<Path>>(path: P) -> Result<SpecificationInfo, Box<dyn Error>> {
    // Open the file in read-only mode with buffer.
    let file = File::open(path)?;
    let reader = BufReader::new(file);

    // Read the JSON contents of the file as an instance of `StructureInfo`.
    let u: SpecificationInfo = serde_json::from_reader(reader)?;

    Ok(u)
}