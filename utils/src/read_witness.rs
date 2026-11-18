use std::fs::File;
use std::io::BufReader;
use std::path::Path;
use std::error::Error;
 use std::collections::HashMap;
use circom_algebra::num_bigint::{BigInt, Sign};
use serde::{Serialize,Deserialize};



#[derive(Deserialize, Serialize, Debug, Clone)]
pub struct WitnessInfo {
    pub witness: HashMap<usize, String>,
    pub different: HashMap<usize, String>,
}


pub fn read_witness<P: AsRef<Path>>(path: P) 
    -> Result<(HashMap<usize, BigInt>, HashMap<usize, BigInt>), Box<dyn Error>> {
    // Open the file in read-only mode with buffer.
    let file = File::open(path)?;
    let reader = BufReader::new(file);

    // Read the JSON contents of the file as an instance of `WitnessInfo`.
    let struct_witness_info: WitnessInfo = serde_json::from_reader(reader)?;

    let mut witness_info = HashMap::new();
    for (name, value_str) in &struct_witness_info.witness{
        let value: BigInt = value_str.parse().unwrap();
        witness_info.insert(*name, value);
    }

    let mut different_info = HashMap::new();
    for (name, value_str) in &struct_witness_info.different{
        let value: BigInt = value_str.parse().unwrap();
        different_info.insert(*name, value);
    }

    Ok((witness_info, different_info))

}