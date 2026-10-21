use std::fs::File;
use std::io::BufReader;
use std::path::Path;
use std::error::Error;
 use std::collections::HashMap;
use circom_algebra::num_bigint::{BigInt, Sign};



pub fn read_witness<P: AsRef<Path>>(path: P) -> Result<HashMap<usize, BigInt>, Box<dyn Error>> {
    // Open the file in read-only mode with buffer.
    let file = File::open(path)?;
    let reader = BufReader::new(file);

    // Read the JSON contents of the file as an instance of `StructureInfo`.
    let signal_to_value_str: HashMap<usize, String> = serde_json::from_reader(reader)?;

    let mut signal_to_value = HashMap::new();
    for (name, value_str) in &signal_to_value_str{
        let value: BigInt = value_str.parse().unwrap();
        signal_to_value.insert(*name, value);
    }

    Ok(signal_to_value)

}