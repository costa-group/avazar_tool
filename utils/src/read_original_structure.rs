use serde::{Serialize, Deserialize};
use std::fs::File;
use std::io::{BufReader, BufWriter};
use std::path::Path;
use std::error::Error;
 use std::collections::BTreeMap;


pub fn read_original_structure<P: AsRef<Path>>(path: P) -> Result<BTreeMap<usize, String>, Box<dyn Error>> {
    // Open the file in read-only mode with buffer.
    let file = File::open(path)?;
    let reader = BufReader::new(file);

    // Read the JSON contents of the file as an instance of `StructureInfo`.
    let u: BTreeMap<usize, String> = serde_json::from_reader(reader)?;

    Ok(u)

}
