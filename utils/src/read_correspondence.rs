use std::fs::File;
use std::io::BufReader;
use std::path::Path;
use std::error::Error;
 use std::collections::BTreeMap;



pub fn read_signal_correspondence<P: AsRef<Path>>(path: P) -> Result<(BTreeMap<usize, String>, BTreeMap<String, usize>), Box<dyn Error>> {
    // Open the file in read-only mode with buffer.
    let file = File::open(path)?;
    let reader = BufReader::new(file);

    // Read the JSON contents of the file as an instance of `StructureInfo`.
    let name_to_signal: BTreeMap<String, usize> = serde_json::from_reader(reader)?;

    let mut signal_to_name = BTreeMap::new();
    for (name, pos) in &name_to_signal{
        signal_to_name.insert(*pos, name.clone());
    }


    Ok((signal_to_name, name_to_signal))

}