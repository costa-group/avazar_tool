use serde::{Serialize, Deserialize};
use std::fs::File;
use std::io::{BufReader, BufWriter};
use std::path::Path;
use std::error::Error;


#[derive(Deserialize, Debug)]
pub struct TimingInfo{
    pub clustering: f32,
    pub dag_construction: f32,
    pub equivalency: f32,
    pub total: f32,
}

#[derive(Deserialize, Debug)]
pub struct NodeInfo{
    pub node_id: usize,
    pub constraints: Vec<usize>, //ids of the constraints
    pub input_signals: Vec<usize>,
    pub output_signals: Vec<usize>,
    pub signals: Vec<usize>, 
    pub successors: Vec<usize> //ids of the successors 

}

#[derive(Deserialize, Debug)]
pub struct StructureInfo {
    pub timing: TimingInfo,
    pub nodes: Vec<NodeInfo>, //all the nodes of the circuit, position of the node is not the position.
    pub local_equivalency: Vec<Vec<usize>>, //equivalence classes, each inner vector is a class
    pub structural_equivalency: Vec<Vec<usize>>, //equivalence classes, each inner vector is a class
}

#[derive(Deserialize, Debug)]
struct StructureReader {
    timing: TimingInfo,
    nodes: Vec<NodeInfo>, //all the nodes of the circuit, position of the node is not the position.
    equivalency_local: Option<Vec<Vec<usize>>>, //equivalence classes, each inner vector is a class
    equivalency_structural: Option<Vec<Vec<usize>>>, //equivalence classes, each inner vector is a class

 }



pub fn read_structure<P: AsRef<Path>>(path: P) -> Result<StructureInfo, Box<dyn Error>> {
    // Open the file in read-only mode with buffer.
    let file = File::open(path)?;
    let reader = BufReader::new(file);

    // Read the JSON contents of the file as an instance of `StructureInfo`.
    let u: StructureReader = serde_json::from_reader(reader)?;

    let mut local_equivalence = Vec::new();
    if u.equivalency_local.is_some() { 
    	local_equivalence = u.equivalency_local.unwrap(); 
    } else{
    	// in case no equivalence is given then each node is equivalent to itself only
    	for n in &u.nodes{
    		local_equivalence.push(vec![n.node_id]);
    	}
    }

    let mut structural_equivalence = Vec::new();
    if u.equivalency_structural.is_some() { 
    	structural_equivalence = u.equivalency_structural.unwrap(); 
    } else { 
    	structural_equivalence = local_equivalence.clone();
    }

    let structure_info = StructureInfo {
        timing: u.timing,
        nodes: u.nodes,
        local_equivalency: local_equivalence,
        structural_equivalency: structural_equivalence,
    };
    Ok(structure_info)
}
