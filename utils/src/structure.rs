use serde::{Serialize,Deserialize};
use std::fs::File;
use std::io::BufReader;
use std::path::Path;
use std::error::Error;


#[derive(Deserialize,Serialize, Debug)]
pub struct TimingInfo{
    pub clustering: f32,
    pub dag_construction: f32,
    pub equivalency: f32,
    pub total: f32,
}

#[derive(Deserialize,Serialize, Debug, Clone)]
pub struct NodeInfo{
    pub node_id: usize,
    pub constraints: Vec<usize>, //ids of the constraints
    pub input_signals: Vec<usize>,
    pub output_signals: Vec<usize>,
    pub signals: Vec<usize>, 
    pub successors: Vec<usize> //ids of the successors 

}

#[derive(Deserialize, Serialize, Debug)]
pub struct StructureInfo {
    // pub timing: TimingInfo,
    pub nodes: Vec<NodeInfo>, //all the nodes of the circuit, position of the node is not the position.
    pub local_equivalency: Vec<Vec<usize>>, //equivalence classes, each inner vector is a class
    pub structural_equivalency: Vec<Vec<usize>>, //equivalence classes, each inner vector is a class
}

#[derive(Deserialize, Debug)]
struct StructureReader {
    // timing: TimingInfo,
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

    Ok(transform_structure_reader(u))
}

pub fn transform_structure_reader(
    u: StructureReader
) -> StructureInfo{
    let mut local_equivalence = Vec::new();
    if u.equivalency_local.is_some() { 
    	local_equivalence = u.equivalency_local.unwrap(); 
    } else{
    	// in case no equivalence is given then each node is equivalent to itself only
    	for n in &u.nodes{
    		local_equivalence.push(vec![n.node_id]);
    	}
    }

    let structural_equivalence;
    if u.equivalency_structural.is_some() { 
    	structural_equivalence = u.equivalency_structural.unwrap(); 
    } else { 
    	structural_equivalence = local_equivalence.clone();
    }

    let structure_info = StructureInfo {
        // timing: u.timing,
        nodes: u.nodes,
        local_equivalency: local_equivalence,
        structural_equivalency: structural_equivalence,
    }

}


pub fn generate_empty_structure(
    n_constraints: usize, 
    n_signals:usize,
    n_outputs: usize,
    n_inputs: usize
) -> StructureInfo{
    

    // let aux_timing = TimingInfo{
    //     clustering: 0.0,
    //     dag_construction: 0.0,
    //     equivalency: 0.0,
    //     total: 0.0
    // };

    let node = NodeInfo{
        node_id: 0,
        constraints: (0..n_constraints).collect(),
        output_signals: (1.. n_outputs + 1).collect(),
        input_signals: (n_outputs + 1..n_outputs + n_inputs + 1).collect(),
        signals: (1..n_signals).collect(),
        successors: vec![]
    };
    StructureInfo{
        // timing: aux_timing,
        nodes: vec![node],
        local_equivalency: vec![vec![0]],
        structural_equivalency: vec![vec![0]],

    }
   
}
