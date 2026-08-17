use serde::{Serialize,Deserialize};
use std::collections::HashMap;
use std::fs::File;
use std::io::BufReader;
use std::path::Path;
use std::error::Error;

#[derive(Deserialize, Serialize, Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[serde(rename_all = "snake_case")]
pub enum TimingCategories {
    GraphConstruction,
    Clustering,
    DagConstruction,
    SecondaryClustering,
    SecondaryDagConstruction,
    Equivalency,
    Total
}
pub type TimingInfo = HashMap<TimingCategories, f32>;

pub fn add_timing_info(fst: &mut TimingInfo, snd: TimingInfo) -> () {
    for (key, val) in snd.into_iter() {
        *fst.entry(key).or_default() += val;
    }
}

#[derive(Deserialize,Serialize, Debug, Clone)]
pub struct NodeInfo{
    pub node_id: usize,
    pub node_name:String,
    pub component_name: String,
    pub constraints: Vec<usize>, //ids of the constraints
    pub input_signals: Vec<usize>,
    pub output_signals: Vec<usize>,
    pub signals: Vec<usize>, 
    pub is_custom: bool,
    pub is_deterministic: bool,
    pub predecessors: Vec<usize>, //ids of the predecessors
    pub successors: Vec<usize> //ids of the successors 

}

#[derive(Deserialize, Serialize, Debug)]
pub struct StructureInfo {
    pub timing: TimingInfo,
    pub nodes: Vec<NodeInfo>, //all the nodes of the circuit, position of the node is not the position.
    pub local_equivalency: Vec<Vec<usize>>, //equivalence classes, each inner vector is a class
    pub structural_equivalency: Vec<Vec<usize>>, //equivalence classes, each inner vector is a class
}

#[derive(Serialize, Deserialize, Debug)]
pub struct StructureReader {
    pub timing: TimingInfo,
    pub nodes: Vec<NodeInfo>, //all the nodes of the circuit, position of the node is not the position.
    pub equivalency_local: Option<Vec<Vec<usize>>>, //equivalence classes, each inner vector is a class
    pub equivalency_structural: Option<Vec<Vec<usize>>>, //equivalence classes, each inner vector is a class
}

pub struct WeightedArcs<T> {
    pub original_nodes: Vec<T>,
    pub arcs: Vec<(T, T, f64)>
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

    StructureInfo {
        timing: u.timing,
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
    

    let aux_timing = TimingInfo::new();

    let node = NodeInfo{
        node_name: "main".to_string(),
        component_name:  "main".to_string(),
        node_id: 0,
        constraints: (0..n_constraints).collect(),
        output_signals: (1.. n_outputs + 1).collect(),
        input_signals: (n_outputs + 1..n_outputs + n_inputs + 1).collect(),
        signals: (1..n_signals).collect(),
        is_custom: false,
        is_deterministic: false,
        predecessors: vec![],
        successors: vec![]
    };
    StructureInfo{
        timing: aux_timing,
        nodes: vec![node],
        local_equivalency: vec![vec![0]],
        structural_equivalency: vec![vec![0]],

    }
   
}
