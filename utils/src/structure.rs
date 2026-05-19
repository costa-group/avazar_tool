use serde::{Serialize,Deserialize};
use std::fs::File;
use std::io::BufReader;
use std::path::Path;
use std::error::Error;
use std::ops::AddAssign;
use circom_algebra::algebra::Constraint;

#[derive(Deserialize,Serialize, Debug)]
pub struct TimingInfo{
    pub graph_construction: Option<f32>,
    pub clustering: f32,
    pub dag_construction: f32,
    pub equivalency: f32,
    pub total: f32,
}

impl AddAssign for TimingInfo {
    
    fn add_assign(&mut self, other: Self) -> () {
        self.graph_construction = self.graph_construction.map(|x| other.graph_construction.map(|y| x + y)).flatten();
        self.clustering += other.clustering;
        self.dag_construction += other.dag_construction;
        self.equivalency += other.equivalency;
        self.total += other.total;
    }
} 

#[derive(Deserialize,Serialize, Debug, Clone)]
pub struct NodeInfo{
    pub node_id: usize,
    pub node_name:String,
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

pub fn print_node_info(node: &NodeInfo, constraints: &Vec<Constraint<usize>>){
    println!("Input signals: {:?}", node.input_signals);
    println!("Output signals: {:?}", node.output_signals);
    println!("Signals: {:?}", node.signals);
    println!("Successors: {:?}", node.successors);
    println!("Is custom: {}", node.is_custom);
    println!("Is deterministic: {}", node.is_deterministic);


    for c in &node.constraints{
        let c = &constraints[*c];
        c.print_pretty_constraint();
    }
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
    

    let aux_timing = TimingInfo{
        clustering: 0.0,
        graph_construction: Some(0.0),
        dag_construction: 0.0,
        equivalency: 0.0,
        total: 0.0
    };

    let node = NodeInfo{
        node_name: "main".to_string(),
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
