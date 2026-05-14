use std::collections::{HashMap, BTreeMap};
use circom_algebra::algebra::Constraint;
use utils::read_r1cs::read_r1cs;
use utils::read_specification::read_smt_specification;

use utils::structure::*;
use utils::equivalence_structure::*;
use std::path::PathBuf;


pub fn process_constraints(input: &PathBuf) -> (
    Vec<Constraint<usize>>,
    Vec<usize>,
    usize,
    usize
 ) {
    let input: &String = &format!("{}", input.display());
    let result = read_r1cs(input).unwrap();
    let constraint_list = result.constraints;
    let mut formatted_list = Vec::new();
    for (a, b, c) in constraint_list{
        formatted_list.push(Constraint::new(a,b,c));
    }
    (
        formatted_list,
        result.signals,
        result.header_data.public_outputs,
        result.header_data.public_inputs + result.header_data.private_inputs,
    )
}


pub fn process_smt_formula(input: &PathBuf) ->(
    Vec<String>,
    Vec<String>,
    Vec<String>,
    Vec<String>
){
    let input: &String = &format!("{}", input.display());
    let result = read_smt_specification(input).unwrap();
    (
        result.constraints,
        result.signals,
        result.output_signals,
        result.input_signals
    )
}

pub fn process_structure(structure: &StructureInfo) -> (HashMap<usize, usize>, HashMap<usize, usize>, HashMap<usize, usize>, usize){
    
    // Process the structure and return maps:
    // Map nodeid -> position in structure.nodes
    // Map node_id -> id_local_equiv_class (position in the array of local equiv classes)
    // Map node_id -> id_structural_equiv_class (position in the array of structural equiv classes)
    // Usize fresh node_id

    let mut local_equivalence_classes = HashMap::new();
    let mut structural_equivalence_classes = HashMap::new();
    let mut id_equiv_class = 0;
    let mut max_node_id = 0;

    let mut nodeid2pos = HashMap::new(); // node id to position in vector
    let mut pos = 0;
    for node in &structure.nodes {
        nodeid2pos.insert(node.node_id, pos);
        pos += 1;
        max_node_id = std::cmp::max(max_node_id, node.node_id);
    }


    for eq_class in &structure.local_equivalency{
        for node_id in eq_class{
            local_equivalence_classes.insert(*node_id, id_equiv_class);
        }
        id_equiv_class += 1;
    }

    id_equiv_class = 0;
    for eq_class in &structure.structural_equivalency{
        for node_id in eq_class{
            structural_equivalence_classes.insert(*node_id, id_equiv_class);
        }
        id_equiv_class += 1;
    }

    (nodeid2pos, local_equivalence_classes, structural_equivalence_classes, max_node_id + 1)
}


pub fn process_equivalence_structure(structure: &EquivalenceStructureInfo) -> (HashMap<usize, usize>, HashMap<usize, usize>, HashMap<usize, usize>, usize){
    
    // Process the structure and return maps:
    // Map nodeid -> position in structure.nodes
    // Map node_id -> id_local_equiv_class (position in the array of local equiv classes)
    // Map node_id -> id_structural_equiv_class (position in the array of structural equiv classes)
    // Usize fresh node_id

    let mut local_equivalence_classes = HashMap::new();
    let mut structural_equivalence_classes = HashMap::new();
    let mut id_equiv_class = 0;
    let mut max_node_id = 0;

    let mut nodeid2pos = HashMap::new(); // node id to position in vector
    let mut pos = 0;
    for node in &structure.nodes {
        nodeid2pos.insert(node.node_id, pos);
        pos += 1;
        max_node_id = std::cmp::max(max_node_id, node.node_id);
    }


    for eq_class in &structure.local_equivalency{
        for node_id in eq_class{
            local_equivalence_classes.insert(*node_id, id_equiv_class);
        }
        id_equiv_class += 1;
    }

    id_equiv_class = 0;
    for eq_class in &structure.structural_equivalency{
        for node_id in eq_class{
            structural_equivalence_classes.insert(*node_id, id_equiv_class);
        }
        id_equiv_class += 1;
    }

    (nodeid2pos, local_equivalence_classes, structural_equivalence_classes, max_node_id + 1)
}


pub fn get_constraint_info_component(info: &BTreeMap<usize, String>, c: usize) -> (usize, String,usize){
    let mut previous_c = 0;
    let mut previous_comp = "";
    for (init, comp) in info{
        if *init > c{
            return (previous_c, previous_comp.to_string(), *init);
        } else{
            previous_c = *init;
            previous_comp = comp;
        }
    }
    (previous_c, previous_comp.to_string(), 0)

}