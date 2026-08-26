use std::collections::{HashMap, HashSet};
use strum_macros::Display;
use clap::ValueEnum;

use circuits_constraints_and_algebra::circuit::Circuit;
use circuits_constraints_and_algebra::constraint::Constraint;
use circuit_graphing::directed_acyclic_graph::DAGNode;
use utils::small_utilities::{DecomposeOptions, CopyableDecomposeOptions};
use crate::decompose_circuit::{decompose_circuit_and_return_dagnodes, convert_dagnodes_to_structure_reader};
use crate::smt_hybrid::{guided_clustering::guided_clustering};
use utils::structure::{StructureReader, TimingInfo, add_timing_info};

pub mod guided_clustering;
pub mod shared_merge;
pub mod shared_merge_applications;

#[derive(Debug, Default, Display, Copy, Clone, ValueEnum, PartialEq)]
pub enum HybridClusteringMethods {
    #[default]
    GuidedClustering
}

#[derive(Debug, Default, Copy, Clone)]
pub struct HybridClusteringMethodOptions {
    pub tiebreaking_strategy: TiebreakingStrategy,
    pub recipient_requires_subsets: bool,
}

#[derive(Debug, Default, Display, Copy, Clone, ValueEnum, PartialEq)]
pub enum TiebreakingStrategy {
    #[default]
    FirstInList
}

pub struct HybridClusteringOptions<'a> {
    pub guide_decompose_options: DecomposeOptions<'a>,
    pub hybrid_decompose_method: HybridClusteringMethods,
    pub hybrid_decompose_options: HybridClusteringMethodOptions,
}

// NOTE: the semantic link between nodes is given by the nodes having the same usize identifier -- this is vital and assumed in later functions

fn circuit_and_smt_hybrid_clustering<'a, Cons: Constraint, Circ: Circuit<Cons> , Atom: Constraint, Smt: Circuit<Atom>>(
    circ: &'a Circ, smt: &'a Smt,
    options: HybridClusteringOptions<'a>,
    debug: usize
) -> (TimingInfo, HashMap<usize, DAGNode<'a, Cons, Circ>>, HashMap<usize, DAGNode<'a, Atom, Smt>>) { //  {

    let HybridClusteringOptions { guide_decompose_options, hybrid_decompose_method, hybrid_decompose_options, .. } = options;

    let (mut timing_info, mut guide_clustering) = decompose_circuit_and_return_dagnodes(circ, &mut (0..), guide_decompose_options);

    let (recipient_clustering, secondary_timing) = match hybrid_decompose_method {
        HybridClusteringMethods::GuidedClustering => {
            guided_clustering(circ, smt, &mut guide_clustering, hybrid_decompose_options, debug)
        }

    };

    add_timing_info(&mut timing_info, secondary_timing);
    // Both sides, unconditionally: the pairing is only meaningful if each side admits an
    // order, and a cycle would surface much later as a nonsensical verdict.
    let _ = DAGNode::get_topological_ordering(&guide_clustering);
    let _ = DAGNode::get_topological_ordering(&recipient_clustering);

    (timing_info, guide_clustering, recipient_clustering)
}

pub fn circuit_and_smt_hybrid_clustering_into_structurereader<'a, Cons: Constraint, Circ: Circuit<Cons> , Atom: Constraint, Smt: Circuit<Atom>>(
    circ: &'a Circ, smt: &'a Smt,
    options: HybridClusteringOptions<'a>,
    debug: usize
) -> (StructureReader, StructureReader) {

    let (timing_info, guide_clustering, recipient_clustering) = circuit_and_smt_hybrid_clustering(circ, smt, options, debug);

    (
        convert_dagnodes_to_structure_reader(timing_info.clone(), guide_clustering, None, None, None, None),
        convert_dagnodes_to_structure_reader(timing_info, recipient_clustering, None, None, None, None)
    )

}

use circuits_constraints_and_algebra::smt_formula::{FormulaAtom, Formula};

fn structure_driven_circuit_and_smt_hybrid_clustering<'a, Cons: Constraint + 'a, Circ: Circuit<Cons> + 'a>(
    circ: &'a Circ, circuit_structure: &StructureReader, smt: &'a Formula,
    options: HybridClusteringOptions<'a>,
    debug: usize
) -> Vec<(TimingInfo, HashMap<usize, DAGNode<'a, Cons, Circ>>, HashMap<usize, DAGNode<'a, FormulaAtom, Formula>>)> {

    let HybridClusteringOptions { guide_decompose_options, hybrid_decompose_method, mut hybrid_decompose_options, .. } = options;
    hybrid_decompose_options.recipient_requires_subsets = true;

    let id_to_index: HashMap<usize, usize> = circuit_structure.nodes.iter().enumerate().map(|(idx, node)| (node.node_id, idx)).collect();
    
    if !id_to_index.contains_key(&0) || id_to_index[&0] != 0 {panic!("No root node in circuit structure");};
    if circuit_structure.nodes[0].component_name.len() > 0 {panic!("Node 0 in given structure is not main component");};

    let mut visited: HashSet<usize> = HashSet::new();
    let mut id_generator = 0..;

    // the key for the pairs is the index of the template in the StructureReader nodes Vec
    let mut clusterings: Vec< Option<(TimingInfo, HashMap<usize, DAGNode<'a, Cons, Circ>>, HashMap<usize, DAGNode<'a, FormulaAtom, Formula>>)> > = (0..id_to_index.len()).into_iter().map(|_| None).collect();

    let mut name_components: Vec<&str> = vec!["main"];

    fn dfs_tree_visit<'a, 'b, Cons: Constraint + 'a, Circ: Circuit<Cons> + 'a>(
        id: usize, id_generator: &mut dyn Iterator<Item = usize>, 
        circ: &'a Circ, smt: &'a Formula, circuit_structure: &'b StructureReader,
        guide_decompose_options: CopyableDecomposeOptions, hybrid_decompose_method: HybridClusteringMethods, hybrid_decompose_options: HybridClusteringMethodOptions, debug: usize,
        id_to_index: &HashMap<usize, usize>, visited: &mut HashSet<usize>,
        // TODO: add remaining things to finish this
        clusterings: &mut Vec<Option<(TimingInfo, HashMap<usize, DAGNode<'a, Cons, Circ>>, HashMap<usize, DAGNode<'a, FormulaAtom, Formula>>)>>, name_components: &mut Vec<&'b str>) -> () {

        if visited.contains(&id) {panic!("Given circuit structure is not a tree");}

        let template_name = name_components.join(".").to_string();
        if debug > 1 { println!("----------------- template_name {} ------------------", template_name.clone()); }
        let smt_template_atoms = smt.get_atomrange_for_component(&template_name).expect("No template found with name").collect();

        // get subcircuits for each, pass subcircuits to clustering to get DAGNodes, convert DAGNodes to toplevel circuits, add to clusterings
        let node = &circuit_structure.nodes[id_to_index[&id]];
        let inputs: HashSet<usize> = node.input_signals.iter().copied().collect();
        let outputs: HashSet<usize> = node.output_signals.iter().copied().collect();

        let circuit_subcircuit = circ.take_subcircuit(&node.constraints, Some(&inputs), Some(&outputs), None, None);
        let smt_subcircuit    = smt.take_subcircuit(&smt_template_atoms, Some(&inputs), Some(&outputs), None, None);

        let (mut timing_info, mut smt_clustering) = decompose_circuit_and_return_dagnodes(&smt_subcircuit, id_generator, guide_decompose_options.into_decompose_options());

        let (circuit_clustering, other_timing) = match hybrid_decompose_method {
            HybridClusteringMethods::GuidedClustering => {
                guided_clustering(&smt_subcircuit, &circuit_subcircuit, &mut smt_clustering, hybrid_decompose_options, debug)
            }
        };

        add_timing_info(&mut timing_info, other_timing);

        // map indices back to previous and move cluster to toplevel -- signals are original signals due to LightweightCircuit
        let circ_inverse_constraint_mapping: Option<&[usize]> = Some(&node.constraints);
        let smt_inverse_constraint_mapping: Option<&[usize]> = Some(&smt_template_atoms);

        let circuit_clustering: HashMap<usize, DAGNode<'a, Cons, Circ>> = circuit_clustering.into_iter().map(
            |(key, mut node)| {node.map_internal_indices(circ_inverse_constraint_mapping, None);(key, node.replace_circ(circ))}
        ).collect();
        let smt_clustering: HashMap<usize, DAGNode<'a, FormulaAtom, Formula>> = smt_clustering.into_iter().map(
            |(key, mut node)| {node.map_internal_indices(smt_inverse_constraint_mapping, None);(key, node.replace_circ(smt))}
        ).collect();

        // add to clusterings
        clusterings[id_to_index[&id]] =  Some((timing_info, circuit_clustering, smt_clustering));
        visited.insert(id);

        // Move on to children
        for child_id in node.successors.iter().copied() {

            // descend to child and make recursive call
            name_components.push(&circuit_structure.nodes[id_to_index[&child_id]].component_name.as_str());
            dfs_tree_visit(child_id, id_generator, circ, smt, circuit_structure, guide_decompose_options, hybrid_decompose_method, hybrid_decompose_options, debug, id_to_index, visited, clusterings, name_components);
            name_components.pop();

        }
    }

    dfs_tree_visit(0, &mut id_generator, circ, smt, circuit_structure, guide_decompose_options.into_copy_decompose_options(), hybrid_decompose_method, hybrid_decompose_options, debug, &id_to_index, &mut visited, &mut clusterings, &mut name_components);

    clusterings.into_iter().enumerate().map(|(idx, option)| option.expect(&format!("Didn't produce clustering for index instance with idx {idx}"))).collect()
}

pub fn structure_driven_circuit_and_smt_hybrid_clustering_into_structurereader<'a, Cons: Constraint + 'a, Circ: Circuit<Cons> + 'a>(
    circ: &'a Circ, circuit_structure: &StructureReader, smt: &'a Formula,
    options: HybridClusteringOptions<'a>,
    debug: usize
) -> Vec<(StructureReader, StructureReader)> {

    let clusterings = structure_driven_circuit_and_smt_hybrid_clustering(circ, circuit_structure, smt, options, debug);

    // let mut timers: TimingInfo = TimingInfo::default();

    clusterings.into_iter().map(
        |(timing, guide, recipient)| 
        (
            convert_dagnodes_to_structure_reader(timing.clone(), guide, None, None, None, None),
            convert_dagnodes_to_structure_reader(timing, recipient, None, None, None, None)
        )
    ).collect()
}
