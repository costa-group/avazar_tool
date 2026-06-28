use std::collections::{HashMap, HashSet};

use std::borrow::Borrow;
use itertools::Itertools;
use std::time::{Instant};

use super::{DAGNode};
use circuits_and_constraints::constraint::Constraint;
use circuits_and_constraints::circuit::Circuit;
use circuits_and_constraints::utils::signals_to_constraints_with_them;
use utils::small_utilities::{HierarchyMode};
use utils::union_find::{UnionFind};
use super::satisfiability_hierarchy::dag_from_partition_solver;
// use super::extension_hierarchy::{extension_hierarchy, merge_equivalence_classes_by_distance};
use super::mixed_graph::MixedGraph;

fn get_intial_components<'a, C: Constraint + 'a, S: Circuit<C> + 'a>(
        circ: &'a S, partition: Vec<Vec<usize>>,
        dead_ends_as_outputs: bool, _debug: usize
    ) -> MixedGraph {
    // have partitions keep Vec<Vec<usize>>, index by vec index throughout until we make the DAGNodes
    // sorted arr signal list
    let n_parts = partition.len();
    let part_to_signals_arr: Vec<Vec<usize>> = partition.iter().map(|part|
        part.iter().copied().flat_map(|idx| circ.get_constraints()[idx].borrow().signals()).sorted_unstable().dedup().collect()
    ).collect();

    let input_parts: HashSet<usize> = (0..n_parts).filter(|key| part_to_signals_arr[*key].iter().any(|sig| circ.signal_is_input(sig))).collect();
    let mut output_parts: HashSet<usize> = (0..n_parts).filter(|key| part_to_signals_arr[*key].iter().any(|sig| circ.signal_is_output(sig))).collect();

    const NO_PART: usize = usize::MAX;
    let mut coni_to_part: Vec<usize> = vec![NO_PART; circ.n_constraints()];
    for (idx, part) in partition.iter().enumerate() {
        for coni in part.iter().copied() {
            match coni_to_part[coni] {
                NO_PART => {coni_to_part[coni] = idx;}
                _ => {panic!("Given partition has overlapping parts");}
            }
        }
    }

    // get the signal indices
    let sig_to_coni = signals_to_constraints_with_them(circ.get_constraints(), None, None);
    
    let mut last_seen_at: Vec<usize> = vec![0;n_parts];
    // note that this is not sorted
    let adjacencies: Vec<Vec<usize>> = (0..n_parts).map(|idx| 
        {let mut neighbours =  Vec::new();
        for part in part_to_signals_arr[idx].iter().copied().flat_map(|sig| sig_to_coni[&sig].iter().copied().map(|coni| coni_to_part[coni])).filter(|opart_id| *opart_id != idx) {
            if last_seen_at[part] != idx + 1 {
                last_seen_at[part] = idx + 1;
                neighbours.push(part);
            }
        }
        neighbours}
    ).collect();

    // include dead-ends as outputs
    if dead_ends_as_outputs{ output_parts.extend((0..n_parts).filter(|parti| !input_parts.contains(parti) && adjacencies[*parti].len() == 1)); }
    
    MixedGraph::new(partition, adjacencies, input_parts, output_parts)
}

fn conservative_hierarchy<'a, C: Constraint + 'a, S: Circuit<C> + 'a>(
    circ: &'a S, node_id_generator: &mut dyn Iterator<Item = usize>,
    mut graph: MixedGraph, timer: Instant, debug: usize) -> HashMap<usize, DAGNode<'a, C, S>> {

    if debug > 1 { println!("LOG: Found distances to sources in {:?}", timer.elapsed().as_secs_f32()); }

    // make the preorder
    graph.orient_by_partial_order();
    graph.orient_leaf_parts();

    if debug > 1 { println!("LOG: Constructed preorder in {:?}", timer.elapsed().as_secs_f32()); }

    // DAGNode indices might not be 0..n_parts so now need to do some pointer work
    // need idx => node_id for arcs 
    let (mut nodes, _, _) = graph.initialise_dagnodes(circ, node_id_generator);
    if debug > 1 { println!("LOG: Initialised nodes in {:?}", timer.elapsed().as_secs_f32()); }

    // merge remaining nodes
    let mut undirected_components = UnionFind::new(false);
    for e in 0..graph.m {
        if !graph.edge_oriented(e) {undirected_components.union([graph.edges[e].0, graph.edges[e].1].into_iter())}
    }

    let mut coni_to_node: Vec<usize> = vec![0; circ.n_constraints()];
    for (coni, node_id) in nodes.values().flat_map(|node| node.constraints.iter().map(|coni| (coni, node.id))) { coni_to_node[*coni] = node_id };

    if debug > 1 { println!("LOG: Determined fuzzy components in {:?}", timer.elapsed().as_secs_f32()); }

    let components_to_merge = undirected_components.get_components();
    if debug > 1 { println!("LOG: Need to merge {:?} components with total size {:?}", components_to_merge.len(), components_to_merge.iter().map(|s| s.len()).sum::<usize>()); }

    let sig_to_coni = signals_to_constraints_with_them(circ.get_constraints(), None, None);
    for to_merge in components_to_merge.into_iter() {
        DAGNode::merge_nodes(to_merge.into_iter().collect(), &mut nodes, &sig_to_coni, &mut coni_to_node);
    }
    if debug > 1 { println!("LOG: Merged fuzzy components in {:?}", timer.elapsed().as_secs_f32()); }

    nodes
}

fn optimisation_hierarchy<'a, C: Constraint + 'a, S: Circuit<C> + 'a>(
    circ: &'a S, node_id_generator: &mut dyn Iterator<Item = usize>,
    mut graph: MixedGraph, timer: Instant, debug: usize) -> HashMap<usize, DAGNode<'a, C, S>> {
    
    // Preprocessing Step: Merge all equivalence class together
    // Calculate Distances and Orient Edges
    graph.merge_equivalence_classes_by_distance_and_orient();

    // Have SAT Solver decide on other fuses
    let to_merge = dag_from_partition_solver(&graph, debug);
        
    let mut undirected_components = UnionFind::new(false);
    for (u, v) in to_merge.into_iter() {
        undirected_components.union([u, v].into_iter());
    }
    for v in 0..graph.n {undirected_components.find(v);}

    graph = graph.merge(undirected_components);
    graph.orient_by_partial_order();

    if (0..graph.m).into_iter().filter(|&e| !graph.edge_oriented(e)).count() > 0 {panic!("Fusing left following unoriented edges (max 100 shown): {:?}", (0..graph.m).into_iter().filter(|&e| !graph.edge_oriented(e)).map(|e| graph.edges[e]).take(100).collect::<Vec<_>>())}
    let (nodes, _, _) = graph.initialise_dagnodes(circ, node_id_generator);
    nodes
}

pub fn dag_from_partition<'a, C: Constraint + 'a, S: Circuit<C> + 'a>(
    circ: &'a S, partition: Vec<Vec<usize>>, node_id_generator: &mut dyn Iterator<Item = usize>,
    dead_ends_as_outputs: bool, hierarchy_mode: HierarchyMode, debug: usize) -> HashMap<usize, DAGNode<'a, C, S>> {

    let timer = Instant::now();

    let graph = get_intial_components(circ, partition, dead_ends_as_outputs, debug);

    if debug > 1 { println!("LOG: Total-edges {:?}, max-edges {:?}", graph.adjacencies.iter().map(|set| set.len()).sum::<usize>() >> 1, graph.adjacencies.iter().map(|set| set.len()).max()); }
    if debug > 1 { println!("LOG: Adjacency preprocessing done in {:?}", timer.elapsed().as_secs_f32()); }

    match hierarchy_mode {
        HierarchyMode::Conservative => conservative_hierarchy(
            circ, node_id_generator, graph, 
            timer, debug),
        HierarchyMode::Optimisation => optimisation_hierarchy(
            circ, node_id_generator, graph, 
            timer, debug),
        HierarchyMode::Extension => {panic!("Extension is currently unimplemented awaiting retooling");}
        // HierarchyMode::Extension => extension_hierarchy(
        //     circ, node_id_generator, graph, 
        //     timer, debug)
    }
}
