use std::time::{Instant};
use std::borrow::Borrow;
use std::collections::{HashSet, HashMap};

use circom_algebra::num_bigint::BigInt;
use circuits_and_constraints::lightweight_circuit::LightweightCircuit;
use circuits_and_constraints::circuit::Circuit;
use circuits_and_constraints::constraint::Constraint;
use utils::structure::{NodeInfo, StructureReader, TimingInfo};
use circuit_graphing::directed_acyclic_graph::DAGNode;
use circuit_graphing::directed_acyclic_graph::dag_from_partition::dag_from_partition;
use circuit_graphing::directed_acyclic_graph::dag_postprocessing::merge_passthrough;
use circuit_graphing::directed_acyclic_graph::equivalence_classes::{subcircuit_fingerprinting_equivalency, subcircuit_fingerprint_with_structural_augmentation_equivalency, subcircuit_fingerprinting_equivalency_and_structural_augmentation_equivalency};
use circuit_graphing::graphing_circuits::{shared_signal_graph_graphrs};
use crate::argument_parsing::{GraphBackend, EquivalenceMode};
use crate::leiden_clustering::{CanLeiden};


pub fn decompose_node<C: Constraint>(
    prime: &BigInt, 
    constraints: &Vec<C>, 
    inputs: &[usize], 
    outputs: &[usize],
    resolution: Option<f64>,
    target_size: Option<f64>,
    equivalence_mode: EquivalenceMode,
    graph_backend: GraphBackend,
    node_id_generator: Option<&mut dyn Iterator<Item = usize>>,
    inverse_coni_mapping: Option<&[usize]>,
    inverse_sig_mapping: Option<&[usize]>,
    maximum_cluster_size: Option<usize>,
    minimum_equivalence_size: Option<usize>,
    equivalence_comparison_budget: Option<usize>,
    debug: bool) -> StructureReader {

    let lw_circ = LightweightCircuit::<C>::from(prime, constraints, inputs, outputs);
    decompose_circuit(
        &lw_circ, 
        resolution, target_size, equivalence_mode, graph_backend, node_id_generator,
        inverse_coni_mapping, inverse_sig_mapping, maximum_cluster_size, 
        minimum_equivalence_size, equivalence_comparison_budget,
        debug)
}

fn decompose_circuit_and_return_dagnodes<'a, C: Constraint, S: Circuit<C>>(
    circuit: &'a S,
    resolution: Option<f64>,
    target_size: Option<f64>,
    graph_backend: GraphBackend,
    node_id_generator: &mut dyn Iterator<Item = usize>,
    inverse_coni_mapping: Option<&[usize]>,
    inverse_sig_mapping: Option<&[usize]>,
    _debug: bool
) -> (TimingInfo, HashMap<usize, DAGNode<'a, C, S>>) {

    let mut timing_info: TimingInfo = TimingInfo{
    	clustering: 0.0,
        graph_construction: 0.0,
    	dag_construction: 0.0,
    	equivalency: 0.0,
    	total: 0.0,
    };

    let graph_construction_timer = Instant::now();
    
    let backend = graph_backend;
    let graph: Box<dyn CanLeiden> = 
        match backend {
            GraphBackend::GraphRS => {
                Box::new(shared_signal_graph_graphrs(circuit))
            }
            GraphBackend::SingleClustering => {
                panic!("SingleClustering currently unsupported due to dependency issues")
                // Box::new(shared_signal_graph_single_clustering(circuit))
            }
        };
    
    timing_info.graph_construction = graph_construction_timer.elapsed().as_secs_f32();

    // Partition Graph
    let partition_timer = Instant::now();

    let resolution = match resolution { Some(r) => r, None => ((graph.num_edges() << 1) as f64)/(target_size.unwrap_or(f64::log2(graph.num_edges() as f64)).powi(2)) };
    let partition: Vec<Vec<usize>> = graph.get_partition(resolution, 5, 25565);
    
    //insert_and_print_timing(debug, &mut timing, "clustering", partition_timer.elapsed());
    timing_info.clustering = partition_timer.elapsed().as_secs_f32();
    timing_info.total += timing_info.clustering;

    // Convert into DAG
    let dagnode_timer = Instant::now();
    
    let mut dagnodes = dag_from_partition(circuit, partition, node_id_generator);
    merge_passthrough(circuit, &mut dagnodes);
    
    //insert_and_print_timing(debug, &mut timing, "dag_construction_merging", dagnode_timer.elapsed());
    timing_info.dag_construction = dagnode_timer.elapsed().as_secs_f32();
    timing_info.total += timing_info.dag_construction;

    if inverse_coni_mapping.is_some() || inverse_sig_mapping.is_some() {
        for node in dagnodes.values_mut() {node.map_internal_indices(inverse_coni_mapping, inverse_sig_mapping);} 
    }

    (timing_info, dagnodes)
}

fn decompose_nodes_until_max_size<'a, C: Constraint, S: Circuit<C>>(
    circuit: &'a S,
    timing: &mut TimingInfo,
    dagnodes: &mut HashMap<usize, DAGNode<'a, C, S>>,
    resolution: Option<f64>,
    target_size: Option<f64>,
    graph_backend: GraphBackend,
    node_id_generator: &mut dyn Iterator<Item = usize>,
    maximum_cluster_size: usize,
    debug: bool
) -> () {

    let mut node_id_stack: Vec<usize> = dagnodes.keys().copied().collect();
    let constraints = circuit.get_constraints();

    // for each node in dagnode
    while node_id_stack.len() > 0 {

        let node_id = node_id_stack.pop().unwrap();

        // if it is too big
        if dagnodes[&node_id].len() > maximum_cluster_size {

            // remove it from dagnodes, and create a lightweight circuit
            let node = dagnodes.remove(&node_id).unwrap();
            
            let lwcirc = LightweightCircuit::<C>::from(
                circuit.prime(), 
                node.get_constraint_indices().map(|coni| constraints[coni].borrow()).collect::<Vec<_>>(), 
                node.get_input_signals(), 
                node.get_output_signals()
            );

            // recluster that node
            let (new_timing, new_dagnodes) = decompose_circuit_and_return_dagnodes(
                &lwcirc, resolution, target_size, graph_backend, node_id_generator,
                Some(&node.get_constraint_indices().collect::<Vec<_>>()), None, debug
            );

            let mut new_dagnodes: HashMap<usize, DAGNode<'a, C, S>> = 
                new_dagnodes.into_iter().map(|(id, node)| (id, node.replace_circ(circuit))).collect();

            // cluster is stable
            if new_dagnodes.len() == 1 {
                dagnodes.insert(node_id, node);
                continue;
            }

            // fix the successor/predecessor links for internal to external
            let signal_to_nodeid = DAGNode::signal_to_nodes(new_dagnodes.values());
            
            let signal_to_successors = DAGNode::signal_to_nodes(node.get_successors().into_iter().map(|id| &dagnodes[id]));
            let signal_to_predecessors = DAGNode::signal_to_nodes(node.get_predecessors().into_iter().map(|id| &dagnodes[id]));

            for new_node in new_dagnodes.values_mut() {
                let new_predecessors = new_node.signals().into_iter()
                                            .flat_map(|sig| signal_to_predecessors.get(&sig).into_iter().flatten())
                                            .copied().collect::<HashSet<usize>>();
                let new_successors = new_node.signals().into_iter()
                                            .flat_map(|sig| signal_to_successors.get(&sig).into_iter().flatten())
                                            .copied().collect::<HashSet<usize>>();
                new_node.add_predecessors(new_predecessors.into_iter());
                new_node.add_successors(new_successors.into_iter());
            }

            // TODO: code duplication -- fixes successor/predecessor links for external to internal
            for predecessor in node.get_predecessors() {
                let new_successors = dagnodes[predecessor].signals().into_iter()
                    .flat_map(|sig| signal_to_nodeid.get(&sig).into_iter().flatten())
                    .copied().collect::<HashSet<usize>>().into_iter();

                let predecessor_node = dagnodes.get_mut(&predecessor).unwrap();

                predecessor_node.remove_successors(node_id);
                predecessor_node.add_successors(new_successors);
            }

            for successor in node.get_successors() {
                let new_predecessors = dagnodes[successor].signals().into_iter()
                    .flat_map(|sig| signal_to_nodeid.get(&sig).into_iter().flatten())
                    .copied().collect::<HashSet<usize>>().into_iter();
                let successor_node = dagnodes.get_mut(&successor).unwrap();

                successor_node.remove_predecessor(node_id);
                successor_node.add_predecessors(new_predecessors);
            }

            // add to nodes to check and dagnodes
            node_id_stack.extend(new_dagnodes.keys().copied());
            dagnodes.extend(new_dagnodes.into_iter());

            // update times
            *timing += new_timing
        }
    }

}

pub fn decompose_circuit<C: Constraint, S: Circuit<C>>(
    circuit: &S,
    resolution: Option<f64>,
    target_size: Option<f64>,
    equivalence_mode: EquivalenceMode,
    graph_backend: GraphBackend,
    node_id_generator: Option<&mut dyn Iterator<Item = usize>>,
    inverse_coni_mapping: Option<&[usize]>,
    inverse_sig_mapping: Option<&[usize]>,
    maximum_cluster_size: Option<usize>,
    minimum_equivalence_size: Option<usize>,
    equivalence_comparison_budget: Option<usize>,
    debug: bool
) -> StructureReader {

    let mut default_id_generator = 0..;
    let node_id_generator = node_id_generator.unwrap_or(&mut default_id_generator);

    let (mut timing_info, mut dagnodes) = decompose_circuit_and_return_dagnodes(
        circuit, resolution, target_size, graph_backend, node_id_generator, None, None, debug
    );

    // if recursive
    if maximum_cluster_size.is_some() {
        decompose_nodes_until_max_size(circuit, &mut timing_info, &mut dagnodes, resolution, target_size, graph_backend, 
            node_id_generator, maximum_cluster_size.unwrap(), debug);
    }

    let equivalency_timer = Instant::now();
    let (mut equivalency_local, mut equivalency_structural): (Option<Vec<Vec<usize>>>, Option<Vec<Vec<usize>>>) = (None, None);
    match equivalence_mode {
        EquivalenceMode::None => (),
        EquivalenceMode::Local => {
            equivalency_local = Some(subcircuit_fingerprinting_equivalency(
                &mut dagnodes, minimum_equivalence_size, equivalence_comparison_budget));},
        EquivalenceMode::Structural => {
            equivalency_structural = Some(subcircuit_fingerprint_with_structural_augmentation_equivalency(
                &mut dagnodes, minimum_equivalence_size, equivalence_comparison_budget));}
        EquivalenceMode::Total => {
            let (equivalency_local_, equivalency_structural_) = subcircuit_fingerprinting_equivalency_and_structural_augmentation_equivalency(
                &mut dagnodes, minimum_equivalence_size, equivalence_comparison_budget);
            (equivalency_local, equivalency_structural) = (Some(equivalency_local_), Some(equivalency_structural_))
        }
    };

    //insert_and_print_timing(debug, &mut timing, "equivalency", equivalency_timer.elapsed());
    timing_info.equivalency = equivalency_timer.elapsed().as_secs_f32();
    timing_info.total += timing_info.equivalency;

    let dagnode_info: Vec<NodeInfo> = dagnodes.into_values().map(|node| node.to_json(inverse_coni_mapping, inverse_sig_mapping)).collect();
    StructureReader {timing: timing_info, nodes: dagnode_info, equivalency_local: equivalency_local, equivalency_structural: equivalency_structural}
}
