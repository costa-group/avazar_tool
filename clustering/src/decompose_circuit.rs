use std::collections::{HashMap, HashSet};
use std::time::{Instant};
use std::borrow::Borrow;

use circom_algebra::num_bigint::BigInt;
use circuits_and_constraints::lightweight_circuit::LightweightCircuit;
use circuits_and_constraints::circuit::Circuit;
use circuits_and_constraints::constraint::Constraint;
use utils::structure::{NodeInfo, StructureReader, TimingInfo};
use circuit_graphing::directed_acyclic_graph::{DAGNode};
use circuit_graphing::directed_acyclic_graph::dag_from_partition::dag_from_partition;
use circuit_graphing::directed_acyclic_graph::dag_postprocessing::merge_passthrough;
use circuit_graphing::directed_acyclic_graph::equivalence_classes::{subcircuit_fingerprinting_equivalency, subcircuit_fingerprint_with_structural_augmentation_equivalency, subcircuit_fingerprinting_equivalency_and_structural_augmentation_equivalency};
use circuit_graphing::graphing_circuits::{shared_signal_graph};
use circuit_graphing::leiden_clustering::{CanLeiden};
use circuit_graphing::bridge_partitioning::{bridge_partitioning};
use utils::small_utilities::{EquivalenceMode, ClusteringPreprocessing, DecomposeOptions};

pub fn decompose_node<C: Constraint>(
    prime: &BigInt,
    constraints: &Vec<C>, 
    inputs: &[usize], 
    outputs: &[usize],
    decompose_options: DecomposeOptions) -> StructureReader {

    let lw_circ = LightweightCircuit::<C>::from(prime, constraints, inputs, outputs);
    decompose_circuit(&lw_circ, decompose_options)
}

fn decompose_circuit_and_return_dagnodes<'a, C: Constraint, S: Circuit<C>>(
    circuit: &'a S,
    node_id_generator: &mut dyn Iterator<Item = usize>,
    decompose_options: DecomposeOptions
) -> (TimingInfo, HashMap<usize, DAGNode<'a, C, S>>) {

    if decompose_options.debug > 0 {println!("LOG: Beginning Clustering of {:?} constraints", circuit.n_constraints());}
    let mut timing_info: TimingInfo = TimingInfo{
    	clustering: 0.0,
        graph_construction: Some(0.0),
    	dag_construction: 0.0,
    	equivalency: 0.0,
    	total: 0.0,
    };

    let partition: Vec<Vec<usize>> ;
    if decompose_options.existing_partition.is_none() {
        let graph_construction_timer = Instant::now();
        let graph: Box<dyn CanLeiden> = shared_signal_graph(circuit, decompose_options.graph_backend, decompose_options.debug);
        
        timing_info.graph_construction = Some(graph_construction_timer.elapsed().as_secs_f32());
        if decompose_options.debug > 0 {println!("LOG: Finished graph construction in {:?}s", timing_info.graph_construction.unwrap());}

        // Partition Graph
        let partition_timer = Instant::now();

        let resolution = match decompose_options.resolution { Some(r) => r, None => ((graph.num_edges() << 1) as f64)/(decompose_options.target_size.unwrap_or(f64::log2(graph.num_edges() as f64)).powi(2)) };
        partition = graph.get_partition(resolution, decompose_options.leiden_max_iterations.unwrap_or(5), 25565);
        
        //insert_and_print_timing(debug, &mut timing, "clustering", partition_timer.elapsed());
        timing_info.clustering = partition_timer.elapsed().as_secs_f32();
        timing_info.total += timing_info.clustering;
        if decompose_options.debug > 0 {println!("LOG: Finished clustering in {:?}s", timing_info.clustering);}
        if decompose_options.debug > 1{println!("LOG: Partitioned into {:?} parts", partition.len());}
    } else {
        partition = decompose_options.existing_partition.unwrap();
    }

    // Convert into DAG
    let dagnode_timer = Instant::now();
    
    let mut dagnodes = dag_from_partition(circuit, partition, node_id_generator, decompose_options.debug);
    merge_passthrough(circuit, &mut dagnodes);
    
    //insert_and_print_timing(debug, &mut timing, "dag_construction_merging", dagnode_timer.elapsed());
    timing_info.dag_construction = dagnode_timer.elapsed().as_secs_f32();
    timing_info.total += timing_info.dag_construction;

    if decompose_options.inverse_coni_mapping.is_some() || decompose_options.inverse_sig_mapping.is_some() {
        for node in dagnodes.values_mut() {node.map_internal_indices(decompose_options.inverse_coni_mapping, decompose_options.inverse_sig_mapping);} 
    }
    if decompose_options.debug > 0 {println!("LOG: Finished DAG construction in {:?}s", timing_info.dag_construction);}
    if decompose_options.debug > 1{println!("LOG: DAG has {:?} nodes", dagnodes.len());}

    (timing_info, dagnodes)
}

fn decompose_circuit_over_dagnodes<'a, C: Constraint, S: Circuit<C>>(
    circuit: &'a S,
    timing: &mut TimingInfo,
    dagnodes: &HashMap<usize, DAGNode<'a, C, S>>,
    decompose_options: DecomposeOptions
) -> HashMap<usize, DAGNode<'a, C, S>> {

    let mut node_id_generator = 0..;
    let constraints = circuit.get_constraints();
    let mut new_dagnodes: HashMap<usize, DAGNode<'a, C, S>> = HashMap::new();
    let mut previd_to_newids: HashMap<usize, HashSet<usize>> = HashMap::new();

    // cluster each node individually
    for (nodid, node) in dagnodes.into_iter() {

        if node.len() == 1 {
            let new_id = node_id_generator.next().unwrap();
            new_dagnodes.insert(new_id, DAGNode::new(circuit, new_id, node.get_constraint_indices().collect(), node.get_input_signals().clone(), node.get_output_signals().clone(), None, None));
            previd_to_newids.insert(*nodid, [new_id].into_iter().collect());
            continue;
        }
            
        let lwcirc = LightweightCircuit::<C>::from(
            circuit.prime(), 
            node.get_constraint_indices().map(|coni| constraints[coni].borrow()).collect::<Vec<_>>(), 
            node.get_input_signals(), 
            node.get_output_signals()
        );

        let current_options = DecomposeOptions {
            resolution: decompose_options.resolution,
            target_size: decompose_options.target_size,
            leiden_max_iterations: decompose_options.leiden_max_iterations,
            graph_backend: decompose_options.graph_backend,
            inverse_coni_mapping: Some(&node.get_constraint_indices().collect::<Vec<_>>()),
            debug: decompose_options.debug.checked_sub(1).unwrap_or_default(),
            ..Default::default()
        };

        let (new_timing, iteration_dagnodes) = decompose_circuit_and_return_dagnodes(
            &lwcirc, &mut node_id_generator, current_options
        );

        previd_to_newids.insert(*nodid, iteration_dagnodes.keys().copied().collect());
        new_dagnodes.extend(iteration_dagnodes.into_iter().map(|(id, node)| (id, node.replace_circ(circuit))));
        *timing += new_timing;
    }

    // fix predecessor/successor links between nodes

    let signal_to_nodeids = DAGNode::signal_to_nodes(new_dagnodes.values());
    for (nodid, node) in dagnodes.into_iter() {

        let new_predecessors: HashSet<&usize> = node.get_predecessors().into_iter().flat_map(|prev_id| previd_to_newids[prev_id].iter()).collect();
        let new_successors: HashSet<&usize> = node.get_successors().into_iter().flat_map(|prev_id| previd_to_newids[prev_id].iter()).collect();

        for subnode in previd_to_newids[nodid].iter() {
            let adjacent_nodes: HashSet<&usize> = new_dagnodes[subnode].signals().into_iter().flat_map(|signal| signal_to_nodeids[&signal].iter()).collect();
            new_dagnodes.get_mut(subnode).unwrap().add_predecessors(adjacent_nodes.intersection(&new_predecessors).copied().copied());
            new_dagnodes.get_mut(subnode).unwrap().add_successors(adjacent_nodes.intersection(&new_successors).copied().copied());

            // no need to update the other way as they will appear in this process for corresponding node
        }
    }

    new_dagnodes
}

pub fn decompose_circuit<C: Constraint, S: Circuit<C>>(
    circuit: &S,
    mut decompose_options: DecomposeOptions
) -> StructureReader {

    let mut timing_info: TimingInfo = TimingInfo{
    	clustering: 0.0,
        graph_construction: Some(0.0),
    	dag_construction: 0.0,
    	equivalency: 0.0,
    	total: 0.0,
    };

    // Options required for 2nd part and not first
    let equivalence_mode = decompose_options.equivalence_mode;
    let equivalence_comparison_budget = decompose_options.equivalence_comparison_budget;
    let minimum_equivalence_size = decompose_options.equivalence_comparison_budget;
    let inverse_coni_mapping = decompose_options.inverse_coni_mapping.take();
    let inverse_sig_mapping = decompose_options.inverse_sig_mapping.take();
    let debug = decompose_options.debug;

    let mut dagnodes = match decompose_options.preprocessing {
        ClusteringPreprocessing::None => {
            let (new_timing, new_dagnodes) = decompose_circuit_and_return_dagnodes(
                circuit, &mut (0..), decompose_options
            );
            timing_info += new_timing;
            new_dagnodes
        }
        _ => {
            let preprocessed_nodes = match decompose_options.preprocessing {
                ClusteringPreprocessing::BridgeFinding => bridge_partitioning(circuit, true, decompose_options.debug),
                _ => {panic!("Unimplemented partitioning method {:?}", decompose_options.preprocessing);}
            };
            decompose_circuit_over_dagnodes(
                circuit, &mut timing_info, &preprocessed_nodes, decompose_options
            )
        }
    };

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

    timing_info.equivalency = equivalency_timer.elapsed().as_secs_f32();
    timing_info.total += timing_info.equivalency;
    if debug > 0 {println!("LOG: Finished equivalence in {:?}s", timing_info.equivalency);}

    let dagnode_info: Vec<NodeInfo> = dagnodes.into_values().map(|node| node.to_json(inverse_coni_mapping, inverse_sig_mapping)).collect();
    StructureReader {timing: timing_info, nodes: dagnode_info, equivalency_local: equivalency_local, equivalency_structural: equivalency_structural}
}
