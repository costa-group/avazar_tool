use std::time::{Instant};

use circom_algebra::num_bigint::BigInt;
use circuits_and_constraints::lightweight_circuit::LightweightCircuit;
use circuits_and_constraints::circuit::Circuit;
use circuits_and_constraints::constraint::Constraint;
use utils::structure::{NodeInfo, StructureReader, TimingInfo};
use circuit_graphing::directed_acyclic_graph::dag_from_partition::dag_from_partition;
use circuit_graphing::directed_acyclic_graph::dag_postprocessing::merge_passthrough;
use circuit_graphing::directed_acyclic_graph::equivalence_classes::{subcircuit_fingerprinting_equivalency, subcircuit_fingerprint_with_structural_augmentation_equivalency, subcircuit_fingerprinting_equivalency_and_structural_augmentation_equivalency};
use circuit_graphing::graphing_circuits::{shared_signal_graph_single_clustering, shared_signal_graph_graphrs};
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
    inverse_coni_mapping: Option<&[usize]>,
    inverse_sig_mapping: Option<&[usize]>,
    debug: bool) -> StructureReader {

    let lw_circ = LightweightCircuit::<C>::from(prime, constraints, inputs, outputs);
    decompose_circuit(&lw_circ, resolution, target_size, equivalence_mode, graph_backend, inverse_coni_mapping, inverse_sig_mapping, debug)
}

pub fn decompose_circuit<C: Constraint, S: Circuit<C>>(
    circuit: &S,
    resolution: Option<f64>,
    target_size: Option<f64>,
    equivalence_mode: EquivalenceMode,
    graph_backend: GraphBackend,
    inverse_coni_mapping: Option<&[usize]>,
    inverse_sig_mapping: Option<&[usize]>,
    _debug: bool
) -> StructureReader {

    let mut timing_info: TimingInfo = TimingInfo{
    	clustering: 0.0,
        graph_construction: 0.0,
    	dag_construction: 0.0,
    	equivalency: 0.0,
    	total: 0.0,
    };

    /*
    fn insert_and_print_timing(debug: bool, timing: &mut HashMap<&'static str, Duration>, key: &'static str, val: Duration) {
    	timing.insert(key, val);
    	if debug {println!("Completed {}: {:?}", key, timing.get(&key));}
    }
    */

    let graph_construction_timer = Instant::now();
    
    let backend = graph_backend;
    let graph: Box<dyn CanLeiden> = 
        match backend {
            GraphBackend::GraphRS => {
                Box::new(shared_signal_graph_graphrs(circuit))
            }
            GraphBackend::SingleClustering => {
                Box::new(shared_signal_graph_single_clustering(circuit))
            }
        };
    
    //insert_and_print_timing(debug, &mut timing, "graph_construction", graph_construction_timer.elapsed());
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
    
    let mut dagnodes = dag_from_partition(circuit, partition);
    merge_passthrough(circuit, &mut dagnodes);
    
    //insert_and_print_timing(debug, &mut timing, "dag_construction_merging", dagnode_timer.elapsed());
    timing_info.dag_construction = dagnode_timer.elapsed().as_secs_f32();
    timing_info.total += timing_info.dag_construction;

    let equivalency_timer = Instant::now();
    let (mut equivalency_local, mut equivalency_structural): (Option<Vec<Vec<usize>>>, Option<Vec<Vec<usize>>>) = (None, None);
    match equivalence_mode {
        EquivalenceMode::None => (),
        EquivalenceMode::Local => {equivalency_local = Some(subcircuit_fingerprinting_equivalency(&mut dagnodes));},
        EquivalenceMode::Structural => {equivalency_structural = Some(subcircuit_fingerprint_with_structural_augmentation_equivalency(&mut dagnodes));}
        EquivalenceMode::Total => {
            let (equivalency_local_, equivalency_structural_) = subcircuit_fingerprinting_equivalency_and_structural_augmentation_equivalency(&mut dagnodes);
            (equivalency_local, equivalency_structural) = (Some(equivalency_local_), Some(equivalency_structural_))
        }
    };

    //insert_and_print_timing(debug, &mut timing, "equivalency", equivalency_timer.elapsed());
    timing_info.equivalency = equivalency_timer.elapsed().as_secs_f32();
    timing_info.total += timing_info.equivalency;


    //insert_and_print_timing(debug, &mut timing, "total", total_time);


    let dagnode_info: Vec<NodeInfo> = dagnodes.into_values().map(|node| node.to_json(inverse_coni_mapping, inverse_sig_mapping)).collect();
    StructureReader {timing: timing_info, nodes: dagnode_info, equivalency_local: equivalency_local, equivalency_structural: equivalency_structural}
}
