use std::collections::HashMap;
use std::time::{Instant, Duration};
use std::fmt::Debug;
use serde::{Serialize};

use circuits_and_constraints::circuit::Circuit;
use circuits_and_constraints::constraint::Constraint;
use circuit_graphing::directed_acyclic_graph::{NodeInfo};
use circuit_graphing::directed_acyclic_graph::dag_from_partition::dag_from_partition;
use circuit_graphing::directed_acyclic_graph::dag_postprocessing::merge_passthrough;
use circuit_graphing::directed_acyclic_graph::equivalence_classes::{subcircuit_fingerprinting_equivalency, subcircuit_fingerprint_with_structural_augmentation_equivalency, subcircuit_fingerprinting_equivalency_and_structural_augmentation_equivalency};
use circuit_graphing::graphing_circuits::{shared_signal_graph_single_clustering, shared_signal_graph_graphrs};
use crate::argument_parsing::{GraphBackend, EquivalenceMode};
use crate::leiden_clustering::{CanLeiden};

#[derive(Debug, Serialize)]
pub struct StructureReader {
    timing: HashMap<&'static str, Duration>,
    nodes: Vec<NodeInfo>,
    equivalency_local: Option<Vec<Vec<usize>>>,
    equivalency_structural: Option<Vec<Vec<usize>>>
}

pub fn decompose_circuit<C: Constraint, S: Circuit<C>>(
    circuit: &S,
    resolution: Option<f64>,
    target_size: Option<f64>,
    equivalence_mode: EquivalenceMode,
    graph_backend: GraphBackend,
    debug: bool
) -> StructureReader {

    let mut timing:  HashMap<&'static str, Duration> = HashMap::new();
    fn insert_and_print_timing(debug: bool, timing: &mut HashMap<&'static str, Duration>, key: &'static str, val: Duration) {timing.insert(key, val);if debug {println!("Completed {}: {:?}", key, timing.get(&key));}}

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
    
    insert_and_print_timing(debug, &mut timing, "graph_construction", graph_construction_timer.elapsed());

    // Partition Graph
    let partition_timer = Instant::now();

    let resolution = match resolution { Some(r) => r, None => ((graph.num_edges() << 1) as f64)/(target_size.unwrap_or(f64::log2(graph.num_edges() as f64)).powi(2)) };
    let partition: Vec<Vec<usize>> = graph.get_partition(resolution, 5, 25565);
    
    insert_and_print_timing(debug, &mut timing, "clustering", partition_timer.elapsed());

    // Convert into DAG
    let dagnode_timer = Instant::now();
    
    let mut dagnodes = dag_from_partition(circuit, partition);
    merge_passthrough(circuit, &mut dagnodes);
    
    insert_and_print_timing(debug, &mut timing, "dag_construction_merging", dagnode_timer.elapsed());

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

    insert_and_print_timing(debug, &mut timing, "equivalency", equivalency_timer.elapsed());

    let total_time: Duration = timing.values().sum();
    insert_and_print_timing(debug, &mut timing, "total", total_time);

    let dagnode_info: Vec<NodeInfo> = dagnodes.into_values().map(|node| node.to_json(None, None)).collect();
    StructureReader {timing: timing, nodes: dagnode_info, equivalency_local: equivalency_local, equivalency_structural: equivalency_structural}
}