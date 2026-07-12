use std::time::{Instant};
use std::marker::{Send, Sync};

use circuits_constraints_and_algebra::algebra::EncodableConstraint;
use utils::structure::{TimingInfo};
use utils::small_utilities::{DecomposeOptions};
use crate::hierarchy_solver::{ResultInfo, hierarchy_solver, HierarchyOptions};
use circuits_constraints_and_algebra::constraint::Constraint;
use circuits_constraints_and_algebra::circuit::Circuit;
use circuit_graphing::graphing_circuits::{undo_clique_clusters, shared_signal_graph};
use circuit_graphing::leiden_clustering::{CanLeiden};

// TODO: get first working version with determinism, then generalise to any problem with similar input/output property

pub fn decompose_circuit_and_check_determinism<C: Constraint + EncodableConstraint + Send + Sync + Clone, S: Circuit<C> + Sync>(
    circuit: &S,
    decompose_options: DecomposeOptions
) -> ResultInfo {

    // Step 1: Get partition

    if decompose_options.debug > 0 {println!("LOG: Beginning Clustering of {:?} constraints", circuit.n_constraints());}
    let mut timing_info = TimingInfo {
    	clustering: 0.0,
        graph_construction: Some(0.0),
    	dag_construction: 0.0,
    	equivalency: 0.0,
    	total: 0.0,
    };

    let partition: Vec<Vec<usize>>;
    if decompose_options.existing_partition.is_none() {
        let graph_construction_timer = Instant::now();
        let (graph, clique_clusters): (Box<dyn CanLeiden>, Vec<Vec<usize>>) = shared_signal_graph(circuit, decompose_options.graph_backend, decompose_options.clique_cluster_size, decompose_options.debug);
        
        timing_info.graph_construction = Some(graph_construction_timer.elapsed().as_secs_f32());
        timing_info.total += timing_info.graph_construction.unwrap();

        if decompose_options.debug > 0 {println!("LOG: Finished graph construction in {:?}s", timing_info.graph_construction.unwrap());}

        // Partition Graph
        let partition_timer = Instant::now();

        let resolution = match decompose_options.resolution { Some(r) => r, None => ((graph.num_edges() << 1) as f64)/(decompose_options.target_size.unwrap_or(f64::log2(graph.num_edges() as f64)).powi(2)) };
        let init_partition = graph.get_partition(resolution, decompose_options.leiden_max_iterations.unwrap_or(5), decompose_options.seed);

        partition = if decompose_options.clique_cluster_size.is_some() {
            undo_clique_clusters(circuit, init_partition, clique_clusters)
        } else {
            init_partition
        };
        
        //insert_and_print_timing(debug, &mut timing, "clustering", partition_timer.elapsed());
        timing_info.clustering = partition_timer.elapsed().as_secs_f32();
        timing_info.total += timing_info.clustering;
        if decompose_options.debug > 0 {println!("LOG: Finished clustering in {:?}s", timing_info.clustering);}
        if decompose_options.debug > 1{println!("LOG: Partitioned into {:?} parts", partition.len());}
    } else {
        partition = decompose_options.existing_partition.unwrap();
    }

    if decompose_options.extract_raw_partition {
        use std::fs::File;
        use std::io::BufWriter;
        use std::io::Write;

        let file = File::create("partition.json").unwrap();
        let mut writer = BufWriter::new(file);

        // Write the result.
        let value = serde_json::to_string_pretty(&partition).unwrap();
        writer.write(value.as_bytes()).expect("Error when extracting raw partition");
        writer.flush().expect("Error when extracting raw partition");
    }

    use crate::hierarchy_solver::{PreprocessingMethods}; 
    use crate::hierarchy_solver::determinism::DeterminismFormula;

    let options = HierarchyOptions {
        preprocessing: vec![PreprocessingMethods::DualDistanceOrdering, PreprocessingMethods::MergeDistanceClasses],
        num_cores: 8,
        debug: decompose_options.debug,
        ..Default::default()
    };

    hierarchy_solver::<C, S, DeterminismFormula>(circuit, partition, options)
}