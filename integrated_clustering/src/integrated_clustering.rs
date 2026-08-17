use std::time::{Instant};
use std::marker::{Send, Sync};

use circuits_constraints_and_algebra::algebra::EncodableConstraint;
use utils::structure::{TimingInfo, StructureInfo, NodeInfo, TimingCategories};
use utils::small_utilities::{DecomposeOptions};
use crate::hierarchy_solver::{hierarchy_solver, HierarchyOptions, IntegratedHierarchy, determinism::DeterminismFormula};
use circuits_constraints_and_algebra::constraint::Constraint;
use circuits_constraints_and_algebra::circuit::Circuit;
use circuit_graphing::graphing_circuits::{undo_clique_clusters, shared_signal_graph};
use circuit_graphing::leiden_clustering::{CanLeiden};
use zkgenver::determinism::determinism_check::{prove_safety_internal, ResultInfoDeterminism, DeterminismOptions};

// TODO: get first working version with determinism, then generalise to any problem with similar input/output property

pub fn decompose_circuit_and_check_determinism<C: Constraint + EncodableConstraint + Send + Sync + Clone + 'static, S: Circuit<C> + Sync + 'static>(
    circuit: &S,
    decompose_options: DecomposeOptions,
    hierarchy_options: HierarchyOptions,
    determinism_options: DeterminismOptions,
    extract_integrated_hierarchy: Option<PathBuf>
) -> ResultInfoDeterminism {

    // Step 1: Get partition

    if decompose_options.debug > 0 {println!("LOG: Beginning Clustering of {:?} constraints", circuit.n_constraints());}
    let mut timing_info = TimingInfo::new();

    let partition: Vec<Vec<usize>>;
    if decompose_options.existing_partition.is_none() {
        let graph_construction_timer = Instant::now();
        let (graph, clique_clusters): (Box<dyn CanLeiden>, Vec<Vec<usize>>) = shared_signal_graph(circuit, decompose_options.graph_backend, decompose_options.clique_cluster_size, decompose_options.debug);
        
        timing_info.insert(TimingCategories::GraphConstruction, graph_construction_timer.elapsed().as_secs_f32());
        *timing_info.entry(TimingCategories::Total).or_default() += timing_info[&TimingCategories::GraphConstruction];

        if decompose_options.debug > 0 {println!("LOG: Finished graph construction in {:?}s", timing_info[&TimingCategories::GraphConstruction]);}

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
        timing_info.insert(TimingCategories::Clustering, partition_timer.elapsed().as_secs_f32());
        *timing_info.entry(TimingCategories::Total).or_default() += timing_info[&TimingCategories::Clustering];
        if decompose_options.debug > 0 {println!("LOG: Finished clustering in {:?}s", timing_info[&TimingCategories::Clustering]);}
        if decompose_options.debug > 1 {println!("LOG: Partitioned into {:?} parts", partition.len());}
    } else {
        partition = decompose_options.existing_partition.unwrap();
    }

    if let Some(path) = decompose_options.extract_raw_partition {
        use std::fs::File;
        use std::io::BufWriter;
        use std::io::Write;

        let file = File::create(path).unwrap();
        let mut writer = BufWriter::new(file);

        // Write the result.
        let value = serde_json::to_string_pretty(&partition).unwrap();
        writer.write(value.as_bytes()).expect("Error when extracting raw partition");
        writer.flush().expect("Error when extracting raw partition");
    }

    // get hierarchy_from integrated_hierarchy
    let results = hierarchy_solver::<C, S, DeterminismFormula>(circuit, partition, hierarchy_options);
    let IntegratedHierarchy {nodes, verified_nodes, ..} = results;

    // Convert to format for determinism check
    let constraints = circuit.constraints().into_iter().cloned().collect::<Vec<_>>();
    let mut dagnode_info: Vec<NodeInfo> = nodes.into_values().map(|node| node.to_json(None, None)).collect();
    for node in dagnode_info.iter_mut() {node.is_deterministic = verified_nodes.contains(&node.node_id);}
    // TODO: refactor to be able to pass remaining information about known implications to solver
    let all_separate_equivalence_class: Vec<Vec<usize>> = dagnode_info.iter().map(|x| vec![x.node_id]).collect();
    let mut structure = StructureInfo {timing: timing_info, nodes: dagnode_info, local_equivalency: all_separate_equivalence_class.clone(), structural_equivalency: all_separate_equivalence_class};

    if let Some(path) = extract_integrated_hierarchy {write_output_into_file(path, &structure);}

    let (results_info, _) = prove_safety_internal(
        &constraints,
        &mut structure,
        circuit.prime(),
        determinism_options
    );

    results_info
}

use std::io::BufWriter;
use std::fs::File;
use std::path::{PathBuf, Path};
use std::error::Error;
use std::io::Write;
fn write_output_into_file<P: AsRef<Path>>(path: P, result: &StructureInfo) -> Result<(), Box<dyn Error>> {
    // Open the file in read-only mode with buffer.

    let file = File::create(path)?;
    let mut writer = BufWriter::new(file);

    // Write the result.
    let value = serde_json::to_string_pretty(result)?;
    writer.write(value.as_bytes())?;
    writer.flush()?;
    Ok(())
}