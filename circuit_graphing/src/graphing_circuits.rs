use combinatorial::Combinations;
use rustc_hash::{FxHashMap};
use std::time::{Instant};
use itertools::Itertools;

use xgraph::{Graph as XGraph};

use circuits_and_constraints::circuit::Circuit;
use circuits_and_constraints::constraint::Constraint;
use circuits_and_constraints::utils::signals_to_constraints_with_them;
use utils::small_utilities::GraphBackend;
use utils::structure::WeightedArcs;
use utils::union_find::UnionFind;

use crate::leiden_clustering::CanLeiden;

pub fn undo_clique_clusters<C: Constraint>(circ: &impl Circuit<C>, partition: Vec<Vec<usize>>, mut clique_clusters: Vec<Vec<usize>>) -> Vec<Vec<usize>> {

    let mut coni_to_clique: FxHashMap<usize, usize> = FxHashMap::default();
    for (i, clique) in clique_clusters.iter().enumerate() {
        for coni in clique.into_iter() {
            coni_to_clique.insert(*coni, circ.n_constraints()+i);
        }
    }

    // remove all the isolated in the clique_cluster if any exist
    // replace any clique_clusters with their clique
    let mut new_partition = Vec::new();
    for part in partition.into_iter() {
        if part.iter().any(|coni| coni_to_clique.contains_key(coni)) {continue;}
        new_partition.push(
            part.into_iter().flat_map(
                |coni| if coni >= circ.n_constraints() {
                    std::mem::take(&mut clique_clusters[coni - circ.n_constraints()]).into_iter()
                } else {
                    vec![coni].into_iter() //TODO: can refactor this to not allocate a temp array 
                }
            ).collect()
        );
    }

    return new_partition
}

fn get_weighted_arcs<C: Constraint>(circ: &impl Circuit<C>, clique_cluster_size: Option<usize>, debug: usize) -> ( FxHashMap<[usize;2], usize>, Vec<Vec<usize>> ) {

    let signal_to_coni_timer = Instant::now();
    let signal_to_coni = signals_to_constraints_with_them(&circ.get_constraints(), None, None);
    if debug > 1 {println!("LOG: finished signal_to_coni calculation in {:?}s", signal_to_coni_timer.elapsed().as_secs_f32());}
    let mut weights: FxHashMap<[usize;2], usize> = FxHashMap::default();

    let mut clique_clusters: Vec<Vec<usize>> = Vec::new();
    let mut coni_to_clique: FxHashMap<usize, usize> = FxHashMap::default();

    if clique_cluster_size.is_some() {

        // get connected components of all cliques above required size
        let mut clique_clusters_uf = UnionFind::new(false);

        for clique in signal_to_coni.values() {
            if clique.len() >= clique_cluster_size.unwrap() {
                clique_clusters_uf.union(clique.iter().copied())
            }
        }
        
        clique_clusters = clique_clusters_uf.get_components();

        // create mapping used in replacement
        for (i, part) in clique_clusters.iter().enumerate() {
            let clique_id = circ.n_constraints()+i;

            // adding the weighted-loop for correct partitioning
            weights.insert([clique_id, clique_id], part.len() * (part.len() - 1));

            for coni in part.into_iter() {
                coni_to_clique.insert(*coni, clique_id);
            }
        }        
    }

    // if constraint in clique already then replace with that clique id
    let check_and_replace = |coni: usize| if coni_to_clique.contains_key(&coni) {coni_to_clique[&coni]} else {coni};
    let transform_pair = |pair: Vec<usize>| if clique_cluster_size.is_none() {pair} else {pair.into_iter().map(check_and_replace).sorted().collect::<Vec<_>>()};

    let weights_timer = Instant::now();
    for pair in signal_to_coni.into_values().flat_map(|conis| Combinations::of_size(conis, 2)) {
        weights.entry(transform_pair(pair).try_into().unwrap()).and_modify(|x| *x += 1).or_insert(1);
    }
    if debug > 1 {println!("LOG: finished weights calculation in {:?}s", weights_timer.elapsed().as_secs_f32());}
    (weights, clique_clusters)
}

fn shared_signal_graph_xgraph<C: Constraint>(circ: &impl Circuit<C>, clique_cluster_size: Option<usize>, debug: usize) -> (XGraph<f64, (), ()>, Vec<Vec<usize>>) {
    let (weights, clique_clusters) = get_weighted_arcs(circ, clique_cluster_size, debug);
    let mut graph = XGraph::new(false);
    // nodes are indices of the 
    graph.add_nodes_batch(std::iter::repeat(()).take(circ.n_constraints()));
    graph.add_edges_batch(weights.into_iter().map(|(pair, val)| (pair[0], pair[1], val as f64, ())).collect::<Vec<_>>()).unwrap();
    
    (graph, clique_clusters)
}

fn shared_signal_graph_graphrs<C: Constraint>(circ: &impl Circuit<C>, clique_cluster_size: Option<usize>, debug: usize) -> (WeightedArcs<usize>, Vec<Vec<usize>>) {

    let (weights, clique_clusters) = get_weighted_arcs(circ, clique_cluster_size, debug);
    ( WeightedArcs {original_nodes: (0..circ.n_constraints()+clique_clusters.len()).collect(), arcs: weights.into_iter().map(|([k0, k1], w)| (k0, k1, w as f64)).collect()}, clique_clusters)
}

pub fn shared_signal_graph<C: Constraint>(circ: &impl Circuit<C>, backend: GraphBackend, clique_cluster_size: Option<usize>, debug: usize) -> (Box<dyn CanLeiden>, Vec<Vec<usize>>) {
    match backend {
            GraphBackend::GraphRS => {
                let (graph, clique_clusters) = shared_signal_graph_graphrs(circ, clique_cluster_size, debug);
                (Box::new(graph), clique_clusters)
            }
            GraphBackend::SingleClustering => {
                panic!("SingleClustering currently unsupported due to dependency issues")
                // Box::new(shared_signal_graph_single_clustering(circuit))
            }
            GraphBackend::XGraph => {
                let (graph, clique_clusters) = shared_signal_graph_xgraph(circ, clique_cluster_size, debug);
                (Box::new(graph), clique_clusters)
            }
        }
}