use combinatorial::Combinations;
use std::collections::BTreeMap;
use std::time::{Instant};

use graphrs::Edge as RSEdge;
use graphrs::IdentityIndexer;
use graphrs::{Graph as RSGraph, GraphSpecs};
use xgraph::{Graph as XGraph};

use circuits_and_constraints::circuit::Circuit;
use circuits_and_constraints::constraint::Constraint;
use circuits_and_constraints::utils::signals_to_constraints_with_them;
use utils::small_utilities::GraphBackend;

use crate::leiden_clustering::CanLeiden;


fn get_weighted_arcs<C: Constraint>(circ: &impl Circuit<C>, debug: bool) -> BTreeMap<[usize;2], usize> {

    let signal_to_coni_timer = Instant::now();
    let signal_to_coni = signals_to_constraints_with_them(&circ.get_constraints(), None, None);
    if debug {println!("LOG: finished signal_to_coni calculation in {:?}s", signal_to_coni_timer.elapsed().as_secs_f32());}
    let mut weights: BTreeMap<[usize;2], usize> = BTreeMap::new();

    let weights_timer = Instant::now();
    for pair in signal_to_coni.into_values().flat_map(|conis| Combinations::of_size(conis, 2)) {
        weights.entry(pair.try_into().unwrap()).and_modify(|x| *x += 1).or_insert(1);
    }
    if debug {println!("LOG: finished weights calculation in {:?}s", weights_timer.elapsed().as_secs_f32());}
    weights
}

fn shared_signal_graph_xgraph<C: Constraint>(circ: &impl Circuit<C>, debug: bool) -> XGraph<f64, (), ()> {
    let weights = get_weighted_arcs(circ, debug);
    let mut graph = XGraph::new(false);
    // nodes are indices of the 
    graph.add_nodes_batch(std::iter::repeat(()).take(circ.n_constraints()));
    graph.add_edges_batch(weights.into_iter().map(|(pair, val)| (pair[0], pair[1], val as f64, ())).collect::<Vec<_>>()).unwrap();
    
    graph
}

fn shared_signal_graph_graphrs<C: Constraint>(circ: &impl Circuit<C>, debug: bool) -> RSGraph<usize, IdentityIndexer> {

    let weights = get_weighted_arcs(circ, debug);
    let mut graph = RSGraph::new(GraphSpecs::undirected_create_missing(), IdentityIndexer);
    if debug {println!("LOG: now adding {:?} edges into graph", weights.len())};
    let mut i = 0;
    let mut j = 0;
    let adding_edges_timer = Instant::now();
    for (pair, val) in weights.into_iter() {
        let _ = graph.add_edge((pair[0], pair[1], val as f64));
        if debug{
            if i >= 1000000 {
                j += 1; i = 0;
                println!("LOG: Added {:?} million edges in {:?}s", j, adding_edges_timer.elapsed().as_secs_f32());
            }
            i += 1;
        }
    }

    graph
}

pub fn shared_signal_graph<C: Constraint>(circ: &impl Circuit<C>, backend: GraphBackend, debug: bool) -> Box<dyn CanLeiden> {
    match backend {
            GraphBackend::GraphRS => {
                Box::new(shared_signal_graph_graphrs(circ, debug))
            }
            GraphBackend::SingleClustering => {
                panic!("SingleClustering currently unsupported due to dependency issues")
                // Box::new(shared_signal_graph_single_clustering(circuit))
            }
            GraphBackend::XGraph => {
                Box::new(shared_signal_graph_xgraph(circ, debug))
            }
        }
}