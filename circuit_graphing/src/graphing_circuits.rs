use combinatorial::Combinations;
use std::collections::BTreeMap;

use graphrs::{Graph as RSGraph, GraphSpecs};

use circuits_and_constraints::circuit::Circuit;
use circuits_and_constraints::constraint::Constraint;
use circuits_and_constraints::utils::signals_to_constraints_with_them;

fn get_weighted_arcs<C: Constraint>(circ: &impl Circuit<C>, debug: bool) -> BTreeMap<[usize;2], usize> {

    let signal_to_coni = signals_to_constraints_with_them(&circ.get_constraints(), None, None);
    if debug {println!("LOG: finished signal_to_coni calculation");}
    let mut weights: BTreeMap<[usize;2], usize> = BTreeMap::new();

    for pair in signal_to_coni.into_values().flat_map(|conis| Combinations::of_size(conis, 2)) {
        weights.entry(pair.try_into().unwrap()).and_modify(|x| *x += 1).or_insert(1);
    }
    weights
}

// pub fn shared_signal_graph_single_clustering<C: Constraint>(circ: &impl Circuit<C>) -> CSRNetwork<f64, f64> {

//     let weights = get_weighted_arcs(circ);
//     CSRNetwork::from_edges(weights.iter().map(|(pair, val)| (pair.0, pair.1, *val as f64)).collect::<Vec<_>>().as_ref(), vec![1 as f64; circ.n_constraints()])
// }

pub fn shared_signal_graph_graphrs<C: Constraint>(circ: &impl Circuit<C>, debug: bool) -> RSGraph<usize,usize> {

    let weights = get_weighted_arcs(circ, debug);
    if debug {println!("LOG: finished weights calculation");}

    let mut graph = RSGraph::new(GraphSpecs::undirected_create_missing());
    let _ = graph.add_edge_tuples_weighted(weights.into_iter().map(|(pair, val)| (pair[0], pair[1], val as f64)).collect::<Vec<_>>());

    graph
}