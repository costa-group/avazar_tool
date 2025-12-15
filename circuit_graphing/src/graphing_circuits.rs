use combinatorial::Combinations;
use std::collections::HashMap;

use single_clustering::network::CSRNetwork;
use graphrs::{Graph as RSGraph, GraphSpecs};

use circuits_and_constraints::circuit::Circuit;
use circuits_and_constraints::constraint::Constraint;
use circuits_and_constraints::utils::signals_to_constraints_with_them;

fn get_weighted_arcs<C: Constraint>(circ: &impl Circuit<C>) -> HashMap<(usize, usize), usize> {

    let signal_to_coni = signals_to_constraints_with_them(&circ.get_constraints(), None, None);
    let mut weights: HashMap<(usize, usize), usize> = HashMap::new();

    for pair in signal_to_coni.keys().flat_map(|signal| Combinations::of_size(signal_to_coni.get(signal).unwrap(), 2)).map(|pair| (*pair[0], *pair[1])){
        weights.insert(pair, 1 + weights.get(&pair).unwrap_or(&0));
    }
    weights
}

pub fn shared_signal_graph_single_clustering<C: Constraint>(circ: &impl Circuit<C>) -> CSRNetwork<f64, f64> {

    let weights = get_weighted_arcs(circ);
    CSRNetwork::from_edges(weights.iter().map(|(pair, val)| (pair.0, pair.1, *val as f64)).collect::<Vec<_>>().as_ref(), vec![1 as f64; circ.n_constraints()])
}

pub fn shared_signal_graph_graphrs<C: Constraint>(circ: &impl Circuit<C>) -> RSGraph<usize,usize> {

    let weights = get_weighted_arcs(circ);

    let mut graph = RSGraph::new(GraphSpecs::undirected_create_missing());
    let _ = graph.add_edge_tuples_weighted(weights.into_iter().map(|(pair, val)| (pair.0, pair.1, val as f64)).collect::<Vec<_>>());

    graph
}