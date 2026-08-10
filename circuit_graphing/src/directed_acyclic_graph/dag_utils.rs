use std::collections::{HashMap};

use super::{DAGNode};
use circuits_constraints_and_algebra::constraint::Constraint;
use circuits_constraints_and_algebra::circuit::Circuit;
use utils::small_utilities::merge_sorted_vecs;

// A collection of utils for DAGS

/// Comparison operator between (dist to in, dist to out) pair
///
/// $x < y <=>$ `x.0 < y.0 && (y.1 <= x.1) || x.0 == y.0 && (y.1 < x.1)`
pub fn lt(x: (usize, usize), y: (usize, usize)) -> bool {x.0 < y.0 && (y.1 <= x.1) || x.0 == y.0 && (y.1 < x.1)}

/// Adds an arc to a DAGNode hierarchy maintaining input/output signals and successor/predecessor relationships
pub fn add_arc_to_nodes<'a, C: Constraint + 'a, S: Circuit<C> + 'a>(arc: (usize, usize), idx_to_nodeid: &Vec<usize>, part_to_signals_arr: &Vec<Vec<usize>>, nodes: &mut HashMap<usize, DAGNode<'a, C, S>>) -> () {
    let (l, r) = arc;
    let l_id = idx_to_nodeid[l]; let r_id = idx_to_nodeid[r];

    let shared_signals: Vec<usize> = merge_sorted_vecs(&part_to_signals_arr[l], &part_to_signals_arr[r]);

    {let lnode: &mut DAGNode<C, S> = nodes.get_mut(&l_id).unwrap();

    lnode.add_successors([r_id].into_iter());
    lnode.update_output_signals(shared_signals.iter().copied());};

    {let rnode: &mut DAGNode<C, S> = nodes.get_mut(&r_id).unwrap();
    
    rnode.add_predecessors([l_id].into_iter());
    rnode.update_input_signals(shared_signals.into_iter())};
}