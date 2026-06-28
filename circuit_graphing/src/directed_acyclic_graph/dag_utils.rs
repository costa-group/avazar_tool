use std::collections::{HashMap, HashSet};

use super::{DAGNode};
use circuits_and_constraints::constraint::Constraint;
use circuits_and_constraints::circuit::Circuit;
use utils::small_utilities::merge_sorted_vecs;
use utils::union_find::{UnionFind};

pub fn lt(x: (usize, usize), y: (usize, usize)) -> bool {x.0 < y.0 && (y.1 <= x.1) || x.0 == y.0 && (y.1 < x.1)}

pub fn merge_parts_and_adjacencies(partition: &Vec<Vec<usize>>, adjacencies: &Vec<Vec<usize>>, input_parts: &HashSet<usize>, output_parts: &HashSet<usize>, mut undirected_components: UnionFind) -> 
    (Vec<Vec<usize>>, Vec<Vec<usize>>, HashSet<usize>, HashSet<usize>, HashMap<usize, usize>)
{
    let components = undirected_components.get_components();
    let parent_to_newidx: HashMap<usize, usize> = components.iter().enumerate().map(|(idx, part)| (undirected_components.find(part[0]), idx)).collect();

    let mut merged_partition : Vec<Vec<usize>> = vec![Vec::new(); parent_to_newidx.len()];
    let mut merged_adjacencies : Vec<Vec<usize>> = vec![Vec::new(); parent_to_newidx.len()];
    let merged_inputs: HashSet<usize> = input_parts.into_iter().copied().map(|x| parent_to_newidx[&undirected_components.find(x)]).collect();
    let merged_outputs: HashSet<usize> = output_parts.into_iter().copied().map(|x| parent_to_newidx[&undirected_components.find(x)]).collect();

    for part in components.into_iter() {
        let newidx = parent_to_newidx[&undirected_components.find(part[0])];
        let part = part.into_iter().collect::<HashSet<_>>();

        merged_partition[newidx] = part.iter().copied().flat_map(|v| partition[v].iter().copied()).collect();
        merged_adjacencies[newidx] = part.iter().copied().flat_map(|v| adjacencies[v].iter().copied()).map(|x| parent_to_newidx[&undirected_components.find(x)]).collect::<HashSet<_>>().into_iter().filter(|x| *x != newidx).collect();
    }

    (merged_partition, merged_adjacencies, merged_inputs, merged_outputs, parent_to_newidx)
}

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