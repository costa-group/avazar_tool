use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use priority_queue::PriorityQueue;

use circuit_graphing::directed_acyclic_graph::mixed_graph::MixedGraph;

pub fn extend_dag_cycles_cover(graph: &mut MixedGraph, viable_arcs: Vec<(usize, usize)>) -> Vec<(usize, usize)> {
    // Need &mut MixedGraph for efficiency but the graph shouldn't actually be mutated.

    // Set all viable_arcs to be in the graph
    graph.orient_by_arcs(&viable_arcs);

    // Use Johnson's Algorithm for Cycle-enumeration to get set of all cycles
    //   -- cycles can only be from added arcs so account for this
    let vertices_of_interest = viable_arcs.iter().flat_map(|&(a, b)| [a,b].into_iter()).collect::<HashSet<_>>();
    let cycles = johnson_cycle_enumeration(graph, Some(vertices_of_interest));
    graph.deorient_arcs(&viable_arcs);

    let sets_of_edges: Vec<HashSet<(usize, usize)>> = cycles.into_iter().map(|cycle| (0..cycle.len()-1).into_iter().map(|i| (cycle[i], cycle[i+1])).collect() ).collect();

    // Get minimum covering of the sets to choose maximum number of viable_arcs
    //  instead of minimum do greedy here to be fast
    let edge_cover: HashSet<(usize, usize)> = greedy_hitting_set_approximation(&sets_of_edges).into_iter().copied().collect();
    
    viable_arcs.into_iter().filter(|e| !edge_cover.contains(e)).collect()
}

fn greedy_hitting_set_approximation<'a, T: Hash + Eq>(sets: &'a Vec<HashSet<T>>) -> Vec<&'a T> {

    let mut elem_to_uncovered_sets: HashMap<&T, HashSet<usize>> = HashMap::new();
    for (i, set) in sets.into_iter().enumerate() {for elem in set.into_iter() {
        elem_to_uncovered_sets.entry(elem).or_insert(HashSet::new()).insert(i);
    }}

    let mut queue: PriorityQueue<&T, usize> = elem_to_uncovered_sets.iter().map(|(key, indices)| (*key, indices.len())).collect();
    let mut chosen: Vec<&T> = Vec::new();

    while queue.len() > 0 {

        let (next, _) = queue.pop().unwrap();
        let uncovered_sets = elem_to_uncovered_sets.remove(&next).unwrap();
        let mut affected_elems: HashSet<&T> = HashSet::new();
        for idx in uncovered_sets.into_iter() {for elem in sets[idx].iter() { affected_elems.insert(elem);elem_to_uncovered_sets.entry(elem).and_modify(|set| {set.remove(&idx);}); }}
        for elem in affected_elems.into_iter() {queue.change_priority(elem, elem_to_uncovered_sets[elem].len());}
        chosen.push(next);
    }
    // Greedily choose element in the most number of uncovered sets

    // update uncovered sets for remaining vertices

    chosen
}

fn johnson_cycle_enumeration(graph: &MixedGraph, vertices_of_interest: Option<HashSet<usize>>) -> Vec<Vec<usize>> {

    // ordering
    let mut order_to_vertex: Option<Vec<usize>>;
    let mut vertex_to_order: Option<Vec<usize>>;
    let max_ordered = vertices_of_interest.as_ref().map_or(graph.n, |x| x.len());
    if vertices_of_interest.is_some() {
        vertex_to_order = Some(vec![usize::MAX; graph.n]);
        order_to_vertex = Some(vec![usize::MAX; graph.n]);
        let vertices_of_interest = vertices_of_interest.unwrap();
        for (i, v) in vertices_of_interest.iter().copied().chain((0..graph.n).into_iter().filter(|x| !vertices_of_interest.contains(x))).enumerate() {
            order_to_vertex.as_mut().map(|arr| arr[i] = v);
            vertex_to_order.as_mut().map(|arr| arr[v] = i);
        }
    } else {
        order_to_vertex = None; vertex_to_order = None;
    }

    let mut cycles: Vec<Vec<usize>> = Vec::new();
    let mut blocked: Vec<bool> = vec![false; graph.n];
    let mut block_assoc: Vec<HashSet<usize>> = vec![HashSet::new(); graph.n];
    let mut stack: Vec<usize> = Vec::new();

    fn unblock(idx: usize, blocked: &mut Vec<bool>, block_assoc: &mut Vec<HashSet<usize>>) -> () {
        blocked[idx] = false;
        // clone because of mutable borrows
        for child in block_assoc[idx].clone() {
            if blocked[child] {unblock(child, blocked, block_assoc);}
        }
        block_assoc[idx].clear();
    }

    fn circuit(root: usize, idx: usize, adjacency: &Vec<HashSet<usize>>, vertex_to_order: &Option<Vec<usize>>, stack: &mut Vec<usize>, blocked: &mut Vec<bool>, block_assoc: &mut Vec<HashSet<usize>>, cycles: &mut Vec<Vec<usize>>) -> bool {

        let mut found: bool = false;
        blocked[idx] = true;
        stack.push(idx);

        let children_with_greater_order = |idx: usize| adjacency[idx].iter().copied().filter(|&child| vertex_to_order.as_ref().map_or(root, |arr| arr[root]) <= vertex_to_order.as_ref().map_or(child, |arr| arr[child]) );
        for child in children_with_greater_order(idx) {
            if child == root {cycles.push(stack.clone()); found = true;}
            else if !blocked[child] {
                if circuit(root, child, adjacency, vertex_to_order, stack, blocked, block_assoc, cycles) {found = true};// not sure how rust optimises || so not taking chances
            }
        }
        if found {unblock(idx, blocked, block_assoc);}
        else { for child in children_with_greater_order(idx) {
            block_assoc[child].insert(idx);
        }}

        stack.pop();
        found
    }

    let mut root: usize = 0;
    while root <= max_ordered {
        let vert = order_to_vertex.as_ref().map_or(root, |arr| arr[root]);
        for v in (root..graph.n).into_iter().map(|o| order_to_vertex.as_ref().map_or(o, |arr| arr[o]) ) {
            blocked[v] = false; block_assoc[v] = HashSet::new();
        }
        circuit(vert, vert, &graph.dir_adjacencies, &vertex_to_order, &mut stack, &mut blocked, &mut block_assoc, &mut cycles);
        root += 1;
    }

    cycles
}

