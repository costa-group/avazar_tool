/// There seems to be some literature on Extending DAGS
//      https://proceedings.mlr.press/v213/luttermann23a/luttermann23a.pdf
//      https://proceedings.mlr.press/v161/wienobst21a/wienobst21a.pdf
//      https://www.jmlr.org/papers/volume2/chickering02a/chickering02a.pdf
//      https://arxiv.org/pdf/1302.4972
//      All this is very interesting -- but all these algorithms are *minimum* O(n^3) -- and all of them deal with markov equivalence

use std::collections::{HashMap, HashSet, VecDeque};
use std::borrow::Borrow;
use rustc_hash::FxHashSet;
use itertools::Itertools;
use std::time::{Instant};

use super::{DAGNode};
use circuits_and_constraints::constraint::Constraint;
use circuits_and_constraints::circuit::Circuit;
use utils::small_utilities::{distance_to_source_set, merge_sorted_vecs};
use utils::union_find::{UnionFind};
use super::dag_utils::{lt, add_arc_to_nodes, merge_parts_and_adjacencies};
use super::export_to_dzn::write_dzn;
use super::mixed_graph::MixedGraph;

// If a vertex has exactly two un-oriented edges - and no others - and there is an adjacent vertex with an increasing index we orient toward that increasing distance
fn exactly_two_edges_stairs(dir_adjacencies: &mut Vec<HashSet<usize>>, adjacencies: &Vec<Vec<usize>>, input_parts: &HashSet<usize>, output_parts: &HashSet<usize>, part_to_preorder: &Vec<(usize, usize)>) {
    let mut forced_arc_direction_stack: Vec<usize> = (0..adjacencies.len()).into_iter().collect();
    while forced_arc_direction_stack.len() > 0 {
        let v = forced_arc_direction_stack.pop().unwrap();
        if input_parts.contains(&v) || output_parts.contains(&v) {continue;}

        let fuzzy: Vec<usize> = adjacencies[v].iter().copied().filter(|&u| !dir_adjacencies[v].contains(&u) && !dir_adjacencies[u].contains(&v)).collect();
        // Case: exactly 2 arcs, both fuzzy, and adjacent vertices have index -1, +1
        if adjacencies[v].len() == 2 && fuzzy.len() == 2 {

            // check that there is an adjacent vertex with input dist +1
            let plus_one = adjacencies[v].iter().copied().filter(|&u| part_to_preorder[u].0 == part_to_preorder[v].0 + 1).next();
            if plus_one.is_none() {continue;}
            let plus_one = plus_one.unwrap();
            let minus_one = adjacencies[v].iter().copied().filter(|&u| part_to_preorder[u].0 + 1 == part_to_preorder[v].0).next().unwrap();

            // -1 index shouldbe input, and +1 index should be output
            dir_adjacencies[minus_one].insert(v);
            dir_adjacencies[v].insert(plus_one);

            forced_arc_direction_stack.push(minus_one);
            forced_arc_direction_stack.push(plus_one);
        } 
    }
}

// If a vertex does not yet have an outgoing arc, and exactly one un-oriented edge has greater index
// TODO: prove safety -- will be safe as arcs only go upstairs
fn soft_upstairs_orientation(dir_adjacencies: &mut Vec<HashSet<usize>>, adjacencies: &Vec<Vec<usize>>, input_parts: &HashSet<usize>, output_parts: &HashSet<usize>, part_to_preorder: &Vec<(usize, usize)>) {
    let mut stack: Vec<usize> = (0..adjacencies.len()).into_iter().collect();
    while stack.len() > 0 {
        let v = stack.pop().unwrap();
        if input_parts.contains(&v) || output_parts.contains(&v)  {continue;}

        let fuzzy_upstep: Vec<usize> = adjacencies[v].iter().copied().filter(|&u| !dir_adjacencies[v].contains(&u) && !dir_adjacencies[u].contains(&v) && part_to_preorder[v].0 < part_to_preorder[u].0).collect();
        if dir_adjacencies[v].len() == 0 && fuzzy_upstep.len() == 1 {

            dir_adjacencies[v].insert(fuzzy_upstep[0]);
            stack.push(fuzzy_upstep[0]);

        }

        let fuzzy_downstep: Vec<usize> = adjacencies[v].iter().copied().filter(|&u| !dir_adjacencies[v].contains(&u) && !dir_adjacencies[u].contains(&v) && part_to_preorder[v].0 > part_to_preorder[u].0).collect();
        if adjacencies[v].iter().copied().filter(|&u| dir_adjacencies[u].contains(&v)).count() == 0 && fuzzy_downstep.len() == 1 {

            dir_adjacencies[fuzzy_downstep[0]].insert(v);
            stack.push(fuzzy_downstep[0]);

        }
    }
}

// All arcs go in the upstairs orientation
fn hard_upstairs_orientation(dir_adjacencies: &mut Vec<HashSet<usize>>, adjacencies: &Vec<Vec<usize>>, input_parts: &HashSet<usize>, output_parts: &HashSet<usize>, part_to_preorder: &Vec<(usize, usize)>) {
    for v in 0..adjacencies.len() {
        dir_adjacencies[v] = adjacencies[v].iter().copied().filter(|&u| lt(part_to_preorder[v], part_to_preorder[u]) || part_to_preorder[v].0 < part_to_preorder[u].0 ).collect()
    }
}

// If a vertex has exactly one un-oriented edges - and no others - it orients it away (treating it as a constraint)
fn exactly_one_arc(dir_adjacencies: &mut Vec<HashSet<usize>>, adjacencies: &Vec<Vec<usize>>, input_parts: &HashSet<usize>, output_parts: &HashSet<usize>, part_to_preorder: &Vec<(usize, usize)>) {
    
    for v in 0..adjacencies.len() {
        if input_parts.contains(&v) || output_parts.contains(&v) || adjacencies[v].len() != 1 || dir_adjacencies[v].len() > 0 {continue;}
        dir_adjacencies[adjacencies[v][0]].insert(v);
    }
}

// If a vertex has exactly one un-oriented edge, and all others point in a single direction it orients the remaining edge in the opposite direction
fn exactly_one_unoriented_edge_all_others_single_direction(dir_adjacencies: &mut Vec<HashSet<usize>>, adjacencies: &Vec<Vec<usize>>, input_parts: &HashSet<usize>, output_parts: &HashSet<usize>, part_to_preorder: &Vec<(usize, usize)>) {
    let mut forced_arc_direction_stack: Vec<usize> = (0..adjacencies.len()).into_iter().collect();
    while forced_arc_direction_stack.len() > 0 {
        let v = forced_arc_direction_stack.pop().unwrap();
        if input_parts.contains(&v) || output_parts.contains(&v) {continue;}

        let fuzzy: Vec<usize> = adjacencies[v].iter().copied().filter(|&u| !dir_adjacencies[v].contains(&u) && !dir_adjacencies[u].contains(&v)).collect();
        // Case: exactly 1 fuzzy arc and all oriented arcs are in a single direction
        if fuzzy.len() == 1 {
            
            let directions: HashSet<usize> = adjacencies[v].iter().copied().map(
                |u| if dir_adjacencies[u].contains(&v) {2} else if dir_adjacencies[v].contains(&u) {1} else {0}
                ).collect();
            if directions.len() > 2 {continue;}
            let direction = directions.into_iter().max().unwrap();

            // remaining un-oriented arc should be in the other direction
            // NOTE: if singular edge defaults to pointing in -- this is wrong for constants
            let u = fuzzy[0];
            if direction == 2 {dir_adjacencies[v].insert(u);} else
                                {dir_adjacencies[u].insert(v);}
            forced_arc_direction_stack.push(u);
        }
    }
}

fn distance_to_source_set_under_prorder(source_set: impl Iterator<Item = usize>, adjacencies: &Vec<Vec<usize>>, lt: impl Fn(usize, usize) -> Option<bool>) -> Vec<usize> {

    let mut distance: Vec<usize> = vec![usize::MAX; adjacencies.len()];
    let mut queue: VecDeque<usize> = source_set.collect();
    for idx in queue.iter() {distance[*idx] = 0;}

    while queue.len() > 0 {
        let curr = queue.pop_front().unwrap();
        let next_distance = distance[curr] + 1;
        for adj in adjacencies[curr].iter().copied().filter(|&adj| lt(curr, adj).is_none_or( |x| x ) ) {
            if distance[adj] == usize::MAX {
                queue.push_back(adj);
                distance[adj] = next_distance;
            }
        }
    }

    distance
}

// TODO: convince self that this will never lower the number of oriented edges
// This is technically better than nothing (assuming the above) but it doesn't seem to help at all
//      the hard case is when do we decide to go downstairs and doesn't help.
//      Does help in general with repeated clusters -- though this structure hasn't been problematic otherwise.
fn iteratively_update_distances_under_preorder(dir_adjacencies: &mut Vec<HashSet<usize>>, adjacencies: &Vec<Vec<usize>>, edges: &Vec<(usize, usize)>, input_parts: &HashSet<usize>, output_parts: &HashSet<usize>, part_to_preorder: &Vec<(usize, usize)>)
    -> Vec<(usize, usize)> {

    let mut updated_at_least_one_arc = true;
    let mut current_preorder: Option<Vec<(usize, usize)>> = None;

    fn get_preorder(x: usize, current_preorder: &Option<Vec<(usize, usize)>>, part_to_preorder: &Vec<(usize, usize)>) -> (usize, usize) {
        current_preorder.as_ref().map(|arr| arr[x]).unwrap_or(part_to_preorder[x])
    }

    fn compare(x:usize, y:usize, current_preorder: &Option<Vec<(usize, usize)>>, part_to_preorder: &Vec<(usize, usize)>) -> Option<bool> {
        let x_ord = get_preorder(x, current_preorder, part_to_preorder); let y_ord = get_preorder(y, current_preorder, part_to_preorder);
        if lt(x_ord, y_ord) {Some(true)} else if lt(y_ord, x_ord) {Some(false)} else {None}
    }

    let mut oriented_edges = edges.into_iter().filter(|&&(x, y)| compare(x, y, &current_preorder, part_to_preorder).is_some()).count();
    println!("oriented_edges: {:?}", oriented_edges);

    while updated_at_least_one_arc {
        

        let distance_to_inputs = distance_to_source_set_under_prorder(input_parts.into_iter().copied(), adjacencies, |x, y| compare(x, y, &current_preorder, part_to_preorder));
        let distance_to_outputs = distance_to_source_set_under_prorder(output_parts.into_iter().copied(), adjacencies, |x, y| compare(y, x, &current_preorder, part_to_preorder));

        current_preorder = Some((0..adjacencies.len()).into_iter().map(|x| (distance_to_inputs[x], distance_to_outputs[x])).collect());
        let new_oriented_edges = edges.into_iter().filter(|&&(x, y)| compare(x, y, &current_preorder, part_to_preorder).is_some() ).count();
        
        updated_at_least_one_arc = new_oriented_edges > oriented_edges;
        oriented_edges = new_oriented_edges;
        println!("oriented_edges: {:?}", oriented_edges);
    }

    *dir_adjacencies = adjacencies.iter().enumerate().map(|(v, part)| part.into_iter().copied().filter(|&u| compare(v, u, &current_preorder, part_to_preorder).is_some_and(|x| x) ).collect()).collect();

    current_preorder.unwrap()
}

pub fn merge_equivalence_classes_by_distance(mut graph: MixedGraph) ->
    (MixedGraph, Vec<(usize, usize)>, Vec<(usize, usize)>) {
    
    let mut part_to_preorder: Vec<(usize, usize)> = Vec::new();

    // merge equivalence classes into layers
    let exists_nontrivial_equivalence_classes = true;
    while exists_nontrivial_equivalence_classes {

        println!("---------------------------------------");
        let distance_to_inputs = distance_to_source_set(graph.input_parts.iter().copied(), &graph.adjacencies);
        let distance_to_outputs = distance_to_source_set(graph.output_parts.iter().copied(), &graph.adjacencies);
        part_to_preorder = (0..graph.n).map(|key| (distance_to_inputs[key], distance_to_outputs[key])).collect();

        let num_fuzzy_edges: usize = graph.edges.iter().map(|&(a, b)| if !lt(part_to_preorder[a], part_to_preorder[b]) && !lt(part_to_preorder[b], part_to_preorder[a]) {1} else {0}).sum();
        println!("num_fuzzy: {:?}", num_fuzzy_edges);

        // Merge equivalence class
        let mut equal_distance = UnionFind::new(false);
        for v in 0..n_parts {equal_distance.find(v);}
        
        for &(a, b) in edges.iter() {
            if part_to_preorder[a] == part_to_preorder[b] {equal_distance.union([a, b].into_iter());}
        }

        use utils::small_utilities::count_ints;
        if equal_distance.get_components().len() == partition.len() {
            break;
        }

        println!("merging: {:?}", count_ints(equal_distance.get_components().into_iter().map(|part| part.len())));
        graph = graph.merge(equal_distance);
        
    }

    (graph, part_to_preorder)
}

pub fn extension_hierarchy<'a, C: Constraint + 'a, S: Circuit<C> + 'a>(
    circ: &'a S, partition: Vec<Vec<usize>>, node_id_generator: &mut dyn Iterator<Item = usize>,
    adjacencies: Vec<Vec<usize>>, input_parts: HashSet<usize>, output_parts: HashSet<usize>, 
    timer: Instant, debug: usize) -> HashMap<usize, DAGNode<'a, C, S>> {
    
    let (partition, adjacencies, input_parts, output_parts, part_to_preorder, edges) = merge_equivalence_classes_by_distance(partition, adjacencies, input_parts, output_parts);
    let n_parts = partition.len();
    let mut dir_adjacencies: Vec<HashSet<usize>> = adjacencies.iter().enumerate().map(|(v, part)| part.into_iter().copied().filter(|&u| lt(part_to_preorder[v], part_to_preorder[u])).collect() ).collect();
    
    //let part_to_preorder = iteratively_update_distances_under_preorder(&mut dir_adjacencies, &adjacencies, &edges, &input_parts, &output_parts, &part_to_preorder);

    // hard_upstairs_orientation(&mut dir_adjacencies, &adjacencies, &input_parts, &output_parts, &part_to_preorder);

    // exactly_two_edges_stairs(&mut dir_adjacencies, &adjacencies, &input_parts, &output_parts, &part_to_preorder);
    soft_upstairs_orientation(&mut dir_adjacencies, &adjacencies, &input_parts, &output_parts, &part_to_preorder);
    exactly_one_arc(&mut dir_adjacencies, &adjacencies, &input_parts, &output_parts, &part_to_preorder);

    let init_direction: Vec<usize> = edges.iter().map(|&(a,b)| if dir_adjacencies[a].contains(&b) {2} else {if dir_adjacencies[b].contains(&a) {1} else {0}}).collect();
    println!("num_fuzzy: {:?}", init_direction.iter().copied().filter(|x| *x == 0).count());
    println!("vertices w/o outgoing edges: {:?}", (1..adjacencies.len()+1).into_iter().filter(|&v| dir_adjacencies[v-1].len() == 0).collect::<Vec<_>>());

    // write_dzn("data.dzn", &adjacencies, &edges, &vec![], &init_direction, &input_parts, &output_parts);

    // write_to_dzn(&adjacencies, &input_parts, &output_parts);
    panic!("Currently Unfinished, requires more work");
    

    let arcs = Vec::new(); //extension_hierarchy_solver(&adjacencies, &edges, &pdag, debug);

    let part_to_signals_arr: Vec<Vec<usize>> = partition.iter().map(|part|
        part.into_iter().copied().flat_map(|idx| circ.get_constraints()[idx].borrow().signals()).sorted_unstable().dedup().collect()
    ).collect();

    let mut nodes : HashMap<usize, DAGNode<'a, C, S>> = partition.into_iter().enumerate().map(|(idx, part)| {
        (idx, 
        DAGNode::new(
            circ, 
            idx, 
            part, 
            part_to_signals_arr[idx].iter().copied().filter(|sig| circ.signal_is_input(sig)).collect(), // get global labelled signal in initially
            part_to_signals_arr[idx].iter().copied().filter(|sig| circ.signal_is_output(sig)).collect(),
            None, None))
    }).collect();

    let idx_to_nodeid: Vec<usize> = (0..n_parts).into_iter().collect();

    for arc in arcs.into_iter() {add_arc_to_nodes(arc, &idx_to_nodeid, &part_to_signals_arr, &mut nodes);}

    nodes
}


// Algorithm from https://ftp.cs.ucla.edu/pub/stat_ser/r185-dor-tarsi.pdf
// this maintains the same set of Vee-structures -- not what we need
pub fn pdag_extension(adjacency: &Vec<Vec<usize>>, edges: &Vec<(usize, usize)>, pdag: &Vec<usize>, debug: usize) -> Vec<(usize, usize)> {

    let mut remaining: FxHashSet<usize> = (0..adjacency.len()).into_iter().collect();
    let mut rem_adjacency: Vec<FxHashSet<usize>> = adjacency.into_iter().map(|adj| adj.iter().copied().collect() ).collect();

    let mut undirected_adjacent: Vec<Vec<usize>> = vec![Vec::new(); adjacency.len()];
    let mut out_degree: Vec<usize> = vec![0; adjacency.len()];
    let mut sinks: FxHashSet<usize> = (0..adjacency.len()).into_iter().collect();
    for (i, &(l, r)) in edges.iter().enumerate() {
        if pdag[i] == 0 {undirected_adjacent[r].push(l); undirected_adjacent[l].push(r);}
        else if pdag[i] == 1 {sinks.remove(&r);out_degree[r] += 1;}
        else {sinks.remove(&l);out_degree[l] += 1;}
    }

    println!("sinks.len() {:?}", sinks.len());

    let mut arcs: Vec<(usize, usize)> = Vec::new();

    // While A is not empty
    while remaining.len() > 0 {

        println!("### SINKS and ADJ ###");
        println!("sinks.len() {:?}", sinks.len());
        
        let mut chosen: Option<usize> = None;

        for v in sinks.iter().copied().sorted() {
            // Choose vertex v s.t.
            //  v is a sink in pdag
            //  all undirected adjacent to x are adjacent to all adjacent to x
            if undirected_adjacent[v].iter().copied().filter(|u| remaining.contains(u)).all(|u| rem_adjacency[v].iter().copied().filter(|x| *x != u).all(|x| rem_adjacency[u].contains(&x)) ) {
                chosen = Some(v);
                break
            }
        }

        if chosen.is_none() {panic!("Does not admit a hierarchy");}
        println!("chosen: {:?}", chosen.unwrap());


        // remove chose from A 
        let chosen = chosen.unwrap();
        remaining.remove(&chosen);
        sinks.remove(&chosen);
        let to_alter: Vec<usize> = rem_adjacency[chosen].iter().copied().collect();
        for u in to_alter.into_iter() {
            rem_adjacency[u].remove(&chosen);
            arcs.push((u, chosen));
            if out_degree[u] > 0 {out_degree[u] -= 1;}
            if out_degree[u] == 0 {sinks.insert(u);}
        }
    }

    arcs
}
