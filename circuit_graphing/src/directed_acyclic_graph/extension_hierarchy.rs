/// There seems to be some literature on Extending DAGS
//      https://proceedings.mlr.press/v213/luttermann23a/luttermann23a.pdf
//      https://proceedings.mlr.press/v161/wienobst21a/wienobst21a.pdf
//      https://www.jmlr.org/papers/volume2/chickering02a/chickering02a.pdf
//      https://arxiv.org/pdf/1302.4972
//      All this is very interesting -- but all these algorithms are *minimum* O(n^3) -- and all of them deal with markov equivalence

use std::collections::{HashMap, HashSet};
use rustc_hash::FxHashSet;
use itertools::Itertools;
use std::time::{Instant};

use super::{DAGNode};
use circuits_constraints_and_algebra::constraint::Constraint;
use circuits_constraints_and_algebra::circuit::Circuit;
use super::dag_utils::{lt};
use super::mixed_graph::MixedGraph;

// The following are a series of private methods that orient edges in a MixedGraph in some manner as described.

// If a vertex has exactly two un-oriented edges - and no others - and there is an adjacent vertex with an increasing index we orient toward that increasing distance
fn exactly_two_edges_stairs(graph: &mut MixedGraph, part_to_preorder: &Vec<(usize, usize)>) {

    let mut forced_arc_direction_stack: Vec<usize> = (0..graph.n).into_iter().collect();
    while forced_arc_direction_stack.len() > 0 {
        let v = forced_arc_direction_stack.pop().unwrap();
        if graph.input_parts.contains(&v) || graph.output_parts.contains(&v) {continue;}

        let fuzzy: Vec<usize> = graph.adjacencies[v].iter().copied().filter(|&u| !graph.pair_oriented(u, v)).collect();
        // Case: exactly 2 arcs, both fuzzy, and adjacent vertices have index -1, +1
        if graph.adjacencies[v].len() == 2 && fuzzy.len() == 2 {

            // check that there is an adjacent vertex with input dist +1
            let plus_one = graph.adjacencies[v].iter().copied().filter(|&u| part_to_preorder[u].0 == part_to_preorder[v].0 + 1).next();
            if plus_one.is_none() {continue;}
            let plus_one = plus_one.unwrap();
            let minus_one = graph.adjacencies[v].iter().copied().filter(|&u| part_to_preorder[u].0 + 1 == part_to_preorder[v].0).next().unwrap();

            // -1 index shouldbe input, and +1 index should be output
            graph.dir_adjacencies[minus_one].insert(v);
            graph.dir_adjacencies[v].insert(plus_one);

            forced_arc_direction_stack.push(minus_one);
            forced_arc_direction_stack.push(plus_one);
        } 
    }
}

// If a vertex does not yet have an outgoing arc, and exactly one un-oriented edge has greater index
// TODO: prove safety -- will be safe as arcs only go upstairs
fn soft_upstairs_orientation(graph: &mut MixedGraph, part_to_preorder: &Vec<(usize, usize)>) {
    let mut stack: Vec<usize> = (0..graph.n).into_iter().collect();
    while stack.len() > 0 {
        let v = stack.pop().unwrap();
        if graph.input_parts.contains(&v) || graph.output_parts.contains(&v)  {continue;}

        let fuzzy_upstep: Vec<usize> = graph.adjacencies[v].iter().copied().filter(|&u| !graph.pair_oriented(u, v) && part_to_preorder[v].0 < part_to_preorder[u].0).collect();
        if graph.dir_adjacencies[v].len() == 0 && fuzzy_upstep.len() == 1 {

            graph.dir_adjacencies[v].insert(fuzzy_upstep[0]);
            stack.push(fuzzy_upstep[0]);

        }

        let fuzzy_downstep: Vec<usize> = graph.adjacencies[v].iter().copied().filter(|&u| !graph.pair_oriented(u, v) && part_to_preorder[v].0 > part_to_preorder[u].0).collect();
        if graph.adjacencies[v].iter().copied().filter(|&u| graph.dir_adjacencies[u].contains(&v)).count() == 0 && fuzzy_downstep.len() == 1 {

            graph.dir_adjacencies[fuzzy_downstep[0]].insert(v);
            stack.push(fuzzy_downstep[0]);

        }
    }
}

// All arcs go in the upstairs orientation
fn hard_upstairs_orientation(graph: &mut MixedGraph, part_to_preorder: &Vec<(usize, usize)>) {
    for v in 0..graph.n {
       graph.dir_adjacencies[v] = graph.adjacencies[v].iter().copied().filter(|&u| lt(part_to_preorder[v], part_to_preorder[u]) || part_to_preorder[v].0 < part_to_preorder[u].0 ).collect()
    }
}

// If a vertex has exactly one un-oriented edges - and no others - it orients it away (treating it as a constraint)
fn exactly_one_arc(graph: &mut MixedGraph) {
    
    for v in 0..graph.n {
        if graph.input_parts.contains(&v) || graph.output_parts.contains(&v) || graph.adjacencies[v].len() != 1 || graph.dir_adjacencies[v].len() > 0 {continue;}
        graph.dir_adjacencies[graph.adjacencies[v][0]].insert(v);
    }
}

// If a vertex has exactly one un-oriented edge, and all others point in a single direction it orients the remaining edge in the opposite direction
fn exactly_one_unoriented_edge_all_others_single_direction(graph: &mut MixedGraph) {
    let mut forced_arc_direction_stack: Vec<usize> = (0..graph.n).into_iter().collect();
    while forced_arc_direction_stack.len() > 0 {
        let v = forced_arc_direction_stack.pop().unwrap();
        if graph.input_parts.contains(&v) || graph.output_parts.contains(&v) {continue;}

        let fuzzy: Vec<usize> = graph.adjacencies[v].iter().copied().filter(|&u| !graph.pair_oriented(u, v)).collect();
        // Case: exactly 1 fuzzy arc and all oriented arcs are in a single direction
        if fuzzy.len() == 1 {
            
            let directions: HashSet<usize> = graph.adjacencies[v].iter().copied().map(
                |u| if graph.dir_adjacencies[u].contains(&v) {2} else if graph.dir_adjacencies[v].contains(&u) {1} else {0}
                ).collect();
            if directions.len() > 2 {continue;}
            let direction = directions.into_iter().max().unwrap();

            // remaining un-oriented arc should be in the other direction
            // NOTE: if singular edge defaults to pointing in -- this is wrong for constants
            let u = fuzzy[0];
            if direction == 2 {graph.dir_adjacencies[v].insert(u);} else
                                {graph.dir_adjacencies[u].insert(v);}
            forced_arc_direction_stack.push(u);
        }
    }
}

// TODO: convince self that this will never lower the number of oriented edges
// This is technically better than nothing (assuming the above) but it doesn't seem to help at all
//      the hard case is when do we decide to go downstairs and doesn't help.
//      Does help in general with repeated clusters -- though this structure hasn't been problematic otherwise.
// Moved to MixedGraph method iterative_orient_by_partial_order
// fn iteratively_update_distances_under_preorder(graph: &mut MixedGraph, part_to_preorder: &Vec<(usize, usize)>)    -> Vec<(usize, usize)> 

/// A method based on iteratively extending a partial DAG 
///
/// This method is unfinished without and thus always panics. After the initial orientation any subsequent orientations passed the second can risk creating a cycle, ultimately this method was used as insipiration for the integrated_hierarchy tool
pub fn extension_hierarchy<'a, C: Constraint + 'a, S: Circuit<C> + 'a>(
    circ: &'a S, node_id_generator: &mut dyn Iterator<Item = usize>,
    mut graph: MixedGraph, timer: Instant, debug: usize) -> HashMap<usize, DAGNode<'a, C, S>> {
    
    let part_to_preorder = graph.merge_equivalence_classes_by_distance_and_orient(debug);

    // hard_upstairs_orientation(&mut dir_adjacencies, &adjacencies, &input_parts, &output_parts, &part_to_preorder);

    // exactly_two_edges_stairs(&mut dir_adjacencies, &adjacencies, &input_parts, &output_parts, &part_to_preorder);
    // soft_upstairs_orientation(&mut graph, &part_to_preorder);
    // exactly_one_arc(&mut graph);

    // let init_direction: Vec<usize> = edges.iter().map(|&(a,b)| if dir_adjacencies[a].contains(&b) {2} else {if dir_adjacencies[b].contains(&a) {1} else {0}}).collect();
    // println!("num_fuzzy: {:?}", init_direction.iter().copied().filter(|x| *x == 0).count());
    // println!("vertices w/o outgoing edges: {:?}", (1..adjacencies.len()+1).into_iter().filter(|&v| dir_adjacencies[v-1].len() == 0).collect::<Vec<_>>());

    graph.export_to_dzn();

    panic!("Currently Unfinished, requires more work");
    
    graph.initialise_dagnodes(circ, node_id_generator).0
}


// Algorithm from https://ftp.cs.ucla.edu/pub/stat_ser/r185-dor-tarsi.pdf
// this maintains the same set of Vee-structures -- not what we need
pub fn pdag_extension(adjacency: &Vec<Vec<usize>>, edges: &Vec<(usize, usize)>, pdag: &Vec<usize>, _debug: usize) -> Vec<(usize, usize)> {

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
