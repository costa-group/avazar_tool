use z3::{Optimize, ast::Bool, ast::Int, SatResult};
use std::collections::{HashSet};
use std::time::{Instant};

use utils::small_utilities::distance_to_source_set;
use utils::union_find::UnionFind;
use super::mixed_graph::MixedGraph;

pub fn dag_from_partition_solver(
    graph: &MixedGraph, debug: usize) -> Vec<(usize, usize)> {    
    
    let encoding_timer = Instant::now();

    // Building this according to Cosntraint Optimisation intuition -- need to get people more familiar with SMT to take a look at it.

    // Precalculate distances for some early local information
    //   - Maximum Distance is when no edges are contracted
    //   - Minimum Distance is when all fuzzy edges are contracted
    
    let max_distance_to_inputs = distance_to_source_set(graph.input_parts.iter().copied(), &graph.adjacencies);
    let max_distance_to_outputs = distance_to_source_set(graph.output_parts.iter().copied(), &graph.adjacencies);
    
    let edge_is_fuzzy = |e: usize| {
        // edge_is fuzzy if x_ord.1 - x_ord.0 == x_ord.0 - x_ord.1
        !graph.edge_oriented(e) // wrapping doesn't matter here since we're interested in equality
    };

    let mut total_fuse = UnionFind::new(false);
    for e in 0..graph.m {if edge_is_fuzzy(e) {total_fuse.union([graph.edges[e].0, graph.edges[e].1].into_iter());} else {total_fuse.find(graph.edges[e].0); total_fuse.find(graph.edges[e].1);}}
    let fused_graph = graph.merge(total_fuse);

    let max_part = graph.partition.iter().map(|part| part.iter().copied().max().unwrap() ).max().unwrap();
    let mut coni_to_part = vec![usize::MAX; max_part+1];
    for (i, part) in graph.partition.iter().enumerate() {for coni in part.into_iter().copied() {
        coni_to_part[coni] = i
    }}

    let merged_distance_to_inputs = distance_to_source_set(fused_graph.input_parts.iter().copied(), &fused_graph.adjacencies);
    let merged_distance_to_outputs = distance_to_source_set(fused_graph.output_parts.iter().copied(), &fused_graph.adjacencies);

    let mut min_distance_to_inputs = vec![usize::MAX; graph.n];
    let mut min_distance_to_outputs = vec![usize::MAX; graph.n];

    for (i, part) in fused_graph.partition.iter().enumerate() {
        for coni in part.into_iter().copied() {
            min_distance_to_inputs[coni_to_part[coni]] = merged_distance_to_inputs[i];
            min_distance_to_outputs[coni_to_part[coni]] = merged_distance_to_outputs[i];
        }
    }

    let min_edge_is_fuzzy = |e: usize| {
        // edge_is fuzzy if x_ord.1 - x_ord.0 == x_ord.0 - x_ord.1
        let x_ord = (min_distance_to_inputs[graph.edges[e].0], min_distance_to_outputs[graph.edges[e].0]);
        let y_ord = (min_distance_to_inputs[graph.edges[e].1], min_distance_to_outputs[graph.edges[e].1]);
        x_ord.1.wrapping_sub(x_ord.0) == y_ord.1.wrapping_sub(y_ord.0) // wrapping doesn't matter here since we're interested in equality
    };

    use utils::small_utilities::count_ints;
    println!("range: {:?}", count_ints((0..graph.n).into_iter().map(|x| max_distance_to_inputs[x].wrapping_sub(min_distance_to_inputs[x]))));
    println!("range: {:?}", count_ints((0..graph.n).into_iter().map(|x| max_distance_to_outputs[x].wrapping_sub(min_distance_to_outputs[x]))));
    println!("num_fuzzy_max: {:?}", (0..graph.m).into_iter().filter(|&e| edge_is_fuzzy(e)).count());
    println!("num_fuzzy_min: {:?}", (0..graph.m).into_iter().filter(|&e| min_edge_is_fuzzy(e)).count());

    let mut incidence: Vec<Vec<usize>> = (0..graph.n).into_iter().map(|_| Vec::new()).collect();
    for (i, &(u, v)) in graph.edges.iter().enumerate() {incidence[u].push(i);incidence[v].push(i);}

    let optimiser = Optimize::new();

    // default fixed vars reused to save number of vars
    let int_idxs: Vec<Int> = (0..graph.n).into_iter().map(|i| Int::from_u64(i as u64)).collect();
    let bool_false: Bool = Bool::from_bool(false); let bool_true: Bool = Bool::from_bool(true); 
    let bool_to_Bool = |x: bool| if x {&bool_true} else {&bool_false};

    // For each edge (not arc) we have a boolean decision variable about whether or not that edge is 'fused'
    let fused: Vec<Bool> = (0..graph.m).into_iter().map(|e| Bool::new_const(format!("f_{e}"))).collect();

    // // forall e in 0..graph.m edges_is_fuzzy(e) => fused[e] NOTE: testing only
    // for e in 0..graph.m {optimiser.assert(
    //     bool_to_Bool(edge_is_fuzzy(e)).implies(&fused[e])
    // );}

    // \forall e : fused[e] => edge_is_fuzzy(e)
    for e in 0..graph.m {optimiser.assert(
        fused[e].implies(bool_to_Bool(edge_is_fuzzy(e)))
    );}

    // We map each vertex and edge to a tree T in 0..max_trees (with 0 being not in a tree)
    let v_graph: Vec<Int> = (0..graph.n).into_iter().map(|v| Int::new_const(format!("vt_{v}"))).collect();
    let e_graph: Vec<Int> = (0..graph.m).into_iter().map(|e| Int::new_const(format!("et_{e}"))).collect();

    // if the edge is in the spanning subtree for the fused component (ensures connectedness)
    let e_tree: Vec<Bool> = (0..graph.m).into_iter().map(|e| Bool::new_const(format!("st_{e}"))).collect();
    let max_trees: usize = graph.n >> 1;

    // max_tree bounds

    // \forall e : 0 <= e_graph[e] <= max_trees
    for e in 0..graph.m {optimiser.assert(
        Bool::and(&[e_graph[e].ge(&int_idxs[0]), e_graph[e].le(&int_idxs[max_trees])])
    );}
    // \forall v : 0 <= v_graph[v] <= max_trees
    for v in 0..graph.n {optimiser.assert(
        Bool::and(&[v_graph[v].ge(&int_idxs[0]), v_graph[v].le(&int_idxs[max_trees])])
    );}

    // Constraints to ensure tree correctness

    // \forall e : e_tree[e] -> fused[e] -- i.e. if e is in the subtree e is in a graph
    // \forall e : fused[e] == e_graph[e] >= 0
    // \forall uv : fused[uv] -> e_graph[uv] == v_graph[v] == v_graph[u]
    for e in 0..graph.m {optimiser.assert(Bool::and(&[
        e_tree[e].implies(&fused[e]),
        fused[e].eq(e_graph[e].gt(&int_idxs[0])),
        fused[e].implies(Bool::and(&[e_graph[e].eq(&v_graph[graph.edges[e].0]), e_graph[e].eq(&v_graph[graph.edges[e].1])]))
    ]));}
    // \forall v : all(e incident to v)(not fused[e]) -> v_graph[v] = 0 // expanded into singular OR clause
    // \forall v : v_graph[v] > 0 -> exists(e in incidence[v])(e_tree[v])
    for v in 0..graph.n {optimiser.assert(
        // Bool::or(&[&v_graph[v].eq(&int_idxs[0])].into_iter().chain(incidence[v].iter().copied().map(|e| &fused[e])).collect::<Vec<_>>()), // implied by the next line
        v_graph[v].gt(&int_idxs[0]).implies(Bool::or(&incidence[v].iter().copied().map(|e| &e_tree[e]).collect::<Vec<_>>()))
    );}

    // Num of each v/e in tree
    // We ensure tree with constraints i.e. |V| = |E| + 1
    let vt_size: Vec<Int> = (0..max_trees).into_iter().map(|x| Int::new_const(format!("tv_{x}"))).collect();
    let et_size: Vec<Int> = (0..max_trees).into_iter().map(|x| Int::new_const(format!("te_{x}"))).collect();

    // Note that this is O(n^2). I can't really think of a way to improve this but this really slows us down.
    // \forall t : |V_t| = |E_t| + 1
    let bool_to_int = |b: &Bool| b.ite(&int_idxs[1], &int_idxs[0]);
    for t in 0..max_trees {optimiser.assert(Bool::and(&[
        vt_size[t].eq(Int::add(&(0..graph.n).into_iter().map(|v| bool_to_int(&v_graph[v].eq(&int_idxs[t+1]))).collect::<Vec<_>>())),
        et_size[t].eq(Int::add(&(0..graph.m).into_iter().map(|e| bool_to_int(&Bool::and(&[&e_graph[e].eq(&int_idxs[t+1]), &e_tree[e]]))).collect::<Vec<_>>())),
        et_size[t].gt(&int_idxs[0]).implies(vt_size[t].eq(&et_size[t] + &int_idxs[1]))
    ]));}
    
    // We then have distance variables for in/out, and tightness boolean for each in/out
    //  init values set to 0
    //  edges bound either 1 increment, or equality
    //  tightness is an exact 1 increment -- enforce tightness in each tree
    let min_distances: [&Vec<usize>; 2] = [&min_distance_to_inputs, &min_distance_to_outputs];
    let max_distances: [&Vec<usize>; 2] = [&max_distance_to_inputs, &max_distance_to_outputs];
    let inits: [&HashSet<usize>; 2] = [&graph.input_parts, &graph.output_parts];
    let distances: [Vec<Int>; 2] = [(0..graph.n).into_iter().map(|x| Int::new_const(format!("d1_{x}"))).collect(),
                                    (0..graph.n).into_iter().map(|x| Int::new_const(format!("d2_{x}"))).collect()];
    let tightness: [Vec<Bool>; 2] = [(0..graph.n).into_iter().map(|x| Bool::new_const(format!("t1_{x}"))).collect(),
                                     (0..graph.n).into_iter().map(|x| Bool::new_const(format!("t2_{x}"))).collect()];
    for dir in 0..2 {
        // initialise
        for v in inits[dir].into_iter().copied() {optimiser.assert(distances[dir][v].eq(&int_idxs[0]));}

        // general upper bounds (original distances) min_dist(v) <= d_v <= max_dist(v)
        for v in 0..graph.n {optimiser.assert(
            Bool::and(&[
                distances[dir][v].ge(&int_idxs[min_distances[dir][v]]),
                distances[dir][v].le(&int_idxs[max_distances[dir][v]])
            ])
        );}

        // edge bounds
        for e in 0..graph.m {optimiser.assert(
            fused[e].ite(
                &distances[dir][graph.edges[e].0].eq(&distances[dir][graph.edges[e].1]),
                &Bool::and(&[
                    distances[dir][graph.edges[e].0].le(&distances[dir][graph.edges[e].1] + &int_idxs[1]),
                    distances[dir][graph.edges[e].1].le(&distances[dir][graph.edges[e].0] + &int_idxs[1])
                ])
            )
        );}

        // tightness constraints
        // \forall v : tight[v] -> (v in init \/ exists(u adjacent to v)(dist[v] == dist[u] + 1) )
        for v in 0..graph.n {optimiser.assert(
            tightness[dir][v].implies(Bool::or(
                &[Bool::from_bool(inits[dir].contains(&v))].into_iter().chain(
                    graph.adjacencies[v].iter().copied().map(|u| distances[dir][v].eq(&distances[dir][u] + &int_idxs[1]))
                ).collect::<Vec<_>>()))
        );}

        // tightness correctness for each tree // another O(n^2) operation
        // \forall t : card(T) > 0 -> exists(v in T)(tight[v])
        for t in 0..max_trees {optimiser.assert(
            vt_size[t].gt(&int_idxs[0]).implies(Bool::or(&
                (0..graph.n).into_iter().map(|v| Bool::and(&[
                    &v_graph[v].eq(&int_idxs[t+1]),
                    &tightness[dir][v]
                ])).collect::<Vec<_>>()
            ))
        );}

        // \forall v : v_graph[v] == 0 -> tight[v]
        for v in 0..graph.n {optimiser.assert(
            v_graph[v].eq(&int_idxs[0]).implies(&tightness[dir][v])
        );}
    }

    // Fuzziness Calculations
    let fuzzy = |e: usize| 
        Int::sub(&[&distances[1][graph.edges[e].0], &distances[0][graph.edges[e].0]]).eq(Int::sub(&[&distances[1][graph.edges[e].1], &distances[0][graph.edges[e].1]]));

    // No fuzzy unfused edges
    for e in 0..graph.m {optimiser.assert(fuzzy(e).implies(Bool::or(&[&fused[e], &bool_to_Bool(edge_is_fuzzy(e)).not()])));}

    let num_fused_edges = Int::add(&(0..graph.m).into_iter().map(|e| bool_to_int(&fused[e])).collect::<Vec<_>>());
    optimiser.minimize(&num_fused_edges);

    if debug > 1 {println!("Finished encoding problem in {}", encoding_timer.elapsed().as_secs_f32());}
    let solving_timer = Instant::now();
    
    match optimiser.check(&[]) {
        SatResult::Unsat => {
            panic!("Unable to satisfy hierarchical constraints with core: {:?}", optimiser.get_unsat_core());
        }
        SatResult::Unknown => {
            panic!("Unable to satisfy hierarchical constraints with reason: {:?}", optimiser.get_reason_unknown());
        }
        _ => {}
    }

    if debug > 1 {println!("Finished solving problem in {}", solving_timer.elapsed().as_secs_f32());}

    let model = optimiser.get_model().unwrap();
    let to_fuse: Vec<(usize, usize)> = (0..graph.m).into_iter().filter(|&e| model.eval(&fused[e], true).unwrap().as_bool().unwrap()).map(|e| graph.edges[e]).collect();
    // let distance_to_inputs: Vec<usize> = (0..graph.n).into_iter().map(|v| model.eval(&distances[0][v], true).unwrap().as_u64().unwrap() as usize).collect();
    // let distance_to_outputs: Vec<usize> = (0..graph.n).into_iter().map(|v| model.eval(&distances[1][v], true).unwrap().as_u64().unwrap() as usize).collect();

    to_fuse
}


    

    

    