use z3::{Optimize, ast::Bool, ast::Int, ast::Set, Sort, SatResult::Sat};
use std::collections::{HashSet};
use std::time::{Instant};

use utils::small_utilities::distance_to_source_set;

pub fn dag_from_partition_solver(
    adjacencies: &Vec<Vec<usize>>, input_parts: &HashSet<usize>, output_parts: &HashSet<usize>, debug: usize) -> (Vec<(usize, usize)>, Vec<usize>, Vec<usize>) {    
    
    let encoding_timer = Instant::now();
    let n_parts = adjacencies.len();

    // Building this according to Cosntraint Optimisation intuition -- need to get people more familiar with SMT to take a look at it.
    let edges: Vec<(usize, usize)> = adjacencies.iter().enumerate().flat_map(|(i, adj)| adj.into_iter().copied().map(move |v| (i, v)) ).filter(|(a, b)| a < b).collect();
    let m_edges: usize = edges.len();

    // Precalculate distances for some early local information
    let distance_to_inputs = distance_to_source_set(input_parts.into_iter().copied(), adjacencies);
    let distance_to_outputs = distance_to_source_set(output_parts.into_iter().copied(), adjacencies);
    
    let edge_is_fuzzy = |e: usize| {
        // edge_is fuzzy if x_ord.1 - x_ord.0 == x_ord.0 - x_ord.1
        let x_ord = (distance_to_inputs[edges[e].0], distance_to_outputs[edges[e].0]);
        let y_ord = (distance_to_inputs[edges[e].1], distance_to_outputs[edges[e].1]);
        x_ord.1.wrapping_sub(x_ord.0) == y_ord.1.wrapping_sub(y_ord.0) // wrapping doesn't matter here since we're interested in equality
    };

    let mut incidence: Vec<Vec<usize>> = (0..n_parts).into_iter().map(|_| Vec::new()).collect();
    for (i, &(u, v)) in edges.iter().enumerate() {incidence[u].push(i);incidence[v].push(i);}

    let optimiser = Optimize::new();

    // default fixed vars reused to save number of vars
    let int_idxs: Vec<Int> = (0..n_parts).into_iter().map(|i| Int::from_u64(i as u64)).collect();
    let empty: Set = Set::empty(&Sort::int()); let bool_false: Bool = Bool::from_bool(false); let bool_true: Bool = Bool::from_bool(true); 
    let bool_to_Bool = |x: bool| if x {&bool_true} else {&bool_false};

    // For each edge (not arc) we have a boolean decision variable about whether or not that edge is 'fused'
    let fused: Vec<Bool> = (0..m_edges).into_iter().map(|e| Bool::new_const(format!("f_{e}"))).collect();

    // \forall e : fused[e] => edge_is_fuzzy(e)
    for e in 0..m_edges {optimiser.assert(
        fused[e].implies(bool_to_Bool(edge_is_fuzzy(e)))
    );}

    // We map each vertex and edge to a tree T in 0..max_trees (with 0 being not in a tree)
    let v_trees: Vec<Int> = (0..n_parts).into_iter().map(|v| Int::new_const(format!("vt_{v}"))).collect();
    let e_trees: Vec<Int> = (0..m_edges).into_iter().map(|e| Int::new_const(format!("et_{e}"))).collect();
    let max_trees: usize = n_parts >> 1;

    // max_tree bounds

    // \forall e : 0 <= e_trees[e] <= max_trees
    for e in 0..m_edges {optimiser.assert(
        Bool::and(&[e_trees[e].ge(&int_idxs[0]), e_trees[e].le(&int_idxs[max_trees])])
    );}
    // \forall v : 0 <= v_trees[v] <= max_trees
    for v in 0..n_parts {optimiser.assert(
        Bool::and(&[v_trees[v].ge(&int_idxs[0]), v_trees[v].le(&int_idxs[max_trees])])
    );}

    // Constraints to ensure tree correctness

    // \forall e : fused[e] == e_trees[e] >= 0
    // \forall uv : fused[uv] -> e_trees[uv] == v_trees[v] == v_trees[u]
    for e in 0..m_edges {optimiser.assert(Bool::and(&[
        fused[e].eq(e_trees[e].gt(&int_idxs[0])),
        fused[e].implies(Bool::and(&[e_trees[e].eq(&v_trees[edges[e].0]), e_trees[e].eq(&v_trees[edges[e].1])]))
    ]));}
    // \forall v : all(e incident to v)(not fused[e]) -> v_trees[v] = 0 // expanded into singular OR clause
    for v in 0..n_parts {optimiser.assert(
        Bool::or(
            &[&v_trees[v].eq(&int_idxs[0])].into_iter().chain(incidence[v].iter().copied().map(|e| &fused[e])).collect::<Vec<_>>()
        )
    );}

    // Num of each v/e in tree
    // We ensure tree with constraints i.e. |V| = |E| + 1
    let vt_size: Vec<Int> = (0..max_trees).into_iter().map(|x| Int::new_const(format!("tv_{x}"))).collect();
    let et_size: Vec<Int> = (0..max_trees).into_iter().map(|x| Int::new_const(format!("te_{x}"))).collect();

    // Note that this is O(n^2). I can't really think of a way to improve this but this really slows us down.
    // \forall t : |V_t| = |E_t| + 1
    let bool_to_int = |b: &Bool| b.ite(&int_idxs[1], &int_idxs[0]);
    for t in 0..max_trees {optimiser.assert(Bool::and(&[
        vt_size[t].eq(Int::add(&(0..n_parts).into_iter().map(|v| bool_to_int(&v_trees[v].eq(&int_idxs[t+1]))).collect::<Vec<_>>())),
        et_size[t].eq(Int::add(&(0..m_edges).into_iter().map(|e| bool_to_int(&e_trees[e].eq(&int_idxs[t+1]))).collect::<Vec<_>>())),
        et_size[t].gt(&int_idxs[0]).implies(vt_size[t].eq(Int::add(&[&et_size[t], &int_idxs[1]])))
    ]));}
    
    // We then have distance variables for in/out, and tightness boolean for each in/out
    //  init values set to 0
    //  edges bound either 1 increment, or equality
    //  tightness is an exact 1 increment -- enforce tightness in each tree
    let original_distances: [&Vec<usize>; 2] = [&distance_to_inputs, &distance_to_outputs];
    let inits: [&HashSet<usize>; 2] = [input_parts, output_parts];
    let distances: [Vec<Int>; 2] = [(0..n_parts).into_iter().map(|x| Int::new_const(format!("d1_{x}"))).collect(),
                                    (0..n_parts).into_iter().map(|x| Int::new_const(format!("d2_{x}"))).collect()];
    let tightness: [Vec<Bool>; 2] = [(0..n_parts).into_iter().map(|x| Bool::new_const(format!("t1_{x}"))).collect(),
                                     (0..n_parts).into_iter().map(|x| Bool::new_const(format!("t2_{x}"))).collect()];

    for dir in 0..2 {
        // initialise
        for v in inits[dir].into_iter().copied() {optimiser.assert(distances[dir][v].eq(&int_idxs[0]));}

        // general upper bounds (original distances) 0 <= d_v <= init_dist(v)
        for v in 0..n_parts {optimiser.assert(
            Bool::and(&[
                distances[dir][v].ge(&int_idxs[0]),
                distances[dir][v].le(&int_idxs[original_distances[dir][v]])
            ])
        );}

        // edge bounds
        for e in 0..m_edges {optimiser.assert(
            fused[e].ite(
                &distances[dir][edges[e].0].eq(&distances[dir][edges[e].1]),
                &Bool::and(&[
                    distances[dir][edges[e].0].le(Int::add(&[&distances[dir][edges[e].1], &int_idxs[1]])),
                    distances[dir][edges[e].1].le(Int::add(&[&distances[dir][edges[e].0], &int_idxs[1]]))
                ])
            )
        );}

        // tightness constraints
        // \forall v : tight[v] -> (v in init \/ exists(u adjacent to v)(dist[v] == dist[u] + 1) )
        for v in 0..n_parts {optimiser.assert(
            tightness[dir][v].implies(Bool::or(
                &[Bool::from_bool(inits[dir].contains(&v))].into_iter().chain(
                    adjacencies[v].iter().copied().map(|u| distances[dir][v].eq(Int::add(&[&distances[dir][u], &int_idxs[1]])))
                ).collect::<Vec<_>>()))
        );}

        // tightness correctness for each tree // another O(n^2) operation
        // \forall t : card(T) > 0 -> exists(v in T)(tight[v])
        for t in 0..max_trees {optimiser.assert(
            vt_size[t].gt(&int_idxs[0]).implies(Bool::or(&
                (0..n_parts).into_iter().map(|v| Bool::and(&[
                    &v_trees[v].eq(&int_idxs[t+1]),
                    &tightness[dir][v]
                ])).collect::<Vec<_>>()
            ))
        );}

        // \forall v : v_trees[v] == 0 -> tight[v]
        for v in 0..n_parts {optimiser.assert(
            v_trees[v].eq(&int_idxs[0]).implies(&tightness[dir][v])
        );}
    }

    // Fuzziness Calculations
    let fuzzy = |e: usize| 
        Int::sub(&[&distances[1][edges[e].0], &distances[0][edges[e].0]]).eq(Int::sub(&[&distances[1][edges[e].1], &distances[0][edges[e].1]]));

    // No fuzzy unfused edges
    for e in 0..m_edges {optimiser.assert(fuzzy(e).implies(&fused[e]));}

    let num_fused_edges = Int::add(&(0..m_edges).into_iter().map(|e| bool_to_int(&fused[e])).collect::<Vec<_>>());
    optimiser.minimize(&num_fused_edges);

    if debug > 1 {println!("Finished encoding problem in {}", encoding_timer.elapsed().as_secs_f32());}
    let solving_timer = Instant::now();
    
    if optimiser.check(&[]) != Sat {panic!("Unable to satisfy hierarchical constraints");}

    if debug > 1 {println!("Finished encoding problem in {}", solving_timer.elapsed().as_secs_f32());}

    let model = optimiser.get_model().unwrap();
    let to_fuse: Vec<(usize, usize)> = (0..m_edges).into_iter().filter(|&e| model.eval(&fused[e], true).unwrap().as_bool().unwrap()).map(|e| edges[e]).collect();
    let distance_to_inputs: Vec<usize> = (0..n_parts).into_iter().map(|v| model.eval(&distances[0][v], true).unwrap().as_u64().unwrap() as usize).collect();
    let distance_to_outputs: Vec<usize> = (0..n_parts).into_iter().map(|v| model.eval(&distances[1][v], true).unwrap().as_u64().unwrap() as usize).collect();

    return (to_fuse, distance_to_inputs, distance_to_outputs)
}


    

    

    