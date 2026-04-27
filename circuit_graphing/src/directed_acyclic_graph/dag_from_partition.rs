use std::collections::{HashMap, HashSet};
use rustc_hash::FxHashSet;

use std::borrow::Borrow;
use itertools::Itertools;
use std::time::{Instant};

use super::DAGNode;
use circuits_and_constraints::constraint::Constraint;
use circuits_and_constraints::circuit::Circuit;
use circuits_and_constraints::utils::signals_to_constraints_with_them;
use utils::small_utilities::{distance_to_source_set, merge_sorted_vecs};
use utils::union_find::{UnionFind};

pub fn dag_from_partition<'a, C: Constraint + 'a, S: Circuit<C> + 'a>(
    circ: &'a S, partition: Vec<Vec<usize>>, node_id_generator: &mut dyn Iterator<Item = usize>,
    debug: usize) -> HashMap<usize, DAGNode<'a, C, S>> {

    let timer = Instant::now();

    // have partitions keep Vec<Vec<usize>>, index by vec index throughout until we make the DAGNodes


    // sorted arr signal list
    let n_parts = partition.len();
    let part_to_signals_arr: Vec<Vec<usize>> = partition.iter().map(|part|
        part.iter().copied().flat_map(|idx| circ.get_constraints()[idx].borrow().signals()).sorted_unstable().dedup().collect()
    ).collect();

    let input_parts: HashSet<usize> = (0..n_parts).filter(|key| part_to_signals_arr[*key].iter().any(|sig| circ.signal_is_input(sig))).collect();
    let output_parts: HashSet<usize> = (0..n_parts).filter(|key| part_to_signals_arr[*key].iter().any(|sig| circ.signal_is_output(sig))).collect();

    const NO_PART: usize = usize::MAX;
    let mut coni_to_part: Vec<usize> = vec![NO_PART; circ.n_constraints()];
    for (idx, part) in partition.iter().enumerate() {
        for coni in part.iter().copied() {
            match coni_to_part[coni] {
                NO_PART => {coni_to_part[coni] = idx;}
                _ => {panic!("Given partition has overlapping parts");}
            }
        }
    }

    // get the signal indices
    let sig_to_coni = signals_to_constraints_with_them(circ.get_constraints(), None, None);

    if debug > 1 { println!("LOG: Easy preprocessing done in {:?}", timer.elapsed().as_secs_f32()); }
    
    let mut last_seen_at: Vec<usize> = vec![0;n_parts];
    // note that this is not sorted
    let adjacencies: Vec<Vec<usize>> = (0..n_parts).map(|idx| 
        {let mut neighbours =  Vec::new();
        for part in part_to_signals_arr[idx].iter().copied().flat_map(|sig| sig_to_coni[&sig].iter().copied().map(|coni| coni_to_part[coni])).filter(|opart_id| *opart_id != idx) {
            if last_seen_at[part] != idx + 1 {
                last_seen_at[part] = idx + 1;
                neighbours.push(part);
            }
        }
        neighbours}
    ).collect();

    if debug > 1 { println!("LOG: Total-edges {:?}, max-edges {:?}", adjacencies.iter().map(|set| set.len()).sum::<usize>(), adjacencies.iter().map(|set| set.len()).max()); }
    if debug > 1 { println!("LOG: Adjacency preprocessing done in {:?}", timer.elapsed().as_secs_f32()); }

    let distance_to_inputs = distance_to_source_set(input_parts.into_iter(), &adjacencies);
    let distance_to_outputs = distance_to_source_set(output_parts.into_iter(), &adjacencies);

    if debug > 1 { println!("LOG: Found distances to sources in {:?}", timer.elapsed().as_secs_f32()); }

    // make the preorder
    let part_to_preorder: Vec<(usize, usize)> = (0..n_parts).map(|key| (distance_to_inputs[key], distance_to_outputs[key])).collect();

    
    // DAGNode indices might not be 0..n_parts so now need to do some pointer work
    // need idx => node_id for arcs 
    let idx_to_nodeid: Vec<usize> = node_id_generator.take(n_parts).collect();


    if debug > 1 { println!("LOG: Constructed preorder in {:?}", timer.elapsed().as_secs_f32()); }

    let mut nodes : HashMap<usize, DAGNode<'a, C, S>> = partition.into_iter().enumerate().map(|(idx, part)| {
        (idx_to_nodeid[idx], 
        DAGNode::new(
            circ, 
            idx_to_nodeid[idx], 
            part, 
            part_to_signals_arr[idx].iter().copied().filter(|sig| circ.signal_is_input(sig)).collect(), // get global labelled signal in initially
            part_to_signals_arr[idx].iter().copied().filter(|sig| circ.signal_is_output(sig)).collect(),
            None, None))
    }).collect();

    if debug > 1 { println!("LOG: Initialised nodes in {:?}", timer.elapsed().as_secs_f32()); }

    // define arcs that can be defined and collate the others to be fuzzy
    // TODO: rethink fuzzy adjacencies...

    let mut arcs : Vec<(usize, usize)> = Vec::new();
    let mut fuzzy_adjacencies: HashMap<usize, FxHashSet<usize>> = HashMap::new();

    fn lt(x: (usize, usize), y: (usize, usize)) -> bool {x.0 < y.0 && (y.1 <= x.1) || x.0 == y.0 && (y.1 < x.1)}

    for (idx, adjacent) in adjacencies.into_iter().enumerate() {for idy in adjacent.into_iter() {
        if lt(part_to_preorder[idx], part_to_preorder[idy]) {arcs.push((idx, idy));}
        else if !lt(part_to_preorder[idy], part_to_preorder[idx]) {fuzzy_adjacencies.entry(idx).or_insert_with(|| FxHashSet::default()).insert(idy);}
    }}

    if debug > 1 { println!("LOG: Total fuzzy edges {:?}, max-edges {:?}", fuzzy_adjacencies.values().map(|set| set.len()).sum::<usize>(), fuzzy_adjacencies.values().map(|set| set.len()).max()); }
    if debug > 1 { println!("LOG: Determined fuzzy arcs in {:?}", timer.elapsed().as_secs_f32()); }

    // add arcs to DAG

    fn add_arc_to_nodes<'a, C: Constraint + 'a, S: Circuit<C> + 'a>(arc: (usize, usize), idx_to_nodeid: &Vec<usize>, part_to_signals_arr: &Vec<Vec<usize>>, nodes: &mut HashMap<usize, DAGNode<'a, C, S>>) -> () {
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
    for arc in arcs.into_iter() {add_arc_to_nodes(arc, &idx_to_nodeid, &part_to_signals_arr, &mut nodes);}

    if debug > 1 { println!("LOG: added non-fuzzy arcs in {:?}", timer.elapsed().as_secs_f32()); }

    let mut verts_to_check : Vec<usize> =  fuzzy_adjacencies.keys().filter(|key| fuzzy_adjacencies[key].len() == 1).copied().collect();

    // propagate easy vertices and add the new arcs to the nodes
    while verts_to_check.len() > 0 {

        let idx = verts_to_check.pop().unwrap();
        let node_id = idx_to_nodeid[idx];

        if fuzzy_adjacencies[&idx].len() == 1 && (nodes[&node_id].get_successors().len() == 0 || nodes[&node_id].get_predecessors().len() == 0) {
            // add arc
            let other = fuzzy_adjacencies[&idx].iter().copied().exactly_one().unwrap();
            let arc = if nodes[&node_id].get_successors().len() == 0 {(idx, other)} else {(other, idx)};
            add_arc_to_nodes(arc, &idx_to_nodeid, &part_to_signals_arr, &mut nodes);

            //update graph
            fuzzy_adjacencies.entry(other).and_modify(|set| {set.remove(&idx);} );
            if fuzzy_adjacencies[&other].len() == 1 {verts_to_check.push(other);}
        }
    }

    // merge remaining nodes
    let mut undirected_components = UnionFind::new(false);
    for (idx, adjacent) in fuzzy_adjacencies.into_iter() {
        undirected_components.union([idx].into_iter().chain(adjacent.into_iter()).map(|x| idx_to_nodeid[x]));
    }

    let mut coni_to_node: Vec<usize> = vec![0; circ.n_constraints()];
    for (coni, node_id) in nodes.values().flat_map(|node| node.constraints.iter().map(|coni| (coni, node.id))) { coni_to_node[*coni] = node_id };

    if debug > 1 { println!("LOG: Determined fuzzy components in {:?}", timer.elapsed().as_secs_f32()); }

    let components_to_merge = undirected_components.get_components();
    if debug > 1 { println!("LOG: Need to merge {:?} components with total size {:?}", components_to_merge.len(), components_to_merge.iter().map(|s| s.len()).sum::<usize>()); }

    for to_merge in components_to_merge.into_iter() {
        DAGNode::merge_nodes(to_merge.into_iter().collect(), &mut nodes, &sig_to_coni, &mut coni_to_node);
    }
    if debug > 1 { println!("LOG: Merged fuzzy components in {:?}", timer.elapsed().as_secs_f32()); }

    nodes
}
