use std::collections::{HashMap, HashSet};
use std::borrow::Borrow;
use itertools::Itertools;
use std::time::{Instant};

use super::DAGNode;
use circuits_and_constraints::constraint::Constraint;
use circuits_and_constraints::circuit::Circuit;
use circuits_and_constraints::utils::signals_to_constraints_with_them;
use utils::small_utilities::{distance_to_source_set};
use utils::union_find::{UnionFind};

pub fn dag_from_partition<'a, C: Constraint + 'a, S: Circuit<C> + 'a>(
    circ: &'a S, partition: Vec<Vec<usize>>, node_id_generator: &mut dyn Iterator<Item = usize>,
    debug: usize) -> HashMap<usize, DAGNode<'a, C, S>> {

    let timer = Instant::now();

    let partition: HashMap<usize, Vec<usize>> = node_id_generator.zip(partition.into_iter()).collect();
    
    let part_to_signals_arr: HashMap<usize, HashSet<usize>> = partition.keys().copied().map(|key| (key, partition.get(&key).unwrap().iter().copied().flat_map(|idx| circ.get_constraints()[idx].borrow().signals()).collect::<HashSet<usize>>())).collect();

    let input_parts: HashSet<usize> = partition.keys().copied().filter(|key| part_to_signals_arr.get(key).unwrap().iter().any(|sig| circ.signal_is_input(sig))).collect();
    let output_parts: HashSet<usize> = partition.keys().copied().filter(|key| part_to_signals_arr.get(key).unwrap().iter().any(|sig| circ.signal_is_output(sig))).collect();

    let mut coni_to_part: Vec<Option<&usize>> = vec![None; circ.n_constraints()];
    for (idx, part) in partition.iter() {
        for coni in part.iter().copied() {
            match coni_to_part[coni] {
                Some(_) => {panic!("Given partition has overlapping parts");}
                None => {coni_to_part[coni] = Some(idx);}
            }
        }
    }

    // get the signal indices
    let sig_to_coni = signals_to_constraints_with_them(circ.get_constraints(), None, None);

    if debug > 1 { println!("LOG: Easy preprocessing done in {:?}", timer.elapsed().as_secs_f32()); }

    let adjacent_parts = 
        |part_id: usize| -> HashSet<usize> {part_to_signals_arr.get(&part_id).unwrap().iter().copied().flat_map(|sig| sig_to_coni.get(&sig).unwrap()).map(|coni| coni_to_part[*coni].unwrap()).copied().filter(|opart_id| *opart_id != part_id).collect()};

    let adjacencies: HashMap<usize, HashSet<usize>> = partition.keys().map(|key| (*key, adjacent_parts(*key))).collect();

    if debug > 1 { println!("LOG: Total-edges {:?}, max-edges {:?}", adjacencies.values().map(|set| set.len()).sum::<usize>(), adjacencies.values().map(|set| set.len()).max()); }
    if debug > 1 { println!("LOG: Adjacency preprocessing done in {:?}", timer.elapsed().as_secs_f32()); }

    let distance_to_inputs = distance_to_source_set(input_parts.iter(), &adjacencies);
    let distance_to_outputs = distance_to_source_set(output_parts.iter(), &adjacencies);

    if debug > 1 { println!("LOG: Found distances to sources in {:?}", timer.elapsed().as_secs_f32()); }

    // make the preorder
    let part_to_preorder: HashMap<usize, (usize, usize)> = partition.keys().map(|key| (*key, (*distance_to_inputs.get(key).unwrap_or(&usize::MAX), *distance_to_outputs.get(key).unwrap_or(&usize::MAX)))).collect();

    if debug > 1 { println!("LOG: Constructed preorder in {:?}", timer.elapsed().as_secs_f32()); }

    let mut nodes : HashMap<usize, DAGNode<'a, C, S>> = partition.into_iter().map(|(idx, part)| {
        (idx, 
        DAGNode::new(
            circ, 
            idx, 
            part, 
            part_to_signals_arr.get(&idx).unwrap().into_iter().copied().filter(|sig| circ.signal_is_input(sig)).collect(), // can get around
            part_to_signals_arr.get(&idx).unwrap().into_iter().copied().filter(|sig| circ.signal_is_output(sig)).collect(),
            None, None))
    }).collect();

    if debug > 1 { println!("LOG: Initialised nodes in {:?}", timer.elapsed().as_secs_f32()); }

    // define arcs that can be defined and collate the others to be fuzzy

    let mut arcs : Vec<(usize, usize)> = Vec::new();
    let mut fuzzy_adjacencies: HashMap<usize, HashSet<usize>> = HashMap::new();

    fn lt(x: (usize, usize), y: (usize, usize)) -> bool {x.0 < y.0 && (y.1 <= x.1) || x.0 == y.0 && (y.1 < x.1)}

    for idx in nodes.keys() {for idy in adjacencies[idx].iter() {
        if lt(part_to_preorder[idx], part_to_preorder[idy]) {arcs.push((*idx, *idy));}
        else if !lt(part_to_preorder[idy], part_to_preorder[idx]) {fuzzy_adjacencies.entry(*idx).or_insert_with(|| HashSet::new()).insert(*idy);}
    }}

    if debug > 1 { println!("LOG: Total fuzzy edges {:?}, max-edges {:?}", fuzzy_adjacencies.values().map(|set| set.len()).sum::<usize>(), fuzzy_adjacencies.values().map(|set| set.len()).max()); }
    if debug > 1 { println!("LOG: Determined fuzzy arcs in {:?}", timer.elapsed().as_secs_f32()); }

    // add arcs to DAG

    fn add_arc_to_nodes<'a, C: Constraint + 'a, S: Circuit<C> + 'a>(arc: (usize, usize), part_to_signals_arr: &HashMap<usize, HashSet<usize>>, nodes: &mut HashMap<usize, DAGNode<'a, C, S>>) -> () {
        let (l, r) = arc;

        let shared_signals: Vec<usize> = part_to_signals_arr.get(&l).unwrap().intersection(part_to_signals_arr.get(&r).unwrap()).copied().collect();

        {let lnode: &mut DAGNode<C, S> = nodes.get_mut(&l).unwrap();

        lnode.add_successors([r].into_iter());
        lnode.update_output_signals(shared_signals.iter().copied());};

        {let rnode: &mut DAGNode<C, S> = nodes.get_mut(&r).unwrap();
        
        rnode.add_predecessors([l].into_iter());
        rnode.update_input_signals(shared_signals.into_iter())};
    }
    for arc in arcs.into_iter() {add_arc_to_nodes(arc, &part_to_signals_arr, &mut nodes);}

    if debug > 1 { println!("LOG: added non-fuzzy arcs in {:?}", timer.elapsed().as_secs_f32()); }

    let mut verts_to_check : Vec<usize> =  fuzzy_adjacencies.keys().filter(|key| fuzzy_adjacencies[key].len() == 1).copied().collect();

    // propagate easy vertices and add the new arcs to the nodes
    while verts_to_check.len() > 0 {

        let idx = verts_to_check.pop().unwrap();

        if fuzzy_adjacencies[&idx].len() == 1 && (nodes[&idx].get_successors().len() == 0 || nodes[&idx].get_predecessors().len() == 0) {
            // add arc
            let other = fuzzy_adjacencies[&idx].iter().copied().exactly_one().unwrap();
            let arc = if nodes[&idx].get_successors().len() == 0 {(idx, other)} else {(other, idx)};
            add_arc_to_nodes(arc, &part_to_signals_arr, &mut nodes);

            //update graph
            fuzzy_adjacencies.entry(other).and_modify(|set| {set.remove(&idx);} );
            if fuzzy_adjacencies[&other].len() == 1 {verts_to_check.push(other);}
        }
    }

    // merge remaining nodes
    let mut undirected_components = UnionFind::new(false);
    for (idx, adjacent) in fuzzy_adjacencies.into_iter() {
        undirected_components.union([idx].into_iter().chain(adjacent.into_iter()));
    }

    let mut coni_to_node: Vec<usize> = vec![0; circ.n_constraints()];
    for (coni, node_id) in nodes.values().flat_map(|node| node.constraints.iter().map(|coni| (coni, node.id))) { coni_to_node[*coni] = node_id };

    if debug > 1 { println!("LOG: Determined fuzzy components in {:?}", timer.elapsed().as_secs_f32()); }

    let components_to_merge = undirected_components.get_components();
    if debug > 1 { println!("LOG: Need to merge {:?} components with total size {:?}", components_to_merge.len(), components_to_merge.iter().map(|s| s.len()).sum::<usize>()); }

    for (i, to_merge) in components_to_merge.into_iter().enumerate() {
        DAGNode::merge_nodes(to_merge.into_iter().collect(), &mut nodes, &sig_to_coni, &mut coni_to_node);
    }
    if debug > 1 { println!("LOG: Merged fuzzy components in {:?}", timer.elapsed().as_secs_f32()); }

    nodes
}
