use std::collections::{HashMap, HashSet};

use super::DAGNode;
use circuits_and_constraints::constraint::Constraint;
use circuits_and_constraints::circuit::Circuit;
use circuits_and_constraints::utils::signals_to_constraints_with_them;
use utils::small_utilities::{distance_to_source_set};
use utils::union_find::{UnionFind};

pub fn dag_from_partition<'a, C: Constraint + 'a, S: Circuit<C> + 'a>(circ: &'a S, partition: Vec<Vec<usize>>) -> HashMap<usize, DAGNode<'a, C, S>> {

    let mut partition: HashMap<usize, Vec<usize>> = partition.into_iter().enumerate().collect();
    
    let part_to_signals_arr: HashMap<usize, HashSet<usize>> = partition.keys().copied().map(|key| (key, partition.get(&key).unwrap().iter().copied().flat_map(|idx| circ.get_constraints()[idx].signals()).collect::<HashSet<usize>>())).collect();

    let mut input_parts: HashSet<usize> = partition.keys().copied().filter(|key| part_to_signals_arr.get(key).unwrap().iter().copied().any(|sig| circ.signal_is_input(sig))).collect();
    let mut output_parts: HashSet<usize> = partition.keys().copied().filter(|key| part_to_signals_arr.get(key).unwrap().iter().copied().any(|sig| circ.signal_is_output(sig))).collect();

    let mut coni_to_part: Vec<Option<&usize>> = vec![None; circ.n_constraints()];
    for (idx, part) in partition.iter() {
        for coni in part.iter().copied() {
            match coni_to_part[coni] {
                Some(_) => {panic!("Given partition has overlapping parts");}
                None => {coni_to_part[coni] = Some(idx);}
            }
        }
    }

    let sig_to_coni = signals_to_constraints_with_them(circ.get_constraints(), None, None);

    let adjacent_parts = 
        |part_id: usize| -> HashSet<usize> {part_to_signals_arr.get(&part_id).unwrap().iter().copied().flat_map(|sig| sig_to_coni.get(&sig).unwrap()).map(|coni| coni_to_part[*coni].unwrap()).copied().filter(|opart_id| *opart_id != part_id).collect()};

    let mut adjacencies: HashMap<usize, HashSet<usize>> = partition.keys().map(|key| (*key, adjacent_parts(*key))).collect();
    let mut any_merges: bool = true;
    let mut part_to_preorder: HashMap<usize, (usize, usize)> = HashMap::new();

    drop(part_to_signals_arr);

    while any_merges {
        any_merges = false;

        let distance_to_inputs = distance_to_source_set(input_parts.iter(), &adjacencies);
        let distance_to_outputs = distance_to_source_set(output_parts.iter(), &adjacencies);

        // make the preorder
        part_to_preorder = partition.keys().map(|key| (*key, (*distance_to_inputs.get(key).unwrap_or(&usize::MAX), *distance_to_outputs.get(key).unwrap_or(&usize::MAX)))).collect();
        let mut to_merge = UnionFind::new(false);
        
        // detect equivalent adjacent pairs and merge them
        for parti in partition.keys() {
            for partj in adjacencies.get(parti).unwrap() {
                if part_to_preorder.get(parti).unwrap() == part_to_preorder.get(partj).unwrap() {
                    any_merges = true;
                    to_merge.union([*parti, *partj].into_iter())
                }
            }
        }

        let parts_to_merge: Vec<Vec<usize>> = to_merge.get_components();

        merge_parts(parts_to_merge, &mut input_parts, &mut output_parts, &mut partition, &mut adjacencies);
    }

    let part_to_signals_arr: HashMap<usize, HashSet<usize>> = partition.keys().copied().map(|key| (key, partition.get(&key).unwrap().iter().copied().flat_map(|idx| circ.get_constraints()[idx].signals()).collect::<HashSet<usize>>())).collect();

    let mut nodes : HashMap<usize, DAGNode<'a, C, S>> = partition.into_iter().map(|(idx, part)| {
        (idx, 
        DAGNode::new(
            circ, 
            idx, 
            part, 
            part_to_signals_arr.get(&idx).unwrap().into_iter().copied().filter(|sig| circ.signal_is_input(*sig)).collect(), // can get around
            part_to_signals_arr.get(&idx).unwrap().into_iter().copied().filter(|sig| circ.signal_is_output(*sig)).collect()))
    }).collect();

    let arcs : Vec<(usize, usize)> = nodes.keys().flat_map(|idx| adjacencies.get(idx).unwrap().iter().map(|idy| (*idx, *idy))).filter(|(idx, idy)| {
        let (x0, x1) = part_to_preorder.get(idx).unwrap();
        let (y0, y1) = part_to_preorder.get(idy).unwrap();
        x0 < y0 || (x0 == y0 && x1 > y1) }).collect();

    for arc in arcs.into_iter() {
        let (l, r) = arc;

        let shared_signals: Vec<usize> = part_to_signals_arr.get(&l).unwrap().intersection(part_to_signals_arr.get(&r).unwrap()).copied().collect();

        {let lnode: &mut DAGNode<C, S> = nodes.get_mut(&l).unwrap();

        lnode.add_successors([r].into_iter());
        lnode.update_output_signals(shared_signals.iter().copied());};

        {let rnode: &mut DAGNode<C, S> = nodes.get_mut(&r).unwrap();
        
        rnode.add_predecessors([l].into_iter());
        rnode.update_input_signals(shared_signals.into_iter())};
    }

    nodes
}

fn merge_parts(to_merge: Vec<Vec<usize>>, input_parts: &mut HashSet<usize>, output_parts: &mut HashSet<usize>, partition: &mut HashMap<usize, Vec<usize>>, adjacencies: &mut HashMap<usize, HashSet<usize>>) -> () {

    for batch in to_merge.into_iter() {
        let root = batch[0];

        
        let combined_vertices: Vec<usize> = batch.iter().flat_map(|x| partition.get(x).unwrap().iter().copied()).collect();
        partition.entry(root).insert_entry(combined_vertices);
        
        let mut combined_adjacencies: HashSet<usize> = batch.iter().flat_map(|x| adjacencies.get(x).unwrap().iter().copied()).collect();
        for idx in batch.iter() {combined_adjacencies.remove(idx);};

        adjacencies.entry(root).insert_entry(combined_adjacencies);

        for parti in batch.iter().skip(1) {
            partition.remove(parti);

            let partj_to_remove: Vec<usize> = adjacencies.get(parti).unwrap().iter().filter(|x| !batch.contains(x)).copied().collect();

            for partj in partj_to_remove.iter() {
                let set = adjacencies.get_mut(partj).unwrap();
                set.remove(parti);
                set.insert(root);
            }

            adjacencies.remove(parti);
        }

        fn fix_source_set(source: &mut HashSet<usize>, batch: &Vec<usize>, root: usize) {
            let source_in_batch: Vec<usize> = batch.iter().filter(|x| source.contains(x)).copied().collect();
            if source_in_batch.len() > 0 {
                for idx in source_in_batch.iter() {
                    source.remove(idx);
                };
                source.insert(root);
            };
        }

        fix_source_set(input_parts, &batch, root);
        fix_source_set(output_parts, &batch, root);
    }
}