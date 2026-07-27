use std::collections::{HashMap, HashSet};
use itertools::Itertools;

use circuits_constraints_and_algebra::circuit::Circuit;
use circuits_constraints_and_algebra::constraint::Constraint;
use circuit_graphing::directed_acyclic_graph::{DAGNode};
use utils::small_utilities::dfs_merge_set_in_dag_hashmap_adj;
use circuits_constraints_and_algebra::utils::signals_to_constraints_with_them;

pub fn agree_on_merge(to_merge: &[usize], mut left_side: bool, left_adjecencies: &HashMap<usize, &Vec<usize>>, right_adjacencies: &HashMap<usize, &Vec<usize>>) -> HashSet<usize> {
    
    let mut current_merge: HashSet<usize> = to_merge.into_iter().copied().collect();

    loop {
        let new_merge: HashSet<usize> = dfs_merge_set_in_dag_hashmap_adj(&current_merge, if left_side {left_adjecencies} else {right_adjacencies});
        if new_merge == current_merge {break;}
        current_merge = new_merge;
        left_side = !left_side;
    }
    
    current_merge
}

pub(crate) fn dual_merge_until_property<'a, LCon: Constraint, Left: Circuit<LCon>, RCon: Constraint, Right: Circuit<RCon>>(
    left: &'a Left, right: &'a Right, 
    left_nodes: &mut HashMap<usize, DAGNode<'a, LCon, Left>>, right_nodes: &mut HashMap<usize, DAGNode<'a, RCon, Right>>,
    node_meets_property: fn(&DAGNode<'a, LCon, Left>, &DAGNode<'a, RCon, Right>) -> bool,
    get_minimum_merge_for_property: fn(usize, &HashMap<usize, DAGNode<'a, LCon, Left>>,  &HashMap<usize, DAGNode<'a, RCon, Right>>, &HashMap<usize, Vec<usize>>, &Vec<usize>, &HashMap<usize,Vec<usize>>, &Vec<usize>) -> (Vec<usize>, bool)
) -> () {

    // check that inputs have same keysets once
    assert_eq!(left_nodes.len(), right_nodes.len());
    assert!(left_nodes.keys().all(|k| right_nodes.contains_key(k)));

    let mut stack: Vec<usize> = left_nodes.keys().copied().filter(|key| !node_meets_property(&left_nodes[key], &right_nodes[key])).collect();

    let left_sig_to_coni = signals_to_constraints_with_them::<LCon>(&left.constraints(), None, None);
    let mut left_coni_to_node: Vec<usize> = vec![0; left.n_constraints()];
    for (coni, node_id) in left_nodes.values().flat_map(|node| node.get_constraint_indices().map(|coni| (coni, node.get_id()))) { left_coni_to_node[coni] = node_id };

    let right_sig_to_coni = signals_to_constraints_with_them::<RCon>(&right.constraints(), None, None);
    let mut right_coni_to_node: Vec<usize> = vec![0; right.n_constraints()];
    for (coni, node_id) in right_nodes.values().flat_map(|node| node.get_constraint_indices().map(|coni| (coni, node.get_id()))) { right_coni_to_node[coni] = node_id };

    while stack.len() > 0 && left_nodes.len() > 1 {

        println!("#################################################");

        let val = stack.pop().unwrap();
        if !left_nodes.contains_key(&val) {continue;}
        if node_meets_property(&left_nodes[&val], &right_nodes[&val]) {continue;}

        // doing it this way actually takes longer but is cleaner code
        let left_adjacency : HashMap<usize, &Vec<usize>> = left_nodes.iter().map(|(k, node)| (*k, node.get_successors())).collect();
        let right_adjacency : HashMap<usize, &Vec<usize>> = right_nodes.iter().map(|(k, node)| (*k, node.get_successors())).collect();

        let (min_merge, left_side) = get_minimum_merge_for_property(val, left_nodes, right_nodes, &left_sig_to_coni, &left_coni_to_node, &right_sig_to_coni, &right_coni_to_node);
        let to_merge = agree_on_merge(&min_merge, left_side, &left_adjacency, &right_adjacency);

        if to_merge.len() <= 1 {panic!("Merging solo cluster");}
        let root = *to_merge.iter().next().expect("Merging Empty");

        println!("merged {:?} into {}", to_merge.clone(), root);
        DAGNode::merge_nodes(root, &to_merge, left_nodes, &left_sig_to_coni, &mut left_coni_to_node);
        DAGNode::merge_nodes(root, &to_merge, right_nodes, &right_sig_to_coni, &mut right_coni_to_node);

        // check root again
        if !node_meets_property(&left_nodes[&root], &right_nodes[&root]) {stack.push(root);}
    }
}