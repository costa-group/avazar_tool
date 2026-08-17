use std::collections::{HashMap, HashSet};

use circuits_constraints_and_algebra::circuit::Circuit;
use circuits_constraints_and_algebra::constraint::Constraint;
use circuit_graphing::directed_acyclic_graph::{DAGNode};
use utils::small_utilities::{dfs_merge_set_in_dag_hashmap_adj, dfs_merge_in_dag};
use circuits_constraints_and_algebra::utils::signals_to_constraints_with_them;

pub fn agree_on_merge(mut to_merge: HashSet<usize>, mut left_side: bool, left_adjecencies: &HashMap<usize, &Vec<usize>>, right_adjacencies: &HashMap<usize, &Vec<usize>>) -> HashSet<usize> {
    loop {
        let new_merge: HashSet<usize> = dfs_merge_set_in_dag_hashmap_adj(&to_merge, if left_side {left_adjecencies} else {right_adjacencies});
        if new_merge == to_merge {break;}
        to_merge = new_merge;
        left_side = !left_side;
    }
    
    to_merge
}

pub fn merge_passthrough_shared<'a, LCon: Constraint, Left: Circuit<LCon>, RCon: Constraint, Right: Circuit<RCon>>(
    left: &'a Left, right: &'a Right,
    left_nodes: &mut HashMap<usize, DAGNode<'a, LCon, Left>>, right_nodes: &mut HashMap<usize, DAGNode<'a, RCon, Right>>,
) -> () {

    // Find passthrough signals in each DAG
    // Merging nodes will never create a passthrough signal so we can just handle each individually
    fn get_passthrough_signals<'a, C: Constraint + 'a, S: Circuit<C> + 'a>(node: &DAGNode<'a, C, S>) -> impl Iterator<Item = usize> {
        node.get_input_signals().intersection(node.get_output_signals()).copied()
    }

    fn is_passthrough_for_signal<'a, C: Constraint + 'a, S: Circuit<C> + 'a>(node: &DAGNode<'a, C, S>, signal: &usize) -> bool {
        node.get_input_signals().contains(signal) && node.get_output_signals().contains(signal)
    }

    let left_sig_to_coni = signals_to_constraints_with_them::<LCon>(&left.constraints(), None, None);
    let right_sig_to_coni = signals_to_constraints_with_them::<RCon>(&right.constraints(), None, None);
    let mut left_coni_to_node: Vec<usize> = vec![0; left.n_constraints()];
    for (coni, node_id) in left_nodes.values().flat_map(|node| node.get_constraint_indices().map(|coni| (coni, node.get_id()))) { left_coni_to_node[coni] = node_id };
    let mut right_coni_to_node: Vec<usize> = vec![0; right.n_constraints()];
    for (coni, node_id) in right_nodes.values().flat_map(|node| node.get_constraint_indices().map(|coni| (coni, node.get_id()))) { right_coni_to_node[coni] = node_id };
    
    let left_passthrough_signals: HashSet<usize> = left_nodes.values().flat_map(|node| get_passthrough_signals(node)).collect();
    let right_passthrough_signals: HashSet<usize> = right_nodes.values().flat_map(|node| get_passthrough_signals(node)).collect();

    fn get_to_merge<'a, C: Constraint + 'a, S: Circuit<C> + 'a>(
        signal: usize, nodes: &HashMap<usize, DAGNode<'a, C, S>>, sig_to_coni: &HashMap<usize, Vec<usize>>, coni_to_node: &Vec<usize>, adjacency_hashmap: &HashMap<usize, &Vec<usize>>
    ) -> HashSet<usize> {
        
        // find nodes that contain signal as input but not as output
        let mut non_passthrough_nodes: Vec<usize> = Vec::new();
        let mut passthrough_nodes: Vec<usize> = Vec::new();
        for nodeid in sig_to_coni[&signal].iter().map(|coni| coni_to_node[*coni]).collect::<HashSet<usize>>().into_iter() {
            if is_passthrough_for_signal(&nodes[&nodeid], &signal) {passthrough_nodes.push(nodeid);} else {non_passthrough_nodes.push(nodeid);}
        }
        if passthrough_nodes.len() == 0 {return HashSet::new();}
        if non_passthrough_nodes.len() == 0 {panic!("There does not exist a non-passthrough node for signal {:?}", signal);}

        let chosen_non_passthrough: usize = non_passthrough_nodes[0];
        let non_passthrough_is_parent = nodes[&chosen_non_passthrough].get_output_signals().contains(&signal);

        //find lexicographically most/least node that is passthrough for signal        
        let extremal_passthrough_key = |node_id: &usize|  
            {if non_passthrough_is_parent {nodes[node_id].get_predecessors()} else {nodes[node_id].get_successors()}}.into_iter().filter(|onode_id| is_passthrough_for_signal(&nodes[onode_id], &signal)).count();
        let chosen_extremal_passthrough: usize = passthrough_nodes.into_iter().max_by_key(extremal_passthrough_key).unwrap();

        // do the dfs_can_reach_target_from_sources for those two
        let (parent, child) = if non_passthrough_is_parent {(chosen_non_passthrough, chosen_extremal_passthrough)} else {(chosen_extremal_passthrough, chosen_non_passthrough)};

        // since we have a DAG the only potential path is from parent to child via other nodes -- hence don't need both.

        let to_merge: HashSet<usize> = dfs_merge_in_dag(
            &parent,
            &child,
            adjacency_hashmap,
            None
        );

        to_merge
    }

    let mut left_adjacency : HashMap<usize, &Vec<usize>> = left_nodes.iter().map(|(k, node)| (*k, node.get_successors())).collect();
    let mut right_adjacency : HashMap<usize, &Vec<usize>> = right_nodes.iter().map(|(k, node)| (*k, node.get_successors())).collect();

    for (is_left, signal) in left_passthrough_signals.into_iter().map(|x| (true, x)).chain( right_passthrough_signals.into_iter().map(|x| (false, x)) ) {

        let to_merge = 
            if is_left {get_to_merge(signal, left_nodes, &left_sig_to_coni, &left_coni_to_node, &left_adjacency)} 
            else       {get_to_merge(signal, right_nodes, &right_sig_to_coni, &right_coni_to_node, &right_adjacency)};

        if to_merge.len() == 0 {continue;}
        let to_merge = agree_on_merge(to_merge, !is_left, &left_adjacency, &right_adjacency);

        if to_merge.len() <= 1 {panic!("Merging solo cluster");}
        let root = *to_merge.iter().next().expect("Merging Empty");

        DAGNode::merge_nodes(root, &to_merge, left_nodes, &left_sig_to_coni, &mut left_coni_to_node);
        DAGNode::merge_nodes(root, &to_merge, right_nodes, &right_sig_to_coni, &mut right_coni_to_node);

        left_adjacency = left_nodes.iter().map(|(k, node)| (*k, node.get_successors())).collect();
        right_adjacency = right_nodes.iter().map(|(k, node)| (*k, node.get_successors())).collect();
    }
}

pub(crate) fn dual_merge_until_property<'a, LCon: Constraint, Left: Circuit<LCon>, RCon: Constraint, Right: Circuit<RCon>>(
    left: &'a Left, right: &'a Right, 
    left_nodes: &mut HashMap<usize, DAGNode<'a, LCon, Left>>, right_nodes: &mut HashMap<usize, DAGNode<'a, RCon, Right>>,
    node_meets_property: fn(&DAGNode<'a, LCon, Left>, &DAGNode<'a, RCon, Right>) -> bool,
    get_minimum_merge_for_property: fn(usize, &HashMap<usize, DAGNode<'a, LCon, Left>>,  &HashMap<usize, DAGNode<'a, RCon, Right>>, &HashMap<usize, Vec<usize>>, &Vec<usize>, &HashMap<usize,Vec<usize>>, &Vec<usize>) -> (HashSet<usize>, bool)
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

        let val = stack.pop().unwrap();
        if !left_nodes.contains_key(&val) {continue;}
        if node_meets_property(&left_nodes[&val], &right_nodes[&val]) {continue;}
        // println!("----------------------------------------------");

        // doing it this way actually takes longer but is cleaner code
        let left_adjacency : HashMap<usize, &Vec<usize>> = left_nodes.iter().map(|(k, node)| (*k, node.get_successors())).collect();
        let right_adjacency : HashMap<usize, &Vec<usize>> = right_nodes.iter().map(|(k, node)| (*k, node.get_successors())).collect();

        let (min_merge, left_side) = get_minimum_merge_for_property(val, left_nodes, right_nodes, &left_sig_to_coni, &left_coni_to_node, &right_sig_to_coni, &right_coni_to_node);
        let to_merge = agree_on_merge(min_merge, left_side, &left_adjacency, &right_adjacency);

        if to_merge.len() <= 1 {panic!("Merging solo cluster");}
        let root = *to_merge.iter().next().expect("Merging Empty");

        // println!("merged {:?} into {}", to_merge.clone(), root);
        DAGNode::merge_nodes(root, &to_merge, left_nodes, &left_sig_to_coni, &mut left_coni_to_node);
        DAGNode::merge_nodes(root, &to_merge, right_nodes, &right_sig_to_coni, &mut right_coni_to_node);

        // check root again
        if !node_meets_property(&left_nodes[&root], &right_nodes[&root]) {stack.push(root);}
    }
}