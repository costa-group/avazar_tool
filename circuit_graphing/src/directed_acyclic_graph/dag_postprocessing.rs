use std::collections::{BTreeMap, HashSet, VecDeque};

use super::DAGNode;
use circuits_and_constraints::constraint::Constraint;
use circuits_and_constraints::circuit::Circuit;
use circuits_and_constraints::utils::signals_to_constraints_with_them;
use utils::small_utilities::{dfs_merge_in_dag};

#[allow(dead_code)]
// merge_under_property is unused as merge_passthrough moved to not use it but retained in case of future
fn merge_under_property<'a, C: Constraint + 'a, S: Circuit<C> + 'a>(
    circ: &'a S, nodes: &mut BTreeMap<usize, DAGNode<'a, C, S>>, 
    node_property: fn(&DAGNode<'a, C, S>) -> usize,
    arc_property: fn(&DAGNode<'a, C, S>, &DAGNode<'a, C, S>, bool) -> usize
) -> () {

    let sig_to_coni = signals_to_constraints_with_them(circ.get_constraints(), None, None);
    let mut coni_to_node: Vec<usize> = vec![0; circ.n_constraints()];

    for (coni, node_id) in nodes.values().flat_map(|node| node.constraints.iter().map(|coni| (coni, node.id))) { coni_to_node[*coni] = node_id };

    let mut merge_queue: VecDeque<usize> = nodes.keys().filter(|key| node_property(nodes.get(key).unwrap()) > 0).copied().collect();
    let mut first_unmerged: Option<usize> = None;

    while merge_queue.len() > 0 {

        let nkey: usize = merge_queue.pop_front().unwrap();

        if first_unmerged.is_some_and(|okey| okey == nkey) {
            panic!("unable to completely merge property");};
        if !nodes.contains_key(&nkey) {continue};

        let nnode: &DAGNode<'a, C, S> = nodes.get(&nkey).unwrap();
        if node_property(nnode) == 0 {continue;};

        // for each adjacent get the property value for the arc relationship
        let index_to_nkeys: Vec<&usize> = nnode.get_successors().iter().chain(nnode.get_predecessors()).collect();
        let adjacent_to_property: Vec<usize> = nnode.get_successors().iter().map(|child| arc_property(nnode, nodes.get(child).unwrap(), true)).chain(
                                               nnode.get_predecessors().iter().map(|parent| arc_property(nodes.get(parent).unwrap(), nnode, false))).collect();

        // filter to only those with good properties
        let potential_adjacent: Vec<(usize, &usize)> = index_to_nkeys.into_iter().enumerate().filter(|(i, _)| adjacent_to_property[*i] > 0).collect();

        // handle no good merges edge case
        if potential_adjacent.len() == 0 {
            first_unmerged.get_or_insert(nkey);
            merge_queue.push_back(nkey);
            continue;
        } else {
            first_unmerged = None;
        }

        // find, for each option, the nodes that will need to be merged
        let adjacency_hashmap : BTreeMap<usize, &Vec<usize>> = nodes.iter().map(|(k, node)| (*k, node.get_successors())).collect();
        let required_to_merge: Vec<(usize, Vec<usize>)> = potential_adjacent.into_iter().map(|(idx, &okey)| {
            let (parent, child) = if nnode.get_successors().contains(&okey) {(nkey, okey)} else {(okey, nkey)};
            (
                idx, 
                dfs_merge_in_dag(
                    &parent,
                    &child,
                    &adjacency_hashmap,
                    None
                )
            )
        }).collect();

        // greedily merge the fewest vertices, tiebreaking on potential property
        // TODO: movie copied calls to here?
        let choice_to_merge: Vec<usize> = required_to_merge.into_iter().max_by_key(|(idx, req_to_merge)| (req_to_merge.len(), adjacent_to_property[*idx])).unwrap().1;

        let root: usize =  DAGNode::merge_nodes(choice_to_merge, nodes, &sig_to_coni, &mut coni_to_node);

        // if it still has property add back to queue
        if node_property(nodes.get(&root).unwrap()) > 0 && !merge_queue.contains(&root) {merge_queue.push_back(root)};
    }
}

pub fn merge_passthrough<'a, C: Constraint + 'a, S: Circuit<C> + 'a>(
    circ: &'a S, nodes: &mut BTreeMap<usize, DAGNode<'a, C, S>>, 
) -> () {

    // Merge passthrough now no longer uses merge_under_property to better take advantage of how signals work
    fn get_passthrough_signals<'a, C: Constraint + 'a, S: Circuit<C> + 'a>(node: &DAGNode<'a, C, S>) -> impl Iterator<Item = usize> {
        node.get_input_signals().intersection(node.get_output_signals()).copied()
    }

    fn is_passthrough_for_signal<'a, C: Constraint + 'a, S: Circuit<C> + 'a>(node: &DAGNode<'a, C, S>, signal: &usize) -> bool {
        node.get_input_signals().contains(signal) && node.get_output_signals().contains(signal)
    }

    let sig_to_coni = signals_to_constraints_with_them(circ.get_constraints(), None, None);
    let mut coni_to_node: Vec<usize> = vec![0; circ.n_constraints()];
    for (coni, node_id) in nodes.values().flat_map(|node| node.constraints.iter().map(|coni| (coni, node.id))) { coni_to_node[*coni] = node_id };
    
    let passthrough_signals: HashSet<usize> = nodes.values().flat_map(|node| get_passthrough_signals(node)).collect();

    for signal in passthrough_signals.into_iter() {

        // find nodes that contain signal as input but not as output
        let mut non_passthrough_nodes: Vec<usize> = Vec::new();
        let mut passthrough_nodes: Vec<usize> = Vec::new();
        for nodeid in sig_to_coni[&signal].iter().map(|coni| coni_to_node[*coni]).collect::<HashSet<usize>>().into_iter() {
            if is_passthrough_for_signal(&nodes[&nodeid], &signal) {passthrough_nodes.push(nodeid);} else {non_passthrough_nodes.push(nodeid);}
        }
        if passthrough_nodes.len() == 0 {continue;}
        if non_passthrough_nodes.len() == 0 {panic!("There does not exist a non-passthrough node for signal {:?}", signal);}

        let chosen_non_passthrough: usize = non_passthrough_nodes[0];
        let non_passthrough_is_parent = nodes[&chosen_non_passthrough].get_output_signals().contains(&signal);

        //find lexicographically most/least node that is passthrough for signal        
        let extremal_passthrough_key = |node_id: &usize|  
            {if non_passthrough_is_parent {nodes[node_id].get_predecessors()} else {nodes[node_id].get_successors()}}.into_iter().filter(|onode_id| is_passthrough_for_signal(&nodes[onode_id], &signal)).count();
        let chosen_extremal_passthrough: usize = passthrough_nodes.into_iter().max_by_key(extremal_passthrough_key).unwrap();

        // do the dfs_can_reach_target_from_sources for those two
        let adjacency_hashmap : BTreeMap<usize, &Vec<usize>> = nodes.iter().map(|(k, node)| (*k, node.get_successors())).collect();
        let (parent, child) = if non_passthrough_is_parent {(chosen_non_passthrough, chosen_extremal_passthrough)} else {(chosen_extremal_passthrough, chosen_non_passthrough)};

        // since we have a DAG the only potential path is from parent to child via other nodes -- hence don't need both.

        let to_merge: Vec<usize> = dfs_merge_in_dag(
            &parent,
            &child,
            &adjacency_hashmap,
            None
        );

        // merge nodes
        DAGNode::merge_nodes(to_merge, nodes, &sig_to_coni, &mut coni_to_node);
    }
}