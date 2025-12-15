use std::collections::{HashMap, HashSet, VecDeque};

use super::DAGNode;
use circuits_and_constraints::constraint::Constraint;
use circuits_and_constraints::circuit::Circuit;
use circuits_and_constraints::utils::signals_to_constraints_with_them;
use utils::small_utilities::{dfs_can_reach_target_from_sources};

fn merge_under_property<'a, C: Constraint + 'a, S: Circuit<C> + 'a>(
    circ: &'a S, nodes: &mut HashMap<usize, DAGNode<'a, C, S>>, 
    node_property: fn(&DAGNode<'a, C, S>) -> usize,
    arc_property: fn(&DAGNode<'a, C, S>, &DAGNode<'a, C, S>, bool) -> usize
) -> () {

    let sig_to_coni = signals_to_constraints_with_them(circ.get_constraints(), None, None);
    let mut coni_to_node: Vec<usize> = vec![0; circ.n_constraints()];

    for (coni, node_id) in nodes.values().flat_map(|node| node.constraints.iter().map(|coni| (coni, node.id))) { coni_to_node[*coni] = node_id };

    let mut merge_queue: VecDeque<usize> = nodes.keys().filter(|key| node_property(nodes.get(key).unwrap()) > 0).copied().collect();
    let extra_key: usize = *nodes.keys().max().unwrap() + 1;
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
        let adjacency_hashmap : HashMap<usize, &Vec<usize>> = nodes.iter().map(|(k, node)| (*k, node.get_successors())).collect();
        let required_to_merge: Vec<(usize, Vec<usize>)> = potential_adjacent.into_iter().map(|(idx, &okey)| {
            let extra_key_adjacencies: &Vec<usize> = &nnode.get_successors().iter().copied().chain(nodes.get(&okey).unwrap().get_successors().iter().copied()).collect();
            (
                idx, 
                dfs_can_reach_target_from_sources(
                    &extra_key_adjacencies,
                    &vec![nkey, okey],
                    &adjacency_hashmap
                ).into_iter().filter(|&k| k != extra_key).chain([nkey, okey].into_iter()).collect()
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
    circ: &'a S, nodes: &mut HashMap<usize, DAGNode<'a, C, S>>, 
) -> () {
    fn num_passthrough_signals<'a, C: Constraint + 'a, S: Circuit<C> + 'a>(node: &DAGNode<'a, C, S>) -> usize {
        node.get_input_signals().intersection(node.get_output_signals()).count() // naive version
    }
    fn num_passthrough_signals_capture_by_arc<'a, C: Constraint + 'a, S: Circuit<C> + 'a>(parent: &DAGNode<'a, C, S>, child: &DAGNode<'a, C, S>, is_parent: bool) -> usize {
        let passthrough_node = if is_parent {parent} else {child};
        let passthrough_signals: HashSet<&usize> = passthrough_node.get_input_signals().intersection(passthrough_node.get_output_signals()).collect();
        let capturing_signals: HashSet<&usize> = (if is_parent { child.get_input_signals().difference(child.get_output_signals()) } else {parent.get_output_signals().difference(parent.get_input_signals())}).collect();
        passthrough_signals.intersection(&capturing_signals).count()
    }

    merge_under_property(circ, nodes, num_passthrough_signals, num_passthrough_signals_capture_by_arc)
}