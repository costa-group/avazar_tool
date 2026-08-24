use std::collections::{HashMap, HashSet, BTreeMap, VecDeque};
use itertools::Itertools;

use circuits_constraints_and_algebra::circuit::Circuit;
use circuits_constraints_and_algebra::constraint::Constraint;
use circuit_graphing::directed_acyclic_graph::{DAGNode};

use crate::smt_hybrid::shared_merge::dual_merge_until_property;

pub(crate) fn merge_until_all_left_is_subset_to_right<'a, LCon: Constraint, Left: Circuit<LCon> , RCon: Constraint, Right: Circuit<RCon>>(left: &'a Left, right: &'a Right, core_nodes: &mut HashMap<usize, DAGNode<'a, LCon, Left>>, superset_nodes: &mut HashMap<usize, DAGNode<'a, RCon, Right>>) -> () {

    //
    /// The signals of `left` that could ever be matched on the right at all,
    /// i.e. that the right-hand circuit mentions SOMEWHERE.
    ///
    /// The subset property can only ever be about these. In a real pairing the
    /// two sides do not name the same set of signals: an r1cs has witness-only
    /// wires the specification never mentions (circom's `inv` in `IsZero` is
    /// one: the specification computes with an internal temporary and only
    /// constrains `out`), and a specification has internal temporaries that
    /// correspond to no wire. Demanding that a cluster cover a signal the
    /// other side never mentions is not a property that can be reached by
    /// merging — there is no cluster over there that holds it — so it would
    /// merge everything into one node and then panic.
    fn matchable_signals<'a, LCon: Constraint, Left: Circuit<LCon>, RCon: Constraint, Right: Circuit<RCon>>(
        left: &DAGNode<'a, LCon, Left>, right: &DAGNode<'a, RCon, Right>
    ) -> HashSet<usize> {
        let right_circuit_signals: HashSet<usize> = right.get_circ().get_signals().collect();
        left.signals().into_iter().filter(|sig| right_circuit_signals.contains(sig)).collect()
    }

    fn is_left_signals_nonempty_and_a_subset_of_right_signals<'a, LCon: Constraint, Left: Circuit<LCon> , RCon: Constraint, Right: Circuit<RCon>>(left: &DAGNode<'a, LCon, Left>, right: &DAGNode<'a, RCon, Right>) -> bool {
        let left_signals = matchable_signals(left, right);
        // Nothing to match: the property holds vacuously and merging would not
        // change that. This is NOT the same as the old "cluster with no signals
        // at all, merge it away" case — a cluster can be full of signals and
        // still share none with the other side (constant folding on witness
        // wires the specification never mentions). Forcing a merge there ends
        // up demanding a neighbour that may not exist.
        //
        // A caller must treat such a cluster as "nothing to verify", not as
        // verified: its interface with the other side is empty, so any query
        // built from it is vacuous.
        if left_signals.len() == 0 {return true;}
        let right_signals = right.signals();
        left_signals.is_subset(&right_signals)
    }

    fn select_right_nodes_that_meet_superset_of_left<'a, LCon: Constraint, Left: Circuit<LCon> , RCon: Constraint, Right: Circuit<RCon>>(
        root: usize, left_nodes: &HashMap<usize, DAGNode<'a, LCon, Left>>, right_nodes: &HashMap<usize, DAGNode<'a, RCon, Right>>,
        _left_signal_to_coni: &HashMap<usize, Vec<usize>>, _left_coni_to_node: &Vec<usize>, right_signal_to_coni: &HashMap<usize, Vec<usize>>, right_coni_to_node: &Vec<usize>
    ) -> (HashSet<usize>, bool) {

        // need to choose clusters on right that will get all remaining signals not in left
        let (left, right) = (&left_nodes[&root], &right_nodes[&root]);
        // Only the signals the right-hand side can match: see `matchable_signals`.
        let left_signals = matchable_signals(left, right);
        if left_signals.len() == 0 {
            // left is empty -- merge with arbitrary right adjacent
            let chosen = *right.get_predecessors().into_iter().chain(right.get_successors().into_iter()).min().expect("Empty cluster on left has no adjacent on right");
            return ([root, chosen].into_iter().collect(), false);
        }
        let right_signals = right.signals();
        let remaining_signals = left_signals.difference(&right_signals);

        let mut to_merge: HashSet<usize> = [root].into_iter().collect();

        // for each remaining signal get list of right_clusters that contain that signal
        let signal_to_clusterid: BTreeMap<usize, HashSet<usize>> = remaining_signals.map(|sig| (*sig, right_signal_to_coni[sig].iter().copied().map(|coni| right_coni_to_node[coni]).filter(|id| *id != root).collect()) ).collect();
        for (sig, prospective) in signal_to_clusterid.into_iter() {
            // println!("root_id {:?}, signal {:?}, prospective node_ids with signal {:?}", root, sig, prospective.clone());
            if prospective.len() == 0 {panic!("No potential clusters for missing signal {sig}");}
            if prospective.iter().any(|id| to_merge.contains(id)) {continue;}

            // do BFS until we find a prospective
            let mut visited: HashSet<usize> = HashSet::new();
            visited.insert(root);
            let mut queue = VecDeque::from([root]);
            let mut chosen: Option<usize> = None;
            while queue.len() > 0 {
                let curr = queue.pop_front().unwrap();
                if prospective.contains(&curr) {chosen = Some(curr); break;}
                for adj in right_nodes[&curr].get_successors().into_iter().chain( right_nodes[&curr].get_predecessors().into_iter()) {
                    if !visited.contains(adj) {visited.insert(*adj); queue.push_back(*adj);}
                }
            }
            // println!("BFS visited {:?}", visited);
            // `expect` takes a plain &str and never formats, so the braces used to reach the
            // log verbatim -- exactly the two values needed to diagnose this.
            // The BFS is a preference, not a requirement: it merges along a path so the
            // result stays compact in the DAG. What correctness needs is only that the
            // merged cluster ends up holding `sig`, and `prospective` already lists every
            // cluster that does. When root sits in a component of the right DAG that
            // reaches none of them -- which happens: an isolated cluster has neither
            // predecessors nor successors to walk -- merge with a holder directly rather
            // than giving up on the whole circuit.
            let chosen = chosen.unwrap_or_else(|| {
                let fallback = *prospective.iter().min().expect("prospective is non-empty here");
                println!(
                    "WARNING: cluster {root} needs signal {sig}, but no path in the \
                     specification DAG leads from it to any of the {} cluster(s) holding it \
                     ({:?}); the BFS only reached {} node(s). Merging with {fallback} directly.",
                    prospective.len(), prospective.iter().sorted().collect::<Vec<_>>(),
                    visited.len()
                );
                fallback
            });
            to_merge.insert(chosen);
        }

        (to_merge, false)
    }


    dual_merge_until_property(left, right, core_nodes, superset_nodes, is_left_signals_nonempty_and_a_subset_of_right_signals, select_right_nodes_that_meet_superset_of_left)

}

pub(crate) fn merge_until_all_inputs_outputs_same<'a, LCon: Constraint, Left: Circuit<LCon> , RCon: Constraint, Right: Circuit<RCon>>(left: &'a Left, right: &'a Right, left_nodes: &mut HashMap<usize, DAGNode<'a, LCon, Left>>, right_nodes: &mut HashMap<usize, DAGNode<'a, RCon, Right>>) -> () {

    /// If two input (symmetrically output) sets are different then we can either try add missing inputs or remove extranous inputs from either side only by Merging.
    /// When attempting to add inputs there are various options that can be chosen. Perhaps a good heuristic exists but it seems nebulous at best given that the actual merge is larger, etc.
    /// However, when removing an input there the merge required is forced - we must merge all parents (and hence all ancestors) that contain that signal. This may be overeager but it at least is the best (only) version of its algorithm and we can evaluate it based on practical utility
    /// It shall be discussed whether it is important for them to be exactly the same or not, I shall for now assume that they must be exactly the same

    fn is_left_io_same_as_right_io<'a, LCon: Constraint, Left: Circuit<LCon> , RCon: Constraint, Right: Circuit<RCon>>(left: &DAGNode<'a, LCon, Left>, right: &DAGNode<'a, RCon, Right>) -> bool {
        left.get_input_signals() == right.get_input_signals() && left.get_output_signals() == right.get_output_signals()
    }

    fn select_nodes_to_merge_to_delete_excess_io<'a, LCon: Constraint, Left: Circuit<LCon> , RCon: Constraint, Right: Circuit<RCon>>(
        root: usize, left_nodes: &HashMap<usize, DAGNode<'a, LCon, Left>>, right_nodes: &HashMap<usize, DAGNode<'a, RCon, Right>>,
        _left_signal_to_coni: &HashMap<usize, Vec<usize>>, _left_coni_to_node: &Vec<usize>, _right_signal_to_coni: &HashMap<usize, Vec<usize>>, _right_coni_to_node: &Vec<usize>
    ) -> (HashSet<usize>, bool) {
        
        let (left, right) = (&left_nodes[&root], &right_nodes[&root]);
        
        let mut to_merge: HashSet<usize> = HashSet::new();
        fn select_nodes_from_list_that_contain_any_of_signals<'a, C: Constraint, S: Circuit<C>>(nodes: &HashMap<usize, DAGNode<'a, C, S>>, nodi_list: &Vec<usize>, target_signals: &HashSet<usize>, check_output: bool) -> impl Iterator<Item = usize> {
            nodi_list.into_iter().copied().filter(move |nodi| {
                let target_set = if check_output {nodes[nodi].get_output_signals()} else {nodes[nodi].get_input_signals()};
                target_signals.into_iter().any(|sig| target_set.contains(sig))
            })
        }

        let left_excess_inputs = left.get_input_signals().difference(right.get_input_signals()); let right_excess_inputs = right.get_input_signals().difference(left.get_input_signals());
        let left_excess_outputs = left.get_output_signals().difference(right.get_output_signals()); let right_excess_outputs = right.get_output_signals().difference(left.get_output_signals());
        to_merge.extend(select_nodes_from_list_that_contain_any_of_signals(left_nodes, left.get_predecessors(), &left_excess_inputs.copied().collect(), true));
        to_merge.extend(select_nodes_from_list_that_contain_any_of_signals(right_nodes, right.get_predecessors(), &right_excess_inputs.copied().collect(), true));
        to_merge.extend(select_nodes_from_list_that_contain_any_of_signals(left_nodes, left.get_successors(), &left_excess_outputs.copied().collect(), false));
        to_merge.extend(select_nodes_from_list_that_contain_any_of_signals(right_nodes, right.get_successors(), &right_excess_outputs.copied().collect(), false));

        (to_merge, true)
    }

    dual_merge_until_property(left, right, left_nodes, right_nodes, is_left_io_same_as_right_io, select_nodes_to_merge_to_delete_excess_io)

}