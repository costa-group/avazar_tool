use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use itertools::Itertools;
use std::time::{Instant};

use circuits_constraints_and_algebra::circuit::Circuit;
use circuits_constraints_and_algebra::constraint::Constraint;
use circuit_graphing::directed_acyclic_graph::{DAGNode};
use utils::structure::{TimingInfo, TimingCategories};

use crate::smt_hybrid::{HybridClusteringMethodOptions, TiebreakingStrategy, shared_merge::dual_merge_until_property};

pub(crate) fn guided_clustering<'a, Cons: Constraint, Circ: Circuit<Cons> , Atom: Constraint, Smt: Circuit<Atom>>(
    guide: &'a Circ, recipient: &'a Smt,
    guide_clustering: &mut HashMap<usize, DAGNode<'a, Cons, Circ>>,
    options: HybridClusteringMethodOptions,
    debug: usize
) -> (HashMap<usize, DAGNode<'a, Atom, Smt>>, TimingInfo) {

    let mut timing_info = TimingInfo::new();
    let secondary_clustering_timer = Instant::now();
    // Idea here is that we since we want the SMT clusters to have subsets of the signals then lets just start with the Circuit clustering and get those subsets first
    //    -- I don't know if SMT formuale have any requirements for sub-formulae it feels like its not going to be present

    let mut circ_cluster_signals: HashMap<usize, HashSet<usize>> = guide_clustering.into_iter().map(|(k, v)| (*k, v.signals())).collect();

    if debug > 2 {
        let printable = circ_cluster_signals.clone().into_iter().map(|(key, val)| (key, val.into_iter().sorted().collect::<Vec<_>>())).sorted().collect::<Vec<_>>();
        println!("cluster_to_signal initial: {:?}", printable); 
    }

    let mut signals_to_clusters: HashMap<usize, Vec<usize>> = HashMap::new();
    for (cluster_id, signals) in circ_cluster_signals.iter() {for sig in signals.into_iter().copied() {
        signals_to_clusters.entry(sig).or_insert_with(|| Vec::new()).push(*cluster_id);
    }}

    // For each cluster, get count of how many signals are in common 
    //   if there is a distinct max then put it there
    //   if there is more than one that has the max signals then ... ?
    //     for now pick one arbitrarily TODO: test if that happens often

    let atomi_to_signals: Vec<HashSet<usize>> = (0..recipient.n_constraints()).into_iter().map(|atomi| recipient.get_constraint(atomi).signals()).collect();
    let mut atom_clustered: Vec<bool> = vec![false; recipient.n_constraints()];
    let mut recipient_clusters: HashMap<usize, Vec<usize>> = circ_cluster_signals.keys().copied().map(|k| (k, Vec::new())).collect();
    let empty: Vec<usize> =  Vec::new();

    loop {

        let mut circ_to_max_associated: Vec<Option<(usize, Vec<usize>)>> = vec![None; recipient.n_constraints()];
        
        for atomi in (0..recipient.n_constraints()).into_iter().filter(|atomi| !atom_clustered[*atomi]) {
            let atom_signals = &atomi_to_signals[atomi];
            for cluster_id in atom_signals.iter().copied().flat_map(|sig| signals_to_clusters.get(&sig).unwrap_or_else(|| &empty).iter()).collect::<HashSet<_>>().into_iter().sorted() {
                let num_signals_in_common: usize = circ_cluster_signals[cluster_id].intersection(atom_signals).count();
                if circ_to_max_associated[atomi].as_ref().is_none_or(|inner| inner.0 < num_signals_in_common) {
                    circ_to_max_associated[atomi] = Some((num_signals_in_common, vec![*cluster_id]));
                } else if circ_to_max_associated[atomi].as_ref().is_some_and(|inner| inner.0 == num_signals_in_common) {
                    circ_to_max_associated[atomi].as_mut().unwrap().1.push(*cluster_id);
                }
            }
        }

        let mut any_inserted: bool = false;
        for atomi in 0..recipient.n_constraints() {
            if atom_clustered[atomi] {continue;}
            if circ_to_max_associated[atomi].as_ref().is_some_and(|inner| inner.1.len() == 1 || options.tiebreaking_strategy == TiebreakingStrategy::FirstInList) {
                let chosen_cluster_id = &circ_to_max_associated[atomi].as_ref().unwrap().1[0];
                recipient_clusters.get_mut(chosen_cluster_id).unwrap().push(atomi);
                circ_cluster_signals.get_mut(chosen_cluster_id).unwrap().extend(atomi_to_signals[atomi].iter().copied());
                // Keep the reverse index in step with circ_cluster_signals. It starts from the
                // GUIDE's signals only, so a signal the guide never mentions -- with the
                // specification as the guide, a witness-only wire of the r1cs such as circom's
                // `inv` in `IsZero` -- is absent from it, and stays absent even after the
                // constraint carrying it joins a cluster. Any later constraint whose signals are
                // all of that kind then finds no candidate cluster at all (the `flat_map` over
                // `signals_to_clusters` yields nothing), the round places nothing, and the loop
                // exits leaving those constraints unassigned.
                for sig in atomi_to_signals[atomi].iter().copied() {
                    let holders = signals_to_clusters.entry(sig).or_insert_with(Vec::new);
                    if !holders.contains(chosen_cluster_id) { holders.push(*chosen_cluster_id); }
                }
                any_inserted = true;
                atom_clustered[atomi] = true;
            } 
        }

        if !any_inserted {break;}
    }

    // The clustering has to be a PARTITION of the recipient. The loop above stops as soon as a
    // round places nothing, which leaves every constraint whose signals never meet a cluster
    // unassigned -- and the result is then returned as if it were complete. With the circuit as
    // the recipient that is an r1cs constraint no query ever asserts, so a verification built on
    // this clustering could report success without it: the outputs would be proved from fewer
    // constraints than the circuit actually imposes. Abort instead of returning a partial
    // clustering.
    let unassigned: Vec<usize> = (0..recipient.n_constraints()).filter(|coni| !atom_clustered[*coni]).collect();
    if !unassigned.is_empty() {
        panic!(
            "Guided clustering covered only {} of {} recipient constraints: {:?}{} share no signal with any cluster of the guide, so nothing covers them",
            recipient.n_constraints() - unassigned.len(), recipient.n_constraints(),
            unassigned.iter().take(10).collect::<Vec<_>>(),
            if unassigned.len() > 10 {format!(" (and {} more)", unassigned.len() - 10)} else {String::new()}
        );
    }

    timing_info.insert(TimingCategories::SecondaryClustering, secondary_clustering_timer.elapsed().as_secs_f32());
    *timing_info.entry(TimingCategories::Total).or_default() += timing_info[&TimingCategories::SecondaryClustering];
    if debug > 0 {println!("LOG: Finished secondary clustering in {:?}s", timing_info[&TimingCategories::SecondaryClustering]);}

    if debug > 2 { 
        let printable = guide_clustering.into_iter().map(|(key, part)| (key, part.get_constraint_indices().flat_map(|atomi| guide.get_constraint(atomi).signals().into_iter()).sorted().dedup().collect::<Vec<_>>())).sorted().collect::<Vec<_>>();
        println!("left cluster_to_signals: {:?}", printable);

        let printable = guide_clustering.into_iter().map(|(key, part)| (key, part.get_constraint_indices().sorted().collect::<Vec<_>>())).sorted().collect::<Vec<_>>();
        println!("left cluster_to_coni: {:?}", printable);

        let printable = recipient_clusters.clone().into_iter().map(|(key, part)| (key, part.into_iter().flat_map(|atomi| recipient.get_constraint(atomi).signals().into_iter()).sorted().dedup().collect::<Vec<_>>())).sorted().collect::<Vec<_>>();
        println!("right cluster_to_signals: {:?}", printable);
  
        let printable = recipient_clusters.clone().into_iter().map(|(key, part)| (key, part.into_iter().sorted().collect::<Vec<_>>())).sorted().collect::<Vec<_>>();
        println!("right cluster_to_coni: {:?}", printable);
    }

    // First step is convert this clustering to a DAG
    //  -- it remains to orient the remaining edges which is always possible

    let topological_ordering = DAGNode::<'a, Cons, Circ>::get_topological_ordering(guide_clustering);
    let id_to_order: HashMap<usize, usize> = topological_ordering.into_iter().enumerate().map(|(order, idx)| (idx, order)).collect();

    // recalc these without pollution from previous
    let recipient_cluster_to_signals: HashMap<usize, HashSet<usize>> = recipient_clusters.iter().map(
        |(key, part)| (*key, part.into_iter().copied().flat_map(|coni| recipient.get_constraint(coni).signals().into_iter()).collect())
    ).collect();


    // redo this to eliminate pollution from guide
    let mut signals_to_clusters: HashMap<usize, Vec<usize>> = HashMap::new();
    for (cluster_id, part) in recipient_cluster_to_signals.iter() {for sig in part.into_iter().copied() {signals_to_clusters.entry(sig).or_insert_with(|| Vec::new()).push(*cluster_id);}}

    let mut recipient_clustering: HashMap<usize, _> = recipient_clusters.into_iter().map(
        |(cluster_id, part)| {

            let signals = &recipient_cluster_to_signals[&cluster_id];
            let cluster_order = id_to_order[&cluster_id];
            let predecessors = signals.iter().copied().flat_map(|sig| signals_to_clusters[&sig].iter().copied()).filter(|oid| id_to_order[oid] < cluster_order).collect::<HashSet<_>>().into_iter().sorted().collect::<Vec<_>>();
            let successors = signals.iter().copied().flat_map(|sig| signals_to_clusters[&sig].iter().copied()).filter(|oid| id_to_order[oid] > cluster_order).collect::<HashSet<_>>().into_iter().sorted().collect::<Vec<_>>();

            let predecessor_signals: HashSet<usize> = predecessors.iter().copied().flat_map(|okey| circ_cluster_signals[&okey].iter().copied() ).collect();
            let successor_signals: HashSet<usize> = successors.iter().copied().flat_map(|okey| circ_cluster_signals[&okey].iter().copied() ).collect();
            let input_signals: HashSet<usize> = signals.into_iter().copied().filter(|signal| recipient.signal_is_input(signal) || predecessor_signals.contains(signal) ).collect(); 
            let output_signals: HashSet<usize> = signals.into_iter().copied().filter(|signal| recipient.signal_is_output(signal) || successor_signals.contains(signal) ).collect(); 

            (cluster_id, DAGNode::new(recipient, cluster_id, part, input_signals, output_signals, Some(successors), Some(predecessors)))
    }).collect();

    // Then we need to iteratively look to merge clusters that are not supersets in a manner until we reach a fixed-point which always occurs at least at the complete merge.
    
    let secondary_dag_construction_timer = Instant::now();

    if options.recipient_requires_subsets {
        merge_until_all_left_is_subset_to_right(recipient, guide, &mut recipient_clustering, guide_clustering);
    } else {
        merge_until_all_left_is_subset_to_right(guide, recipient, guide_clustering, &mut recipient_clustering);
    }

    timing_info.insert(TimingCategories::SecondaryDagConstruction, secondary_dag_construction_timer.elapsed().as_secs_f32());
    *timing_info.entry(TimingCategories::Total).or_default() += timing_info[&TimingCategories::SecondaryDagConstruction];
    if debug > 0 {println!("LOG: Finished secondary dag construction in {:?}s", timing_info[&TimingCategories::SecondaryDagConstruction]);}
    
    (recipient_clustering, timing_info)
}

fn merge_until_all_left_is_subset_to_right<'a, LCon: Constraint, Left: Circuit<LCon> , RCon: Constraint, Right: Circuit<RCon>>(left: &'a Left, right: &'a Right, core_nodes: &mut HashMap<usize, DAGNode<'a, LCon, Left>>, superset_nodes: &mut HashMap<usize, DAGNode<'a, RCon, Right>>) -> () {

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