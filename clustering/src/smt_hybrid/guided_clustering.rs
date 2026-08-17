use std::collections::{HashMap, HashSet, VecDeque};
use clap::ValueEnum;
use itertools::Itertools;
use std::time::{Instant};

use circuits_constraints_and_algebra::circuit::Circuit;
use circuits_constraints_and_algebra::constraint::Constraint;
use circuit_graphing::directed_acyclic_graph::{mixed_graph::MixedGraph, DAGNode};
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

    let printable = circ_cluster_signals.clone().into_iter().map(|(key, val)| (key, val.into_iter().sorted().collect::<Vec<_>>())).sorted().collect::<Vec<_>>();
    if debug > 2 { println!("cluster_to_signal initial: {:?}", printable); }

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
        
        for (atomi, atom) in recipient.constraints().into_iter().enumerate().filter(|(atomi, atom)| !atom_clustered[*atomi]) {
            let atom_signals = &atomi_to_signals[atomi];
            for cluster_id in atom_signals.iter().copied().flat_map(|sig| signals_to_clusters.get(&sig).unwrap_or_else(|| &empty).iter()).collect::<HashSet<_>>().into_iter() {
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
                any_inserted = true;
                atom_clustered[atomi] = true;
            } 
        }

        if !any_inserted {break;}
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
    let mut recipient_cluster_to_signals: HashMap<usize, HashSet<usize>> = recipient_clusters.iter().map(
        |(key, part)| (*key, part.into_iter().copied().flat_map(|coni| recipient.get_constraint(coni).signals().into_iter()).collect())
    ).collect();


    // redo this to eliminate pollution from guide
    let mut signals_to_clusters: HashMap<usize, Vec<usize>> = HashMap::new();
    for (cluster_id, part) in recipient_clusters.iter() {for sig in recipient_cluster_to_signals[cluster_id].iter().copied() {signals_to_clusters.entry(sig).or_insert_with(|| Vec::new()).push(*cluster_id);}}

    let mut recipient_clustering: HashMap<usize, _> = recipient_clusters.into_iter().map(
        |(cluster_id, part)| {

            let signals = &recipient_cluster_to_signals[&cluster_id];
            let cluster_order = id_to_order[&cluster_id];
            let predecessors = signals.iter().copied().flat_map(|sig| signals_to_clusters[&sig].iter().copied()).filter(|oid| id_to_order[oid] < cluster_order).collect::<HashSet<_>>().into_iter().collect::<Vec<_>>();
            let successors = signals.iter().copied().flat_map(|sig| signals_to_clusters[&sig].iter().copied()).filter(|oid| id_to_order[oid] > cluster_order).collect::<HashSet<_>>().into_iter().collect::<Vec<_>>();

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
    fn is_left_signals_nonempty_and_a_subset_of_right_signals<'a, LCon: Constraint, Left: Circuit<LCon> , RCon: Constraint, Right: Circuit<RCon>>(left: &DAGNode<'a, LCon, Left>, right: &DAGNode<'a, RCon, Right>) -> bool {
        let left_signals = left.signals();
        if left_signals.len() == 0 {return false;}
        let right_signals = right.signals();
        left_signals.is_subset(&right_signals)
    }

    fn select_right_nodes_that_meet_superset_of_left<'a, LCon: Constraint, Left: Circuit<LCon> , RCon: Constraint, Right: Circuit<RCon>>(
        root: usize, left_nodes: &HashMap<usize, DAGNode<'a, LCon, Left>>, right_nodes: &HashMap<usize, DAGNode<'a, RCon, Right>>,
        left_signal_to_coni: &HashMap<usize, Vec<usize>>, left_coni_to_node: &Vec<usize>, right_signal_to_coni: &HashMap<usize, Vec<usize>>, right_coni_to_node: &Vec<usize>
    ) -> (HashSet<usize>, bool) {

        // need to choose clusters on right that will get all remaining signals not in left
        let (left, right) = (&left_nodes[&root], &right_nodes[&root]);
        let left_signals = left.signals();
        if left_signals.len() == 0 {
            // left is empty -- merge with arbitrary right adjacent
            let chosen = *right.get_predecessors().into_iter().chain(right.get_successors().into_iter()).next().expect("Empty cluster on left has no adjent on right");
            return ([root, chosen].into_iter().collect(), false);
        }
        let right_signals = right.signals();
        let remaining_signals = left_signals.difference(&right_signals);

        let mut to_merge: HashSet<usize> = [root].into_iter().collect();

        // for each remaining signal get list of right_clusters that contain that signal
        let mut signal_to_clusterid: HashMap<usize, HashSet<usize>> = remaining_signals.map(|sig| (*sig, right_signal_to_coni[sig].iter().copied().map(|coni| right_coni_to_node[coni]).filter(|id| *id != root).collect()) ).collect();
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
            to_merge.insert(chosen.expect("Signal {sig} has no prospective nodes connected to {root} on right"));
        }

        (to_merge, false)
    }


    dual_merge_until_property(left, right, core_nodes, superset_nodes, is_left_signals_nonempty_and_a_subset_of_right_signals, select_right_nodes_that_meet_superset_of_left)

}