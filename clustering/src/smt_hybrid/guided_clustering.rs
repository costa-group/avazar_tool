use std::collections::{HashMap, HashSet};
use itertools::Itertools;
use std::time::{Instant};

use circuits_constraints_and_algebra::circuit::Circuit;
use circuits_constraints_and_algebra::constraint::Constraint;
use circuit_graphing::directed_acyclic_graph::{DAGNode};
use utils::structure::{TimingInfo, TimingCategories};

use crate::smt_hybrid::{HybridClusteringMethodOptions, TiebreakingStrategy, shared_merge::merge_passthrough_shared, shared_merge_applications::{merge_until_all_inputs_outputs_same, merge_until_all_left_is_subset_to_right}};

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

    // Check if any clusters on the recipient side are empty, this is considered a break of an assumed property
    // Otherwise this requires uncommenting out the preprocessing step `merge_until_all_clusters_nonempty'
    for (cluster_id, cluster) in recipient_clusters.iter() {if cluster.len() == 0 {
            let guide_cluster = guide_clustering[cluster_id].get_constraint_indices().collect::<Vec<usize>>();
            panic!("Recipient cluster {cluster_id} is empty; Corresponding guide cluster has atoms {guide_cluster:?}");
    }}

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

    // NOTE: uncomment the following two lines if we want to manually remove empty clusters
    // use shared_merge_applications::merge_until_all_clusters_nonempty;
    // merge_until_all_clusters_nonempty(guide, recipient, guide_clustering, &mut recipient_clustering);
    
    merge_passthrough_shared(guide, recipient, guide_clustering, &mut recipient_clustering);
    if options.recipient_requires_subsets {
        merge_until_all_left_is_subset_to_right(recipient, guide, &mut recipient_clustering, guide_clustering);
    } else {
        merge_until_all_left_is_subset_to_right(guide, recipient, guide_clustering, &mut recipient_clustering);
    }
    if options.merge_until_io_same {
        merge_until_all_inputs_outputs_same(guide, recipient, guide_clustering, &mut recipient_clustering);
    }

    timing_info.insert(TimingCategories::SecondaryDagConstruction, secondary_dag_construction_timer.elapsed().as_secs_f32());
    *timing_info.entry(TimingCategories::Total).or_default() += timing_info[&TimingCategories::SecondaryDagConstruction];
    if debug > 0 {println!("LOG: Finished secondary dag construction in {:?}s", timing_info[&TimingCategories::SecondaryDagConstruction]);}
    
    (recipient_clustering, timing_info)
}

