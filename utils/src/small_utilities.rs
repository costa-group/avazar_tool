use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::Hash;
use std::cmp::Ord;
use itertools::Itertools;

use clap::{ValueEnum};
use strum_macros::{Display};

#[derive(Debug, Display, Copy, Clone, ValueEnum)]
pub enum GraphBackend {
    #[strum(serialize = "graphrs")]
    GraphRS,
    #[strum(serialize = "singleclustering")]
    SingleClustering,
    #[strum(serialize = "xgraph")]
    XGraph
}

#[derive(Debug, Display, Copy, Clone, ValueEnum)]
pub enum EquivalenceMode {
    #[strum(serialize = "total")]
    Total,
    #[strum(serialize = "structural")]
    Structural,
    #[strum(serialize = "local")]
    Local,
    #[strum(serialize = "none")]
    None
}

#[derive(Debug, Display, Copy, Clone, ValueEnum)]
pub enum ClusteringPreprocessing {
    #[strum(serialize = "none")]
    None,
    #[strum(serialize = "bridgefinding")]
    BridgeFinding,
}

#[derive(Debug, Display, Copy, Clone, ValueEnum)]
pub enum FileType {
    #[strum(serialize = "r1cs")]
    R1CS,
    #[strum(serialize = "acir")]
    ACIR
}

pub fn distance_to_source_set<'a, T: Hash + Ord + Copy>(source_set: impl Iterator<Item = &'a T>, adjacencies: &'a HashMap<T, HashSet<T>>) -> HashMap<&'a T, usize> {

    let mut distance: HashMap<&T, usize> = source_set.map(|idx| (idx, 0)).collect();
    let mut queue: VecDeque<&T> = distance.keys().copied().collect();

    while queue.len() > 0 {
        let curr = queue.pop_front().unwrap();
        let next_distance = distance[curr] + 1;
        for adj in adjacencies.get(curr).unwrap().into_iter() {
            if let std::collections::hash_map::Entry::Vacant(entry) = distance.entry(adj) {
                queue.push_back(adj);
                entry.insert(next_distance);
            }
        }
    }

    distance
}

pub fn dfs_merge_in_dag_with_bfs_preprocessing(parent: &usize, child: &usize, adjacencies: &HashMap<usize, &Vec<usize>>, preprocessing_steps: usize) -> HashSet<usize> {
    let mut can_reach_t: HashMap<&usize, bool> = HashMap::from([(child, true)]);
    let mut current_iteration: HashSet<&usize> = HashSet::from([child]);

    for _ in 0..preprocessing_steps {
        current_iteration = current_iteration.into_iter().flat_map(|vertex| adjacencies[vertex].into_iter()).filter(|vertex| !can_reach_t.contains_key(vertex)).collect();
        can_reach_t.extend(current_iteration.iter().copied().map(|vertex| (vertex, false)));
    }

    dfs_merge_in_dag(parent, child, adjacencies, Some(can_reach_t))
}

pub fn dfs_merge_in_dag(parent: &usize, child: &usize, adjacencies: &HashMap<usize, &Vec<usize>>, can_reach_t: Option<HashMap<&usize, bool>>) -> HashSet<usize> {

    let mut can_reach_t: HashMap<&usize, bool> = can_reach_t.unwrap_or(HashMap::from([(child, true)]));
    let mut stack: Vec<&usize> = vec![parent];

    while stack.len() > 0 {

        let curr: &usize = stack.last().unwrap();
        if can_reach_t.contains_key(curr) {
            stack.pop();
            continue;
        };

        stack.extend(adjacencies[curr].into_iter().filter(|adj| can_reach_t.get(*adj).is_none()));

        if adjacencies[curr].into_iter().any(|adj| can_reach_t.get(adj).copied().unwrap_or(false) ) {
            can_reach_t.entry(curr).or_insert(true);
        } else if adjacencies[curr].into_iter().all(|adj| !can_reach_t.get(adj).copied().unwrap_or(true) ) {
            can_reach_t.entry(curr).or_insert(false);
        }

    }

    can_reach_t.into_iter().filter(|(_, val)| *val).map(|(k, _)| k).copied().collect()
}

pub fn count_ints<T: Hash + Eq + Ord>(source: impl IntoIterator<Item = T>) -> Vec<(T, usize)> {
    let mut counter: HashMap<T, usize> = HashMap::new();
    for num in source.into_iter() {
        *counter.entry(num).or_insert(0) += 1
    }
    counter.into_iter().sorted().collect()
}