use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::Hash;
use std::cmp::Ord;
use std::path::PathBuf;
use itertools::Itertools;

use clap::{ValueEnum};
use strum_macros::{Display};

#[derive(Debug, Default, Display, Copy, Clone, ValueEnum, PartialEq)]
pub enum GraphBackend {
    #[strum(serialize = "graphrs")]
    #[default]
    GraphRS,
    #[strum(serialize = "singleclustering")]
    SingleClustering,
    #[strum(serialize = "xgraph")]
    XGraph
}

#[derive(Debug, Default, Display, Copy, Clone, ValueEnum, PartialEq)]
pub enum EquivalenceMode {
    #[strum(serialize = "total")]
    Total,
    #[strum(serialize = "structural")]
    Structural,
    #[strum(serialize = "local")]
    Local,
    #[strum(serialize = "none")]
    #[default]
    None
}

#[derive(Debug, Default, Display, Copy, Clone, ValueEnum, PartialEq)]
pub enum ClusteringPreprocessing {
    #[strum(serialize = "none")]
    #[default]
    None,
    #[strum(serialize = "bridgefinding")]
    BridgeFinding,
}

#[derive(Debug, Default, Display, Copy, Clone, ValueEnum, PartialEq)]
pub enum HierarchyMode {
    #[strum(serialize = "conservative")]
    #[default]
    Conservative,
    #[strum(serialize = "optimisation")]
    Optimisation,
    #[strum(serialize = "extension")]
    Extension,
}

#[derive(Debug, Default, Display, Copy, Clone, ValueEnum, PartialEq)]
pub enum FileType {
    #[strum(serialize = "r1cs")]
    #[default]
    R1CS,
    #[strum(serialize = "acir")]
    ACIR,
    #[strum(serialize = "generic")]
    Generic
}

#[derive(Debug, Clone, Default)]
pub struct DecomposeOptions<'a> {
    pub resolution: Option<f64>,
    pub target_size: Option<f64>,
    pub leiden_max_iterations: Option<usize>,
    pub equivalence_mode: EquivalenceMode,
    pub graph_backend: GraphBackend,
    pub preprocessing: ClusteringPreprocessing,
    pub hierarchy_mode: HierarchyMode,
    pub inverse_coni_mapping: Option<&'a [usize]>,
    pub inverse_sig_mapping: Option<&'a [usize]>,
    pub minimum_equivalence_size: Option<usize>,
    pub equivalence_comparison_budget: Option<usize>,
    pub existing_partition: Option<Vec<Vec<usize>>>,
    pub extract_raw_partition: Option<PathBuf>,
    pub clique_cluster_size: Option<usize>,
    pub dead_ends_as_outputs: bool,
    pub manually_check_acyclic: bool,
    pub seed: Option<u64>,
    pub debug: usize
}

impl<'a> DecomposeOptions<'a> {
    pub fn into_copy_decompose_options(&self) -> CopyableDecomposeOptions {
        CopyableDecomposeOptions {
            resolution: self.resolution,
            target_size: self.target_size,
            leiden_max_iterations: self.leiden_max_iterations,
            graph_backend: self.graph_backend,
            preprocessing: self.preprocessing,
            hierarchy_mode: self.hierarchy_mode,
            clique_cluster_size: self.clique_cluster_size,
            dead_ends_as_outputs: self.dead_ends_as_outputs,
            manually_check_acyclic: self.manually_check_acyclic,
            seed: self.seed,
            debug: self.debug
    }}
}

#[derive(Debug, Clone, Copy, Default)]
pub struct CopyableDecomposeOptions {
    pub resolution: Option<f64>,
    pub target_size: Option<f64>,
    pub leiden_max_iterations: Option<usize>,
    pub graph_backend: GraphBackend,
    pub preprocessing: ClusteringPreprocessing,
    pub hierarchy_mode: HierarchyMode,
    pub clique_cluster_size: Option<usize>,
    pub dead_ends_as_outputs: bool,
    pub manually_check_acyclic: bool,
    pub seed: Option<u64>,
    pub debug: usize
}

// Version that can be copied at the cost of reduced options
impl CopyableDecomposeOptions {
    pub fn into_decompose_options(&self) -> DecomposeOptions<'_> {
        DecomposeOptions {
            resolution: self.resolution,
            target_size: self.target_size,
            leiden_max_iterations: self.leiden_max_iterations,
            equivalence_mode: EquivalenceMode::None,
            graph_backend: self.graph_backend,
            preprocessing: self.preprocessing,
            hierarchy_mode: self.hierarchy_mode,
            inverse_coni_mapping: None,
            inverse_sig_mapping: None,
            minimum_equivalence_size: None,
            equivalence_comparison_budget: None,
            existing_partition: None,
            extract_raw_partition: None,
            clique_cluster_size: self.clique_cluster_size,
            dead_ends_as_outputs: self.dead_ends_as_outputs,
            manually_check_acyclic: self.manually_check_acyclic,
            seed: self.seed,
            debug: self.debug
    }}
}


// takes two sorted vecs and returns a sorted vec
pub fn merge_sorted_vecs(left: &Vec<usize>, right: &Vec<usize>) -> Vec<usize> {
        let (mut l_pointer, mut r_pointer) = (0, 0);
        let mut out: Vec<usize> = Vec::new();
        while l_pointer < left.len() && r_pointer < right.len() {
            match left[l_pointer].cmp(&right[r_pointer]) {
                std::cmp::Ordering::Equal => {
                    out.push(left[l_pointer]); l_pointer += 1; r_pointer += 1;
                },
                std::cmp::Ordering::Less => {
                    l_pointer += 1;
                },
                std::cmp::Ordering::Greater => {
                    r_pointer += 1;
                }
            }
        }

        out
    }

pub fn distance_to_source_set(source_set: impl Iterator<Item = usize>, adjacencies: &Vec<Vec<usize>>) -> Vec<usize> {

    let mut distance: Vec<usize> = vec![usize::MAX; adjacencies.len()];
    let mut queue: VecDeque<usize> = source_set.collect();
    for idx in queue.iter() {distance[*idx] = 0;}

    while queue.len() > 0 {
        let curr = queue.pop_front().unwrap();
        let next_distance = distance[curr] + 1;
        for adj in adjacencies[curr].iter().copied() {
            if distance[adj] == usize::MAX {
                queue.push_back(adj);
                distance[adj] = next_distance;
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

pub fn dfs_merge_set_in_dag_hashmap_adj(target_set: &HashSet<usize>, adjacencies: &HashMap<usize, &Vec<usize>>) -> HashSet<usize> {

    let mut can_reach_t: HashMap<usize, bool> = target_set.into_iter().copied().map(|v| (v, true)).collect();
    let mut stack: Vec<usize> = target_set.into_iter().copied().flat_map(|v| adjacencies[&v].into_iter().copied()).collect();

    while stack.len() > 0 {

        let curr: usize = *stack.last().unwrap();
        if can_reach_t.contains_key(&curr) {
            stack.pop();
            continue;
        };

        stack.extend(adjacencies[&curr].into_iter().copied().filter(|adj| can_reach_t.get(adj).is_none()));

        if adjacencies[&curr].into_iter().copied().any(|adj| can_reach_t.get(&adj).copied().unwrap_or(false) ) {
            can_reach_t.entry(curr).or_insert(true);
        } else if adjacencies[&curr].into_iter().copied().all(|adj| !can_reach_t.get(&adj).copied().unwrap_or(true) ) {
            can_reach_t.entry(curr).or_insert(false);
        }

    }

    can_reach_t.into_iter().filter(|(_, val)| *val).map(|(k, _)| k).collect()
}


pub fn dfs_merge_set_in_dag(target_set: &[usize], adjacencies: &[HashSet<usize>]) -> HashSet<usize> {

    let mut can_reach_t: HashMap<usize, bool> = target_set.into_iter().copied().map(|v| (v, true)).collect();
    let mut stack: Vec<usize> = target_set.into_iter().copied().flat_map(|v| adjacencies[v].iter().copied()).collect();

    while stack.len() > 0 {

        let curr: usize = *stack.last().unwrap();
        if can_reach_t.contains_key(&curr) {
            stack.pop();
            continue;
        };

        stack.extend(adjacencies[curr].iter().copied().filter(|adj| can_reach_t.get(adj).is_none()));

        if adjacencies[curr].iter().copied().any(|adj| can_reach_t.get(&adj).copied().unwrap_or(false) ) {
            can_reach_t.entry(curr).or_insert(true);
        } else if adjacencies[curr].iter().copied().all(|adj| !can_reach_t.get(&adj).copied().unwrap_or(true) ) {
            can_reach_t.entry(curr).or_insert(false);
        }

    }

    can_reach_t.into_iter().filter(|(_, val)| *val).map(|(k, _)| k).collect()
}


pub fn count_ints<T: Hash + Eq + Ord>(source: impl IntoIterator<Item = T>) -> Vec<(T, usize)> {
    let mut counter: HashMap<T, usize> = HashMap::new();
    for num in source.into_iter() {
        *counter.entry(num).or_insert(0) += 1
    }
    counter.into_iter().sorted().collect()
}