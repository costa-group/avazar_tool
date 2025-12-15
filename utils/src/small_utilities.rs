use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::Hash;
use itertools::Itertools;

pub fn distance_to_source_set<'a, T: Eq + Hash + Copy>(source_set: impl Iterator<Item = &'a T>, adjacencies: &'a HashMap<T, HashSet<T>>) -> HashMap<&'a T, usize> {

    let mut distance: HashMap<&T, usize> = source_set.map(|idx| (idx, 0)).collect();
    let mut queue: VecDeque<&T> = distance.keys().copied().collect();

    while queue.len() > 0 {
        let curr = queue.pop_front().unwrap();
        queue.extend(adjacencies.get(curr).unwrap().into_iter().filter(|key| !distance.contains_key(key)));
        let next_distance = distance.get(curr).unwrap() + 1;
        for adj in adjacencies.get(curr).unwrap().into_iter() {distance.entry(adj).or_insert(next_distance);}
    };

    distance
}

pub fn dfs_can_reach_target_from_sources(source: &Vec<usize>, targets: &Vec<usize>, adjacencies: &HashMap<usize, &Vec<usize>>) -> Vec<usize> {

    let mut can_reach_t: HashMap<&usize, bool> = targets.iter().map(|t| (t, true)).collect();
    let mut stack: Vec<&usize> = source.into_iter().collect();

    while stack.len() > 0 {

        let curr: &usize = stack.last().unwrap();
        if can_reach_t.contains_key(curr) {
            stack.pop();
            continue;
        };

        stack.extend(adjacencies.get(curr).unwrap().iter().filter(|adj| can_reach_t.get(*adj).is_none()));

        if adjacencies.get(curr).unwrap().iter().any(|adj| can_reach_t.get(adj).copied().unwrap_or(false) ) {
            can_reach_t.entry(curr).or_insert(true);
        } else if adjacencies.get(curr).unwrap().iter().all(|adj| !can_reach_t.get(adj).copied().unwrap_or(true) ) {
            can_reach_t.entry(curr).or_insert(false);
        }

    }

    can_reach_t.into_iter().filter(|(_, val)| *val).map(|(k, _)| k).copied().filter(|k| !targets.contains(k)).collect()
}

pub fn count_ints<T: Hash + Eq + Ord>(source: impl IntoIterator<Item = T>) -> Vec<(T, usize)> {
    let mut counter: HashMap<T, usize> = HashMap::new();
    for num in source.into_iter() {
        *counter.entry(num).or_insert(0) += 1
    }
    counter.into_iter().sorted().collect()
}