use std::collections::{HashMap, HashSet};

pub struct UnionFind {
    parent: HashMap<usize, isize>,
    representatives: Option<HashSet<usize>>
}

impl UnionFind {

    pub fn new(representative_tracking: bool) -> Self {
        Self {parent: HashMap::new(), representatives: if representative_tracking {Some(HashSet::new())} else {None}}
    }

    pub fn find(&mut self, idx: usize) -> usize {
        if !self.representatives.is_none() && !self.parent.contains_key(&idx) {self.representatives.as_mut().map(|set| set.insert(idx));};

        let entry = *self.parent.entry(idx).or_insert(-1);

        if entry < 0 {
            idx
        } else {
            let parent = self.find(entry as usize);
            self.parent.entry(idx).insert_entry(parent as isize);
            parent
        }
    }

    pub fn union(&mut self, idxs: impl Iterator<Item = usize>) -> () {

        let mut representatives: Vec<usize> = idxs.map(|idx| self.find(idx)).collect::<HashSet<usize>>().into_iter().collect();
        representatives.sort_by_key(|idx| self.parent.get(idx).unwrap());

        if representatives.len() > 1 && self.parent.get(&representatives[0]) == self.parent.get(&representatives[1]) {self.parent.entry(representatives[0]).and_modify(|entry| *entry -= 1);};

        for repr in representatives.iter().skip(1) {
            if !self.representatives.is_none() {self.representatives.as_mut().map(|set| set.remove(repr));};
            self.parent.entry(*repr).insert_entry(representatives[0] as isize);
        }
    }

    pub fn get_components(&mut self) -> Vec<Vec<usize>> {
        let mut components: HashMap<usize, Vec<usize>> = HashMap::new();
        let keys: Vec<_> = self.parent.keys().copied().collect();

        for parti in keys {
            components.entry(self.find(parti)).or_insert(Vec::new()).push(parti);
        }

        components.into_values().collect()
    }
}