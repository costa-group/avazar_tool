use std::collections::{HashMap, HashSet};
use std::array::from_fn;
use std::hash::Hash;
use std::cmp::Eq;

use utils::assignment::Assignment;

pub fn iterated_label_propagation<const N: usize, H: Hash + Eq + Copy>(
    indices_to_adjacent: &[HashMap<usize, &Vec<usize>>; N],
    init_label_to_indices: [HashMap<H, Vec<usize>>; N]
) -> [HashMap<usize, Vec<usize>>; N] {

    let mut singular_classes: [HashMap<usize, Vec<usize>>; N] = from_fn(|_| HashMap::new());
    
    let mut index_to_label: [HashMap<usize, usize>; N] = from_fn(|_| HashMap::new());
    
    fn remove_lone_classes<const N: usize, H: Hash + Eq + Copy>(
        label_to_indices: [HashMap<H, Vec<usize>>; N], 
        singular_classes: &mut [HashMap<usize, Vec<usize>>; N], 
        index_to_label: &mut [HashMap<usize, usize>; N],
        max_singular_label: usize) -> ([HashMap<usize, Vec<usize>>; N], usize) {

        let mut singular_renaming = Assignment::<H, 1>::new(max_singular_label);
        let mut nonsingular_classes: Vec<H> = Vec::new();

        for key in (0..N).into_iter().flat_map(|idx| label_to_indices[idx].keys()).collect::<HashSet<&H>>() {
            // a class is singular if every appearance of it is singular
            if (0..N).into_iter().all(|idx| label_to_indices[idx].get(key).is_none_or(|class| class.len() == 1)) {
                for idx in (0..N).filter(|idx| label_to_indices[*idx].contains_key(key)) {
                    let new_key = singular_renaming.get_assignment([key]);
                    for index in label_to_indices[idx][key].iter().copied() {index_to_label[idx].insert(index, new_key);}
                    singular_classes[idx].insert(new_key, vec![label_to_indices[idx][key][0]]);
                }
            } else {
                nonsingular_classes.push(*key);
            }
        }

        let new_max_singular_label = max_singular_label + singular_renaming.len();

        let mut nonsingular_renaming = Assignment::<H, 1>::new(new_max_singular_label);
        let mut new_label_to_indices: [HashMap<usize, Vec<usize>>; N] = from_fn(|_| HashMap::new());

        for (idx, mut hm) in label_to_indices.into_iter().enumerate() {
            let keys_to_move: Vec<&H> = nonsingular_classes.iter().filter(|&key| hm.contains_key(key)).collect();

            for key in keys_to_move.into_iter() {

                let new_key = nonsingular_renaming.get_assignment([key]);
                for index in hm[key].iter().copied() {index_to_label[idx].insert(index, new_key);}
                new_label_to_indices[idx].insert(new_key, hm.remove(key).unwrap());

            }
        }
        
        (new_label_to_indices, new_max_singular_label)
    }

    fn propogate_adjacent_labels<const N: usize>(
        label_to_indices: [HashMap<usize, Vec<usize>>; N],
        index_to_label: &[HashMap<usize, usize>; N],
        indices_to_adjacent: &[HashMap<usize, &Vec<usize>>; N],
        max_singular_label: usize
    ) -> ([HashMap<usize, Vec<usize>>; N], bool) {

        let mut renaming = Assignment::<(&usize, Vec<&usize>), 1>::new(max_singular_label);
        let mut new_label_to_indices: [HashMap<usize, Vec<usize>>; N] = from_fn(|_| HashMap::new());

        // construct hashmap to store values for assignment
        let index_to_hash: [HashMap<usize, (&usize, Vec<&usize>)>; N] = from_fn(|idx| 
            label_to_indices[idx].values().flat_map(|class| class.into_iter()).map(
                |index| (*index, 
                            (   index_to_label[idx].get(index).unwrap(),
                                indices_to_adjacent[idx][index].into_iter().map(|oindex| index_to_label[idx].get(oindex).unwrap()).collect::<Vec<&usize>>()))
            ).collect()
        );

        for idx in 0..N {
            for (index, hash) in index_to_hash[idx].iter() {
                let new_key = renaming.get_assignment([hash]);
                new_label_to_indices[idx].entry(new_key).or_insert_with(|| Vec::new()).push(*index);
            }
        }

        let changes = (0..N).any(|idx| new_label_to_indices[idx].len() != label_to_indices[idx].len());

        (new_label_to_indices, changes)
    }


    let (mut label_to_indices, mut max_singular_label) = remove_lone_classes(init_label_to_indices, &mut singular_classes, &mut index_to_label, 0);
    let mut changes = true;
    while changes {

        (label_to_indices, changes) = propogate_adjacent_labels(label_to_indices, &index_to_label, indices_to_adjacent, max_singular_label);
        (label_to_indices, max_singular_label) = remove_lone_classes(label_to_indices, &mut singular_classes, &mut index_to_label, max_singular_label)

    }

    for (idx, hm) in label_to_indices.into_iter().enumerate() {
        for (key, class) in hm.into_iter() {
            singular_classes[idx].insert(key, class);
        }
    }

    singular_classes
}