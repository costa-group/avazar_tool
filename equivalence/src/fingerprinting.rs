use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::cmp::Eq;
use std::fmt::Debug;
use itertools::Itertools;

use circuits_and_constraints::circuit::Circuit;
use circuits_and_constraints::constraint::Constraint;
use utils::assignment::Assignment;

// started with arrays, now need 1 runtime length...
fn from_fn<T>(n: usize, f: impl FnMut(usize) -> T) -> Vec<T> {(0..n).into_iter().map(f).collect()}

pub fn iterated_refinement<'a, C: Constraint, S: Circuit<C>, H: Hash + Eq>(
        circuits: &[&'a S],
        norms_being_fingerprinted: &'a [&'a Vec<C>],
        signal_to_normi: &[&HashMap<usize, Vec<usize>>],
        init_fingerprints_to_normi: &[&HashMap<H, Vec<usize>>],
        init_fingerprints_to_signals: &[&HashMap<H, Vec<usize>>],
        start_with_constraints: bool,
        per_iteration_postprocessing: Option<fn(&mut [HashMap<usize, (usize, usize)>], &mut [HashMap<(usize, usize), Vec<usize>>], &mut [HashMap<usize, (usize, usize)>], &mut [HashMap<(usize, usize), Vec<usize>>], &mut [HashMap<(usize, usize), usize>] ) -> ()>,
        strict_unique: bool,
        debug: bool
    ) -> (Vec<HashMap<usize, Vec<usize>>>, Vec<HashMap<usize, Vec<usize>>>, Vec<HashMap<usize, usize>>, Vec<HashMap<usize, usize>>) {

    let n: usize = circuits.len();
    if norms_being_fingerprinted.len() != n || signal_to_normi.len() != n || init_fingerprints_to_normi.len() != n || init_fingerprints_to_signals.len() != n {panic!("passed inputs of different_sizes to fingerprinting");};

    let signal_sets: Vec<HashSet<usize>> = from_fn(n, |idx| circuits[idx].get_signals().collect());

    let mut norm_fingerprints: Vec<HashMap<usize, (usize, usize)>> = from_fn(n, |_| HashMap::new());
    let mut sig_fingerprints: Vec<HashMap<usize, (usize, usize)>> = from_fn(n, |_| HashMap::new());

    let mut signals_to_update: Vec<HashSet<usize>>;

    let (init_num_singular_norm_fingerprints, mut norms_to_update) = iterated_refinement_preprocessing(init_fingerprints_to_normi, &mut norm_fingerprints, !start_with_constraints as usize + 1, strict_unique);
    let (init_num_singular_sig_fingerprints, init_signals_to_update) = iterated_refinement_preprocessing(init_fingerprints_to_signals, &mut sig_fingerprints, start_with_constraints as usize + 1, strict_unique);

    fn exit_postprocessing(index_to_label_and_roundnum: &[HashMap<usize, (usize, usize)>]) -> (Vec<HashMap<usize, Vec<usize>>>, Vec<HashMap<usize, usize>>) {
            let n = index_to_label_and_roundnum.len();

            let mut label_to_indices: Vec<HashMap<usize, Vec<usize>>> = from_fn(n, |_| HashMap::new());
            let mut index_to_label:  Vec<HashMap<usize, usize>> = from_fn(n, |_| HashMap::new());

            let mut final_assignment = Assignment::<(usize, usize), 1>::new(0);
            
            for (idx, hm) in index_to_label_and_roundnum.iter().enumerate() {
                for index in hm.keys() {
                    let label = final_assignment.get_assignment([hm.get(index).unwrap()]);
                    index_to_label[idx].insert(*index, label);
                    label_to_indices[idx].entry(label).or_insert(Vec::new()).push(*index)
                }
            }

            (label_to_indices, index_to_label)
        }

    let (mut any_norms_to_update, mut any_sigs_to_update): (bool, bool) = (norms_to_update.iter().any(|arr| arr.len() > 0), init_signals_to_update.iter().any(|arr| arr.len() > 0));

    if !any_norms_to_update && !any_sigs_to_update {
        // TODO: these might not line up at first !!

        let (return_fingerprints_to_normi, return_norm_fingerprints) = exit_postprocessing(&norm_fingerprints);
        let (return_fingerprints_to_signals, return_sig_fingerprints) = exit_postprocessing(&sig_fingerprints);

        (return_fingerprints_to_normi, return_fingerprints_to_signals, return_norm_fingerprints, return_sig_fingerprints)
    } else {

        let (mut previous_distinct_norm_fingerprints, mut previous_distinct_sig_fingerprints): (Vec<usize>, Vec<usize>) = 
            (from_fn(n, |idx| init_fingerprints_to_normi[idx].len()), from_fn(n, |idx| init_fingerprints_to_signals[idx].len()));
        let (mut break_on_next_norm, mut break_on_next_signal): (bool, bool) = (false, false);

        let mut normi_raw_fingerprints: Vec<Vec<Option<C::Fingerprint<'a, (usize, usize)>>>> = from_fn(n, |idx| (0..norms_being_fingerprinted[idx].len()).into_iter().map(|_| None).collect());
        let mut sig_raw_fingerprints: Vec<Vec<Option<S::SignalFingerprint<'a, (usize, usize)>>>> = from_fn(n, |idx| (0..circuits[idx].n_wires()).into_iter().map(|_| None).collect());

        let mut fingerprints_to_normi: Vec<HashMap<(usize, usize), Vec<usize>>> = from_fn(n, |_| HashMap::new());
        let mut fingerprints_to_signals: Vec<HashMap<(usize, usize), Vec<usize>>> = from_fn(n, |_| HashMap::new());

        let mut num_singular_norm_fingerprints: HashMap<usize, usize> = [(!start_with_constraints as usize + 1, init_num_singular_norm_fingerprints)].into_iter().collect();
        let mut num_singular_sig_fingerprints: HashMap<usize, usize> = [(start_with_constraints as usize + 1, init_num_singular_sig_fingerprints)].into_iter().collect();

        let (mut prev_fingerprints_to_normi_count, mut prev_fingerprints_to_sig_count): (Vec<HashMap<(usize, usize), usize>>, Vec<HashMap<(usize, usize), usize>>) = (from_fn(n, |_| HashMap::new()), from_fn(n, |_| HashMap::new()));
        let (mut prev_fingerprints_to_normi, mut prev_fingerprints_to_sig): (Vec<HashMap<(usize, usize), Vec<usize>>>, Vec<HashMap<(usize, usize), Vec<usize>>>) = (from_fn(n, |_| HashMap::new()), from_fn(n, |_| HashMap::new()));
        let mut prev_normi_to_fingerprints: Vec<HashMap<usize, (usize, usize)>> = from_fn(n, |idx| (0..norms_being_fingerprinted[idx].len()).into_iter().map(|normi| (normi, *norm_fingerprints[idx].get(&normi).unwrap())).collect());
        let mut prev_sig_to_fingerprints: Vec<HashMap<usize, (usize, usize)>> = from_fn(n, |idx| signal_sets[idx].iter().copied().map(|sig| (sig, *sig_fingerprints[idx].get(&sig).unwrap())).collect());

        let get_to_update_normi = |normi: usize, idx: usize| norms_being_fingerprinted[idx][normi].signals().into_iter().collect::<Vec<_>>();
        let get_to_update_signal = |sig: usize, idx: usize| signal_to_normi[idx].get(&sig).unwrap().into_iter().copied().collect::<Vec<_>>();

        // this lets 0 be some unique check round_num value.
        let mut round_num = 3;

        fn loop_iteration<'a, C: Constraint, S: Circuit<C>, H: 'a + Hash + Eq + Clone + Debug>(
            circuits: &[&'a S], norms_being_fingerprinted: &'a [&'a Vec<C>], round_num: usize, strict_unique: bool,
            indices_to_update: Vec<HashSet<usize>>, signal_to_normi: &[&HashMap<usize, Vec<usize>>],
            per_iteration_postprocessing: Option<fn(&mut [HashMap<usize, (usize, usize)>], &mut [HashMap<(usize, usize), Vec<usize>>], &mut [HashMap<usize, (usize, usize)>], &mut [HashMap<(usize, usize), Vec<usize>>], &mut [HashMap<(usize, usize), usize>] ) -> ()>,
            get_fingerprint: impl Fn(usize, &S, &mut Option<H>, &'a Vec<C>, &HashMap<usize, (usize, usize)>, &HashMap<usize, (usize, usize)>, &HashMap<usize, Vec<usize>>),
            last_loop: bool, get_to_update: impl Fn(usize, usize) -> Vec<usize>,
            index_to_label: &mut [HashMap<usize, (usize, usize)>], label_to_indices: &mut Vec<HashMap<(usize, usize), Vec<usize>>>, 
            raw_fingerprints: &mut [Vec<Option<H>>], other_index_to_label: &mut [HashMap<usize, (usize, usize)>],
            prev_index_to_label: &mut [HashMap<usize, (usize, usize)>], prev_label_to_indices: &mut [HashMap<(usize, usize), Vec<usize>>], prev_label_to_indices_count: &mut [HashMap<(usize, usize), usize>],
            prev_other_index_to_label: &mut Vec<HashMap<usize, (usize, usize)>>,
            prev_distinct_labels: &mut Vec<usize>, num_singular_labels: &mut HashMap<usize, usize>, other_num_singular: &HashMap<usize, usize>, debug: bool
        ) -> (bool, Vec<HashSet<usize>>) {

            let n = circuits.len();

            if debug {
                println!("----------------------- {:?} ----------------------", round_num);
                println!("num_to_update {:?}", indices_to_update[0].len());
                println!("num_singular {:?}", num_singular_labels[&(round_num - 2)]);
                println!("other_num_singular {:?}", other_num_singular[&(round_num - 1)]);
            }
            let mut assignment = Assignment::<H, 1>::new(num_singular_labels[&(round_num - 2)]);
            if debug {let _ = assignment.enable_inverse();}

            // Fingerprint everything that needs to be update
            for (idx, (to_update, raw_fingerprints_idx) ) in indices_to_update.into_iter().zip(raw_fingerprints.into_iter()).enumerate() {
                let mut offset: usize = 0;
                let mut tail: &mut [Option<H>] = raw_fingerprints_idx;
                let mut head: &mut [Option<H>];

                for index in to_update.into_iter().sorted() {
                    (head, tail) = tail.split_at_mut(index - offset + 1);
                    let raw_fingerprint: &mut Option<H> = &mut head[index - offset];
                    offset = index + 1;

                    get_fingerprint(index, circuits[idx], raw_fingerprint , norms_being_fingerprinted[idx], &other_index_to_label[idx], &prev_index_to_label[idx], signal_to_normi[idx]);

                    let new_hash: usize = assignment.get_assignment([raw_fingerprint.as_ref().unwrap()]);
                    index_to_label[idx].insert(index, (round_num, new_hash));
                    label_to_indices[idx].entry((round_num, new_hash)).or_insert(Vec::new()).push(index);
                }
            }

            // Do any postprocessing if necessary
            if let Some(f) = per_iteration_postprocessing {
                f(index_to_label, label_to_indices, prev_index_to_label, prev_label_to_indices, prev_label_to_indices_count);
            }

            if debug {println!("previous_distinct {:?}", prev_distinct_labels);}

            // update loop exit checking
            let break_on_next_loop = (0..n).into_iter().all(|idx| num_singular_labels[&(round_num - 2)] + label_to_indices[idx].len() == prev_distinct_labels[idx]);
            *prev_distinct_labels = from_fn(n, |idx| num_singular_labels[&(round_num - 2)] + label_to_indices[idx].len());

            if debug {println!("current distinct {:?}", prev_distinct_labels); println!("break on next loop: {:?}", break_on_next_loop); sanity_check_fingerprinting(&assignment, index_to_label, label_to_indices, prev_index_to_label);}

            // Handle the context switch if isn't the last loop
            if !last_loop {
                let (new_prev_other_index_to_label, other_indices_to_update) = fingerprint_switch(
                    index_to_label, label_to_indices, num_singular_labels, prev_index_to_label, prev_label_to_indices, prev_label_to_indices_count, get_to_update,
                    other_index_to_label, other_num_singular, round_num, strict_unique
                );

                if round_num > 3 {*prev_other_index_to_label = new_prev_other_index_to_label;} // first round is special case for encoding structure

                *label_to_indices = from_fn(n, |_| HashMap::new());
                if debug {println!("{:?}", from_fn(n, |idx| other_indices_to_update[idx].len()));}
                (break_on_next_loop, other_indices_to_update)
            } else {
                (break_on_next_loop, from_fn(n, |_| HashSet::new()))
            }
        }

        // Functions that calculate the fingerprint for each item type
        let get_norm_fingerprint = |index: usize, _: &S, raw_fingerprint: &mut Option<C::Fingerprint<'a, (usize, usize)>>, norms_being_fingerprinted: &'a Vec<C>, other_index_to_label: &HashMap<usize, (usize, usize)>, _: &HashMap<usize, (usize, usize)>, _: &HashMap<usize, Vec<usize>>|
            norms_being_fingerprinted[index].fingerprint(raw_fingerprint, other_index_to_label);

        let get_sig_fingerprint = |index: usize, circ: &S, raw_fingerprint: &mut Option<S::SignalFingerprint<'a, (usize, usize)>>, norms_being_fingerprinted: &'a Vec<C>, other_index_to_label: &HashMap<usize, (usize, usize)>, prev_index_to_label: &HashMap<usize, (usize, usize)>, signal_to_normi: &HashMap<usize, Vec<usize>>|
            circ.fingerprint_signal(&index, raw_fingerprint, norms_being_fingerprinted, other_index_to_label, prev_index_to_label, signal_to_normi);

        // handle starting with signals
        if !start_with_constraints {
            (break_on_next_signal, _) = loop_iteration(circuits, norms_being_fingerprinted, round_num, strict_unique,
                init_signals_to_update.clone(), signal_to_normi, per_iteration_postprocessing, get_sig_fingerprint, 
                !break_on_next_norm && !break_on_next_signal, get_to_update_signal,
                &mut sig_fingerprints, &mut fingerprints_to_signals, &mut sig_raw_fingerprints, &mut norm_fingerprints,
                &mut prev_sig_to_fingerprints, &mut prev_fingerprints_to_sig, &mut prev_fingerprints_to_sig_count,
                &mut prev_normi_to_fingerprints, &mut previous_distinct_sig_fingerprints, 
                &mut num_singular_sig_fingerprints, &num_singular_norm_fingerprints, debug
            );
            any_norms_to_update = norms_to_update.iter().any(|arr| arr.len() > 0);
            round_num += 1;
        }

        while any_norms_to_update {
            // Run loop for norms
            if break_on_next_norm {break;}
            (break_on_next_norm, signals_to_update) = loop_iteration(circuits, norms_being_fingerprinted, round_num, strict_unique,
                norms_to_update, signal_to_normi, per_iteration_postprocessing, get_norm_fingerprint, 
                break_on_next_norm || break_on_next_signal, get_to_update_normi,
                &mut norm_fingerprints, &mut fingerprints_to_normi, &mut normi_raw_fingerprints, &mut sig_fingerprints,
                &mut prev_normi_to_fingerprints, &mut prev_fingerprints_to_normi, &mut prev_fingerprints_to_normi_count,
                &mut prev_sig_to_fingerprints, &mut previous_distinct_norm_fingerprints, 
                &mut num_singular_norm_fingerprints, &num_singular_sig_fingerprints, debug
            );
            if round_num == 3 {signals_to_update = init_signals_to_update.clone();} // ensure we encode structural at least once
            any_sigs_to_update = signals_to_update.iter().any(|arr| arr.len() > 0);
            round_num += 1;

            // Run loop for signals
            if !any_sigs_to_update || break_on_next_signal {break;}
            (break_on_next_signal, norms_to_update) = loop_iteration(circuits, norms_being_fingerprinted, round_num, strict_unique,
                signals_to_update, signal_to_normi, per_iteration_postprocessing, get_sig_fingerprint, 
                break_on_next_norm || break_on_next_signal, get_to_update_signal,
                &mut sig_fingerprints, &mut fingerprints_to_signals, &mut sig_raw_fingerprints, &mut norm_fingerprints,
                &mut prev_sig_to_fingerprints, &mut prev_fingerprints_to_sig, &mut prev_fingerprints_to_sig_count,
                &mut prev_normi_to_fingerprints, &mut previous_distinct_sig_fingerprints, 
                &mut num_singular_sig_fingerprints, &num_singular_norm_fingerprints, debug
            );
            any_norms_to_update = norms_to_update.iter().any(|arr| arr.len() > 0);
            round_num += 1;

            
        };

        let (return_fingerprints_to_normi, return_norm_fingerprints) = exit_postprocessing(&norm_fingerprints);
        let (return_fingerprints_to_signals, return_sig_fingerprints) = exit_postprocessing(&sig_fingerprints);

        (return_fingerprints_to_normi, return_fingerprints_to_signals, return_norm_fingerprints, return_sig_fingerprints)
    }
} 

fn iterated_refinement_preprocessing<H: Hash + Eq>(label_to_indices: &[&HashMap<H, Vec<usize>>], index_to_label: &mut [HashMap<usize, (usize, usize)>], init_round: usize, strict_unique: bool)
 -> (usize, Vec<HashSet<usize>>) {

    let n = label_to_indices.len();

    let mut nonsingular_keys: Vec<Vec<&H>> = from_fn(n, |_| Vec::new());
    let mut singular_remapping = Assignment::<H, 1>::new(0);

    for index in 0..n {
        for label in label_to_indices[index].keys() {
            if key_is_unique(label, index, label_to_indices, strict_unique) {
                index_to_label[index].insert(label_to_indices[index][label][0], (init_round, singular_remapping.get_assignment([label])));
            } else {
                nonsingular_keys[index].push(label)
            }
        }
    }

    let mut to_update: Vec<HashSet<usize>> = from_fn(n, |_| HashSet::new());
    let num_singular = singular_remapping.len();

    let mut nonsingular_remapping = Assignment::<&H, 1>::new(num_singular);

    for (idx, nonsingular_vec) in nonsingular_keys.iter().enumerate() {
        for label in nonsingular_vec.into_iter() {

            to_update[idx].extend(&label_to_indices[idx][label]);
            for index in label_to_indices[idx][label].iter().copied() { index_to_label[idx].insert(index, (init_round, nonsingular_remapping.get_assignment([&label]))); }
        }
    }

    (num_singular, to_update)
 }

fn key_is_unique<H: Hash + Eq>(label: &H, index: usize, labels_to_indices: &[&HashMap<H, Vec<usize>>], strict: bool) -> bool {
    if strict {
        labels_to_indices.iter().all(|hm| hm.get(label).is_some_and(|vec| vec.len() == 1))
    } else {
        labels_to_indices[index].get(label).is_some_and(|vec| vec.len() == 1)
    }
}

fn fingerprint_switch(
    fingerprints: &mut [HashMap<usize, (usize, usize)>], fingerprints_to_index: &mut Vec<HashMap<(usize, usize), Vec<usize>>>, num_singular_fingerprints: &mut HashMap<usize, usize>,
    prev_fingerprints: &[HashMap<usize, (usize, usize)>], prev_fingerprints_to_index: &mut [HashMap<(usize, usize), Vec<usize>>], prev_fingerprints_to_index_count: &mut [HashMap<(usize, usize), usize>], 
    get_to_update: impl Fn(usize, usize) -> Vec<usize>, other_fingerprints: &[HashMap<usize, (usize, usize)>], other_num_singular: &HashMap<usize, usize>, round_num: usize, strict: bool
) -> (Vec<HashMap<usize, (usize, usize)>>, Vec<HashSet<usize>>) {
    // TODO: reset Assignment outside -- with passed offset 
    let n = prev_fingerprints.len();

    let mut next_to_update: Vec<HashSet<usize>> = from_fn(n, |_| HashSet::new());
    let mut add_to_update = |index: usize, idx: usize| {
        next_to_update[idx].extend(get_to_update(index, idx).into_iter().filter(
        // other_num_singular[round] is the number of singular fingerprints at that time, if oind_label.1 > that then it means it's not singular and should be looked at again
        |oind: &usize| {let (prev_round, other_label): (usize, usize) = other_fingerprints[idx][oind]; other_label >= other_num_singular[&prev_round]}
    ))
    };

    let mut nonsingular_fingerprints: Vec<Vec<(usize, usize)>> = from_fn(n, |_| Vec::new());

    let mut singular_renaming = Assignment::<(usize, usize), 1>::new(*num_singular_fingerprints.get(&(round_num-2)).unwrap());

    let fingerprints_to_index_refs: Vec<&_> = from_fn(n, |idx| &fingerprints_to_index[idx]);

    for idx in 0..n {
        for label in fingerprints_to_index[idx].keys() {
            if key_is_unique(label, idx, &fingerprints_to_index_refs, strict) {

                let index = fingerprints_to_index[idx].get(label).unwrap()[0];
                fingerprints[idx].insert(index, (round_num, singular_renaming.get_assignment([label])));
                add_to_update(index, idx);

                let prev_fingerprint = prev_fingerprints[idx].get(&index).unwrap();

                if round_num > 4 && prev_fingerprint.0 >= 3 {
                    prev_fingerprints_to_index_count[idx].entry(*prev_fingerprint).and_modify(|val| *val -= 1);
                    if *prev_fingerprints_to_index_count[idx].get(prev_fingerprint).unwrap() == 0 {
                        prev_fingerprints_to_index[idx].remove(prev_fingerprint);
                        prev_fingerprints_to_index_count[idx].remove(prev_fingerprint);
                    }
                }

            } else {
                nonsingular_fingerprints[idx].push(*label);
            }
        }
    }

    num_singular_fingerprints.insert(round_num, *num_singular_fingerprints.get(&(round_num-2)).unwrap() + singular_renaming.len() );
    let num_singular_fingerprints_this_round: usize = num_singular_fingerprints[&round_num];

    // now we collect all the labels that have actually changed by comparing the old/new sets
    // TODO: do this better, so not comparing each class multiple times
    // TODO: when the prev_fingerprint was from a very old round -- this struggles

    for (idx, nonsingular_batch) in nonsingular_fingerprints.into_iter().enumerate() {

        for label in nonsingular_batch.into_iter() {

            // reindex to avoid clashes with singular keys, faster than re-hashing again
            let new_label = (round_num, label.1 + num_singular_fingerprints_this_round);

            prev_fingerprints_to_index[idx].insert(new_label, fingerprints_to_index[idx].remove(&label).unwrap());

            let class: &Vec<usize> = prev_fingerprints_to_index[idx].get(&new_label).unwrap();

            prev_fingerprints_to_index_count[idx].insert(new_label, class.len());

            for index in class.into_iter().copied() {fingerprints[idx].insert(index, new_label);}

            let mut labels_to_delete: Vec<(usize, usize)> = Vec::new();
            let an_old_key: &(usize, usize) = prev_fingerprints[idx].get(&class[0]).unwrap();

            if round_num <= 4 || an_old_key.0 < 3 {
                for index in class.into_iter().copied() {add_to_update(index, idx)};
            } else {
                // Only when the class is truly unchanged (i.e. has not had anything removed) will do we consider it unchaged, sorting here also requires fewest sort calls
                if *prev_fingerprints_to_index_count[idx].get(an_old_key).unwrap() == class.len() && class.into_iter().sorted().eq(prev_fingerprints_to_index[idx].get(an_old_key).unwrap().into_iter().sorted()) {
                    // class has not changed, delete old info as it is redundant
                    labels_to_delete.push(*an_old_key);
                } else {
                    // class has changed -- need to check these on next iteration, need to update index counts / delete if empty
                    for index in class.into_iter() {

                        add_to_update(*index, idx);

                        let index_old_key = prev_fingerprints[idx].get(index).unwrap();
                        prev_fingerprints_to_index_count[idx].entry(*index_old_key).and_modify(|val| *val -= 1);

                        if *prev_fingerprints_to_index_count[idx].get(index_old_key).unwrap() == 0 {
                            labels_to_delete.push(*index_old_key);
                        }
                    }
                }
            }

            // deleting here because of class borrow checking -- specifically the for index in class.into_iter() loop will always cause problems -- 
            for label_to_delete in labels_to_delete.iter() {
                prev_fingerprints_to_index[idx].remove(label_to_delete);
                prev_fingerprints_to_index_count[idx].remove(label_to_delete);
            }
        }
    }

    let new_prev_other_index_to_label: Vec<HashMap<usize, (usize, usize)>> = from_fn(n, |idx| next_to_update[idx].iter().map(|index| (*index, *other_fingerprints[idx].get(index).unwrap())).collect());

    *fingerprints_to_index = from_fn(n, |_| HashMap::new());
    (new_prev_other_index_to_label, next_to_update)
}

// use utils::small_utilities::count_ints;

fn sanity_check_fingerprinting<H: Hash + Eq + Clone + Debug>(
    assignment: &Assignment<H, 1>, _index_to_label: &[HashMap<usize, (usize, usize)>], label_to_indices: &[HashMap<(usize, usize), Vec<usize>>],
    prev_index_to_label: &[HashMap<usize, (usize, usize)>]) -> () {
    /*
    function used to debug behaviour
    */

    let n = label_to_indices.len();
    
    let keys_in_only_one: HashSet<(usize, usize)> = label_to_indices[0].keys().copied().collect::<HashSet<_>>().symmetric_difference(&label_to_indices[1].keys().copied().collect::<HashSet<_>>()).copied().collect();
    let keys_in_both: HashSet<(usize, usize)> = label_to_indices[0].keys().copied().collect::<HashSet<_>>().intersection(&label_to_indices[1].keys().copied().collect::<HashSet<_>>()).copied().collect();

    let different_keys_in_both: Vec<(usize, usize)> = keys_in_both.into_iter().filter(|key| label_to_indices[0].get(&key).unwrap().len() != label_to_indices[1].get(&key).unwrap().len()).collect();

    // let num_per_count = from_fn::<Vec<((usize, usize), usize)>, 2, _>(|idx| count_ints(index_to_label[idx].values().copied().collect::<Vec<_>>()));
    let different_fingerprints: Vec<(usize, usize)> = keys_in_only_one.into_iter().chain(different_keys_in_both.into_iter()).collect();
    
    if different_fingerprints.len() != 0 {

        let mut prev_label_to_labels: HashMap<(usize, usize), HashSet<(usize, usize)>> = HashMap::new();
        for key in different_fingerprints.iter() {
            for idx in 0..n {
                if let Some(indices) = label_to_indices[idx].get(key) {
                    let prev_label = *prev_index_to_label[idx].get(&indices[0]).unwrap();
                    prev_label_to_labels.entry(prev_label).or_insert(HashSet::new()).insert(*key);
                }
            }
        }

        let different_fingerprints_no_roundnum: Vec<usize> = different_fingerprints.into_iter().map(|(_, val)| val).collect();

        println!("{:?}", prev_label_to_labels);
        println!("{:?}", different_fingerprints_no_roundnum);
        println!("{:?}", assignment.get_offset());
        for ((rn, old_hash), new_keys) in prev_label_to_labels.into_iter() {
            println!("---------------------------- {:?}: {:?}-------------------------", (rn, old_hash), new_keys);
            println!("old fingerprint {}: {:?}", old_hash, assignment.get_inv_assignment(old_hash));

            for (_, hash) in new_keys.into_iter() {
                println!("fingerprint {}: {:?}", hash, assignment.get_inv_assignment(hash));
            }
        }
        panic!("sanity check failed");
    }
}