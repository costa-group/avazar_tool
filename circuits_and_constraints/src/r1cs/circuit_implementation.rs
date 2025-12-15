use circom_algebra::num_bigint::BigInt;
use rustsat::instances::ObjectVarManager;
use rustsat::types::{Clause};
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::cmp::Eq;
use std::array::from_fn;
use itertools::{Itertools};
use rand::seq::SliceRandom;
use rand::Rng;
use std::fmt::Debug;

use utils::read_r1cs::read_r1cs;
use super::{R1CSConstraint, R1CSData, SignalList, HeaderData};
use crate::circuit::Circuit;
use crate::constraint::Constraint;

#[derive(Hash, PartialEq, Eq, Debug, Ord, PartialOrd)]
enum PairKey<T: Hash + Eq + Ord> {
    One(T),
    Two(T, T)
}

impl Circuit<R1CSConstraint> for R1CSData {
    
    fn new() -> Self {
        Self::new()
    }

    fn prime(&self) -> &BigInt {&self.header_data.field}
    fn n_constraints(&self) -> usize {self.header_data.number_of_constraints}
    fn n_wires(&self) -> usize {self.header_data.total_wires}
    
    
    fn get_constraints(&self) -> &Vec<R1CSConstraint> {&self.constraints}
    fn get_mut_constraints(&mut self) -> &mut Vec<R1CSConstraint> {&mut self.constraints}

    fn normi_to_coni(&self) -> &Vec<usize> {unimplemented!("This function is not implemented yet")}
    fn n_inputs(&self) -> usize {self.header_data.public_inputs + self.header_data.private_inputs}
    fn n_outputs(&self) -> usize {self.header_data.public_outputs}
    fn signal_is_input(&self, signal: usize) -> bool {self.header_data.public_outputs < signal && signal <= self.header_data.public_inputs + self.header_data.private_inputs + self.header_data.public_outputs} 
    fn signal_is_output(&self, signal: usize) -> bool {0 < signal && signal <= self.header_data.public_outputs}
    fn get_signals(&self) -> impl Iterator<Item = usize> {1..self.header_data.total_wires}
    fn get_input_signals(&self) -> impl Iterator<Item = usize> {self.header_data.public_outputs+1..=self.header_data.public_inputs + self.header_data.private_inputs + self.header_data.public_outputs}
    fn get_output_signals(&self) -> impl Iterator<Item = usize> {1..=self.header_data.public_outputs}
    fn parse_file(&mut self, file: &str) -> () {
        let parsed_circuit = read_r1cs(file).unwrap();

        self.header_data = parsed_circuit.header_data;
        self.constraints = parsed_circuit.constraints;
        self.signals = parsed_circuit.signals;
        // self.custom_gates = parsed_circuit.custom_gates;
        // self.custom_gates_used_data = parsed_circuit.custom_gates_used_data;
        // self.custom_gates_applied_data = parsed_circuit.custom_gates_applied_data;

    }
    
    fn take_subcircuit(
        &self, 
        constraint_subset: &Vec<usize>, 
        input_signals: Option<&HashSet<usize>>, 
        output_signals: Option<&HashSet<usize>>, 
        signal_map: Option<&HashMap<usize,usize>>, 
        _return_signal_mapping: Option<bool> // TODO: implement in the mapping overhoal
    ) -> R1CSData {
        // Assumes correct inputs

        // more annoying type-checking stuff
        let signal_mapping_: HashMap<usize, usize>;
        let signal_mapping: &HashMap<usize, usize>;

        let n_inputs: usize;
        let n_outputs: usize;

        // Construct the mapping
        if signal_map.is_none() {
            // construct from input/output_signals

            let (inputs, outputs) = (input_signals.unwrap(), output_signals.unwrap());

            if inputs.intersection(outputs).count() > 0 {panic!("Gave overlapping input/output to take_subcircuit");}

            signal_mapping_ = outputs.iter().copied().chain(inputs.iter().copied()).chain(
                constraint_subset.into_iter().flat_map(|cons| self.constraints[*cons].signals().into_iter()).collect::<HashSet<_>>().difference(&outputs.iter().chain(inputs.iter()).copied().collect::<HashSet<_>>()).copied()
            ).enumerate().map(|(idx, val)| (val, idx+1)).collect();

            n_inputs = inputs.len();
            n_outputs = outputs.len();

            signal_mapping = &signal_mapping_;
        } else {

            signal_mapping = signal_map.unwrap();

            n_inputs = self.get_input_signals().filter(|sig| signal_mapping.get(sig).is_some()).count();
            n_outputs = self.get_output_signals().filter(|sig| signal_mapping.get(sig).is_some()).count();

        }

        let new_constraintlist = constraint_subset.into_iter().copied().map(|normi| &self.constraints[normi]).map(|con|
            (con.0.iter().map(|(key, val)| (if key == &0 {0} else {signal_mapping[key]}, val.clone())).collect::<HashMap<usize, BigInt>>(),
            con.1.iter().map(|(key, val)| (if key == &0 {0} else {signal_mapping[key]}, val.clone())).collect::<HashMap<usize, BigInt>>(),
            con.2.iter().map(|(key, val)| (if key == &0 {0} else {signal_mapping[key]}, val.clone())).collect::<HashMap<usize, BigInt>>())
        ).collect::<Vec<R1CSConstraint>>();

        R1CSData::from(
            self.prime().clone(), 0, signal_mapping.len() + 1,
            n_outputs, n_inputs, 0, 0,
            new_constraintlist.len(),
            new_constraintlist,
            SignalList::new(),
            false, None, None
        ) 
    }
    
    fn singular_class_requires_additional_constraints() -> bool {false}

    fn encode_single_norm_pair(
        norms: &[&R1CSConstraint; 2],
        is_ordered: bool,
        variable_manager: &mut ObjectVarManager,
        fingerprint_to_signals: &[HashMap<usize, Vec<usize>>; 2],
        signal_to_fingerprint: &[HashMap<usize, usize>; 2],
        _is_singular_class: bool
    ) -> Vec<Clause> {

        let dicts: [[&HashMap<usize, BigInt>; 3];2] = from_fn::<_, 2, _>(|idx| [&norms[idx].0, &norms[idx].1, &norms[idx].2]);
        let allkeys = from_fn::<_, 2, _>(|idx| norms[idx].signals());

        let (app, inv) = if is_ordered {_compare_norms_with_ordered_parts(&dicts, &allkeys)} else {_compare_norms_with_unordered_parts(&dicts, &allkeys)};

        let mut clauses: Vec<Clause> = Vec::new();
        for j in 0..3 {if !inv[0][j].keys().sorted().eq(inv[1][j].keys().sorted()) {return clauses}}

        fn _get_value_for_key<'a>(dicts: &[[&'a HashMap<usize, BigInt>; 3];2], is_ordered: bool, i: usize, j: usize, key: &usize) -> PairKey<&'a BigInt> {
            if is_ordered || j == 2 {return PairKey::One(dicts[i][j].get(key).unwrap());}
            let (smallint, bigint) = sort_pair_bigint(dicts[i][0].get(key), dicts[i][1].get(key));
            if j == 0 {
                PairKey::Two(smallint.unwrap(), bigint.unwrap())
            } else {
                PairKey::One(bigint.unwrap()) // None <= Some(T)
            }
        }

        for i in 0..2 {
            for key in allkeys[i].iter() {
                
                // get all signals that are in the intersection of all inv -- i.e. those that have the same value in each part key appears in -- bidirection means that not enforcing non-appearance doesn't matter but does extend enconding I guess... TODO
                let mut compatible_by_inv = app[i][key].iter().copied().map(|j| inv[1-i][j][&_get_value_for_key(&dicts, is_ordered, i, j, key)].iter().copied().collect::<HashSet<usize>>() );
                let first_set = compatible_by_inv.next().unwrap();
                let compatible_by_all_inv = compatible_by_inv.fold(first_set, |acc, hs| &acc & &hs);

                // ensure that they also have the same fingerprint
                let dummy: Vec<usize> = Vec::new(); // annoying type matching stuff
                let oset: HashSet<usize> = &compatible_by_all_inv | &(fingerprint_to_signals[1-i].get(&signal_to_fingerprint[i][key]).unwrap_or_else(|| &dummy).into_iter().copied().collect::<HashSet<usize>>());

                // this means signal has not viable pair and hence norm pair is invalid
                if oset.len() == 0 {return Vec::new();}

                // collect into clause and push to clauses vec
                clauses.push(Clause::from_iter(oset.into_iter().map( |osig| variable_manager.object_var::<(bool, [usize; 2])>((false, if i == 0 {[*key, osig]} else {[osig, *key]})).pos_lit())));
            }
        }

        clauses
    }

    fn shuffle_signals(self, rng: &mut impl Rng) -> Self {
        let mut outputs: Vec<usize> = self.get_output_signals().into_iter().collect();
        let mut inputs: Vec<usize> = self.get_input_signals().into_iter().collect();
        let mut remaining: Vec<usize> = (self.n_outputs() + self.n_inputs() + 1..self.n_wires()).into_iter().collect();
    
        outputs.shuffle(rng);
        inputs.shuffle(rng);
        remaining.shuffle(rng);
    
        let mapping: Vec<usize> = [0].into_iter().chain(outputs.into_iter()).chain(inputs.into_iter()).chain(remaining.into_iter()).collect();

        // constructing new constraint lists needs to consume the current one and for that we need to consume Self -- this avoids cloning a whole bunch of BigInts
        let Self {header_data, constraints, signals, ..} = self;
        let HeaderData {field, field_size, total_wires, public_outputs, public_inputs, private_inputs, number_of_labels, number_of_constraints } = header_data;

        let new_constraints = constraints.into_iter().map(|cons|
            (cons.0.into_iter().map(|(k, val)| (mapping[k], val)).collect::<HashMap<usize, BigInt>>(),
             cons.1.into_iter().map(|(k, val)| (mapping[k], val)).collect::<HashMap<usize, BigInt>>(),
             cons.2.into_iter().map(|(k, val)| (mapping[k], val)).collect::<HashMap<usize, BigInt>>())
        ).collect::<Vec<R1CSConstraint>>();

        R1CSData::from(
            field,
            field_size,
            total_wires,
            public_outputs,
            public_inputs,
            private_inputs,
            number_of_labels,
            number_of_constraints,
            new_constraints,
            signals,
            false,
            None,
            None
        )
    }
}

fn sort_pair_bigint<'a>(left: Option<&'a BigInt>, right: Option<&'a BigInt>) -> (Option<&'a BigInt>, Option<&'a BigInt>) {if left <= right {(left, right)} else {(right, left)}}

fn _compare_norms_with_unordered_parts<'a>(dicts: &[[&'a HashMap<usize, BigInt>; 3];2], allkeys: &[HashSet<usize>; 2]
) -> ([HashMap<usize, Vec<usize>>;2], [[HashMap<PairKey<&'a BigInt>, Vec<usize>>; 3];2]) {
    // # inv[Ci][I][value] = set({keys in Ci with value I})
    // #   if I == 0, key in both A, B, if I == 1, key in A xor B, if I == 2, key in C
    let mut inv: [[HashMap<PairKey<&BigInt>, Vec<usize>>; 3];2] = from_fn::<_, 2, _>(|_|
        from_fn::<_, 3, _>(|_| HashMap::new())
    );

    // # app[Ci][key] = [I for key appearance in Ci]
    // #   if I == 0, key in both A, B, if I == 1, key in A xor B, if I == 2, key in C  
    let mut app: [HashMap<usize, Vec<usize>>;2] = from_fn::<_, 2, _>(|_| HashMap::new());

    for i in 0..2 {
        for key in allkeys[i].iter() {

            let idx_val = (0..2).into_iter().filter(|j| dicts[i][*j].contains_key(key)).map(|j| j + 1).sum();
            let in_c = dicts[i][2].contains_key(key);

            // fills in app
            if idx_val != 0 {app[i].entry(*key).or_insert_with(|| Vec::new()).push(if idx_val == 3 {0} else {1});}
            if in_c {app[i].entry(*key).or_insert_with(|| Vec::new()).push(2);}

            // fills in inv
            match idx_val {
                0 => (),
                3 => {
                    let (smallint, bigint) = sort_pair_bigint(dicts[i][0].get(key), dicts[i][1].get(key));
                    inv[i][0].entry(PairKey::Two(smallint.unwrap(), bigint.unwrap())).or_insert_with(|| Vec::new()).push(*key);
                }
                _ => {inv[i][1].entry(PairKey::One(dicts[i][idx_val-1].get(key).unwrap())).or_insert_with(|| Vec::new()).push(*key);}
            }

            if in_c {inv[i][2].entry(PairKey::One(dicts[i][2].get(key).unwrap())).or_insert_with(|| Vec::new()).push(*key);}
        }
    }
    (app, inv)
}

fn _compare_norms_with_ordered_parts<'a>(dicts: &[[&'a HashMap<usize, BigInt>; 3];2], _allkeys: &[HashSet<usize>; 2]
) -> ([HashMap<usize, Vec<usize>>;2], [[HashMap<PairKey<&'a BigInt>, Vec<usize>>; 3];2]) {

    // # inv[Ci][part][value] = set({keys in Ci with value in Ci.part})
    // inv = list(map(lambda _ : list(map(lambda _ : dict(), range(3))), range(2)))
    let mut inv: [[HashMap<PairKey<&BigInt>, Vec<usize>>; 3];2] = from_fn::<_, 2, _>(|_|
        from_fn::<_, 3, _>(|_| HashMap::new())
    );

    
    // # app[Ci][key] = [parts in Ci that key appears in]
    // app = list(map(lambda _ : dict(), range(2)))
    let mut app: [HashMap<usize, Vec<usize>>;2] = from_fn::<_, 2, _>(|_| HashMap::new());

    for (i, j) in (0..2).into_iter().cartesian_product((0..3).into_iter()) {
        let part = dicts[i][j];
        for key in part.keys().copied() {
            if key == 0 {continue}
            inv[i][j].entry(PairKey::One(&part[&key])).or_insert_with(|| Vec::new()).push(key);
            app[i].entry(key).or_insert_with(|| Vec::new()).push(j);
        }
    }

    (app, inv)
}