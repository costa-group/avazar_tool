use circom_algebra::num_bigint::BigInt;
use std::collections::{HashSet, HashMap};
use std::hash::Hash;
use std::cmp::Eq;
use rand::Rng;
use std::array::from_fn;
use itertools::Itertools;
use std::mem::swap;
use std::fmt::Debug;
use std::borrow::Cow;
use rustsat::instances::ObjectVarManager;
use rustsat::types::{Clause};

use super::{R1CSConstraint};
use crate::constraint::{Constraint, ShuffleConstraint};
use crate::normalisation::division_normalise;
use circom_algebra::modular_arithmetic::{mul, div};
use crate::utils::FingerprintIndex;

impl Constraint for R1CSConstraint {

    fn normalise<'a>(&'a self, prime: &'a BigInt) -> Vec<R1CSConstraint> {

        // first normalise the quadratic term if there is one
        let mut choices_ab: Vec<(Cow<'_, BigInt>, Cow<'_, BigInt>)> = Vec::new();
        let choices_a: Vec<Cow<'a, BigInt>>;
        let choices_b: Vec<Cow<'a, BigInt>>;

        if self.is_nonlinear() {
            choices_a = self.0.get(&0).map(|bigint| vec![Cow::Borrowed(bigint)]).unwrap_or_else(|| division_normalise( self.0.values(), prime, true ) );
            choices_b = self.1.get(&0).map(|bigint| vec![Cow::Borrowed(bigint)]).unwrap_or_else(|| division_normalise( self.1.values(), prime, true ) );
        
            choices_ab.extend(choices_a.into_iter().cartesian_product(choices_b.into_iter()));
        }

        // now collect the choices for AB with the choices for C
        let big_one = BigInt::from(1);
        let choices: Vec<((Cow<'_, BigInt>, Cow<'_, BigInt>), Cow<'_, BigInt>)>;
        let choices_c: Vec<Cow<'a, BigInt>>;

        // if C has a constant normalise by that
        if let Some(c_constant) = self.2.get(&0) {
            if choices_ab.len() == 0 {choices_ab.push((Cow::Borrowed(&big_one), Cow::Borrowed(&big_one)))}
            choices = choices_ab.into_iter().cartesian_product([Cow::Borrowed(c_constant)].into_iter()).collect();

        // Otherwise if there are no AB choices normalise by C division norm
        } else if choices_ab.len() == 0 {
            choices_ab.push((Cow::Borrowed(&big_one), Cow::Borrowed(&big_one)));
            choices_c = division_normalise( self.2.values(), prime, true );
            choices = choices_ab.into_iter().cartesian_product(choices_c.into_iter()).collect();
        // Otherwise if there are AB choices, normalise by this and calculate the appropriate c_factor
        } else {
            choices_c = choices_ab.iter().map(|(l, r)| Cow::Owned(mul(&l, &r, prime))).collect();
            choices = choices_ab.into_iter().zip(choices_c.into_iter()).collect();
        }

        choices.into_iter().map(|((a_factor, b_factor), c_factor)| {
            let nonlinear_part_a = self.0.keys().map(|sig| (*sig, div(self.0.get(sig).unwrap(), &a_factor, prime).ok().unwrap()) ).collect::<HashMap<usize, BigInt>>();
            let nonlinear_part_b = self.1.keys().map(|sig| (*sig, div(self.1.get(sig).unwrap(), &b_factor, prime).ok().unwrap()) ).collect::<HashMap<usize, BigInt>>();
            let nonlinear_part_c = self.2.keys().map(|sig| (*sig, div(self.2.get(sig).unwrap(), &c_factor, prime).ok().unwrap()) ).collect::<HashMap<usize, BigInt>>();
            if nonlinear_part_a.values().sorted().cmp(nonlinear_part_b.values().sorted()).is_gt() {
                (nonlinear_part_b, nonlinear_part_a, nonlinear_part_c)
            } else {
                (nonlinear_part_a, nonlinear_part_b, nonlinear_part_c)
            }
        }).collect()
    }

    fn signals(&self) -> HashSet<usize>{
        self.0.keys().chain(self.1.keys()).chain(self.2.keys()).filter(|signal| **signal != 0).copied().collect() //probably quite ugly
    }

    type Fingerprint<'a, T: Hash + Eq + Default + Copy + Ord + Debug> = Vec<(FingerprintIndex<T>, ((Option<&'a BigInt>, Option<&'a BigInt>), Option<&'a BigInt>, Option<&'a BigInt>))>  where Self: 'a;

    fn fingerprint<'a, T: Hash + Eq + Default + Copy + Ord + Debug>(&'a self, fingerprint: &mut Option<Self::Fingerprint<'a, T>>, signal_to_fingerprint: &HashMap<usize, T>) -> () {

        fn _get_signal_fingerprint<T: Hash + Eq + Default + Copy>(sig: &usize, signal_to_fingerprint: &HashMap<usize, T>) -> T {
                if sig == &0 {T::default()} else {*signal_to_fingerprint.get(sig).unwrap()}
            }

        if let Some(existing_fingerprint) = fingerprint.as_mut() {
            for item in existing_fingerprint.into_iter() {
                item.0.fingerprint = _get_signal_fingerprint(&item.0.index, signal_to_fingerprint);
            }
            existing_fingerprint.sort();
        } else {

            type Characteristic<'a> = ((Option<&'a BigInt>, Option<&'a BigInt>), Option<&'a BigInt>, Option<&'a BigInt>);
            let mut new_fingerprint: HashMap<usize, Characteristic> = HashMap::new();

            for key in self.2.keys() {new_fingerprint.entry(*key).or_insert_with(|| Characteristic::default()).2 = self.2.get(key);}

            if self.is_ordered() {
                for key in self.0.keys() {new_fingerprint.entry(*key).or_insert_with(|| Characteristic::default()).0.0 = self.0.get(key);}
                for key in self.1.keys() {new_fingerprint.entry(*key).or_insert_with(|| Characteristic::default()).1 = self.1.get(key);}
            } else {

                let (lsignals, rsignals) = (self.0.keys().copied().collect::<HashSet<_>>(), self.1.keys().copied().collect::<HashSet<_>>());

                let in_both = lsignals.intersection(&rsignals).copied().collect::<HashSet<_>>();
                let (only_left, only_right) = (lsignals.difference(&in_both), rsignals.difference(&in_both));

                let sort_pair_bigint = |left: Option<&'a BigInt>, right: Option<&'a BigInt>| if left <= right {(left, right)} else {(right, left)};

                for key in in_both.iter().copied() {
                    new_fingerprint.entry(key).or_insert_with(|| Characteristic::default()).0 = sort_pair_bigint(self.0.get(&key), self.1.get(&key));}
                for (key, bigint) in only_left.map(|sig| (sig, self.0.get(sig))).chain(only_right.map(|sig| (sig, self.1.get(sig)))) {
                    new_fingerprint.entry(*key).or_insert_with(|| Characteristic::default()).1 = bigint;
                }
            }

            let mut new_fingerprint: Vec<(FingerprintIndex<T>, Characteristic)> = 
                new_fingerprint.into_iter().map(|(sig, characteristic): (usize, Characteristic)| (FingerprintIndex {fingerprint: _get_signal_fingerprint(&sig, signal_to_fingerprint), index: sig}, characteristic)).collect();
            new_fingerprint.sort();
            *fingerprint = Some(new_fingerprint);
        }
    }

    fn fingerprint_signal<'a, T: Hash + Eq + Default + Copy + Ord + Debug>(
        signal: &usize,
        fingerprint: &mut Option<Self::Fingerprint<'a, T>>, 
        normalised_constraints: &'a Vec<Self>, 
        normalised_constraint_to_fingerprints: &HashMap<usize, T>, 
        _prev_signal_to_fingerprint: &HashMap<usize, T>, 
        signal_to_normi: &HashMap<usize, Vec<usize>>
    ) -> () where Self: 'a + Sized {

        if let Some(existing_fingerprint) = fingerprint.as_mut() {
            for item in existing_fingerprint.into_iter() {
                item.0.fingerprint = *normalised_constraint_to_fingerprints.get(&item.0.index).unwrap();
            }
            existing_fingerprint.sort();
        } else {

            
            let mut new_fingerprint = Vec::new();

            for normi in signal_to_normi.get(signal).unwrap().into_iter().copied() {

                let fi_index = FingerprintIndex { fingerprint: *normalised_constraint_to_fingerprints.get(&normi).unwrap(), index: normi };
                let norm = &normalised_constraints[normi];
                let is_ordered: bool = norm.is_ordered();
                // tuples don't play nice with iterables
                let (a_val, b_val, c_val): (Option<&'a BigInt>, Option<&'a BigInt>, Option<&'a BigInt>) = (norm.0.get(signal), norm.1.get(signal), norm.2.get(signal));

                if is_ordered {
                    new_fingerprint.push(
                        (fi_index, ((a_val, None), b_val, c_val))
                    );
                } else {
                    let first_term: (Option<&'a BigInt>, Option<&'a BigInt>);
                    let second_term: Option<&'a BigInt>;

                    if a_val.is_some() && b_val.is_some() {
                        first_term = sort_pair_bigint(a_val, b_val);
                        second_term = None;
                    } else {
                        first_term = (None, None);
                        if a_val.is_some() {
                            second_term = a_val;
                        } else {
                            second_term = b_val;
                        }  
                    } 

                    new_fingerprint.push(
                        (fi_index, (first_term,second_term,c_val))
                    );
                }
            }

            new_fingerprint.sort();
            *fingerprint = Some(new_fingerprint);
        }
    }

    fn is_nonlinear(&self) -> bool{
        self.0.len() > 0 && self.1.len() > 0
    }

    fn is_ordered(&self) -> bool {!(self.0.len() > 0 && self.1.len() > 0 && self.0.values().sorted().eq(self.1.values().sorted()))}
    fn is_bridge_constraint(&self, prime: &BigInt, strict: bool) -> bool {
        !self.is_nonlinear() && self.2.len() == 2 && self.2.values().sum::<BigInt>() == *prime && (!strict || self.2.values().any(|coef| *coef == BigInt::from(1)))
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
}

impl ShuffleConstraint for R1CSConstraint {
    fn add_random_constant_factor(&mut self, rng: &mut impl Rng, field: &BigInt) -> () {
        let factors: [u64; 2] = from_fn(|_| rng.random::<u32>() as u64);
    
        let a_bigfactor = &BigInt::from(factors[0]);
        let b_bigfactor = &BigInt::from(factors[1]);
        let c_bigfactor = &BigInt::from(factors[0] * factors[1]);

        for (bigint, big_factor) in self.0.values_mut().map(|bigint| (bigint, a_bigfactor)).chain(
                                    self.1.values_mut().map(|bigint| (bigint, b_bigfactor))).chain(
                                    self.2.values_mut().map(|bigint| (bigint, c_bigfactor))) 
            {*bigint = mul(big_factor, bigint, field)}
    }

    fn shuffle_constraint_internals(&mut self, rng: &mut impl Rng) -> () {
        // HashMap is already unordered so no need to shuffle there

        // Swap A/B parts at random
        if rng.random::<bool>() {
            swap(&mut self.0, &mut self.1);
        }
    }
}

#[derive(Hash, PartialEq, Eq, Debug, Ord, PartialOrd)]
enum PairKey<T: Hash + Eq + Ord> {
    One(T),
    Two(T, T)
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