use circom_algebra::num_bigint::BigInt;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::cmp::Eq;
use std::fmt::Debug;
use std::borrow::{Cow};
use std::array::from_fn;
use rustsat::instances::ObjectVarManager;
use rustsat::types::Clause;
use itertools::Itertools;

use super::{ACIRConstraint};
use crate::constraint::Constraint;
use crate::normalisation::division_normalise;
use crate::utils::FingerprintIndex;
use circom_algebra::modular_arithmetic::{div};
use utils::assignment::Assignment;

impl Constraint for ACIRConstraint {

    fn normalise<'a>(&'a self, prime: &'a BigInt) -> Vec<Self> where Self: Sized {

        let factors: Vec<Cow<'a, BigInt>>;

        if self.constant.as_ref().is_some_and(|constant| *constant != BigInt::from(0)) {factors = vec![Cow::Borrowed(self.constant.as_ref().unwrap())];}
        else if self.mult.len() > 0 {factors = division_normalise(self.mult.values(), prime, true); }
        else {factors = division_normalise(self.linear.values(), prime, true);}

        factors.into_iter().map(|factor|
            ACIRConstraint {
                mult: self.mult.iter().map(|(k, v): (&_, &BigInt)| (*k, div(v, &factor, prime).ok().unwrap())).collect(),
                linear: self.linear.iter().map(|(k, v): (&_, &BigInt)| (*k, div(v, &factor, prime).ok().unwrap())).collect(),
                constant: self.constant.as_ref().map(|constant| div(constant, &factor, prime).ok().unwrap())
            }
        ).collect()
    }
    fn signals(&self) -> HashSet<usize> {self.linear.keys().copied().chain(self.mult.keys().flat_map(|&(l, r)| [l, r])).collect()}

    type Fingerprint<'a, T: Hash + Eq + Default + Copy + Ord + Debug> = (Vec<(FingerprintIndex<T>, (Vec<(FingerprintIndex<T>, &'a BigInt)>, Option<&'a BigInt>))>, Option<&'a BigInt>) where Self: 'a;

    fn fingerprint<'a, T: Hash + Eq + Default + Copy + Ord + Debug>(&'a self, fingerprint: &mut Option<Self::Fingerprint<'a, T>>, signal_to_fingerprint: &HashMap<usize, T>) -> () {

        // TODO: think about refactoring Circuit to have two distinct fingerprints and split this one in two -- hmm signal is still gonna look like the above tho

        if let Some(existing_fingerprint) = fingerprint.as_mut() {
            for item in existing_fingerprint.0.iter_mut() {
                item.0.fingerprint = signal_to_fingerprint[&item.0.index];
                for mult_item in item.1.0.iter_mut() {
                    mult_item.0.fingerprint = signal_to_fingerprint[&mult_item.0.index];
                }
                item.1.0.sort();
            }
            existing_fingerprint.0.sort();
        } else {

            type Characteristic<'a, T> = (Vec<(FingerprintIndex<T>, &'a BigInt)>, Option<&'a BigInt>);
            let mut new_fingerprint: HashMap<usize, Characteristic<T>> = HashMap::new();

            for signal in self.linear.keys() {new_fingerprint.insert(*signal, (Vec::new(), Some(&self.linear[signal])));}
            for key in self.mult.keys() { // assumes no duplicate keys (i.e. keys are sorted)
                let coef = &self.mult[key];
                let (lsig, rsig) = *key;

                let entry = new_fingerprint.entry(lsig).or_insert_with(|| (Vec::new(), None));
                entry.0.push((FingerprintIndex {fingerprint: signal_to_fingerprint[&rsig], index: rsig}, coef));
                let entry = new_fingerprint.entry(rsig).or_insert_with(|| (Vec::new(), None));
                entry.0.push((FingerprintIndex {fingerprint: signal_to_fingerprint[&lsig], index: lsig}, coef));
            }
            for value in new_fingerprint.values_mut() { value.0.sort(); }

            let mut new_fingerprint: Vec<(FingerprintIndex<T>, Characteristic<T>)> = 
                new_fingerprint.into_iter().map(|(sig, characteristic): (usize, Characteristic<T>)| (FingerprintIndex {fingerprint: signal_to_fingerprint[&sig], index: sig}, characteristic)).collect();
            new_fingerprint.sort();
            *fingerprint = Some((new_fingerprint, self.constant.as_ref()));
        }

    }
    fn fingerprint_signal<'a, T: Hash + Eq + Default + Copy + Ord + Debug>(
        signal: &usize, 
        fingerprint: &mut Option<Self::Fingerprint<'a, T>>,
        normalised_constraints: &'a Vec<Self>, 
        normalised_constraint_to_fingerprints: &HashMap<usize, T>, 
        prev_signal_to_fingerprint: &HashMap<usize, T>, 
        signal_to_normi: &HashMap<usize, Vec<usize>>
        ) -> () where Self: 'a + Sized {
        
        if let Some(existing_fingerprint) = fingerprint.as_mut() {
            for item in existing_fingerprint.0.iter_mut() {
                item.0.fingerprint = normalised_constraint_to_fingerprints[&item.0.index];
                for mult_item in item.1.0.iter_mut() {
                    mult_item.0.fingerprint = prev_signal_to_fingerprint.get(&mult_item.0.index).copied().unwrap_or_default();
                }
                item.1.0.sort();
            }
            existing_fingerprint.0.sort();
        } else {

            type Characteristic<'a, T> = (Vec<(FingerprintIndex<T>, &'a BigInt)>, Option<&'a BigInt>);
            let mut new_fingerprint: HashMap<usize, Characteristic<T>> = HashMap::new();

            for normi in signal_to_normi[signal].iter().copied() {
                let norm = &normalised_constraints[normi];
                let mut characteristic: Characteristic<T> = (
                    norm.mult.iter().filter(|&(&(lsig, rsig), _)| *signal == lsig || *signal == rsig).map(|(&(lkey, rkey), coef)| ({if lkey == *signal {rkey} else {lkey}}, coef)).map(
                        |(osig, coef)| (FingerprintIndex {fingerprint: prev_signal_to_fingerprint.get(&osig).copied().unwrap_or_default(), index: osig}, coef)).collect::<Vec<(FingerprintIndex<T>, &'a BigInt)>>(),
                    norm.linear.get(signal)
                );
                characteristic.0.sort();
                new_fingerprint.insert(normi, characteristic);
            }

            let mut new_fingerprint: Vec<(FingerprintIndex<T>, Characteristic<T>)> = 
                new_fingerprint.into_iter().map(|(normi, characteristic): (usize, Characteristic<T>)| (FingerprintIndex {fingerprint: normalised_constraint_to_fingerprints[&normi], index: normi}, characteristic)).collect();
            new_fingerprint.sort();
            *fingerprint = Some((new_fingerprint, None));
        }
    }
    
    fn is_nonlinear(&self) -> bool {self.mult.len() > 0}
    fn is_ordered(&self) -> bool {true} // irelevant
    fn singular_class_requires_additional_constraints() -> bool {true}

    fn encode_single_norm_pair(
        norms: &[&Self; 2],
        _is_ordered: bool,
        signal_pair_encoder: &mut ObjectVarManager,
        fingerprint_to_signals: &[HashMap<usize, Vec<usize>>; 2],
        signal_to_fingerprint: &[HashMap<usize, usize>; 2],
        is_singular_class: bool
    ) -> Vec<Clause> {
        // Worse encoding than in R1CS because of arbitrary signal-pairs... epxlodes for arbtirary polynomials very quickly
        //  each n-ary equivalence implies up to k-1 (n-1)-ary equivalences which are unordered and so on for O(kn) layers each of which takes... etc

        // options limited to those with same linear coeff and number + coefficient of nonlinear for this specific norm
        //     for every potential pair (a,b) from the above values
        //        if (a,b) match implies various other bi-implications based on the coefficients in their separate nonlinear pairs

        let mut inverse_nonlinear_part: [HashMap<usize, HashMap<&BigInt, Vec<usize>>>; 2] = [HashMap::new(), HashMap::new()];
        for (idx, norm) in norms.into_iter().enumerate() {
            for (&(l, r), v) in norm.mult.iter() {
                inverse_nonlinear_part[idx].entry(l).or_insert_with(|| HashMap::new()).entry(v).or_insert_with(|| Vec::new()).push(r);
                inverse_nonlinear_part[idx].entry(r).or_insert_with(|| HashMap::new()).entry(v).or_insert_with(|| Vec::new()).push(l);
            }
        }

        if is_singular_class {return encode_from_fingerprints(&inverse_nonlinear_part, signal_pair_encoder, fingerprint_to_signals, is_singular_class);}

        let curr_fingerprint_to_signals = fingerprint_signals_in_current_norms(norms, &inverse_nonlinear_part, signal_to_fingerprint);

        // If the fingerprints differ once restricted to the two norms then return an empty vec

        let fingerprints_in_both = curr_fingerprint_to_signals[0].keys().collect::<HashSet<&usize>>().intersection(&curr_fingerprint_to_signals[1].keys().collect::<HashSet<&usize>>()).copied().collect::<Vec<&usize>>();
        if (0..2).into_iter().any(|idx| fingerprints_in_both.len() != curr_fingerprint_to_signals[idx].len()) || fingerprints_in_both.into_iter().any(
            |key| curr_fingerprint_to_signals[0][key].len() != curr_fingerprint_to_signals[1][key].len()
        ) {return Vec::new();}

        encode_from_fingerprints(&inverse_nonlinear_part, signal_pair_encoder, &curr_fingerprint_to_signals, is_singular_class)
    }
}

fn fingerprint_signals_in_current_norms<'a>(
    norms: &[&'a ACIRConstraint; 2],
    inverse_nonlinear_part: &[HashMap<usize, HashMap<&'a BigInt, Vec<usize>>>; 2],
    signal_to_fingerprint: &[HashMap<usize, usize>; 2],
    ) -> [HashMap<usize, Vec<usize>>; 2] {

        let signals: [HashSet<usize>; 2] = from_fn(|idx| norms[idx].signals());

        type Hashable<'a> = (Option<&'a BigInt>, Vec<(usize, &'a BigInt)>);
        let get_hashable = |idx: usize, sig: &usize| -> Hashable<'a> {(
            norms[idx].linear.get(sig),
            inverse_nonlinear_part[idx].get(sig).into_iter().flatten().flat_map(|(key, osigs)| osigs.iter().map(|osig| (signal_to_fingerprint[idx][osig], *key) )).sorted().collect()
        )};

        let mut norm_pair_assignment = Assignment::<Hashable<'a>, 1>::new(0);
        let mut curr_fingerprint_to_signals: [HashMap<usize, Vec<usize>>; 2] = from_fn(|_| HashMap::new());
        let signal_hashables: [HashMap<usize, Hashable<'a>>; 2] = from_fn(|idx| signals[idx].iter().map(|sig| (*sig, get_hashable(idx, sig))).collect());

        for idx in 0..2 { for signal in signals[idx].iter() {
            let fingerprint = norm_pair_assignment.get_assignment([&signal_hashables[idx][signal]]);
            curr_fingerprint_to_signals[idx].entry(fingerprint).or_insert_with(|| Vec::new()).push(*signal);
        }}

        curr_fingerprint_to_signals
    }

fn encode_from_fingerprints(
        inverse_nonlinear_part: &[HashMap<usize, HashMap<&BigInt, Vec<usize>>>; 2], 
        signal_pair_encoder: &mut ObjectVarManager, 
        curr_fingerprint_to_signals: &[HashMap<usize, Vec<usize>>; 2],
        is_singular_class: bool
    ) -> Vec<Clause> {

        let mut clauses: Vec<Clause> = Vec::new();

        for fingerprint in curr_fingerprint_to_signals[0].keys() {for idx in 0..2 { for signal in curr_fingerprint_to_signals[idx][fingerprint].iter() {

            if !is_singular_class {
                // if the class isn't singular then the fingerprints have been refined and the at least one must be added to the clauses
                //      otherwise the fingerprints are unrefined and the at least one is covered in the bijection encoding elsewhere
                clauses.push(Clause::from_iter(
                    curr_fingerprint_to_signals[1-idx][fingerprint].iter().copied().map(|osig| 
                        signal_pair_encoder.object_var::<(bool, [usize; 2])>((false, if idx == 0 {[*signal, osig]} else {[osig, *signal]})).pos_lit()
                    )
                ))
            }

            // auxiliary constraints dependent on mult pairings
            if inverse_nonlinear_part[idx].contains_key(signal) {
                for osig in curr_fingerprint_to_signals[1-idx][fingerprint].iter().copied() {
                    // correctness clauses
                    //   for every pair (lsig, rsig) of potential signals (by fingerprint)
                    //     each other sig in mult paired with lsig and corresponding val v is mapped to at least one such osig for rsig and vice versa
                    
                    let sigs = if idx == 0 {[*signal, osig]} else {[osig, *signal]};
                    let pair_assignment = signal_pair_encoder.object_var::<(bool, [usize; 2])>((false, sigs.clone())).neg_lit();

                    for jdx in 0..2 {for coef in inverse_nonlinear_part[jdx][&sigs[jdx]].keys() {for lopt in inverse_nonlinear_part[jdx][&sigs[jdx]][coef].iter().copied() {
                        clauses.push(Clause::from_iter(
                            // coef always present due to sigs having the same fingerprint
                            inverse_nonlinear_part[1-jdx][&sigs[1-jdx]][coef].iter().map(
                                |&ropt| signal_pair_encoder.object_var::<(bool, [usize; 2])>((false, if jdx == 0 {[lopt, ropt]} else {[ropt, lopt]})).pos_lit()
                            ).chain([pair_assignment])
                        ))                        
                    }}}
            }}
        }}}

        clauses
    }