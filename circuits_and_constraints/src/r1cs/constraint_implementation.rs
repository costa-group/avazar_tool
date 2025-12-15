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

use super::{R1CSConstraint};
use crate::constraint::{Constraint};
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

    fn is_nonlinear(&self) -> bool{
        self.0.len() > 0 && self.1.len() > 0
    }
    fn get_coefficients(&self) -> impl Hash + Eq{
        unimplemented!("This function is not implemented yet")
    }

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

    fn is_ordered(&self) -> bool {!(self.0.len() > 0 && self.1.len() > 0 && self.0.values().sorted().eq(self.1.values().sorted()))}

}