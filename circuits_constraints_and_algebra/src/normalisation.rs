use std::collections::{HashSet, HashMap};
use itertools::Itertools;
use std::borrow::Cow;

use crate::num_bigint::BigInt;
use crate::modular_arithmetic::{add, div, ArithmeticError};

fn non_zero_sum_normalise<'a>(lineq: impl Iterator<Item = &'a BigInt>, prime: &'a BigInt) -> Result<BigInt, ArithmeticError> {
    
    let sum: BigInt = lineq.into_iter().fold(BigInt::from(0), |curr, next| add(&curr, next, prime));
    if sum == BigInt::from(0) {
        Err(ArithmeticError::DivisionByZero)
    } else {
        Ok(sum)
    }
}

pub fn division_normalise<'a>(_lineq: impl Iterator<Item = &'a BigInt>, prime: &'a BigInt, early_exit: bool) -> Vec<Cow<'a, BigInt>> {

    // If can early exit then do
    let lineq: Vec<&'a BigInt> = _lineq.collect();
    let ee_value: Option<BigInt> = if early_exit {non_zero_sum_normalise(lineq.iter().copied(), prime).ok()} else {None};

    if let Some(choice) = ee_value {
        [Cow::Owned(choice)].into_iter().collect()
    } else {

        let unique_lineq: Vec<&'a BigInt> = lineq.into_iter().collect::<HashSet<&'a BigInt>>().into_iter().collect();
        
        // If can early exit with unique then do

        let ee_value: Option<BigInt> = if early_exit {non_zero_sum_normalise(unique_lineq.iter().copied(), prime).ok()} else {None};
        if let Some(choice) = ee_value {
            [Cow::Owned(choice)].into_iter().collect()
        } else {

            fn find_next_subset<'a>(lineq: Vec<&'a BigInt>, prime: &'a BigInt) -> Vec<&'a BigInt> {

                let mut equiv_classes: HashMap<BigInt, Vec<usize>> = HashMap::new();

                for (l, r) in (0..lineq.len()).into_iter().cartesian_product((0..lineq.len()).into_iter()) {
                    equiv_classes.entry(div(lineq[l], lineq[r], prime).ok().expect("Value passed to lineq for divisionnorm is 0")).or_insert(Vec::new()).push(l);
                }

                let equiv_classes_vec = equiv_classes.into_iter().collect::<Vec<_>>();
                equiv_classes_vec.iter().min_by_key(|&(k, class)| (class.len(), k)).unwrap().1.iter().copied().map(|idx| lineq[idx]).collect()
            }

            let mut prev_length: usize = 0;
            let mut subset = unique_lineq;

            while prev_length != subset.len() {
                prev_length = subset.len();
                subset = find_next_subset(subset, prime);
            }

            // this ensures we can actually be early exiting -- performance loss is minimal as this is basically always <2 BigInts -- still annoying
            subset.into_iter().map(|val| Cow::Borrowed(val)).collect()
        }
    }
}