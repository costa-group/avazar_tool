use rustsat::instances::{SatInstance, ObjectVarManager};
use rustsat::types::{Clause, Lit, Var};
use rustsat::types::constraints::{PbConstraint};
use std::collections::{HashSet, HashMap};
use std::array::from_fn;
use thiserror::Error;

use circuits_and_constraints::constraint::Constraint;
use circuits_and_constraints::circuit::Circuit;

#[derive(Debug, Error)]
pub enum EncodingError {
    #[error("Some fingerprint class has different sizes")]
    FingerprintAssumptionError,
    #[error("Norm {0} in first circuit has no valid norm to pair")]
    NormHasNoValidPair(usize)
}

pub fn encode_comparison<C: Constraint, S: Circuit<C>>(
    normalised_constraints: &[&Vec<C>; 2],
    fingerprint_to_normi: &[HashMap<usize, Vec<usize>>; 2],
    fingerprint_to_signals: &[HashMap<usize, Vec<usize>>; 2],
    signal_to_fingerprint: &[HashMap<usize, usize>; 2]
) -> Result<SatInstance<ObjectVarManager>, EncodingError> {

    const N: usize = 2;

    // with rusts BorrowChecker there is no nice way to have multiple mutable semantically different accesses to a single struct, so we use a bool flag instead
    //    (true, [usize, 2]) indicates a norm pair i,j
    //    (false, [usize, 2]) indicates a signal pair i,j
    let mut formula = SatInstance::new_with_manager(ObjectVarManager::from_next_free(Var::new(0)));

    // testing that input sets are correct -- We assume that the Vec's are correctly NonEmpty
    let normi_keys_in_both = fingerprint_to_normi[0].keys().collect::<HashSet<&usize>>().intersection(&fingerprint_to_normi[1].keys().collect::<HashSet<&usize>>()).copied().collect::<Vec<&usize>>();
    if (0..N).into_iter().any(|idx| normi_keys_in_both.len() != fingerprint_to_normi[idx].len()) {return Err(EncodingError::FingerprintAssumptionError);}

    let signal_keys_in_both = fingerprint_to_signals[0].keys().collect::<HashSet<&usize>>().intersection(&fingerprint_to_signals[1].keys().collect::<HashSet<&usize>>()).copied().collect::<Vec<&usize>>();
    if (0..N).into_iter().any(|idx| signal_keys_in_both.len() != fingerprint_to_signals[idx].len()) {return Err(EncodingError::FingerprintAssumptionError);}

    for key in normi_keys_in_both.into_iter() {

        // if singular encode by singular, other encode generically
        if S::singular_class_requires_additional_constraints() && fingerprint_to_normi[0][key].len() == 1 {
            let is_ordered = normalised_constraints[0][fingerprint_to_normi[0][key][0]].is_ordered();
            let viable_pairs = S::encode_single_norm_pair(
                &from_fn::<_, 2, _>(|idx| &normalised_constraints[idx][fingerprint_to_normi[idx][key][0]]),
                is_ordered,
                formula.var_manager_mut(),
                fingerprint_to_signals,
                signal_to_fingerprint,
                true
            );

            if viable_pairs.len() == 0 {return Err(EncodingError::NormHasNoValidPair(fingerprint_to_normi[0][key][0]));}
            viable_pairs.into_iter().for_each(|clause| formula.add_clause(clause));
        } else {
            if let Err(error) = encode_single_norm_class::<C, S>(
                from_fn::<_, 2, _>(|idx| &fingerprint_to_normi[idx][key]),
                normalised_constraints,
                fingerprint_to_signals,
                signal_to_fingerprint,
                &mut formula
            ) {return Err(error);}
        }

    }

    // encode signal bijection
    for key in signal_keys_in_both.into_iter() {
        // if there bijection is forced, than add the unary lit to the formula
        if fingerprint_to_signals[0][key].len() == 1 {
            let lit = formula.var_manager_mut().object_var::<(bool, [usize;2])>((false, from_fn::<_, 2, _>(|idx| fingerprint_to_signals[idx][key][0]))).pos_lit();
            formula.add_unit(lit);
        }
        // otherwise encode the constraint as an equality
        else {
            for idx in 0..2 {
                for signal in fingerprint_to_signals[idx].get(&key).unwrap().into_iter().copied() {

                    let sat_variables: Vec<Lit> = fingerprint_to_signals[1-idx].get(&key).unwrap().into_iter().copied().map(|osignal| 
                        formula.var_manager_mut().object_var::<(bool, [usize;2])>((false, if idx == 0 {[signal, osignal]} else {[osignal, signal]})).pos_lit() //need arr to be in order of circuits
                    ).collect();

                    formula.add_pb_constr(PbConstraint::new_eq(sat_variables.into_iter().map(|sig| (sig, 1)), 1));
                }
            }
        }
    }

    Ok(formula)
}

fn encode_single_norm_class<C: Constraint, S: Circuit<C>>(
    class: [&Vec<usize>; 2],
    normalised_constraints: &[&Vec<C>; 2],
    fingerprint_to_signals: &[HashMap<usize, Vec<usize>>; 2],
    signal_to_fingerprint: &[HashMap<usize, usize>; 2],
    formula: &mut SatInstance<ObjectVarManager>
) -> Result<(), EncodingError> {

    let is_ordered = normalised_constraints[0][class[0][0]].is_ordered();

    for normi in class[0].into_iter().copied() {

        let mut normi_options = Clause::new();

        for normj in class[1].into_iter().copied() {

            // Get clauses implied by single-norm-pair
            let mut ij_clauses = S::encode_single_norm_pair(
                &[&normalised_constraints[0][normi], &normalised_constraints[1][normj]],
                is_ordered,
                formula.var_manager_mut(),
                fingerprint_to_signals,
                signal_to_fingerprint,
                false
            );

            // empty implies that pair is invalid
            if ij_clauses.len() == 0 {continue;}

            // add option variable to options and add as implication to each of the above clauses
            let sat_variable: Var = formula.var_manager_mut().object_var::<(bool, [usize;2])>((true, [normi, normj]));
            normi_options.add(sat_variable.pos_lit());

            ij_clauses.iter_mut().for_each(|clause| clause.add(sat_variable.neg_lit()));
            ij_clauses.into_iter().for_each(|clause| formula.add_clause(clause));
        }

        // empty implies that normi has no valid pairing
        if normi_options.len() == 0 {return Err(EncodingError::NormHasNoValidPair(normi));}
        else {formula.add_clause(normi_options);}
    }

    Ok(())
}