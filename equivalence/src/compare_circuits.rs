use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::cmp::Eq;
use std::array::from_fn;
use std::time::{Instant, Duration};
use thiserror::Error;
use rustsat::solvers::{Solve, SolverResult};

use circuits_and_constraints::constraint::Constraint;
use circuits_and_constraints::circuit::Circuit;
use circuits_and_constraints::utils::{signals_to_constraints_with_them};

use crate::encoding::{EncodingError, encode_comparison};
use crate::fingerprinting::{iterated_refinement};

#[derive(Debug, Error)]
pub enum AssumptionError {
    #[error("Circuits had different num constraints: {0} {1}")]
    DifferentNumConstraints(usize, usize),
    #[error("Circuits had different num signals: {0} {1}")]
    DifferentNumSignals(usize, usize),
    #[error("Circuits had different num norms: {0} {1}")]
    DifferentNumNorms(usize, usize)
}

#[derive(Debug, Error)]
pub enum FingerprintError {
    #[error("Circuits had {1} classes for {0}s unique to one circuit")]
    DifferentFingerprints(&'static str, usize),
    #[error("Circuits had {1} classes for {0}s with differently sized classes")]
    DifferentFingerprintClasses(&'static str, usize)
}

#[derive(Debug, Error)]
pub enum NonequivalentReason {
    #[error("Discrepancy with Input Assumption: {0}")]
    Ass(#[source] AssumptionError),
    #[error("Error with Fingerprinting Result: {0}")]
    Fin(#[source] FingerprintError),
    #[error("Error during Encoding: {0}")]
    Enc(#[source] EncodingError),
    #[error("Error during Encoding: {0}")]
    Other(#[source] anyhow::Error),
    #[error("Equivalence encoded found unsatisfiable")] //TODO: maybe include unsat core but likely unhelpful
    Unsatisfiable
}

#[derive(Debug, Default)]
pub struct ComparisonData {
    pub result: bool,
    pub reason: Option<NonequivalentReason>,
    pub timing: HashMap<&'static str, Duration>,
    pub norm_mapping: Option<Vec<usize>>,
    pub sig_mapping: Option<Vec<usize>>
}

pub fn compare_circuits<C: Constraint, S: Circuit<C>>(circuits: &[&S; 2], debug: bool) -> ComparisonData {compare_circuits_with_inits(circuits, None, None, None, None, debug)}

pub fn compare_circuits_with_inits<C: Constraint, S: Circuit<C>>(
    circuits: &[&S; 2],
    input_normalised_constraints: Option<&[&Vec<C>; 2]>,
    input_signals_to_normi: Option<&[&HashMap<usize, Vec<usize>>; 2]>,
    input_fingerprint_to_normi: Option<&[&HashMap<usize, Vec<usize>>; 2]>,
    input_fingerprint_to_signal: Option<&[&HashMap<usize, Vec<usize>>; 2]>,
    debug: bool
) -> ComparisonData {

    fn get_with_error(err: NonequivalentReason, timing: HashMap<&'static str, Duration>) -> ComparisonData {ComparisonData {result: false, reason: Some(err), timing: timing, norm_mapping: None, sig_mapping: None}}
    fn insert_and_print_timing(debug: bool, timing: &mut HashMap<&'static str, Duration>, key: &'static str, val: Duration) {timing.insert(key, val);if debug {println!("Completed {}: {:?}", key, timing.get(&key));}}

    let mut timing: HashMap<&'static str, Duration> = HashMap::new();

    // ########### PREPROCESSING #############
    let preprocessing_timer = Instant::now();

    // Bit ugly but only want to actually do the calculation in the case that the input is None
    let _normalised_constraints: [Vec<C>; 2] = from_fn(|idx| if input_normalised_constraints.is_none() {circuits[idx].normalise_constraints()} else {Vec::new()});
    let _normalised_constraints_refs: [&Vec<C>; 2] = from_fn(|idx| &_normalised_constraints[idx]);
    let normalised_constraints: &[&Vec<C>; 2] = input_normalised_constraints.unwrap_or(&_normalised_constraints_refs);

    let _signals_to_normi: [HashMap<usize, Vec<usize>>; 2] = from_fn(|idx| if input_signals_to_normi.is_none() {signals_to_constraints_with_them(&normalised_constraints[idx], None, None)} else {HashMap::new()} );
    let _signals_to_normi_refs = from_fn(|idx| &_signals_to_normi[idx]);
    let signals_to_normi = input_signals_to_normi.unwrap_or(&_signals_to_normi_refs);

    for (lval, rval, reason) in [
        (circuits[0].n_wires(), circuits[1].n_wires(), AssumptionError::DifferentNumSignals(circuits[0].n_wires(), circuits[1].n_wires())), 
        (circuits[0].n_constraints(), circuits[1].n_constraints(), AssumptionError::DifferentNumConstraints(circuits[0].n_constraints(), circuits[1].n_constraints())), 
        (normalised_constraints[0].len(), normalised_constraints[1].len(), AssumptionError::DifferentNumNorms(normalised_constraints[0].len(), normalised_constraints[1].len()))] {
        if lval != rval {return get_with_error(NonequivalentReason::Ass(reason), timing); }
    }

    let _init_fingerprint_to_normi: [HashMap<usize, Vec<usize>>; 2] = from_fn(|idx| if input_fingerprint_to_normi.is_none() {[(1, (0..normalised_constraints[idx].len()).into_iter().collect())].into_iter().collect()} else {HashMap::new()});
    let _init_fingerprint_to_normi_refs = from_fn(|idx| &_init_fingerprint_to_normi[idx]);
    let init_fingerprints_to_normi = input_fingerprint_to_normi.unwrap_or(&_init_fingerprint_to_normi_refs);

    let _init_fingerprint_to_signals: [HashMap<usize, Vec<usize>>; 2] = from_fn(|idx|
        if input_fingerprint_to_signal.is_none() {
            [(1, circuits[idx].get_output_signals().into_iter().collect()),
            (2, circuits[idx].get_input_signals().into_iter().collect()),
            (3, circuits[idx].get_signals().filter(|&sig| !circuits[idx].signal_is_input(sig) && !circuits[idx].signal_is_output(sig)).collect())
            ].into_iter().collect()
        } else {
            HashMap::new()
        }
    );
    let _init_fingerprint_to_signals_refs = from_fn(|idx| &_init_fingerprint_to_signals[idx]);
    let init_fingerprints_to_signals = input_fingerprint_to_signal.unwrap_or(&_init_fingerprint_to_signals_refs);

    insert_and_print_timing(debug, &mut timing, "preprocessing", preprocessing_timer.elapsed());

    // ########### FINGERPRINTING #############
    let fingerprinting_timer = Instant::now();
    
    let (fingerprints_to_normi, fingerprints_to_sig, _, sig_fingerprints) = iterated_refinement(
        circuits, normalised_constraints, signals_to_normi, init_fingerprints_to_normi, init_fingerprints_to_signals, true, None, false, debug
    );

    // fixing for compile-time checking
    let fingerprints_to_normi: [_; 2] = fingerprints_to_normi.try_into().unwrap();
    let fingerprints_to_sig: [_; 2] = fingerprints_to_sig.try_into().unwrap();
    let sig_fingerprints: [_; 2] = sig_fingerprints.try_into().unwrap();

    // sanity checking
    for (is_norm, label_to_indices) in [(true, &fingerprints_to_normi), (false, &fingerprints_to_sig)] {
        if let Err(reason) = sanity_check_fingerprints(is_norm, label_to_indices) {return get_with_error(NonequivalentReason::Fin(reason), timing);}
    }

    insert_and_print_timing(debug, &mut timing, "fingerprinting", fingerprinting_timer.elapsed());

    // ########### ENCODING #############
    let encoding_timer = Instant::now();

    let _formula = encode_comparison::<_, S>(normalised_constraints, &fingerprints_to_normi, &fingerprints_to_sig, &sig_fingerprints);

    if let Err(reason) = _formula {return get_with_error(NonequivalentReason::Enc(reason), timing);}

    let formula = _formula.ok().unwrap();

    // TODO: allow glucose argument passthrough
    let mut solver = rustsat_kissat::Kissat::default();
    if let Err(reason) = solver.add_cnf(formula.into_cnf().0) {return get_with_error(NonequivalentReason::Other(reason), timing);}

    insert_and_print_timing(debug, &mut timing, "encoding", encoding_timer.elapsed());

    // ########### SOLVING #############
    let solving_timer = Instant::now();

    let res = solver.solve();
    if let Err(reason) = res {return get_with_error(NonequivalentReason::Other(reason), timing);}

    let result: bool = res.unwrap() == SolverResult::Sat;
    insert_and_print_timing(debug, &mut timing, "solving", solving_timer.elapsed());

    // ########### POSTPROCESSING ###########

    let reason = if !result {Some(NonequivalentReason::Unsatisfiable)} else {None};
    let total_time: Duration = timing.values().sum();
    insert_and_print_timing(debug, &mut timing, "total", total_time);

    // TODO: handle and return the mappings -- will require refactoring encoding to store the object_map lits ...

    ComparisonData {result: result, reason: reason, timing: timing, norm_mapping: None, sig_mapping: None}
}

fn sanity_check_fingerprints<T: Hash + Eq + Copy>(is_norm: bool, label_to_indices: &[HashMap<T, Vec<usize>>]) -> Result<(), FingerprintError> {
    let index_type: &'static str = if is_norm {"norm"} else {"signal"};

    let keys_in_only_one: HashSet<T> = label_to_indices[0].keys().copied().collect::<HashSet<_>>().symmetric_difference(&label_to_indices[1].keys().copied().collect::<HashSet<_>>()).copied().collect();
    let keys_in_both: HashSet<T> = label_to_indices[0].keys().copied().collect::<HashSet<_>>().intersection(&label_to_indices[1].keys().copied().collect::<HashSet<_>>()).copied().collect();

    if keys_in_only_one.len() > 0 {return Err(FingerprintError::DifferentFingerprints(index_type, keys_in_only_one.len()));}

    let different_keys_in_both: Vec<T> = keys_in_both.into_iter().filter(|key| label_to_indices[0].get(&key).unwrap().len() != label_to_indices[1].get(&key).unwrap().len()).collect();

    if keys_in_only_one.len() > 0 {return Err(FingerprintError::DifferentFingerprintClasses(index_type, different_keys_in_both.len()));}

    Ok(())
}