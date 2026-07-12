use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread;
use std::time::Duration;
use std::str::FromStr;
use num_bigint_dig::BigInt;
use crate::PossibleResult;
use circom_algebra::{encodable_constraint_impl::Signal2Bounds, algebra::{Constraint, ExecutedInequation, EncodableConstraint}};

use z3::Config;
use z3::Solver;
use z3::*;
use z3::with_z3_config;

pub type Signal2BoundsZ3 = HashMap<usize, ExecutedInequation<usize>>;

pub fn try_prove_safety_with_z3<C: EncodableConstraint + Sync>(
    inputs: &Vec<usize>,
    outputs: &Vec<usize>,
    signals: &Vec<usize>,
    constraints: &Vec<C>,
    implications_safety: &Vec<(Vec<usize>, Vec<usize>)>,
    deductions: &Signal2Bounds,
    field: &BigInt,
    verification_timeout: u64,
    opt_apply_deduction_assigned: bool,
    logs: &mut Vec<String>,
) -> PossibleResult {
    try_prove_safety_with_z3_internal(
        inputs,
        outputs,
        signals,
        constraints,
        implications_safety,
        deductions,
        field,
        verification_timeout,
        opt_apply_deduction_assigned,
        logs,
        None,
    )
}

pub fn try_prove_safety_with_z3_cancel<C: EncodableConstraint + Sync>(
    inputs: &Vec<usize>,
    outputs: &Vec<usize>,
    signals: &Vec<usize>,
    constraints: &Vec<C>,
    implications_safety: &Vec<(Vec<usize>, Vec<usize>)>,
    deductions: &Signal2Bounds,
    field: &BigInt,
    verification_timeout: u64,
    opt_apply_deduction_assigned: bool,
    logs: &mut Vec<String>,
    cancel_flag: &AtomicBool,
) -> PossibleResult {
    try_prove_safety_with_z3_internal(
        inputs,
        outputs,
        signals,
        constraints,
        implications_safety,
        deductions,
        field,
        verification_timeout,
        opt_apply_deduction_assigned,
        logs,
        Some(cancel_flag),
    )
}

fn try_prove_safety_with_z3_internal<C: EncodableConstraint + Sync>(
    inputs: &Vec<usize>,
    outputs: &Vec<usize>,
    signals: &Vec<usize>,
    constraints: &Vec<C>,
    implications_safety: &Vec<(Vec<usize>, Vec<usize>)>,
    deductions: &Signal2Bounds,
    field: &BigInt,
    verification_timeout: u64,
    opt_apply_deduction_assigned: bool,
    logs: &mut Vec<String>,
    cancel_flag: Option<&AtomicBool>,
) -> PossibleResult {
    let mut cfg = Config::new();
    cfg.set_timeout_msec(verification_timeout);

    with_z3_config(
        &cfg,
        || {
            internal_try_prove_safety_with_z3(
                inputs,
                outputs,
                signals,
                constraints,
                implications_safety,
                deductions,
                field,
                opt_apply_deduction_assigned,
                logs,
                cancel_flag
            )
        }
    )

}



fn internal_try_prove_safety_with_z3<C: EncodableConstraint>(
    inputs: &Vec<usize>,
    outputs: &Vec<usize>,
    signals: &Vec<usize>,
    constraints: &Vec<C>,
    implications_safety: &Vec<(Vec<usize>, Vec<usize>)>,
    deductions: &Signal2Bounds,
    field: &BigInt,
    opt_apply_deduction_assigned: bool,
    logs: &mut Vec<String>,
    cancel_flag: Option<&AtomicBool>,
) -> PossibleResult {
    

    let solver = Solver::new();
    let zero = z3::ast::Int::from_i64(0);
    let field_z3 = z3::ast::Int::from_str(&field.to_string()).unwrap();
    let mut aux_signals_to_smt_rep = HashMap::new();
    let mut aux_signals_to_smt_rep_aux = HashMap::new();

    for s in signals {
        let is_input = inputs.contains(s);

        let aux_signal_to_smt = z3::ast::Int::new_const(format!("s_{}", s));
        let copy_aux_signal_to_smt = if !is_input {
            z3::ast::Int::new_const(format!("saux_{}", s))
        } else {
            z3::ast::Int::new_const(format!("s_{}", s))
        };
        aux_signals_to_smt_rep.insert(*s, aux_signal_to_smt.clone());
        aux_signals_to_smt_rep_aux.insert(*s, copy_aux_signal_to_smt.clone());

        match deductions.get(s) {
            None => {
                solver.assert(&aux_signal_to_smt.ge(&zero));
                solver.assert(&aux_signal_to_smt.lt(&field_z3));
                solver.assert(&copy_aux_signal_to_smt.ge(&zero));
                solver.assert(&copy_aux_signal_to_smt.lt(&field_z3));
            }
            Some(bounds) => {
                let condition = get_z3_condition_bounds(
                    &aux_signal_to_smt,
                    &bounds.min,
                    &bounds.max,
                    &field,
                );
                solver.assert(&condition);

                let condition = get_z3_condition_bounds(
                    &copy_aux_signal_to_smt,
                    &bounds.min,
                    &bounds.max,
                    &field,
                );
                solver.assert(&condition);
            }
        }
    }

    let mut i = 0;
    for constraint in constraints {
        constraint.insert_constraint_in_smt_z3(
            &solver,
            &aux_signals_to_smt_rep,
            &field,
            &deductions,
            i,
            &field_z3,
            false,
        );
        i = i + 1;
        constraint.insert_constraint_in_smt_z3(
            &solver,
            &aux_signals_to_smt_rep_aux,
            &field,
            &deductions,
            i,
            &field_z3,
            false,
        );
        i = i + 1;
    }

    if opt_apply_deduction_assigned {
        for constraint in constraints {
            constraint.apply_deduction_assigned(
                &solver,
                &aux_signals_to_smt_rep,
                &aux_signals_to_smt_rep_aux,
            );
        }
    } else {
        for constraint in constraints {
            constraint.apply_deduction_rule_homologues(
                &solver,
                &aux_signals_to_smt_rep,
                &aux_signals_to_smt_rep_aux,
                &deductions,
                &field,
                &field_z3,
            );
        }
        
    }

    for (inputs_imp, outputs_imp) in implications_safety {
        let mut implication_left = z3::ast::Bool::from_bool(true);
        for s in inputs_imp {
            let s_1 = aux_signals_to_smt_rep.get(s).unwrap();
            let s_2 = aux_signals_to_smt_rep_aux.get(s).unwrap();
            implication_left &= s_1.eq(s_2);
        }
        let mut implication_right = z3::ast::Bool::from_bool(true);
        for s in outputs_imp {
            let s_1 = aux_signals_to_smt_rep.get(s).unwrap();
            let s_2 = aux_signals_to_smt_rep_aux.get(s).unwrap();
            implication_right &= s_1.eq(s_2);
        }

        solver.assert(&implication_left.implies(&implication_right));
    }

    let mut all_outputs_equal = z3::ast::Bool::from_bool(true);
    for s in outputs {
        let s_1 = aux_signals_to_smt_rep.get(s).unwrap();
        let s_2 = aux_signals_to_smt_rep_aux.get(s).unwrap();
        all_outputs_equal &= s_1.eq(s_2);
    }

    solver.assert(&!all_outputs_equal);

    if cancel_flag.map_or(false, |flag| flag.load(Ordering::Relaxed)) {
        logs.push(format!("### CANCELLED BEFORE CHECKING CIVER Z3 MODEL\n"));
        return PossibleResult::UNKNOWN;
    }

    let finished = AtomicBool::new(false);
    let check_result = thread::scope(|scope| {
        let handle = solver.get_context().handle();
        let finished_ref = &finished;
        if let Some(cancel_flag_ref) = cancel_flag {
            scope.spawn(move || {
                while !finished_ref.load(Ordering::Relaxed) {
                    if cancel_flag_ref.load(Ordering::Relaxed) {
                        handle.interrupt();
                        break;
                    }
                    thread::sleep(Duration::from_millis(10));
                }
            });
        }

        let result = solver.check();
        finished.store(true, Ordering::SeqCst);
        result
    });

    match check_result {
        SatResult::Sat => {
            logs.push(format!(
                "### THE TEMPLATE DOES NOT ENSURE SAFETY. FOUND COUNTEREXAMPLE USING SMT:\n"
            ));

            let model = solver.get_model().unwrap();
            for s in inputs {
                let v = model
                    .eval(aux_signals_to_smt_rep.get(s).unwrap(), true)
                    .unwrap();
                logs.push(format!("Input signal {}: {}\n", s, v.to_string()));
            }
            for s in outputs {
                let v = model
                    .eval(aux_signals_to_smt_rep.get(s).unwrap(), true)
                    .unwrap();
                let v1 = model
                    .eval(aux_signals_to_smt_rep_aux.get(s).unwrap(), true)
                    .unwrap();

                logs.push(format!(
                    "Output signal {}: values {} | {}\n",
                    s,
                    v.to_string(),
                    v1.to_string()
                ));
            }

            PossibleResult::FAILED
        }
        SatResult::Unsat => {
            logs.push(format!("### WEAK SAFETY ENSURED BY THE TEMPLATE\n"));
            PossibleResult::VERIFIED
        }
        _ => {
            logs.push(format!(
                "### UNKNOWN: VERIFICATION OF WEAK SAFETY USING THE SPECIFICATION TIMEOUT\n"
            ));
            PossibleResult::UNKNOWN
        }
    }
}

pub fn get_z3_condition_bounds(
    signal: &z3::ast::Int,
    min: &BigInt,
    max: &BigInt,
    field: &BigInt,
) -> z3::ast::Bool {
    if min >= &BigInt::from(0) {
        &signal.ge(&z3::ast::Int::from_str(&min.to_string()).unwrap())
            &
            &signal.le(&z3::ast::Int::from_str(&max.to_string()).unwrap())
    } else {
        &z3::ast::Int::from_str(&(field + min).to_string())
            .unwrap()
            .le(signal)
            &
            &signal.lt(&z3::ast::Int::from_str(&field.to_string()).unwrap())
            |
            &z3::ast::Int::from_i64(0).le(signal)
            &
            signal.le(&z3::ast::Int::from_str(&max.to_string()).unwrap())
    }
}
