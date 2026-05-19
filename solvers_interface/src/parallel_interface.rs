use crate::{CorrectnessVerification, EquivalenceVerification, PossibleResult, PossibleSolver, SafetyVerification};
use crate::{civer_interface, ffsol_interface, cvc5_interface, nia_z3_interface, yices_interface, z3_interface};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc;
use std::sync::mpsc::RecvTimeoutError;
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};

// The cancel token is always passed even to solvers that ignore it (equivalence/correctness),
// so all three verification kinds can share the same run_parallel core.
type Task = Box<dyn FnOnce(Arc<AtomicBool>) -> (PossibleResult, Vec<String>) + Send>;

fn filter_available(candidates: &[(&'static str, PossibleSolver)]) -> Vec<&'static str> {
    candidates.iter().filter_map(|&(name, solver)| {
        if solver.is_available() {
            Some(name)
        } else {
            let bin = solver.required_binary().unwrap_or(name);
            println!("ALL: skipping '{}' — binary '{}' not found in PATH", name, bin);
            None
        }
    }).collect()
}

fn run_parallel(label: &str, timeout_ms: u64, tasks: Vec<(&'static str, Task)>) -> (PossibleResult, Vec<String>) {
    let start = Instant::now();
    println!("ALL: Starting parallel {} verification with: {}",
        label, tasks.iter().map(|(n, _)| *n).collect::<Vec<_>>().join(", "));

    if tasks.is_empty() {
        println!("ALL: no solvers available — all required binaries are missing");
        return (PossibleResult::UNKNOWN, vec!["### ALL: NO SOLVERS AVAILABLE\n".to_string()]);
    }

    let (tx, rx) = mpsc::channel::<(&'static str, PossibleResult, Vec<String>)>();
    let cancel = Arc::new(AtomicBool::new(false));
    let n = tasks.len();
    let mut winner: Option<(&'static str, PossibleResult, Vec<String>)> = None;
    // Tracked separately from `total` because thread::scope joins all threads after the loop,
    // adding cleanup time that should not count toward the decisive result latency.
    let mut winner_time: Option<f64> = None;
    let mut unknown_count = 0usize;
    let mut fallback_logs: Vec<String> = Vec::new();

    thread::scope(|scope| {
        for (name, task) in tasks {
            let tx = tx.clone();
            let cancel_clone = Arc::clone(&cancel);
            scope.spawn(move || {
                if cancel_clone.load(Ordering::Relaxed) { return; }
                println!("ALL: launching solver {}", name);
                let result = task(cancel_clone);
                let _ = tx.send((name, result.0, result.1));
            });
        }
        // Drop the last sender so rx.recv_timeout returns Disconnected once all workers finish.
        drop(tx);

        let global_timeout = Duration::from_millis(timeout_ms);
        loop {
            let elapsed = start.elapsed();
            if elapsed >= global_timeout {
                cancel.store(true, Ordering::SeqCst);
                fallback_logs.push(format!("### ALL: GLOBAL TIMEOUT REACHED AFTER {:.6} seconds\n", elapsed.as_secs_f64()));
                break;
            }
            let remaining = global_timeout - elapsed;
            match rx.recv_timeout(remaining) {
                Ok((name, result, logs)) => match result {
                    PossibleResult::VERIFIED | PossibleResult::FAILED => {
                        cancel.store(true, Ordering::SeqCst);
                        winner = Some((name, result, logs));
                        winner_time = Some(start.elapsed().as_secs_f64());
                        break;
                    }
                    _ => {
                        unknown_count += 1;
                        fallback_logs.push(format!("### ALL: {} returned UNKNOWN\n", name));
                        fallback_logs.extend(logs);
                        if unknown_count == n { break; }
                    }
                },
                Err(RecvTimeoutError::Timeout) => {
                    cancel.store(true, Ordering::SeqCst);
                    fallback_logs.push("### ALL: GLOBAL TIMEOUT WAITING FOR SOLVER RESPONSES\n".to_string());
                    break;
                }
                Err(RecvTimeoutError::Disconnected) => break,
            }
        }
        // Final store ensures any thread that missed the earlier signal also stops.
        cancel.store(true, Ordering::SeqCst);
    });
    // scope join happens here — total includes thread teardown, decisive does not.

    let total = start.elapsed().as_secs_f64();
    if let Some((winner_solver, result, mut logs)) = winner {
        let decisive = winner_time.unwrap_or(total);
        println!("ALL: winner solver = {}, decisive result = {:?}", winner_solver, result);
        println!("ALL: time to decisive result = {:.6} seconds", decisive);
        println!("ALL: total time including cleanup = {:.6} seconds", total);
        logs.push(format!("### ALL: FIRST DECISIVE ANSWER = {:?}, FOUND BY SOLVER {}\n", result, winner_solver));
        logs.push(format!("### ALL: TIME TO DECISIVE RESULT = {:.6} seconds\n", decisive));
        logs.push(format!("### ALL: TOTAL TIME INCLUDING CLEANUP = {:.6} seconds\n", total));
        (result, logs)
    } else {
        println!("ALL: no decisive result, final result = UNKNOWN");
        println!("ALL: total time including cleanup = {:.6} seconds", total);
        fallback_logs.push("### UNKNOWN: ALL PARALLEL SOLVERS TIMED OUT\n".to_string());
        fallback_logs.push(format!("### ALL: TOTAL TIME INCLUDING CLEANUP = {:.6} seconds\n", total));
        (PossibleResult::UNKNOWN, fallback_logs)
    }
}

pub fn study_safety(problem: &SafetyVerification) -> (PossibleResult, Vec<String>) {
    let mut candidates = vec![
        ("ffsol",          PossibleSolver::FFSOL),
        ("ffsol-nolinear", PossibleSolver::FFSOL),
        ("cvc5",           PossibleSolver::CVC5),
        ("yices",          PossibleSolver::YICES),
        ("z3",             PossibleSolver::Z3),
        ("civer",          PossibleSolver::CIVER),
    ];
    // nia-z3 is excluded by default because it is much slower on linear arithmetic;
    // the caller opts in explicitly via include_niaz3_in_all.
    if problem.include_niaz3_in_all {
        candidates.push(("nia-z3", PossibleSolver::NIAZ3));
    }
    let timeout = problem.verification_timeout;
    let tasks = filter_available(&candidates).into_iter().map(|name| {
        let p = problem.clone();
        let task: Task = match name {
            "ffsol"          => Box::new(move |c: Arc<AtomicBool>| ffsol_interface::study_safety_with_cancel(&p, &c, &ffsol_interface::FfsolConfig::default(p.verification_timeout, p.verbose))),
            "ffsol-nolinear" => Box::new(move |c: Arc<AtomicBool>| ffsol_interface::study_safety_with_cancel(&p, &c, &ffsol_interface::FfsolConfig::linear_diactivated(p.verification_timeout, p.verbose))),
            "cvc5"           => Box::new(move |c: Arc<AtomicBool>| cvc5_interface::study_safety_with_cancel(&p, &c)),
            "yices"          => Box::new(move |c: Arc<AtomicBool>| yices_interface::study_safety_with_cancel(&p, &c)),
            "nia-z3"         => Box::new(move |c: Arc<AtomicBool>| nia_z3_interface::study_safety_with_cancel(&p, &c)),
            "z3"             => Box::new(move |c: Arc<AtomicBool>| z3_interface::study_safety_with_cancel(&p, &c)),
            "civer"          => Box::new(move |c: Arc<AtomicBool>| civer_interface::study_safety_with_cancel(&p, &c)),
            _                => Box::new(move |_| (PossibleResult::UNKNOWN, vec!["UNKNOWN SOLVER IN ALL MODE\n".to_string()])),
        };
        (name, task)
    }).collect();
    run_parallel("safety", timeout, tasks)
}

// Equivalence and correctness solver interfaces have no cancel-aware variants, so tasks
// ignore the token with |_|. Remaining threads run to their own per-solver timeout.
pub fn study_equivalence(problem: &EquivalenceVerification) -> (PossibleResult, Vec<String>) {
    let candidates = &[
        ("ffsol",          PossibleSolver::FFSOL),
        ("ffsol-nolinear", PossibleSolver::FFSOL),
        ("cvc5",           PossibleSolver::CVC5),
        ("yices",          PossibleSolver::YICES),
        ("nia-z3",         PossibleSolver::NIAZ3),
        ("z3",             PossibleSolver::Z3),
    ];
    let timeout = problem.verification_timeout;
    let tasks = filter_available(candidates).into_iter().map(|name| {
        let p = problem.clone();
        let task: Task = match name {
            "ffsol"          => Box::new(move |c: Arc<AtomicBool>| ffsol_interface::study_equivalence_with_cancel(&p, &c, &ffsol_interface::FfsolConfig::default(p.verification_timeout, p.verbose))),
            "ffsol-nolinear" => Box::new(move |c: Arc<AtomicBool>| ffsol_interface::study_equivalence_with_cancel(&p, &c, &ffsol_interface::FfsolConfig::linear_diactivated(p.verification_timeout, p.verbose))),
            "cvc5"           => Box::new(move |c: Arc<AtomicBool>| cvc5_interface::study_equivalence_with_cancel(&p, &c)),
            "yices"          => Box::new(move |c: Arc<AtomicBool>| yices_interface::study_equivalence_with_cancel(&p, &c)),
            "nia-z3"         => Box::new(move |c: Arc<AtomicBool>| nia_z3_interface::study_equivalence_with_cancel(&p, &c)),
            "z3"             => Box::new(move |c: Arc<AtomicBool>| z3_interface::study_equivalence_with_cancel(&p, &c)),
            _                => Box::new(move |_| (PossibleResult::UNKNOWN, vec!["UNKNOWN SOLVER IN ALL MODE\n".to_string()])),
        };
        (name, task)
    }).collect();
    run_parallel("equivalence", timeout, tasks)
}

// z3_interface has no study_correctness, so z3 is absent from this candidate list.
pub fn study_correctness(problem: &CorrectnessVerification) -> (PossibleResult, Vec<String>) {
    let candidates = &[
        ("ffsol",          PossibleSolver::FFSOL),
        ("ffsol-nolinear", PossibleSolver::FFSOL),
        ("cvc5",           PossibleSolver::CVC5),
        ("yices",          PossibleSolver::YICES),
        ("nia-z3",         PossibleSolver::NIAZ3),
    ];
    let timeout = problem.verification_timeout;
    let tasks = filter_available(candidates).into_iter().map(|name| {
        let p = problem.clone();
        let task: Task = match name {
            "ffsol"          => Box::new(move |c: Arc<AtomicBool>| ffsol_interface::study_correctness_with_cancel(&p, &c, &ffsol_interface::FfsolConfig::default(p.verification_timeout, p.verbose))),
            "ffsol-nolinear" => Box::new(move |c: Arc<AtomicBool>| ffsol_interface::study_correctness_with_cancel(&p, &c, &ffsol_interface::FfsolConfig::linear_diactivated(p.verification_timeout, p.verbose))),
            "cvc5"           => Box::new(move |c: Arc<AtomicBool>| cvc5_interface::study_correctness_with_cancel(&p, &c)),
            "yices"          => Box::new(move |c: Arc<AtomicBool>| yices_interface::study_correctness_with_cancel(&p, &c)),
            "nia-z3"         => Box::new(move |c: Arc<AtomicBool>| nia_z3_interface::study_correctness_with_cancel(&p, &c)),
            _                => Box::new(move |_| (PossibleResult::UNKNOWN, vec!["UNKNOWN SOLVER IN ALL MODE\n".to_string()])),
        };
        (name, task)
    }).collect();
    run_parallel("correctness", timeout, tasks)
}
