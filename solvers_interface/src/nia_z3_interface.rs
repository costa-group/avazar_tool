use crate::EquivalenceVerification;
use crate::{CorrectnessVerification, PossibleResult, SafetyVerification};
use circom_algebra::algebra::Constraint;
use nix::sys::signal::killpg;
use nix::sys::signal::Signal;
use nix::unistd::Pid;
use num_bigint_dig::BigInt;
use rand::Rng;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::fs::File;
use std::io::Read;
use std::io::Write;
use std::os::unix::process::CommandExt;
use std::process::Command;
use std::process::Stdio;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread;
use std::time::Duration;
use std::time::Instant;
use wait_timeout::ChildExt;

pub fn study_correctness(problem: &CorrectnessVerification) -> (PossibleResult, Vec<String>) {
    let mut logs = Vec::new();

    let smt2_problem = correctness_problem_to_z3_smt2(problem);
    let result_solver = handling_nia_z3_call(&smt2_problem, problem.verification_timeout, problem.verbose, None);

    match result_solver {
        PossibleResult::VERIFIED => {
            logs.push("### THE CONSTRAINT SYSTEMS AND THE FORMULA ARE NOT EQUIVALENT. FOUND COUNTEREXAMPLE USING SMT:\n".to_string());
        }
        PossibleResult::FAILED => {
            logs.push("### THE CONSTRAINT SYSTEM AND THE FORMULA ARE EQUIVALENT\n".to_string());
        }
        PossibleResult::UNKNOWN => {
            logs.push("### UNKNOWN: VERIFICATION OF CORRECTNESS TIMEOUT\n".to_string());
        }
        _ => unreachable!(),
    }

    (result_solver, logs)
}

pub fn study_equivalence(problem: &EquivalenceVerification) -> (PossibleResult, Vec<String>) {
    let mut logs = Vec::new();

    let smt2_problem = equivalence_problem_to_z3_smt2(problem);
    let result_solver = handling_nia_z3_call(&smt2_problem, problem.verification_timeout, problem.verbose, None);

    match result_solver {
        PossibleResult::VERIFIED => {
            logs.push("### THE CONSTRAINT SYSTEMS ARE NOT EQUIVALENT. FOUND COUNTEREXAMPLE USING SMT:\n".to_string());
        }
        PossibleResult::FAILED => {
            logs.push("### THE CONSTRAINT SYSTEMS ARE EQUIVALENT\n".to_string());
        }
        PossibleResult::UNKNOWN => {
            logs.push("### UNKNOWN: VERIFICATION OF EQUIVALENCE TIMEOUT\n".to_string());
        }
        _ => unreachable!(),
    }

    (result_solver, logs)
}

pub fn study_safety(problem: &SafetyVerification) -> (PossibleResult, Vec<String>) {
    let mut logs = Vec::new();

    let smt2_problem = safety_problem_to_z3_smt2(problem);
    let result_solver = handling_nia_z3_call(&smt2_problem, problem.verification_timeout, problem.verbose, None);

    match result_solver {
        PossibleResult::VERIFIED => {
            logs.push("### THE TEMPLATE DOES NOT ENSURE SAFETY. FOUND COUNTEREXAMPLE USING SMT:\n".to_string());
        }
        PossibleResult::FAILED => {
            logs.push("### WEAK SAFETY ENSURED BY THE TEMPLATE\n".to_string());
        }
        PossibleResult::UNKNOWN => {
            logs.push("### UNKNOWN: VERIFICATION OF WEAK SAFETY USING THE SPECIFICATION TIMEOUT\n".to_string());
        }
        _ => unreachable!(),
    }

    (result_solver, logs)
}

pub fn study_safety_with_cancel(problem: &SafetyVerification, cancel_flag: &AtomicBool) -> (PossibleResult, Vec<String>) {
    let mut logs = Vec::new();

    if cancel_flag.load(Ordering::Relaxed) {
        logs.push("### CANCELLED BEFORE STARTING NIA-Z3\n".to_string());
        return (PossibleResult::UNKNOWN, logs);
    }

    let smt2_problem = safety_problem_to_z3_smt2(problem);
    let result_solver = handling_nia_z3_call(
        &smt2_problem,
        problem.verification_timeout,
        problem.verbose,
        Some(cancel_flag),
    );

    match result_solver {
        PossibleResult::VERIFIED => {
            logs.push("### THE TEMPLATE DOES NOT ENSURE SAFETY. FOUND COUNTEREXAMPLE USING SMT:\n".to_string());
        }
        PossibleResult::FAILED => {
            logs.push("### WEAK SAFETY ENSURED BY THE TEMPLATE\n".to_string());
        }
        PossibleResult::UNKNOWN => {
            logs.push("### UNKNOWN: VERIFICATION OF WEAK SAFETY USING THE SPECIFICATION TIMEOUT\n".to_string());
        }
        _ => unreachable!(),
    }

    (result_solver, logs)
}

fn append_declare_and_domain(lines: &mut Vec<String>, name: &str, prime: &BigInt) {
    lines.push(format!("(declare-fun {} () Int)", name));
    lines.push(format!("(assert (<= 0 {}))", name));
    lines.push(format!("(assert (< {} {}))", name, prime));
}

fn sum_terms(terms: Vec<String>) -> String {
    if terms.is_empty() {
        return "0".to_string();
    }
    if terms.len() == 1 {
        return terms[0].clone();
    }
    format!("(+ {})", terms.join(" "))
}

fn linear_expr_to_int(coeffs: &HashMap<usize, BigInt>, signal_to_name: &HashMap<usize, String>) -> String {
    let mut terms = Vec::new();

    for (signal, value) in coeffs {
        if value == &BigInt::from(0) {
            continue;
        }

        if *signal == 0 {
            terms.push(value.to_string());
            continue;
        }

        let s = signal_to_name.get(signal).unwrap();
        if value == &BigInt::from(1) {
            terms.push(s.clone());
        } else {
            terms.push(format!("(* {} {})", s, value));
        }
    }

    sum_terms(terms)
}

fn constraint_to_mod0_assert(
    constraint: &Constraint<usize>,
    signal_to_name: &HashMap<usize, String>,
    prime: &BigInt,
) -> String {
    let a = linear_expr_to_int(constraint.a(), signal_to_name);
    let b = linear_expr_to_int(constraint.b(), signal_to_name);
    let c = linear_expr_to_int(constraint.c(), signal_to_name);

    let product = if constraint.a().is_empty() || constraint.b().is_empty() {
        "0".to_string()
    } else {
        format!("(* {} {})", a, b)
    };

    format!("(assert (= (mod (- {} {}) {}) 0))", c, product, prime)
}

fn all_equal_expr_from_pairs(pairs: &[(String, String)]) -> String {
    if pairs.is_empty() {
        return "true".to_string();
    }

    let mut eqs = Vec::new();
    for (a, b) in pairs {
        eqs.push(format!("(= {} {})", a, b));
    }

    if eqs.len() == 1 {
        eqs[0].clone()
    } else {
        format!("(and {})", eqs.join(" "))
    }
}

fn all_equal_expr_by_ids(
    ids_1: &[usize],
    signal_to_name_1: &HashMap<usize, String>,
    ids_2: &[usize],
    signal_to_name_2: &HashMap<usize, String>,
) -> String {
    let mut pairs = Vec::new();
    for i in 0..ids_1.len() {
        let a = signal_to_name_1.get(&ids_1[i]).unwrap().clone();
        let b = signal_to_name_2.get(&ids_2[i]).unwrap().clone();
        pairs.push((a, b));
    }
    all_equal_expr_from_pairs(&pairs)
}

fn deduction_assertions(
    constraint: &Constraint<usize>,
    signal_to_name_1: &HashMap<usize, String>,
    signal_to_name_2: &HashMap<usize, String>,
) -> Vec<String> {
    let mut out = Vec::new();

    let all_signals = constraint.take_signals();
    let only_linear_signals = constraint.take_only_linear_signals();

    for s_deduced in only_linear_signals {
        let right = format!(
            "(= {} {})",
            signal_to_name_1.get(s_deduced).unwrap(),
            signal_to_name_2.get(s_deduced).unwrap()
        );

        let mut left_pairs = Vec::new();
        for s in &all_signals {
            if *s != s_deduced {
                left_pairs.push((
                    signal_to_name_1.get(s).unwrap().clone(),
                    signal_to_name_2.get(s).unwrap().clone(),
                ));
            }
        }
        let left = all_equal_expr_from_pairs(&left_pairs);
        out.push(format!("(assert (=> {} {}))", left, right));
    }

    out
}

fn safety_implication_expr(
    imp: &(Vec<usize>, Vec<usize>),
    signal_to_name_1: &HashMap<usize, String>,
    signal_to_name_2: &HashMap<usize, String>,
) -> String {
    let mut left_pairs = Vec::new();
    for s in &imp.0 {
        left_pairs.push((
            signal_to_name_1.get(s).unwrap().clone(),
            signal_to_name_2.get(s).unwrap().clone(),
        ));
    }

    let mut right_pairs = Vec::new();
    for s in &imp.1 {
        right_pairs.push((
            signal_to_name_1.get(s).unwrap().clone(),
            signal_to_name_2.get(s).unwrap().clone(),
        ));
    }

    let left = all_equal_expr_from_pairs(&left_pairs);
    let right = all_equal_expr_from_pairs(&right_pairs);
    format!("(=> {} {})", left, right)
}

fn safety_problem_to_z3_smt2(problem: &SafetyVerification) -> String {
    let mut lines = Vec::new();
    lines.push("(set-logic QF_NIA)".to_string());

    let mut signal_to_name_1: HashMap<usize, String> = HashMap::new();
    let mut signal_to_name_2: HashMap<usize, String> = HashMap::new();

    for s in &problem.signals {
        if signal_to_name_1.contains_key(s) {
            continue;
        }

        let n1 = format!("s1_{}", s);
        let n2 = format!("s2_{}", s);

        append_declare_and_domain(&mut lines, &n1, &problem.field);
        append_declare_and_domain(&mut lines, &n2, &problem.field);

        signal_to_name_1.insert(*s, n1);
        signal_to_name_2.insert(*s, n2);
    }

    for c in &problem.constraints {
        lines.push(constraint_to_mod0_assert(c, &signal_to_name_1, &problem.field));
        lines.push(constraint_to_mod0_assert(c, &signal_to_name_2, &problem.field));

        if problem.apply_deduction_assigned {
            lines.extend(deduction_assertions(c, &signal_to_name_1, &signal_to_name_2));
        }
    }

    lines.push(format!(
        "(assert {})",
        all_equal_expr_by_ids(
            &problem.inputs,
            &signal_to_name_1,
            &problem.inputs,
            &signal_to_name_2,
        )
    ));

    for imp in &problem.implications_safety {
        lines.push(format!(
            "(assert {})",
            safety_implication_expr(imp, &signal_to_name_1, &signal_to_name_2)
        ));
    }

    lines.push(format!(
        "(assert (not {}))",
        all_equal_expr_by_ids(
            &problem.outputs,
            &signal_to_name_1,
            &problem.outputs,
            &signal_to_name_2,
        )
    ));

    lines.push("(check-sat)".to_string());
    lines.join("\n")
}

fn equivalence_problem_to_z3_smt2(problem: &EquivalenceVerification) -> String {
    let mut lines = Vec::new();
    lines.push("(set-logic QF_NIA)".to_string());

    let mut signal_to_name_1: HashMap<usize, String> = HashMap::new();
    let mut signal_to_name_2: HashMap<usize, String> = HashMap::new();

    for s in &problem.signals_1 {
        let n = format!("s1_{}", s);
        append_declare_and_domain(&mut lines, &n, &problem.field);
        signal_to_name_1.insert(*s, n);
    }

    for s in &problem.signals_2 {
        let n = format!("s2_{}", s);
        append_declare_and_domain(&mut lines, &n, &problem.field);
        signal_to_name_2.insert(*s, n);
    }

    for c in &problem.constraints_1 {
        lines.push(constraint_to_mod0_assert(c, &signal_to_name_1, &problem.field));
    }

    for c in &problem.constraints_2 {
        lines.push(constraint_to_mod0_assert(c, &signal_to_name_2, &problem.field));
    }

    lines.push(format!(
        "(assert {})",
        all_equal_expr_by_ids(
            &problem.inputs_1,
            &signal_to_name_1,
            &problem.inputs_2,
            &signal_to_name_2,
        )
    ));

    lines.push(format!(
        "(assert (not {}))",
        all_equal_expr_by_ids(
            &problem.outputs_1,
            &signal_to_name_1,
            &problem.outputs_2,
            &signal_to_name_2,
        )
    ));

    lines.push("(check-sat)".to_string());
    lines.join("\n")
}

fn correctness_problem_to_z3_smt2(problem: &CorrectnessVerification) -> String {
    let mut lines = Vec::new();
    lines.push("(set-logic QF_NIA)".to_string());

    let mut signal_to_name_1: HashMap<usize, String> = HashMap::new();

    for s in &problem.signals_1 {
        let n = format!("s_{}", s);
        append_declare_and_domain(&mut lines, &n, &problem.field);
        signal_to_name_1.insert(*s, n);
    }

    let mut seen = HashSet::new();
    for s in &problem.signals_2 {
        if seen.insert(s.clone()) {
            append_declare_and_domain(&mut lines, s, &problem.field);
        }
    }

    for c in &problem.constraints_1 {
        lines.push(constraint_to_mod0_assert(c, &signal_to_name_1, &problem.field));
    }

    for c in &problem.constraints_2 {
        lines.push(c.clone());
    }

    let mut input_pairs = Vec::new();
    for i in 0..problem.inputs_1.len() {
        input_pairs.push((
            signal_to_name_1.get(&problem.inputs_1[i]).unwrap().clone(),
            problem.inputs_2[i].clone(),
        ));
    }

    let mut output_pairs = Vec::new();
    for i in 0..problem.outputs_1.len() {
        output_pairs.push((
            signal_to_name_1.get(&problem.outputs_1[i]).unwrap().clone(),
            problem.outputs_2[i].clone(),
        ));
    }

    lines.push(format!("(assert {})", all_equal_expr_from_pairs(&input_pairs)));
    lines.push(format!("(assert (not {}))", all_equal_expr_from_pairs(&output_pairs)));
    lines.push("(check-sat)".to_string());

    lines.join("\n")
}

pub fn handling_nia_z3_call(
    smt2_text: &str,
    timeout: u64,
    verbose: bool,
    cancel_flag: Option<&AtomicBool>,
) -> PossibleResult {
    let mut rng = rand::thread_rng();
    let random_number: u32 = rng.gen();
    let new_file_name = format!("output_nia_z3_{}.smt2", random_number);

    {
        let mut file = File::create(&new_file_name).expect("Unable to create SMT2 file");
        file.write_all(smt2_text.as_bytes()).expect("Unable to write SMT2 file");
        file.sync_all().expect("Failed to sync SMT2 file to disk");
        file.flush().expect("Failed to flush SMT2 file");
    }

    let mut child = unsafe {
        Command::new("z3")
            .args([&new_file_name])
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .pre_exec(|| {
                libc::setsid();
                Ok(())
            })
            .spawn()
            .expect("Failed to execute the command")
    };

    let mut stdout = child.stdout.take().expect("Failed to take stdout");
    let mut stderr = child.stderr.take().expect("Failed to take stderr");

    let stdout_handle = thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = stdout.read_to_end(&mut buf);
        buf
    });

    let stderr_handle = thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = stderr.read_to_end(&mut buf);
        buf
    });

    let timeout = Duration::from_millis(timeout);
    let check_step = Duration::from_millis(50);
    let start = Instant::now();

    loop {
        if cancel_flag.map_or(false, |flag| flag.load(Ordering::Relaxed)) {
            let pgid = Pid::from_raw(child.id() as i32);
            let _ = killpg(pgid, Signal::SIGKILL);
            break;
        }

        let elapsed = start.elapsed();
        if elapsed >= timeout {
            let pgid = Pid::from_raw(child.id() as i32);
            let _ = killpg(pgid, Signal::SIGKILL);
            break;
        }

        let remaining = timeout - elapsed;
        let step = if remaining < check_step { remaining } else { check_step };
        match child.wait_timeout(step).expect("Failed while waiting for the process") {
            Some(_) => break,
            None => {}
        }
    }

    let status = child.wait().expect("Failed to wait on child");
    let stdout = stdout_handle.join().expect("stdout thread panicked");
    let stderr = stderr_handle.join().expect("stderr thread panicked");

    let output = std::process::Output {
        status,
        stdout,
        stderr,
    };
    let stdout = String::from_utf8_lossy(&output.stdout);

    if !verbose {
        match fs::remove_file(&new_file_name) {
            Ok(_) => {}
            Err(e) => eprintln!("Error when eliminating the file: {}", e),
        }
    }

    if let Some(last_line) = stdout.lines().rev().find(|l| !l.trim().is_empty()) {
        if last_line == "unsat" {
            PossibleResult::VERIFIED
        } else if last_line == "sat" {
            PossibleResult::FAILED
        } else {
            PossibleResult::UNKNOWN
        }
    } else {
        PossibleResult::UNKNOWN
    }
}
