pub mod civer_interface;
pub mod picus_interface;
pub mod ffsol_interface;
pub mod cvc5_interface;
pub mod yices_interface;
pub mod nia_z3_interface;
pub mod z3_interface;
pub mod parallel_interface;
mod smt2_utils;
pub use smt2_utils::sanitize_symbol;
use indexmap::IndexMap;
use std::collections::{HashMap, HashSet, LinkedList};
use std::path::Path;
use num_bigint_dig::BigInt;
use serde::{Serialize,Deserialize};
use clap::ValueEnum;
use strum_macros::Display;

use circuits_constraints_and_algebra::algebra::EncodableConstraint;
use circuits_constraints_and_algebra::r1cs::{R1CSConstraint as Constraint};

#[derive(Debug, Default, Display, Copy, Clone, ValueEnum, PartialEq)]
pub enum PossibleSolver{
    PICUS, CIVER, #[default] FFSOL, CVC5, YICES, NIAZ3, Z3, ALL
}

pub fn check_binary_in_path(binary: &str) -> bool {
    if binary.starts_with('.') || binary.starts_with('/') {
        return Path::new(binary).exists();
    }
    std::process::Command::new("which")
        .arg(binary)
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

impl PossibleSolver {
    /// Returns the external binary required by this solver, or None if it uses a built-in library.
    pub fn required_binary(&self) -> Option<&'static str> {
        match self {
            PossibleSolver::FFSOL  => Some("ffsol"),
            PossibleSolver::CVC5   => Some("cvc5"),
            PossibleSolver::YICES  => Some("yices-smt2"),
            PossibleSolver::NIAZ3  => Some("z3"),
            PossibleSolver::PICUS  => Some("./Picus/run-picus"),
            PossibleSolver::Z3 | PossibleSolver::CIVER | PossibleSolver::ALL => None,
        }
    }

    pub fn is_available(&self) -> bool {
        match self.required_binary() {
            None         => true,
            Some(binary) => check_binary_in_path(binary),
        }
    }

    /// Maps the internal name used in ALL/parallel mode to the corresponding solver variant.
    /// `"ffsol-nolinear"` shares the same binary as `FFSOL`.
    pub fn from_parallel_name(name: &str) -> PossibleSolver {
        match name {
            "ffsol" | "ffsol-nolinear" => PossibleSolver::FFSOL,
            "cvc5"                     => PossibleSolver::CVC5,
            "yices"                    => PossibleSolver::YICES,
            "z3"                       => PossibleSolver::Z3,
            "civer"                    => PossibleSolver::CIVER,
            "nia-z3"                   => PossibleSolver::NIAZ3,
            _                          => PossibleSolver::CIVER,
        }
    }
}


#[derive(PartialEq, Eq, Clone, Copy, Debug, Serialize, Deserialize)] 
pub enum PossibleResult{
    VERIFIED, UNKNOWN, FAILED, NOSTUDIED, NOTHING
} impl PossibleResult {
    pub fn finished_verification(&self) -> bool{
        self == &PossibleResult::VERIFIED || 
        self == &PossibleResult::NOSTUDIED || 
        self == &PossibleResult::NOTHING || 
        self == &PossibleResult::UNKNOWN
    }
    pub fn result_to_str(&self)-> String{
        match self{
            &PossibleResult::FAILED => {format!("FAILED -> FOUND COUNTEREXAMPLE\n")}
            &PossibleResult::UNKNOWN => {format!("UNKNOWN -> VERIFICATION TIMEOUT\n")}
            &PossibleResult::NOTHING => {format!("NOTHING TO VERIFY\n")}
            _ => {format!("VERIFIED\n")}
        }            
    }
}


#[derive(Clone)]
pub struct SafetyVerification<C: EncodableConstraint> {
    pub template_name: String,
    pub original_file: String,
    pub signals: LinkedList<usize>,
    pub inputs: Vec<usize>,
    pub outputs: Vec<usize>,
    pub constraints: Vec<C>,
    pub implications_safety: Vec<(Vec<usize>, Vec<usize>)>,
    pub field: BigInt,
    pub verification_timeout: u64,
    pub added_nodes: HashSet<usize>,
    pub apply_deduction_assigned: bool,
    pub include_niaz3_in_all: bool,
    pub verbose: bool
}

impl<C: EncodableConstraint> SafetyVerification<C>{

    pub fn new(
        template_name: &String,
        original_file: &String,
        signals: LinkedList<usize>,
        inputs: Vec<usize>,
        outputs: Vec<usize>,
        mut constraints: Vec<C>,
        implications_safety: Vec<(Vec<usize>, Vec<usize>)>,
        field: &BigInt,
        verification_timeout: u64,
        apply_deduction_assigned: bool,
        include_niaz3_in_all: bool,
        verbose: bool
    ) -> SafetyVerification<C> {
        for c in constraints.iter_mut() {
            c.fix_constraint(field);
        }

        SafetyVerification {
            template_name: template_name.clone(),
            original_file: original_file.clone(),
            signals,
            inputs,
            outputs,
            implications_safety,
            constraints: constraints,
            field: field.clone(),
            verification_timeout,
            added_nodes: HashSet::new(),
            apply_deduction_assigned,
            include_niaz3_in_all,
            verbose
        }
    }

}

const MAX_SAFE_FILENAME_BYTES: usize = 240;

fn sanitize_name(s: &str, compact_parenthesis: bool) -> String {
    let source = if compact_parenthesis {
        compact_parenthesized_segments(s)
    } else {
        s.to_string()
    };

    source
        .chars()
        .map(|c| if c.is_alphanumeric() || c == '_' || c == '-' { c } else { '_' })
        .collect()
}

fn compact_parenthesized_segments(s: &str) -> String {
    if let Some(start) = s.find('(') {
        if let Some(rel_end) = s[start + 1..].find(')') {
            let end = start + 1 + rel_end;
            let inner = &s[start + 1..end];
            let hash = seahash::hash(inner.as_bytes());

            let mut out = String::with_capacity(s.len());
            out.push_str(&s[..start]);
            out.push_str(&format!("_p{:016x}", hash));
            out.push_str(&s[end + 1..]);
            return out;
        }
    }

    s.to_string()
}

fn ensure_safe_length(
    file_name: String,
    original_file: &str,
    template_name: &str,
    rebuild: impl Fn(&str, &str) -> String,
) -> String {
    if file_name.as_bytes().len() <= MAX_SAFE_FILENAME_BYTES {
        return file_name;
    }
    let original_compact = sanitize_name(original_file, true);
    let template_compact = sanitize_name(template_name, true);
    rebuild(&original_compact, &template_compact)
}

pub fn determinism_smt2_name(original_file: &str, template_name: &str, level: usize, solver: &str) -> String {
    let original = sanitize_name(original_file, false);
    let template = sanitize_name(template_name, false);
    let file_name = format!("determinism_{}_{}_level_{}_{}.smt2", original, template, level, solver);
    ensure_safe_length(file_name, original_file, template_name, |o, t| {
        format!("determinism_{}_{}_level_{}_{}.smt2", o, t, level, solver)
    })
}

pub fn equivalence_smt2_name(original_file: &str, template_name: &str, solver: &str) -> String {
    let random: u32 = rand::Rng::gen(&mut rand::thread_rng());
    let original = sanitize_name(original_file, false);
    if template_name.is_empty() {
        let file_name = format!("equivalence_{}_{}_{}.smt2", original, solver, random);
        ensure_safe_length(file_name, original_file, template_name, |o, _t| {
            format!("equivalence_{}_{}_{}.smt2", o, solver, random)
        })
    } else {
        let template = sanitize_name(template_name, false);
        let file_name = format!("equivalence_{}_{}_{}_{}.smt2", original, template, solver, random);
        ensure_safe_length(file_name, original_file, template_name, |o, t| {
            format!("equivalence_{}_{}_{}_{}.smt2", o, t, solver, random)
        })
    }
}

pub fn correctness_smt2_name(prefix: &str, original_file: &str, template_name: &str, solver: &str) -> String {
    let random: u32 = rand::Rng::gen(&mut rand::thread_rng());
    let original = sanitize_name(original_file, false);
    if template_name.is_empty() {
        let file_name = format!("{}_{}_{}_{}.smt2", prefix, original, solver, random);
        ensure_safe_length(file_name, original_file, template_name, |o, _t| {
            format!("{}_{}_{}_{}.smt2", prefix, o, solver, random)
        })
    } else {
        let template = sanitize_name(template_name, false);
        let file_name = format!("{}_{}_{}_{}_{}.smt2", prefix, original, template, solver, random);
        ensure_safe_length(file_name, original_file, template_name, |o, t| {
            format!("{}_{}_{}_{}_{}.smt2", prefix, o, t, solver, random)
        })
    }
}



#[derive(Clone)]
pub struct EquivalenceVerification {
    pub template_name: String,
    pub original_file: String,
    pub signals_1: LinkedList<usize>,
    pub signals_2: LinkedList<usize>,
    pub inputs_1: Vec<usize>,
    pub outputs_1: Vec<usize>,
    pub inputs_2: Vec<usize>,
    pub outputs_2: Vec<usize>,
    pub constraints_1: Vec<Constraint<usize>>,
    pub constraints_2: Vec<Constraint<usize>>,
    pub implications_equivalence: Vec<(Vec<(usize, usize)>, Vec<(usize, usize)>)>,
    pub field: BigInt,
    pub verification_timeout: u64,
    pub added_nodes: HashSet<usize>,
    pub apply_deduction_assigned: bool,
    pub verbose: bool,
}

impl EquivalenceVerification{

    pub fn new(
        template_name: &String,
        original_file: &String,
        signals_1: LinkedList<usize>,
        signals_2: LinkedList<usize>,
        inputs_1: Vec<usize>,
        inputs_2:Vec<usize>,
        outputs_1: Vec<usize>,
        outputs_2:Vec<usize>,
        constraints_1: Vec<Constraint<usize>>,
        constraints_2: Vec<Constraint<usize>>,
        implications_equivalence: Vec<(Vec<(usize, usize)>, Vec<(usize, usize)>)>,
        field: &BigInt,
        verification_timeout: u64,
        apply_deduction_assigned: bool,
        verbose: bool
    ) -> EquivalenceVerification {
        let mut fixed_constraints_1 = Vec::new();
        for mut c in constraints_1{
            Constraint::fix_constraint(&mut c, field);
            fixed_constraints_1.push(c);
        }
        let mut fixed_constraints_2 = Vec::new();
        for mut c in constraints_2{
            Constraint::fix_constraint(&mut c, field);
            fixed_constraints_2.push(c);
        }

        EquivalenceVerification {
            template_name: template_name.clone(),
            original_file: original_file.clone(),
            signals_1,
            signals_2,
            inputs_1,
            inputs_2,
            outputs_1,
            outputs_2, 
            implications_equivalence,
            constraints_1: fixed_constraints_1,
            constraints_2: fixed_constraints_2,
            field: field.clone(),
            verification_timeout, 
            added_nodes: HashSet::new(),
            apply_deduction_assigned,
            verbose
        }
    }
    
}





/// Debug annotations carried into the generated `.smt2` as comments.
///
/// A query is written in `s_{id}` and `spec_..._v_k`, which say nothing about
/// which wire of the circom program or which tag of the specification they came
/// from. Reading a failed query then means cross-referencing the correspondence
/// file by hand. These are what the emitter turns into `;` comments so the file
/// explains itself.
///
/// Every field is optional: an empty `ProblemAnnotations` produces the same
/// query as before, minus nothing.
#[derive(Default, Clone, Debug)]
pub struct ProblemAnnotations {
    /// Lines for the block at the top of the file (what problem this is).
    pub header: Vec<String>,
    /// Whether the symbols themselves carry the circuit's names
    /// (`r1cs_main_isz_in`) instead of the plain `s_{id}`. Off by default, which
    /// is what `--check_correctness` has always written; the names in
    /// [`Self::signals`] are used for the trailing comments either way, so a
    /// terse file still says which wire each symbol is.
    pub descriptive_symbols: bool,
    /// Circuit signal id -> its name in the original program (`main.lt.in[0]`).
    pub signals: HashMap<usize, String>,
    /// Specification variable -> what it is bound to.
    pub spec_vars: HashMap<String, String>,
    /// Parallel to `constraints_1`: where each constraint comes from.
    pub constraints: Vec<String>,
    /// Parallel to `constraints_2`: where each atom comes from.
    pub atoms: Vec<String>,
    /// Parallel to `implications_equivalence`: what each implication stands in
    /// for, and who is on the hook for proving it.
    pub implications: Vec<String>,
}

impl ProblemAnnotations {
    pub fn is_empty(&self) -> bool {
        self.header.is_empty()
            && self.signals.is_empty()
            && self.spec_vars.is_empty()
            && self.constraints.is_empty()
            && self.atoms.is_empty()
    }
}

/// One line of SMT-LIB comment. Newlines are flattened: a comment runs to the
/// end of the line, so an embedded one would turn the rest of the note into
/// code the solver tries to parse.
/// The verdict of one solver run -- or an abort, when the run was not a verdict
/// at all.
///
/// `UNKNOWN` is kept for the two things it can honestly mean: the process was cut
/// short by US (the `--timeout`, or a cancel from the racing mode), or the solver
/// answered `unknown` itself. Anything else -- a non-zero exit, a crash, an empty
/// answer, an `(error ...)` from a malformed query -- is the SOLVER FAILING, and
/// mapping that to `UNKNOWN` files a bug under "the query was too hard": the run
/// reads as a timeout, the number lands in the report, and nobody looks at the
/// query again. Those abort, with what it takes to reproduce them.
///
/// Call this BEFORE deleting the `.smt2`: on the abort path the file has to
/// survive, and the message points at it.
pub fn solver_verdict(
    solver: &str,
    smt2_path: &str,
    stopped_by_us: bool,
    output: &std::process::Output,
) -> PossibleResult {
    let stdout = String::from_utf8_lossy(&output.stdout);
    let answer = stdout.lines().rev().find(|l| !l.trim().is_empty()).map(str::trim);
    match answer {
        Some("unsat") => PossibleResult::VERIFIED,
        Some("sat") => PossibleResult::FAILED,
        // We killed it: a partial answer, or none at all, is exactly what that
        // looks like, and it is a genuine UNKNOWN.
        _ if stopped_by_us => PossibleResult::UNKNOWN,
        Some("unknown") => PossibleResult::UNKNOWN,
        _ => {
            let stderr = String::from_utf8_lossy(&output.stderr);
            let tail: Vec<&str> = stdout.lines().rev().take(10).collect();
            let tail: Vec<&str> = tail.into_iter().rev().collect();
            panic!(
                "{solver} failed on {smt2_path}: it ran to completion on its own ({status}) \
                 without answering `sat`, `unsat` or `unknown`, so there is no verdict to report \
                 -- and calling it a timeout would hide the failure. The query is kept at \
                 {smt2_path} whatever --verbose says, so it can be replayed.\n\
                 --- last stdout lines ---\n{tail}\n\
                 --- stderr ---\n{stderr}",
                solver = solver,
                smt2_path = smt2_path,
                status = output.status,
                tail = if tail.is_empty() { "(no output)".to_string() } else { tail.join("\n") },
                stderr = if stderr.trim().is_empty() { "(empty)" } else { stderr.trim() },
            )
        }
    }
}

/// The same rule as [`solver_verdict`], for a solver driven through its API
/// instead of as a process (z3, and civer through it).
///
/// The difference is what `unknown` means there. A process solver that never
/// says `sat`, `unsat` or `unknown` has failed; z3 says `unknown` in cases that
/// are perfectly legitimate -- the `set_timeout_msec` we gave it expired, we
/// interrupted it, or the theory is undecidable and it says so
/// (`(incomplete ...)`, `smt tactic failed to show goal to be sat/unsat`, which
/// is the normal answer on a hard nonlinear query). Only z3's own reason tells a
/// real failure apart from those, so that is what is checked; everything else
/// stays UNKNOWN.
///
/// Returns the log line to record, which carries the reason: reporting a plain
/// "TIMEOUT" for a query z3 refused for some other reason is the same hiding
/// this is meant to stop, even where aborting would be wrong.
pub fn api_unknown_verdict(solver: &str, reason: Option<String>) -> String {
    let reason = reason.unwrap_or_default();
    let reason = reason.trim();
    if reason.to_ascii_lowercase().contains("error") {
        panic!(
            "{solver} failed: it answered `unknown` and gave {reason:?} as the reason, which is \
             the solver reporting an error, not a query it could not decide. Calling that a \
             timeout would hide it. Re-run with --verbose to keep the .smt2 of this query.",
            solver = solver,
            reason = reason,
        );
    }
    format!(
        "### {}: UNKNOWN, reason given by the solver: {}\n",
        solver,
        if reason.is_empty() { "(none)" } else { reason }
    )
}

pub fn comment(text: &str) -> String {
    format!("; {}", text.replace('\n', " ").replace('\r', " "))
}

/// Appends `; note` to a line of SMT-LIB.
pub fn with_comment(line: String, note: Option<&String>) -> String {
    match note {
        Some(note) => format!("{}   ; {}", line, note.replace('\n', " ").replace('\r', " ")),
        None => line,
    }
}

#[derive(Clone)]
pub struct CorrectnessVerification {
    pub template_name: String,
    pub original_file: String,
    pub signals_1: LinkedList<usize>,
    pub signals_2: Vec<String>,
    pub inputs_1: Vec<usize>,
    pub outputs_1: Vec<usize>,
    pub inputs_2: Vec<String>,
    pub outputs_2: Vec<String>,
    pub constraints_1: Vec<Constraint<usize>>,
    pub constraints_2: Vec<String>,
    pub implications_equivalence: Vec<(Vec<(usize, String)>, Vec<(usize, String)>)>,
    pub field: BigInt,
    pub verification_timeout: u64,
    pub added_nodes: HashSet<usize>,
    pub verbose: bool,
    pub macros: IndexMap<String, String>,
    /// Prefix of the `.smt2` this problem gets written to.
    ///
    /// `--check_correctness` and `--check_semantic_equivalence` share this
    /// struct and its encoder, so without this their files are
    /// indistinguishable on disk. Defaults to `"correctness"`; the semantic
    /// mode overrides it with [`CorrectnessVerification::with_file_prefix`].
    pub file_prefix: String,
    /// What the emitter turns into comments. See [`ProblemAnnotations`].
    pub annotations: ProblemAnnotations,
}

impl CorrectnessVerification{

    pub fn new(
        template_name: &String,
        original_file: &String,
        signals_1: LinkedList<usize>,
        signals_2: Vec<String>,
        inputs_1: Vec<usize>,
        inputs_2:Vec<String>,
        outputs_1: Vec<usize>,
        outputs_2:Vec<String>,
        constraints_1: Vec<Constraint<usize>>,
        constraints_2: Vec<String>,
        implications_equivalence: Vec<(Vec<(usize, String)>, Vec<(usize, String)>)>,
        field: &BigInt,
        verification_timeout: u64, 
        verbose: bool,
        macros:  IndexMap<String, String>,
    ) -> CorrectnessVerification {
        let mut fixed_constraints_1 = Vec::new();
        for mut c in constraints_1{
            Constraint::fix_constraint(&mut c, field);
            fixed_constraints_1.push(c);
        }


        CorrectnessVerification {
            template_name: template_name.clone(),
            original_file: original_file.clone(),
            signals_1,
            signals_2,
            inputs_1,
            inputs_2,
            outputs_1,
            outputs_2, 
            implications_equivalence,
            constraints_1: fixed_constraints_1,
            constraints_2: constraints_2,
            field: field.clone(),
            verification_timeout, 
            added_nodes: HashSet::new(),
            verbose,
            macros,
            file_prefix: "correctness".to_string(),
            annotations: ProblemAnnotations::default()
        }
    }

    /// Names the `.smt2` files of this problem after `prefix` instead of
    /// `correctness`. Kept as a builder rather than an argument to `new` so the
    /// template-level caller does not have to change.
    pub fn with_file_prefix(mut self, prefix: &str) -> CorrectnessVerification {
        self.file_prefix = prefix.to_string();
        self
    }

    /// Attaches the comments the generated `.smt2` is annotated with.
    pub fn with_annotations(mut self, annotations: ProblemAnnotations) -> CorrectnessVerification {
        self.annotations = annotations;
        self
    }

}