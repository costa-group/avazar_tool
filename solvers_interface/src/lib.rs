pub mod civer_interface;
pub mod picus_interface;
pub mod ffsol_interface;
pub mod cvc5_interface;
pub mod yices_interface;
pub mod nia_z3_interface;
pub mod z3_interface;
pub mod parallel_interface;
mod smt2_utils;
use indexmap::IndexMap;

use std::collections::HashMap;

use std::collections::{HashSet, LinkedList};
use std::path::Path;
use num_bigint_dig::BigInt;
use serde::{Serialize,Deserialize};

use circuits_constraints_and_algebra::algebra::{EncodableConstraint, Constraint};

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum PossibleSolver{
    PICUS, CIVER, FFSOL, CVC5, YICES, NIAZ3, Z3, ALL
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

pub fn correctness_smt2_name(original_file: &str, template_name: &str, solver: &str) -> String {
    let random: u32 = rand::Rng::gen(&mut rand::thread_rng());
    let original = sanitize_name(original_file, false);
    if template_name.is_empty() {
        let file_name = format!("correctness_{}_{}_{}.smt2", original, solver, random);
        ensure_safe_length(file_name, original_file, template_name, |o, _t| {
            format!("correctness_{}_{}_{}.smt2", o, solver, random)
        })
    } else {
        let template = sanitize_name(template_name, false);
        let file_name = format!("correctness_{}_{}_{}_{}.smt2", original, template, solver, random);
        ensure_safe_length(file_name, original_file, template_name, |o, t| {
            format!("correctness_{}_{}_{}_{}.smt2", o, t, solver, random)
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
            macros
        }
    }
    
}