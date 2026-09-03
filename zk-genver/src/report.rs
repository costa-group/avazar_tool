use serde::Serialize;
use std::path::Path;
use std::fs;
use solvers_interface::{PossibleSolver, PossibleResult};

#[derive(Serialize)]
#[serde(rename_all = "snake_case")]
pub enum CheckType {
    Determinism,
    Equivalence,
    Correctness,
    SemanticEquivalence,
}

/// Top-level verdict for the entire circuit.
/// - Verified: no failures, no timeouts
/// - Failed: at least one counterexample found
/// - Unknown: no counterexamples but at least one solver timeout
#[derive(Serialize)]
#[serde(rename_all = "snake_case")]
pub enum OverallResult {
    Verified,
    Failed,
    Unknown,
}

#[derive(Serialize)]
pub struct ReportSummary {
    pub total_nodes: usize,
    pub verified_nodes: usize,
    /// Nodes proven safe by syntactic analysis before SMT (determinism only)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub previously_verified_nodes: Option<usize>,
    pub failed_nodes: usize,
    /// Ran out of time or came back inconclusive: a question left open.
    pub timeout_nodes: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub total_constraints: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub verified_constraints: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub verified_constraints_pct: Option<f64>,
}

#[derive(Serialize)]
pub struct NodeResult {
    pub node_id: usize,
    pub node_name: String,
    /// One of: "VERIFIED", "FAILED", "TIMEOUT", "NOTHING", "NOT_STUDIED"
    pub result: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub num_constraints: Option<usize>,
    /// Wall-clock seconds this node took, solver call included. Absent when the
    /// node was settled without one -- a syntactic proof, say.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub seconds: Option<f64>,
    /// True when the node was proven safe by syntactic analysis (determinism only)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub previously_verified: Option<bool>,
}

#[derive(Serialize)]
pub struct VerificationReport {
    pub check_type: CheckType,
    pub input_circuit: String,
    /// Second circuit path, present only for equivalence checks
    pub second_circuit: Option<String>,
    pub solver: String,
    pub timeout_ms: u64,
    pub overall_result: OverallResult,
    pub summary: ReportSummary,
    pub nodes: Vec<NodeResult>,
    /// Circom template names whose constraints are unverified (determinism + --original_structure only)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub failed_templates: Option<Vec<String>>,
}

pub fn solver_to_str(solver: solvers_interface::PossibleSolver) -> &'static str {
    match solver {
        PossibleSolver::CIVER  => "CIVER",
        PossibleSolver::PICUS  => "PICUS",
        PossibleSolver::FFSOL  => "FFSOL",
        PossibleSolver::CVC5   => "CVC5",
        PossibleSolver::YICES  => "YICES",
        PossibleSolver::NIAZ3  => "NIAZ3",
        PossibleSolver::Z3     => "Z3",
        PossibleSolver::ALL    => "ALL",
    }
}

pub fn possible_result_str(r: &solvers_interface::PossibleResult) -> &'static str {
    match r {
        PossibleResult::VERIFIED   => "VERIFIED",
        PossibleResult::FAILED     => "FAILED",
        PossibleResult::UNKNOWN    => "TIMEOUT",
        PossibleResult::NOSTUDIED  => "NOT_STUDIED",
        PossibleResult::NOTHING    => "NOTHING",
    }
}

pub fn compute_overall(failed_empty: bool, unknown_empty: bool) -> OverallResult {
    if failed_empty && unknown_empty {
        OverallResult::Verified
    } else if !failed_empty {
        OverallResult::Failed
    } else {
        OverallResult::Unknown
    }
}

pub fn write_report(report: &VerificationReport, path: &Path) {
    match serde_json::to_string_pretty(report) {
        Ok(json) => {
            if let Err(e) = fs::write(path, &json) {
                eprintln!("Warning: could not write report to {}: {}", path.display(), e);
            } else {
                println!("Report written to {}", path.display());
            }
        }
        Err(e) => eprintln!("Warning: could not serialize report: {}", e),
    }
}
