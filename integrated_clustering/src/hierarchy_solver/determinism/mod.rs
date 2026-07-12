use std::collections::{LinkedList, HashSet};

use super::SMTFormula;

pub type DeterminismFormula = LinkedList<String>;

use solvers_interface::{PossibleResult, SafetyVerification};
use solvers_interface::civer_interface::study_safety;

use circuit_graphing::directed_acyclic_graph::mixed_graph::MixedGraph;
use circuits_constraints_and_algebra::constraint::Constraint;
use circuits_constraints_and_algebra::circuit::Circuit;
use circuits_constraints_and_algebra::r1cs::R1CSConstraint;

use circuits_constraints_and_algebra::algebra::EncodableConstraint;

impl SMTFormula for DeterminismFormula {
    // TODO: Ask clara again about preprocesing because this seems like it doesn't work

    fn preprocess<C: Constraint, S: Circuit<C>>(_circuit: &S, _graph: &MixedGraph, _index: usize) -> Self {LinkedList::new()}
    // NOTE: the following method might need to be changed if/when more properties are added
    fn finalise_and_check<C: Constraint + EncodableConstraint + Clone + Sync, S: Circuit<C>>(&mut self, circuit: &S, graph: &MixedGraph, index: usize, inputs: &[usize], outputs: &[usize], timeout: u64) -> PossibleResult {
        
        // TODO: this is currently working only for R1CSConstraints as it smt_utils seems to only work for these.
        let problem_statement = SafetyVerification {
            template_name: format!("{index}"),
            original_file: format!("placeholder_filename"),
            signals: graph.partition[index].iter().copied().flat_map(|coni| circuit.get_constraint(coni).signals().into_iter()).collect(),
            inputs: inputs.into_iter().copied().collect(),
            outputs: outputs.into_iter().copied().collect(),
            constraints: graph.partition[index].iter().copied().map(|coni| circuit.get_constraint(coni).clone()).collect(),
            implications_safety: Vec::new(),
            field: circuit.prime().clone(),
            verification_timeout: timeout,
            added_nodes: HashSet::new(),
            apply_deduction_assigned: true,
            include_niaz3_in_all: false, // TODO: query
            verbose: false 
        };

        let (result, _) = study_safety(&problem_statement);
        result
    }
    fn undo_finalise(&mut self) -> () {}

}