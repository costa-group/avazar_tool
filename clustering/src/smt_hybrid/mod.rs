use std::collections::{HashMap, HashSet};
use strum_macros::Display;
use clap::ValueEnum;

use circuits_constraints_and_algebra::circuit::Circuit;
use circuits_constraints_and_algebra::constraint::Constraint;
use circuit_graphing::directed_acyclic_graph::DAGNode;
use utils::small_utilities::DecomposeOptions;
use crate::decompose_circuit::decompose_circuit_and_return_dagnodes;
use crate::smt_hybrid::guided_clustering::guided_clustering;
use utils::structure::StructureReader;

pub mod guided_clustering;
pub mod shared_merge;

#[derive(Debug, Default, Display, Copy, Clone, ValueEnum, PartialEq)]
pub enum HybridClusteringMethods {
    #[default]
    GuidedClustering
}

pub struct HybridClusteringMethodOptions {
    pub tiebreaking_strategy: TiebreakingStrategy,
    pub recipient_requires_subsets: bool,
}

#[derive(Debug, Default, Display, Copy, Clone, ValueEnum, PartialEq)]
pub enum TiebreakingStrategy {
    #[default]
    FirstInList
}

pub struct HybridClusteringOptions<'a> {
    pub guide_decompose_options: DecomposeOptions<'a>,
    pub hybrid_decompose_method: HybridClusteringMethods,
    pub hybrid_decompose_options: HybridClusteringMethodOptions,
}

pub fn circuit_and_smt_hybrid_clustering<'a, Cons: Constraint, Circ: Circuit<Cons> , Atom: Constraint, Smt: Circuit<Atom>>(
    circ: &'a Circ, smt: &'a Smt,
    options: HybridClusteringOptions<'a>,
    debug: usize
) -> StructureReader { // (HashMap<usize, DAGNode<'a, Cons, Circ>>, HashMap<usize, DAGNode<'a, Atom, Smt>>) {

    let HybridClusteringOptions { guide_decompose_options, hybrid_decompose_method, hybrid_decompose_options, .. } = options;

    let (_, mut guide_clustering) = decompose_circuit_and_return_dagnodes(circ, &mut (0..), guide_decompose_options);

    let results = match options.hybrid_decompose_method {
        HybridClusteringMethods::GuidedClustering => {
            guided_clustering(circ, smt, &mut guide_clustering, hybrid_decompose_options, debug);
        }

    };

    unimplemented!("Hybrid Clustering Not Yet Implemented");
}

