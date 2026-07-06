
pub mod determinism;
mod dag_extension;

use rayon::prelude::*;
use rayon::ThreadPoolBuilder;

use std::collections::{HashMap, HashSet};
use std::marker::{Send, Sync};
use serde::{Serialize,Deserialize};
use clap::{ValueEnum};
use strum_macros::{Display};
use std::borrow::Borrow;
use itertools::Itertools;
use std::time::{Instant};

use solvers_interface::{PossibleResult};
use circuit_graphing::directed_acyclic_graph::mixed_graph::MixedGraph;
use circuits_and_constraints::constraint::Constraint;
use circuits_and_constraints::circuit::Circuit;
use utils::small_utilities::dfs_merge_set_in_dag;
use utils::union_find::{UnionFind};

#[derive(Serialize, Deserialize, Default)]
pub struct ResultInfo {
    previously_verified_nodes: HashSet<usize>,
    verified_nodes: HashSet<usize>,
    failed_nodes: HashSet<usize>,
    unknown_nodes: HashSet<usize>,
    unknown_undivisible_nodes: HashSet<usize>,
    pub studied_nodes: HashMap<usize, PossibleResult>,
    total_constraints: usize,
    verified_constraints: usize,
    fails_original_templates: Option<HashSet<String>>,// include which constraints fail in each component or not?
    number_unverified_orig_constraints: Option<usize>, // the number of constraints included in the unverified templates
    number_unverified_orig_constraints_noreps: Option<usize>, // the number of constraints included in the unverified templates
    unverified_nodes_to_templates: Option<HashMap<usize, HashSet<String>>>,
    unverified_nodes_to_nodes: Option<HashMap<usize, HashSet<usize>>>,
}

#[derive(Debug, Default, Display, Copy, Clone, ValueEnum, PartialEq)]
pub enum Property {
    #[default]
    Determinism
}

#[derive(Debug, Display, Copy, Clone, ValueEnum, PartialEq)]
pub enum PreprocessingMethods {
    DualDistanceOrdering,
    MergeDistanceClasses,
}

#[derive(Debug, Default, Display, Copy, Clone, ValueEnum, PartialEq)]
pub enum DAGExtensionMethod {
    #[default]
    CyclesCover,
    MiniZinc
}

#[derive(Debug, Default, Display, Copy, Clone, ValueEnum, PartialEq)]
pub enum SolverTarget {
    #[default]
    AllOutput, 
    OneOutput
}

pub struct HierarchyOptions {
    pub property: Property,
    pub preprocessing: Vec<PreprocessingMethods>,
    pub solver_target: SolverTarget,
    pub dag_extension_method: DAGExtensionMethod,
    pub num_cores: usize,
    pub timeout: usize,
    pub debug: usize
}

impl Default for HierarchyOptions {
    fn default() -> HierarchyOptions {
        HierarchyOptions {
            property: Property::default(),
            preprocessing: Vec::new(),
            solver_target: SolverTarget::default(),
            dag_extension_method: DAGExtensionMethod::default(),
            num_cores: 1,
            timeout: 50,
            debug: 0
        }
    }
}

pub trait SMTFormula {

    fn preprocess<C: Constraint, S: Circuit<C>>(circuit: &S, graph: &MixedGraph, index: usize) -> Self;
    // NOTE: the following method might need to be changed if/when more properties are added
    fn finalise_and_check<C: Constraint, S: Circuit<C>>(&mut self, circuit: &S, graph: &MixedGraph, index: usize, inputs: &[usize], outputs: &[usize], timeout: u64) -> PossibleResult;
    fn undo_finalise(&mut self) -> ();
}

fn apply_orientation_preprocessing(method: PreprocessingMethods, graph: &mut MixedGraph) -> () {
    match method {
        PreprocessingMethods::DualDistanceOrdering => {graph.orient_by_partial_order();}
        PreprocessingMethods::MergeDistanceClasses => {graph.merge_equivalence_classes_by_distance_and_orient(0);}
        _ => {panic!("OrientationMethod {method} has no implementation");}
    }
}

pub fn hierarchy_solver<C: Constraint, S: Circuit<C> + Sync, P: SMTFormula + Send + Sync>(circ: &S, partition: Vec<Vec<usize>>, options: HierarchyOptions) -> ResultInfo {

    // Initialise the Graph from Partition
    let mut graph = MixedGraph::from_circuit(circ, partition, false);
    graph.invert_edge_direction();
    let HierarchyOptions {property, preprocessing, solver_target, num_cores, timeout, dag_extension_method, debug, ..} = options;

    let mut last_instant = Instant::now();

    // Apply any preprocessing steps to the graph to give initial inputs
    for method in preprocessing.into_iter() {apply_orientation_preprocessing(method, &mut graph);}

    if debug > 0 {println!("LOG: hierarchy solver preprocessing done in {:?}", last_instant.elapsed().as_secs_f32()); last_instant = Instant::now();}

    // Step 2: In rounds - in parallel - check all-outputs 
    //  solve DAGNode orientation
    //  Repeat until no new arcs are possible
    let mut parts_to_attempt: Vec<usize> = (0..graph.n).into_iter().collect();
    let thread_pool = ThreadPoolBuilder::new().num_threads(num_cores).build().unwrap();
    let mut results_info = ResultInfo {
        total_constraints: circ.n_constraints(),
        ..Default::default()
    };
    let mut verified_parts: HashSet<usize> = HashSet::new();


    // Preprocess 
    thread_pool.install(
    || {
    
    let mut formulae: Vec<P> = (0..graph.n).into_par_iter().map(|x| P::preprocess(circ, &graph, x)).collect();
    let part_to_signals: Vec<HashSet<usize>> = (0..graph.n).into_par_iter().map(|part_id| graph.partition[part_id].iter().copied().flat_map(|coni| circ.get_constraint(coni).signals().into_iter()).collect()).collect();

    fn create_mutable_pointers<'a, T>(mut mutable_pointer: &'a mut[T], indices: &[usize]) -> Vec<&'a mut T> {
        let mut working_with: Vec<&mut T> = Vec::new();
        let mut offset: usize = 0;
        for index in indices.into_iter().copied() {
            let (left, right) = mutable_pointer.split_at_mut(index - offset +1);
            working_with.push(left.last_mut().unwrap());
            mutable_pointer = right;
            offset = index + 1;
        }

        working_with
    }

    loop {
        // STEP 1: Attempt to prove all outgoing for every vertex

        // NOTE: parts_to_attempt must be sorted here
        let working_with = create_mutable_pointers(&mut formulae, &parts_to_attempt);
        let inputs = parts_to_attempt.iter().copied().map(
            |idx|
            graph.dir_adjacencies[idx].iter().copied().flat_map(|part| graph.partition[part].iter().copied()).flat_map(|coni| circ.get_constraint(coni).signals().into_iter() ).collect::<HashSet<_>>().intersection(&part_to_signals[idx]).copied().collect()
        );

        let outputs = parts_to_attempt.iter().copied().map(
            |idx|
            graph.adjacencies[idx].iter().copied().filter(|odx| !graph.dir_adjacencies[idx].contains(odx)
                ).flat_map(|part| graph.partition[part].iter().copied()).flat_map(|coni|circ.get_constraint(coni).signals().into_iter() ).collect::<HashSet<_>>().intersection(&part_to_signals[idx]).copied().collect()
        );

        let args: Vec<(usize, &mut P, Vec<usize>, Vec<usize>)> = itertools::izip!(parts_to_attempt.iter().copied(), working_with.into_iter(), inputs, outputs).collect();

        // TODO: implement OneOutput - it will require something a little different
        let results: Vec<PossibleResult> = args.into_par_iter().map(|(index, formula, inputs, outputs)| formula.finalise_and_check(circ, &graph, index, &inputs, &outputs, options.timeout as u64)).collect();
        let undo: Vec<_> = create_mutable_pointers(&mut formulae, &parts_to_attempt).into_par_iter().map(|formula| formula.undo_finalise()).collect();


        if !results.iter().any(|res| res == &PossibleResult::VERIFIED) {break;}

        let mut viable_arcs: Vec<(usize, usize)> = Vec::new();

        for part_id in parts_to_attempt.iter().copied() {
            if results[part_id] == PossibleResult::VERIFIED {
                verified_parts.insert(part_id);
                results_info.verified_nodes.insert(part_id);
                viable_arcs.extend(
                    graph.adjacencies[part_id].iter().copied()
                        .filter(|odx| !graph.dir_adjacencies[part_id].contains(odx) && !graph.dir_adjacencies[*odx].contains(&part_id) )
                        .map(|odx| (part_id, odx))
                );
            }
        }

        if debug > 0 {println!("LOG: finished solving for all-outs {:?}", last_instant.elapsed().as_secs_f32()); last_instant = Instant::now();}
        if debug > 1 {println!("LOG: found {:?} viable arcs", viable_arcs.len());}

        // STEP 2: Orient maximum possible edges as DAG and apply these
        let chosen_arcs = match dag_extension_method {
            DAGExtensionMethod::CyclesCover => { crate::hierarchy_solver::dag_extension::cycles_cover_interface::extend_dag_cycles_cover(&mut graph, viable_arcs) },
            DAGExtensionMethod::MiniZinc => { crate::hierarchy_solver::dag_extension::minizinc_interface::extend_dag_minizinc(&graph, viable_arcs) }
            _ => {panic!("DAGExtensionMethod {dag_extension_method} has no implementation");}
        };

        if debug > 0 {println!("LOG: finished solving max arcs in {:?}", last_instant.elapsed().as_secs_f32()); last_instant = Instant::now();}
        if debug > 1 {println!("LOG: managed to orient {:?} viable arcs", chosen_arcs.len());}

        if chosen_arcs.len() == 0 {break;}

        // update parts_to_attempt with parts that had new input
        graph.orient_by_arcs(&chosen_arcs);
        parts_to_attempt = chosen_arcs.into_iter().map(|(_, v)| v).sorted().dedup().collect();
    }

    }
    );
    
    // Step 3: Merge all remaining arcs 
    //    -- TODO: keep known implications to be able to pass to solver next round
    //    -- TODO: keep indices so don't need to remake verified nodes
    let unoriented_edges = (0..graph.m).into_iter().filter(|&e| !graph.edge_oriented(e));
    let mut unoriented_components = UnionFind::new(false);
    for v in 0..graph.n {unoriented_components.find(v);}
    for e in unoriented_edges {unoriented_components.union([graph.edges[e].0,graph.edges[e].1].into_iter());}

    // Step 3.1 expand these to include all vertices that can reach themselves
    //   -- keep expanding any that returned positive as the merge may add new cycles
    let mut parts = unoriented_components.get_component_as_hashmap();
    let mut parts_changed: Vec<usize> = parts.keys().copied().collect();
    while parts_changed.len() > 0 {
        for key in parts_changed.into_iter() {
            // Expand part to include all cycles that would result from the merge
            let to_merge = dfs_merge_set_in_dag(&parts[&key], &graph.dir_adjacencies);
            unoriented_components.union(to_merge.into_iter());
        }

        let new_parts = unoriented_components.get_component_as_hashmap();
        parts_changed = new_parts.keys().copied().filter(|key| new_parts[key].len() != parts[key].len() ).collect();
        parts = new_parts;
    }

    // Step 3.2 Merge these expanded parts
    let (merged_graph, parent_to_newidx) = graph.merge(&mut unoriented_components);
    graph = merged_graph;

    // Step 4: Re-check remaining nodes -- TODO
    unimplemented!("Don't know what to do to pass it back here");
}