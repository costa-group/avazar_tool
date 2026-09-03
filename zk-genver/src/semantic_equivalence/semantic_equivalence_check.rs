//! `--check_semantic_equivalence`: proves the circuit and its llzk
//! specification agree, one hybrid cluster at a time.
//!
//! The verification unit is not a circom template but a **cluster pair** from
//! `clustering::smt_hybrid`: circuit and formula are partitioned together, and
//! cluster `k` of one side is the counterpart of cluster `k` of the other. That
//! shared id is the whole semantic link — no name matching involved.
//!
//! One pass: read the r1cs, structure and correspondence; get the atoms from the
//! llzk preprocessor; cluster once, guided by the specification; verify every
//! pair; aggregate.
//!
//! ## Two ways to cluster
//!
//! By default the component structure drives it: one clustering per instance,
//! and a subcomponent enters its parent's query as an abstraction.
//!
//! With `--resolved_formula` there is no structure to drive anything. The file
//! is `llzk_smt_preprocessor --mode single` output -- every instance's tags in
//! one dictionary, each key prefixed with the instance it came from -- and the
//! whole r1cs is clustered against that one formula, so a cluster may cut across
//! instances. The specification is still read, for the atoms' SMT-LIB text.
//! `prove_flat` and [`flat_mode`](super::flat_mode) are that path.
//!
//! ## Deliberately not here yet
//!
//! - **No re-decomposition.** A cluster that comes back UNKNOWN is not split
//!   further, so `--clustering_size` is not read.
//! - **No equivalence classes.** Every cluster is verified on its own. Biggest
//!   cost of this mode versus the template-level one, and the first thing to add.
//! - **No refinement rounds by default**, only under `--extra_rounds` — with one
//!   difference from the template modes: there a counterexample keeps expanding
//!   whatever the flag says, here every round counts against it.
//!
//! `--apply_predecessors` and `--apply_bidirectional` mean the same here as in
//! the template modes: which way to look for the neighbours to abstract, and
//! then to inline. Successors by default.

use indexmap::IndexMap;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::io::BufReader;

use circuits_constraints_and_algebra::lightweight_circuit::LightweightCircuit;
use circuits_constraints_and_algebra::num_bigint::BigInt;
use circuits_constraints_and_algebra::r1cs::R1CSConstraint as Constraint;
use circuits_constraints_and_algebra::smt_formula::Formula;
use clustering::smt_hybrid::{
    circuit_and_smt_hybrid_clustering_into_structurereader,
    structure_driven_circuit_and_smt_hybrid_clustering_into_structurereader,
    HybridClusteringMethodOptions, HybridClusteringMethods, HybridClusteringOptions,
    TiebreakingStrategy,
};
use serde::Serialize;
use solvers_interface::{PossibleResult, PossibleSolver};
use utils::read_correspondence::read_signal_correspondence;
use utils::read_specification::read_smt_specification;
use utils::small_utilities::DecomposeOptions;
use utils::structure::{transform_structure_reader, NodeInfo, StructureInfo, StructureReader, TimingInfo};
use crate::semantic_equivalence::structure_from_spec::derive_structure;
use circuits_constraints_and_algebra::constraint::Constraint as _;

use crate::processing_utils::process_constraints;
use crate::report;
use crate::semantic_equivalence::atoms::{build_atoms, required_macro_definitions, AtomTable};
use crate::semantic_equivalence::flat_mode::{align_atoms, read_flat_formula, restrict_to_asserted};
use crate::semantic_equivalence::modular_reasoning::{
    check_cluster, child_implication, has_bound_output, index_by_id, unbound_boundary_signals,
    ChildPorts, ClusterPair, InlinedInstances, InstanceInterface, VerificationContext,
};
use crate::Input;

/// The verdict of one cluster pair.
///
/// `LocalCounterexample` has its own variant because it is NOT "the circuit is
/// wrong": a cluster boundary was chosen by the algorithm, not written by anyone,
/// so a counterexample inside it may be unreachable once the abstracted
/// neighbours are taken into account.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ClusterVerdict {
    Verified,
    /// The solver found a counterexample and nothing was abstracted away to
    /// get it: this cluster had no neighbours, so its query is the whole
    /// story and the disagreement is real.
    Failed,
    /// The solver found a counterexample *within this cluster's boundary*,
    /// with at least one neighbouring cluster abstracted rather than
    /// asserted. Inconclusive: the counterexample may be unreachable once the
    /// neighbours are taken into account.
    LocalCounterexample,
    /// Timeout, or the solver gave up.
    Unknown,
}

impl ClusterVerdict {
    fn as_str(&self) -> &'static str {
        match self {
            ClusterVerdict::Verified => "VERIFIED",
            ClusterVerdict::Failed => "FAILED",
            ClusterVerdict::LocalCounterexample => "INCONCLUSIVE_LOCAL_COUNTEREXAMPLE",
            ClusterVerdict::Unknown => "UNKNOWN",
        }
    }
}

/// The clustering as the algorithm returned it, before anything is verified: one
/// entry per structure node, both sides. Unlike `ClusterDump` it covers the
/// specification side's own edges and the instances no query was built for.
#[derive(Serialize)]
pub struct RawClusteringDump {
    /// Position in the returned vector, which is the index into `structure.nodes`.
    pub index: usize,
    pub structure_node_id: usize,
    pub instance: String,
    pub circuit_clusters: Vec<RawClusterNode>,
    pub spec_clusters: Vec<RawClusterNode>,
}

#[derive(Serialize)]
pub struct RawClusterNode {
    pub node_id: usize,
    pub node_name: String,
    pub component_name: String,
    /// r1cs constraint indices on the circuit side, atom indices on the
    /// specification side.
    pub constraints: Vec<usize>,
    pub signals: Vec<usize>,
    pub input_signals: Vec<usize>,
    pub output_signals: Vec<usize>,
    pub predecessors: Vec<usize>,
    pub successors: Vec<usize>,
}

/// `--no_clustering`: one cluster pair per instance, each holding everything that
/// instance has, instead of a partition of it.
///
/// The clustering algorithm does not run at all -- no Leiden over the atoms, no
/// guided assignment of the constraints, no merge passes -- so `--target_size`
/// and `--skip_io_equivalence_merge` have nothing to act on. What comes out has
/// the same shape the real clustering returns (one pair per structure node, in
/// the structure's own order, the two sides sharing a cluster id), which is what
/// everything downstream reads.
///
/// One cluster per instance means no siblings, so nothing of an instance is ever
/// abstracted away from its own query: the verdict is about the whole template,
/// and a counterexample cannot be local to a boundary the algorithm chose. It
/// also means the query is as big as the template, which is the trade.
///
/// The ports are the structure's, intersected with what each side actually
/// mentions -- the same rule `guided_clustering` applies, where a cluster's
/// inputs are the subcircuit inputs AMONG ITS OWN SIGNALS. The circuit side then
/// declares the specification's boundary too, even where no constraint of the
/// instance mentions it: that interface is what the query equates, so it has to
/// exist as a symbol.
fn one_cluster_per_instance(
    structure_reader: &StructureReader,
    structure: &StructureInfo,
    formula: &Formula,
    constraints: &[Constraint<usize>],
) -> Vec<(StructureReader, StructureReader)> {
    let prefixes = instance_prefixes(structure);
    let sorted = |set: HashSet<usize>| {
        let mut v: Vec<usize> = set.into_iter().collect();
        v.sort_unstable();
        v
    };

    structure_reader
        .nodes
        .iter()
        .enumerate()
        .map(|(index, node)| {
            let instance = prefixes
                .get(&node.node_id)
                .cloned()
                .unwrap_or_else(|| "main".to_string());
            let atoms: Vec<usize> = formula
                .get_atomrange_for_component(&instance)
                .unwrap_or_else(|| {
                    panic!(
                        "The specification has no atoms for instance '{}', which the structure \
                         lists as node {}. The two were built from the same walk, so this is a \
                         mismatch between the structure and the specification.",
                        instance, node.node_id
                    )
                })
                .collect();

            let circuit_signals: HashSet<usize> = node
                .constraints
                .iter()
                .flat_map(|c| constraints[*c].signals())
                .collect();
            let spec_signals: HashSet<usize> = atoms
                .iter()
                .flat_map(|a| formula.atoms()[*a].signals.iter().copied())
                .collect();

            let ports = |declared: &Vec<usize>, own: &HashSet<usize>| -> Vec<usize> {
                let mut v: Vec<usize> =
                    declared.iter().copied().filter(|s| own.contains(s)).collect();
                v.sort_unstable();
                v.dedup();
                v
            };
            let spec_inputs = ports(&node.input_signals, &spec_signals);
            let spec_outputs = ports(&node.output_signals, &spec_signals);

            // Everything the constraints touch, plus the specification's boundary:
            // `check_cluster` states the obligation over the SPEC node's ports and
            // declares the circuit's symbols from this list, so a port missing here
            // would be equated to a symbol nothing declared.
            let mut circuit_all = circuit_signals.clone();
            circuit_all.extend(spec_inputs.iter().copied());
            circuit_all.extend(spec_outputs.iter().copied());

            // The cluster id is the instance's position: unique across instances,
            // and the same on both sides, which is the whole semantic link.
            let id = index;
            let one = |constraints: Vec<usize>,
                       signals: Vec<usize>,
                       input_signals: Vec<usize>,
                       output_signals: Vec<usize>| StructureReader {
                timing: TimingInfo::default(),
                nodes: vec![NodeInfo {
                    node_id: id,
                    node_name: format!("node_{}", id),
                    component_name: node.component_name.clone(),
                    constraints,
                    input_signals,
                    output_signals,
                    signals,
                    is_custom: false,
                    is_deterministic: false,
                    predecessors: Vec::new(),
                    successors: Vec::new(),
                }],
                equivalency_local: None,
                equivalency_structural: None,
            };

            (
                one(
                    node.constraints.clone(),
                    sorted(circuit_all),
                    ports(&node.input_signals, &circuit_signals),
                    ports(&node.output_signals, &circuit_signals),
                ),
                one(atoms, sorted(spec_signals), spec_inputs, spec_outputs),
            )
        })
        .collect()
}

fn raw_cluster_nodes(reader: &StructureReader) -> Vec<RawClusterNode> {
    let sorted = |v: &Vec<usize>| { let mut c = v.clone(); c.sort_unstable(); c };
    let mut out: Vec<RawClusterNode> = reader
        .nodes
        .iter()
        .map(|n| RawClusterNode {
            node_id: n.node_id,
            node_name: n.node_name.clone(),
            component_name: n.component_name.clone(),
            constraints: sorted(&n.constraints),
            signals: sorted(&n.signals),
            input_signals: sorted(&n.input_signals),
            output_signals: sorted(&n.output_signals),
            predecessors: sorted(&n.predecessors),
            successors: sorted(&n.successors),
        })
        .collect();
    out.sort_by_key(|n| n.node_id);
    out
}

/// Everything known about one cluster pair, written out by `--dump_dir`.
///
/// The verdict does not say why; what the query can reach does. The part easy to
/// get wrong is the adjacency: two clusters of one instance sharing no signal
/// have no edge, so a counterexample in one is reported as conclusive even when
/// it depends on a fact the other was meant to establish.
#[derive(Serialize)]
pub struct ClusterDump {
    pub cluster_id: usize,
    pub instance: String,
    pub verdict: String,
    /// Indices into the r1cs constraint list.
    pub circuit_constraints: Vec<usize>,
    pub circuit_signals: Vec<usize>,
    pub circuit_inputs: Vec<usize>,
    pub circuit_outputs: Vec<usize>,
    /// Neighbours in the circuit-side DAG, i.e. clusters sharing a signal.
    /// Empty means the cluster is isolated and a FAILED verdict from it is
    /// treated as conclusive.
    pub predecessors: Vec<usize>,
    pub successors: Vec<usize>,
    /// Atom indices on the specification side, and the signals they mention.
    pub spec_atoms: Vec<usize>,
    pub spec_signals: Vec<usize>,
    /// Neighbours on the specification side. Kept apart from the circuit ones:
    /// the two clusterings are built together and share cluster ids, but nothing
    /// forces their edges to agree, and only the circuit-side list is what
    /// `verify_instance` reads to decide whether a counterexample is conclusive.
    pub spec_predecessors: Vec<usize>,
    pub spec_successors: Vec<usize>,
    /// Boundary signals of this cluster the specification never names.
    pub unbound_signals: Vec<usize>,
}

#[derive(Default)]
pub struct ResultInfoSemanticEquivalence {
    /// Verdict per cluster id.
    pub clusters: HashMap<usize, ClusterVerdict>,
    /// Cluster id -> the instance it belongs to, for reporting.
    pub cluster_instance: HashMap<usize, String>,
    /// Cluster id -> how many r1cs constraints it holds.
    pub cluster_size: HashMap<usize, usize>,
    /// Cluster id -> wall-clock seconds spent on it, every refinement round
    /// included, since what a reader wants is what the cluster cost in total.
    pub cluster_seconds: HashMap<usize, f64>,
    /// Boundary signals of a cluster that the specification never names.
    pub unbound_signals: HashMap<usize, Vec<usize>>,
    /// One record per cluster pair, in the order they were verified. Only
    /// filled when `--dump_dir` was given.
    pub cluster_dump: Vec<ClusterDump>,
}

impl ResultInfoSemanticEquivalence {
    fn count(&self, verdict: ClusterVerdict) -> usize {
        self.clusters.values().filter(|v| **v == verdict).count()
    }
}

pub fn prove_semantic_equivalence(user_input: Input) -> Result<(), ()> {
    let spec_path = user_input
        .check_semantic_equivalence
        .as_ref()
        .expect("prove_semantic_equivalence called without a specification");

    // ---- solver gate (same restriction as correctness) --------------------
    if !matches!(
        user_input.solver_option,
        PossibleSolver::FFSOL
            | PossibleSolver::CVC5
            | PossibleSolver::YICES
            | PossibleSolver::NIAZ3
            | PossibleSolver::ALL
    ) {
        println!(
            "Z3, CIVER and PICUS cannot be used to check semantic equivalence. \
             Use FFSOL, CVC5, YICES, NIAZ3 or ALL instead"
        );
        return Err(());
    }

    // ---- inputs ----------------------------------------------------------
    let (constraints, signals, n_outputs, n_inputs) = process_constraints(&user_input.input_r1cs);
    let outputs: Vec<usize> = (1..n_outputs + 1).collect();
    let inputs: Vec<usize> = (n_outputs + 1..n_outputs + n_inputs + 1).collect();

    let correspondence_path = match user_input.input_correspondence.as_ref() {
        Some(p) => p,
        None => {
            eprintln!("--check_semantic_equivalence requires --correspondence");
            return Err(());
        }
    };
    let (pos_to_name, name_to_signal) =
        match read_signal_correspondence(&format!("{}", correspondence_path.display())) {
            Ok(c) => c,
            Err(e) => {
                eprintln!("Could not read the signal correspondence: {}", e);
                return Err(());
            }
        };

    let spec = match read_smt_specification(spec_path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Could not read the specification: {}", e);
            return Err(());
        }
    };

    // ---- the circuit structure -------------------------------------------
    // Derived from the specification and the correspondence unless
    // --input_structure hands one over. `components_info` is the component
    // tree, the parent's `vars_info` holds each child's ports, and the
    // correspondence turns those into signal ids; only the constraint-to-
    // instance split has to be inferred. See `structure_from_spec`.
    let structure_reader: StructureReader = match user_input.input_structure.as_ref() {
        Some(path) => match std::fs::File::open(path)
            .map_err(|e| e.to_string())
            .and_then(|f| serde_json::from_reader(BufReader::new(f)).map_err(|e| e.to_string()))
        {
            Ok(s) => s,
            Err(e) => {
                eprintln!("Could not read the circuit structure: {}", e);
                return Err(());
            }
        },
        None => {
            let constraint_signals: Vec<Vec<usize>> = constraints
                .iter()
                .map(|c| {
                    let mut s: Vec<usize> = c.signals().into_iter().collect();
                    s.sort_unstable();
                    s
                })
                .collect();
            match derive_structure(
                &spec.macros,
                &name_to_signal,
                n_outputs,
                n_inputs,
                &constraint_signals,
            ) {
                Ok(s) => {
                    println!(
                        "LOG: derived the circuit structure from the specification: {} instance(s)",
                        s.nodes.len()
                    );
                    s
                }
                Err(e) => {
                    eprintln!("Could not derive the circuit structure: {}", e);
                    return Err(());
                }
            }
        }
    };
    if let Err(msg) = check_structure_is_usable(&structure_reader) {
        eprintln!("{}", msg);
        return Err(());
    }
    // Written whether it was read or derived: `llzk_smt_preprocessor --structure`
    // needs one, and without this a run that derived its own has nothing to hand
    // it -- which is the whole input of `--resolved_formula`.
    if let Some(dump_dir) = &user_input.dump_dir {
        dump_json(dump_dir, "structure.json", &structure_reader, "Circuit structure");
    }
    let structure: StructureInfo = transform_structure_reader(clone_reader(&structure_reader));

    // ---- one prime for both sides ----------------------------------------
    let field: BigInt = match reconcile_prime(&spec, &user_input.prime) {
        Ok(p) => p,
        Err(msg) => {
            eprintln!("{}", msg);
            return Err(());
        }
    };

    // ---- step 2: the preprocessor ----------------------------------------
    let (formula, table) = match build_atoms(
        &spec.macros,
        &structure,
        &name_to_signal,
        &field,
        inputs.iter().copied().collect::<HashSet<_>>(),
        outputs.iter().copied().collect::<HashSet<_>>(),
        signals.iter().copied().max().unwrap_or(0) + 1,
        if user_input.flag_verbose { 2 } else { 1 },
    ) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("Could not preprocess the specification: {}", e);
            return Err(());
        }
    };

    // The formula as the clustering sees it, in the shape the preprocessor
    // writes: macro -> [ { instance, tag: [signals] } ].
    //
    // What it shows is the footprint the clustering actually gets, which is no
    // longer the preprocessor's: `build_atoms` closes each tag over the
    // temporaries it mentions and adds the tie groups as `equalityN` atoms. So
    // this is NOT byte-comparable with `llzk_smt_preprocessor --mode flat` any
    // more -- that view has the direct footprint, this one the closed one, and
    // the difference between the two IS the closure.
    //
    // No filtering of the invented ids either, and none is needed: after the
    // closure a footprint is r1cs wires and nothing else.
    if let Some(dump_dir) = &user_input.dump_dir {
        let mut by_macro: IndexMap<String, IndexMap<String, IndexMap<String, Vec<usize>>>> =
            IndexMap::new();
        for (idx, info) in table.atoms.iter().enumerate() {
            let signals = formula
                .atoms()
                .get(idx)
                .map(|a| {
                    let mut s = a.signals.clone();
                    s.sort_unstable();
                    s
                })
                .unwrap_or_default();
            // UNION, not insert: one instance can hold several atoms under the
            // same tag, and a JSON object has one key each. Overwriting would
            // show the last of them and quietly hide the rest -- in a file whose
            // whole purpose is to be diffed against the preprocessor's, which
            // unions them too (`merge_pair_resolved`).
            let entry = by_macro
                .entry(info.macro_name.clone())
                .or_default()
                .entry(info.instance.clone())
                .or_default()
                .entry(info.tag.clone())
                .or_insert_with(Vec::new);
            for signal in signals {
                if !entry.contains(&signal) {
                    entry.push(signal);
                }
            }
            entry.sort_unstable();
        }
        // The preprocessor writes the instance name as a field of the object,
        // not as a key, so mirror that.
        let shaped: IndexMap<String, Vec<serde_json::Value>> = by_macro
            .into_iter()
            .map(|(macro_name, instances)| {
                let entries = instances
                    .into_iter()
                    .map(|(instance, tags)| {
                        let mut obj = serde_json::Map::new();
                        obj.insert("instance".to_string(), serde_json::json!(instance));
                        for (tag, signals) in tags {
                            obj.insert(tag, serde_json::json!(signals));
                        }
                        serde_json::Value::Object(obj)
                    })
                    .collect();
                (macro_name, entries)
            })
            .collect();
        dump_json(dump_dir, "resolved.json", &shaped, "Resolved formula");
    }

    // ---- the flat alternative --------------------------------------------
    // With `--resolved_formula` the component structure stops driving the
    // clustering: the circuit is clustered against ONE formula, the whole
    // specification at once, and a cluster is free to cut across instances.
    // Everything above still runs -- the atoms' SMT-LIB text and the bindings
    // come from `build_atoms` either way, and that needs the structure.
    if let Some(flat_path) = user_input.resolved_formula.as_ref() {
        return prove_flat(
            &user_input,
            flat_path,
            &spec,
            &table,
            &constraints,
            &inputs,
            &outputs,
            &field,
            &pos_to_name,
        );
    }

    // ---- step 3: the hybrid clustering, once -----------------------------
    let circuit = LightweightCircuit::<Constraint<usize>>::from(
        &field,
        constraints.iter(),
        inputs.iter(),
        outputs.iter(),
    );

    let decompose_options = DecomposeOptions {
        target_size: if user_input.target_size == 0 {
            None
        } else {
            Some(user_input.target_size as f64)
        },
        debug: if user_input.flag_verbose { 2 } else { 0 },
        ..Default::default()
    };
    let hybrid_options = HybridClusteringOptions {
        manually_check_acyclic: user_input.manually_check_acyclic,
        guide_decompose_options: decompose_options,
        hybrid_decompose_method: HybridClusteringMethods::default(),
        hybrid_decompose_options: HybridClusteringMethodOptions {
            // A soundness condition, not a preference: with the specification as
            // the guide it forces signals(circuit k) subset of signals(spec k),
            // which is what lets a cluster's interface be stated in spec
            // variables at all.
            recipient_requires_subsets: true,
            merge_until_io_same: !user_input.skip_io_equivalence_merge,
            // Same flag that silences the vacuous-obligation check downstream:
            // with it there is one abort left, not two, and only one of them
            // could be silenced.
            empty_clusters_are_an_error: !user_input.allow_empty_clusters,
            ..Default::default()
        },
    };

    let clusterings = if user_input.no_clustering {
        // `--no_clustering`: the templates are the units, whole. See
        // `one_cluster_per_instance` -- nothing of the algorithm above runs.
        let pairs = one_cluster_per_instance(&structure_reader, &structure, &formula, &constraints);
        println!(
            "LOG: --no_clustering: one cluster pair per template, {} of them",
            pairs.len()
        );
        pairs
    } else {
        println!("LOG: clustering circuit and specification together");
        structure_driven_circuit_and_smt_hybrid_clustering_into_structurereader(
            &circuit,
            &structure_reader,
            &formula,
            hybrid_options,
            if user_input.flag_verbose { 2 } else { 1 },
        )
    };

    // Each side is acyclic on its own: the clustering checks it before returning,
    // unconditionally, and panics with "DAG contains a cycle" if it is not. That is
    // the only acyclicity check there is -- the one this mode used to run over the
    // union of both sides' edges plus the proves->assumes edges was removed, since
    // it reported cycles on runs that were fine.
    //
    // What is therefore still ASSUMED here: that the two orders can be taken
    // together. `guided_clustering` orients the recipient with the guide's own
    // topological order, so the two sides cannot disagree on the direction of a
    // shared edge, and `agree_on_merge` keeps every merge acyclic on both sides --
    // but nothing verifies the union, and the per-cluster results only compose if
    // it holds.

    if let Some(dump_dir) = &user_input.dump_dir {
        let prefixes_for_dump = instance_prefixes(&structure);
        let raw: Vec<RawClusteringDump> = clusterings
            .iter()
            .enumerate()
            .map(|(index, (circuit_clusters, spec_clusters))| {
                let structure_node_id = structure.nodes[index].node_id;
                RawClusteringDump {
                    index,
                    structure_node_id,
                    instance: prefixes_for_dump
                        .get(&structure_node_id)
                        .cloned()
                        .unwrap_or_else(|| "?".to_string()),
                    circuit_clusters: raw_cluster_nodes(circuit_clusters),
                    spec_clusters: raw_cluster_nodes(spec_clusters),
                }
            })
            .collect();
        dump_json(dump_dir, "raw_clustering.json", &raw, "Raw clustering");
    }

    // Instance prefix per structure node, built exactly the way the
    // preprocessor and the clustering both build it (root "main", then
    // `parent.component_name`), so the three agree on the key.
    let prefixes = instance_prefixes(&structure);
    let interfaces = instance_interfaces(&structure, &prefixes);

    // ---- step 5 setup: what every query needs ----------------------------
    let macros = required_macro_definitions(&table, &spec.macros);
    let original_file = user_input
        .input_r1cs
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("circuit")
        .to_string();

    let ctx = VerificationContext {
        constraints: &constraints,
        table: &table,
        macros: &macros,
        field: &field,
        instance_adjacency: user_input.instance_adjacency,
        apply_predecessors: user_input.apply_predecessors,
        apply_bidirectional: user_input.apply_bidirectional,
        timeout: user_input.timeout,
        solver: user_input.solver_option,
        verbose: user_input.flag_verbose,
        original_file: &original_file,
        extra_rounds: user_input.extra_rounds,
        signal_names: &pos_to_name,
        allow_empty_clusters: user_input.allow_empty_clusters,
        smt_signal_names: user_input.smt_signal_names,
    };

    // Every instance's clusterings, reachable by prefix: the refinement's second
    // phase asserts a child instance in full, which means reaching outside the
    // instance being verified.
    let mut catalogue: Catalogue = HashMap::new();
    for (idx, (circuit_clusters, spec_clusters)) in clusterings.iter().enumerate() {
        let node_id = structure.nodes[idx].node_id;
        if let (Some(prefix), Some(interface)) = (prefixes.get(&node_id), interfaces.get(&node_id)) {
            catalogue.insert(
                prefix.clone(),
                InstanceEntry { circuit: circuit_clusters, spec: spec_clusters, interface },
            );
        }
    }

    // ---- step 4: verify every cluster pair --------------------------------
    let mut results = ResultInfoSemanticEquivalence::default();

    for (idx, (circuit_clusters, spec_clusters)) in clusterings.iter().enumerate() {
        let node_id = structure.nodes[idx].node_id;
        let instance = match prefixes.get(&node_id) {
            Some(p) => p.clone(),
            None => {
                // A node the walk from the root never reached: the structure
                // is not a single tree rooted at main. The clustering would
                // already have panicked, but be explicit.
                eprintln!(
                    "Node {} is not reachable from the root: cannot tell which instance it is",
                    node_id
                );
                return Err(());
            }
        };

        let interface = interfaces
            .get(&node_id)
            .expect("every structure node has an interface");

        if let Err(msg) = check_partition_coverage(
            &instance,
            &structure.nodes[idx],
            circuit_clusters,
            spec_clusters,
            formula.get_atomrange_for_component(&instance),
        ) {
            eprintln!("{}", msg);
            return Err(());
        }

        verify_instance(
            &instance,
            circuit_clusters,
            spec_clusters,
            interface,
            &catalogue,
            &ctx,
            &mut results,
        );
    }

    print_pretty_results(&results);

    if let Some(report_path) = &user_input.report_output {
        let rep = build_semantic_equivalence_report(&user_input, &results);
        report::write_report(&rep, report_path);
    }

    if let Some(dump_dir) = &user_input.dump_dir {
        dump_json(dump_dir, "clusters.json", &results.cluster_dump, "Cluster dump");
    }

    Ok(())
}

/// `--resolved_formula`: one clustering over the whole circuit and the whole
/// specification, instead of one per component instance.
///
/// The difference to the normal path is entirely in what is handed to the
/// clustering. There, one formula per instance and the structure to keep them
/// apart; here, the resolved file as it stands, and the structure only ever used
/// to build the atoms. What comes back is a single pair of clusterings, verified
/// exactly like any other instance's -- with one instance, no children, and
/// therefore no second refinement phase to inline them: a subcomponent's
/// constraints are already in the same formula, either in the cluster being
/// verified or in a neighbour that gets abstracted.
///
/// See [`flat_mode`](super::flat_mode) for how the atoms are lined up with the
/// file and how the per-instance variables are merged into one namespace.
fn prove_flat(
    user_input: &Input,
    flat_path: &std::path::Path,
    spec: &utils::read_specification::SpecificationInfo,
    table: &AtomTable,
    constraints: &Vec<Constraint<usize>>,
    inputs: &[usize],
    outputs: &[usize],
    field: &BigInt,
    pos_to_name: &std::collections::BTreeMap<usize, String>,
) -> Result<(), ()> {
    let flat = match read_flat_formula(
        flat_path,
        field,
        inputs.iter().copied().collect::<HashSet<_>>(),
        outputs.iter().copied().collect::<HashSet<_>>(),
    ) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("Could not read the resolved formula: {}", e);
            return Err(());
        }
    };
    println!(
        "LOG: read {} atom(s) of instance '{}' from {}",
        flat.formula.atoms().len(),
        flat.instance,
        flat_path.display()
    );

    // The keys that assert nothing are not allowed to shape the partition; see
    // `restrict_to_asserted` for why one of them is otherwise the whole circuit.
    let (flat, unasserted) = restrict_to_asserted(flat, table);
    if !unasserted.is_empty() {
        println!(
            "LOG: {} key(s) of the resolved file answer to no atom, assert `true`, and were left \
             out of the clustering: {:?}{}",
            unasserted.len(),
            unasserted.iter().take(5).collect::<Vec<_>>(),
            if unasserted.len() > 5 { format!(" (and {} more)", unasserted.len() - 5) } else { String::new() }
        );
    }

    // The same line `build_atoms` was given: one past the largest r1cs signal.
    let synthetic_base = constraints
        .iter()
        .flat_map(|c| c.signals().into_iter())
        .max()
        .unwrap_or(0)
        + 1;
    let aligned = align_atoms(table, &flat.formula, &flat.instance, synthetic_base);
    let flat_table = &aligned.table;
    println!(
        "LOG: {} of the {} atom(s) built from the specification are behind a key of the file",
        aligned.matched,
        table.atoms.len()
    );

    // The one number that matters for soundness: an atom no cluster holds is a
    // piece of the specification no query asserts, and every verdict below is
    // then against a weaker specification than the file says.
    if !aligned.absent.is_empty() {
        println!(
            "WARNING: {} atom(s) of the specification are behind no key of the resolved file, so \
             no query asserts them and every verdict below is against a weaker specification: \
             {:?}{}",
            aligned.absent.len(),
            aligned.absent.iter().take(5).collect::<Vec<_>>(),
            if aligned.absent.len() > 5 { format!(" (and {} more)", aligned.absent.len() - 5) } else { String::new() }
        );
    }
    if user_input.flag_verbose {
        // Expected, both of them, and both harmless: a key with no signal is a
        // tag whose body is `true` -- llzk writes one per alias and constant,
        // and `build_atoms` drops them for the same reason -- and a key with no
        // atom is `level0` or an `equalityN` tie group, which the `single` mode
        // writes itself.
        if !flat.empty.is_empty() {
            println!(
                "LOG: {} key(s) of the resolved file list no signal at all and were dropped: {:?}{}",
                flat.empty.len(),
                flat.empty.iter().take(5).collect::<Vec<_>>(),
                if flat.empty.len() > 5 { format!(" (and {} more)", flat.empty.len() - 5) } else { String::new() }
            );
        }
        if !aligned.unmatched.is_empty() {
            println!(
                "LOG: {} key(s) of the resolved file answer to no atom and are asserted as \
                 `true`: {:?}{}",
                aligned.unmatched.len(),
                aligned.unmatched.iter().take(5).collect::<Vec<_>>(),
                if aligned.unmatched.len() > 5 { format!(" (and {} more)", aligned.unmatched.len() - 5) } else { String::new() }
            );
        }
    }

    let circuit = LightweightCircuit::<Constraint<usize>>::from(
        field,
        constraints.iter(),
        inputs.iter(),
        outputs.iter(),
    );

    let decompose_options = DecomposeOptions {
        target_size: if user_input.target_size == 0 {
            None
        } else {
            Some(user_input.target_size as f64)
        },
        debug: if user_input.flag_verbose { 2 } else { 0 },
        ..Default::default()
    };
    let hybrid_options = HybridClusteringOptions {
        manually_check_acyclic: user_input.manually_check_acyclic,
        guide_decompose_options: decompose_options,
        hybrid_decompose_method: HybridClusteringMethods::default(),
        hybrid_decompose_options: HybridClusteringMethodOptions {
            recipient_requires_subsets: true,
            merge_until_io_same: !user_input.skip_io_equivalence_merge,
            // Same flag that silences the vacuous-obligation check downstream:
            // with it there is one abort left, not two, and only one of them
            // could be silenced.
            empty_clusters_are_an_error: !user_input.allow_empty_clusters,
            ..Default::default()
        },
    };

    println!("LOG: clustering the circuit against the resolved formula as a whole");
    // The plain entry point takes the GUIDE first and returns it first, the
    // opposite of the structure-driven one. Guide is the specification here too.
    let (spec_clusters, circuit_clusters) = circuit_and_smt_hybrid_clustering_into_structurereader(
        &flat.formula,
        &circuit,
        hybrid_options,
        if user_input.flag_verbose { 2 } else { 1 },
    );
    println!(
        "LOG: {} cluster(s) over {} r1cs constraint(s) and {} atom(s)",
        spec_clusters.nodes.len(),
        constraints.len(),
        flat.formula.atoms().len()
    );

    if let Some(dump_dir) = &user_input.dump_dir {
        let raw = vec![RawClusteringDump {
            index: 0,
            structure_node_id: 0,
            instance: flat.instance.clone(),
            circuit_clusters: raw_cluster_nodes(&circuit_clusters),
            spec_clusters: raw_cluster_nodes(&spec_clusters),
        }];
        dump_json(dump_dir, "raw_clustering.json", &raw, "Raw clustering");
    }

    let macros = required_macro_definitions(flat_table, &spec.macros);
    let original_file = user_input
        .input_r1cs
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("circuit")
        .to_string();

    let ctx = VerificationContext {
        constraints,
        table: flat_table,
        macros: &macros,
        field,
        instance_adjacency: user_input.instance_adjacency,
        apply_predecessors: user_input.apply_predecessors,
        apply_bidirectional: user_input.apply_bidirectional,
        timeout: user_input.timeout,
        solver: user_input.solver_option,
        verbose: user_input.flag_verbose,
        original_file: &original_file,
        extra_rounds: user_input.extra_rounds,
        signal_names: pos_to_name,
        allow_empty_clusters: user_input.allow_empty_clusters,
        smt_signal_names: user_input.smt_signal_names,
    };

    // No children: the whole circuit is this one instance. The second phase of
    // the refinement therefore never fires, and `collect_inlined` returns
    // nothing -- correct, since there is no other instance left to inline.
    let interface = InstanceInterface::default();
    let mut catalogue: Catalogue = HashMap::new();
    catalogue.insert(
        flat.instance.clone(),
        InstanceEntry { circuit: &circuit_clusters, spec: &spec_clusters, interface: &interface },
    );

    // Coverage over the whole circuit: every r1cs constraint and every atom of
    // the file has to be in some cluster, same rule as per instance.
    let whole = NodeInfo {
        node_id: 0,
        node_name: flat.instance.clone(),
        component_name: String::new(),
        constraints: (0..constraints.len()).collect(),
        input_signals: inputs.to_vec(),
        output_signals: outputs.to_vec(),
        signals: Vec::new(),
        is_custom: false,
        is_deterministic: false,
        predecessors: Vec::new(),
        successors: Vec::new(),
    };
    if let Err(msg) = check_partition_coverage(
        &flat.instance,
        &whole,
        &circuit_clusters,
        &spec_clusters,
        flat.formula.get_atomrange_for_component(&flat.instance),
    ) {
        eprintln!("{}", msg);
        return Err(());
    }

    let mut results = ResultInfoSemanticEquivalence::default();
    verify_instance(
        &flat.instance,
        &circuit_clusters,
        &spec_clusters,
        &interface,
        &catalogue,
        &ctx,
        &mut results,
    );

    print_pretty_results(&results);

    if let Some(report_path) = &user_input.report_output {
        let rep = build_semantic_equivalence_report(user_input, &results);
        report::write_report(&rep, report_path);
    }

    if let Some(dump_dir) = &user_input.dump_dir {
        dump_json(dump_dir, "clusters.json", &results.cluster_dump, "Cluster dump");
    }

    Ok(())
}

/// Writes one debug artefact into `--dump_dir`, creating the directory on first
/// use. A failure here is a warning, never a verdict: these files are for
/// reading, and losing one must not fail a verification that otherwise ran.
fn dump_json<T: serde::Serialize>(dir: &std::path::Path, file_name: &str, value: &T, what: &str) {
    if let Err(e) = std::fs::create_dir_all(dir) {
        eprintln!("Warning: could not create {}: {}", dir.display(), e);
        return;
    }
    let path = dir.join(file_name);
    match serde_json::to_string_pretty(value) {
        Ok(json) => match std::fs::write(&path, &json) {
            Ok(()) => println!("{} written to {}", what, path.display()),
            Err(e) => eprintln!("Warning: could not write {} to {}: {}", what, path.display(), e),
        },
        Err(e) => eprintln!("Warning: could not serialize {}: {}", what, e),
    }
}

/// Verifies every cluster pair of one instance.
fn verify_instance(
    instance: &str,
    circuit_clusters: &StructureReader,
    spec_clusters: &StructureReader,
    interface: &InstanceInterface,
    catalogue: &Catalogue,
    ctx: &VerificationContext,
    results: &mut ResultInfoSemanticEquivalence,
) {
    let circuit_by_id = index_by_id(&circuit_clusters.nodes);
    let spec_by_id = index_by_id(&spec_clusters.nodes);
    let instance_info = ctx.table.instance(instance);

    // Driven from the SPECIFICATION side, like everything else in this mode: it is
    // the specification that says what a cluster's interface is and what has to be
    // proved about it, so it is also what decides which clusters there are to
    // verify. By id, since every query is self-contained.
    let mut ordered: Vec<&NodeInfo> = spec_clusters.nodes.iter().collect();
    ordered.sort_by_key(|n| n.node_id);

    for spec_node in ordered.into_iter() {
        let circuit_node = circuit_of(&circuit_by_id, &spec_node.node_id);

        let pair = ClusterPair {
            instance,
            circuit: circuit_node,
            spec: spec_node,
        };

        println!(
            "LOG: considering cluster {} of {} ({} constraints, {} atoms)",
            spec_node.node_id,
            instance,
            circuit_node.constraints.len(),
            spec_node.constraints.len()
        );

        // The specification node, because `check_cluster` states the obligation over
        // `bound_boundary(pair.spec, ...)`: warning about the circuit node's ports
        // would be reporting a boundary the query never uses.
        // Not the invented ids: a variable with no r1cs wire is one the
        // specification DOES name, it just has nothing circuit-side to equate,
        // and the interface drops it anyway. In the flat mode they are most of
        // a cluster's signals.
        let synthetic: HashSet<usize> = ctx.table.unresolved_ids.values().copied().collect();
        let unbound: Vec<usize> = unbound_boundary_signals(spec_node, instance_info)
            .into_iter()
            .filter(|s| !synthetic.contains(s))
            .collect();
        if !unbound.is_empty() {
            println!(
                "WARNING: cluster {} has {} boundary signal(s) the specification never names: {:?}",
                spec_node.node_id,
                unbound.len(),
                unbound
            );
            results
                .unbound_signals
                .insert(spec_node.node_id, unbound);
        }

        // Nothing to prove: no output of this cluster's boundary is a wire the
        // specification names, so the disagreement clause would be `(not true)`
        // and the query vacuously unsat. `check_cluster` aborts on that -- a pair
        // like this is a clustering that should not have been produced -- and
        // `--allow_empty_clusters` is the way to keep going anyway: no query, no
        // verdict, no line in the report, just this note.
        if ctx.allow_empty_clusters && !has_bound_output(spec_node, instance_info, &synthetic) {
            println!(
                "NOTE: cluster {} of {} has no output the specification names, so there is \
                 nothing to verify in it; passed over (--allow_empty_clusters). It is NOT \
                 counted anywhere: its {} r1cs constraint(s) go unverified.",
                spec_node.node_id,
                instance,
                circuit_node.constraints.len()
            );
            continue;
        }

        let cluster_started = std::time::Instant::now();
        let verdict = verify_cluster_with_refinement(&pair, &circuit_by_id, &spec_by_id,
                                                    interface, catalogue, ctx);

        if verdict == ClusterVerdict::Failed {
            println!(
                "NOTE: cluster {} borders no cluster that was not asserted in full, so nothing \
                 was left abstracted and the circuit really does disagree with its \
                 specification here.",
                spec_node.node_id
            );
        }
        if verdict == ClusterVerdict::LocalCounterexample {
            println!(
                "NOTE: the counterexample for cluster {} is local to its boundary. It borders \
                 clusters that were not asserted in full -- abstracted, or not looked at because \
                 of --apply_predecessors/--apply_bidirectional -- so this does NOT show the \
                 circuit disagrees with its specification.",
                spec_node.node_id
            );
        }

        results.clusters.insert(spec_node.node_id, verdict);
        results.cluster_seconds.insert(
            spec_node.node_id,
            cluster_started.elapsed().as_secs_f64(),
        );
        results
            .cluster_instance
            .insert(spec_node.node_id, instance.to_string());
        results
            .cluster_size
            .insert(spec_node.node_id, circuit_node.constraints.len());
        record_cluster(results, instance, circuit_node, spec_node, verdict);
    }
}

/// Append one cluster pair to the dump. Cheap enough to run unconditionally:
/// the record is only written to disk if `--dump_dir` asked for it.
fn record_cluster(
    results: &mut ResultInfoSemanticEquivalence,
    instance: &str,
    circuit: &NodeInfo,
    spec: &NodeInfo,
    verdict: ClusterVerdict,
) {
    let sorted = |v: &Vec<usize>| { let mut c = v.clone(); c.sort_unstable(); c };
    results.cluster_dump.push(ClusterDump {
        cluster_id: circuit.node_id,
        instance: instance.to_string(),
        verdict: verdict.as_str().to_string(),
        circuit_constraints: sorted(&circuit.constraints),
        circuit_signals: sorted(&circuit.signals),
        circuit_inputs: sorted(&circuit.input_signals),
        circuit_outputs: sorted(&circuit.output_signals),
        predecessors: sorted(&circuit.predecessors),
        successors: sorted(&circuit.successors),
        spec_atoms: sorted(&spec.constraints),
        spec_signals: sorted(&spec.signals),
        spec_predecessors: sorted(&spec.predecessors),
        spec_successors: sorted(&spec.successors),
        unbound_signals: results
            .unbound_signals
            .get(&circuit.node_id)
            .map(|v| sorted(v))
            .unwrap_or_default(),
    });
}

/// One instance's clusterings and subcomponents, reachable by its dotted prefix.
///
/// `verify_instance` works on one instance, but the second phase of the
/// refinement has to reach INTO its children — their clusters, their bindings,
/// their own children — so the whole set is indexed once and passed down.
pub struct InstanceEntry<'a> {
    pub circuit: &'a StructureReader,
    pub spec: &'a StructureReader,
    pub interface: &'a InstanceInterface,
}

pub type Catalogue<'a> = HashMap<String, InstanceEntry<'a>>;

/// Everything the child instances down to `depth` contribute to a query, with the
/// instances one level below them left as implications.
///
/// `depth` 0 inlines nothing: every child of the instance being verified is an
/// implication, which is `check_cluster`'s own doing and what the whole of phase 1
/// runs with. `depth` 1 asserts the direct children in full and abstracts the
/// grandchildren, and so on.
fn collect_inlined(
    catalogue: &Catalogue,
    table: &AtomTable,
    root: &str,
    depth: usize,
) -> InlinedInstances {
    let mut out = InlinedInstances::default();
    if depth == 0 {
        return out;
    }
    // Descend level by level, asserting every instance on the way down.
    let mut level: Vec<String> = vec![root.to_string()];
    for _ in 1..=depth {
        let mut next: Vec<String> = Vec::new();
        for parent in level.iter() {
            let Some(entry) = catalogue.get(parent) else { continue };
            let parent_info = table.instance(parent);
            for child in entry.interface.children.iter() {
                let Some(child_entry) = catalogue.get(&child.instance) else { continue };
                next.push(child.instance.clone());
                out.names.push(child.instance.clone());
                for node in child_entry.circuit.nodes.iter() {
                    out.constraints.extend(node.constraints.iter().copied());
                    out.signals.extend(node.signals.iter().copied());
                }
                for node in child_entry.spec.nodes.iter() {
                    out.atoms.extend(node.constraints.iter().copied());
                }
                let child_info = table.instance(&child.instance);
                out.spec_vars.extend(child_info.spec_vars.iter().cloned());
                // The ports are the only wires the two instances share, and each
                // names them its own way.
                for signal in child.inputs.iter().chain(child.outputs.iter()) {
                    if let (Some(inner), Some(outer)) = (
                        child_info.signal_to_spec_var.get(signal),
                        parent_info.signal_to_spec_var.get(signal),
                    ) {
                        if inner != outer {
                            out.port_equalities.push(format!("(= {} {})", inner, outer));
                        }
                    }
                }
            }
        }
        level = next;
        if level.is_empty() {
            break;
        }
    }
    // `level` now holds the deepest instances asserted: THEIR children are what
    // takes their place as implications.
    for parent in level.iter() {
        let Some(entry) = catalogue.get(parent) else { continue };
        let parent_info = table.instance(parent);
        for grandchild in entry.interface.children.iter() {
            let implication = child_implication(grandchild, parent_info);
            if !implication.0.is_empty() || !implication.1.is_empty() {
                out.implications.push(implication);
            }
        }
    }
    out.constraints.sort_unstable();
    out.constraints.dedup();
    out.signals.sort_unstable();
    out.signals.dedup();
    out.atoms.sort_unstable();
    out.atoms.dedup();
    out.port_equalities.sort();
    out.port_equalities.dedup();
    out.spec_vars.sort();
    out.spec_vars.dedup();
    out
}

/// Whether going one level deeper than `depth` would assert anything new.
fn has_instances_at(catalogue: &Catalogue, root: &str, depth: usize) -> bool {
    let mut level: Vec<String> = vec![root.to_string()];
    for _ in 0..=depth {
        let mut next: Vec<String> = Vec::new();
        for parent in level.iter() {
            if let Some(entry) = catalogue.get(parent) {
                next.extend(
                    entry.interface.children.iter()
                        .filter(|c| catalogue.contains_key(&c.instance))
                        .map(|c| c.instance.clone()),
                );
            }
        }
        level = next;
        if level.is_empty() {
            return false;
        }
    }
    true
}

/// The counterpart of a cluster id on the circuit side.
///
/// Both clusterings carry the same id set by construction --
/// `dual_merge_until_property` asserts the keysets match and merges the same ids
/// on both sides -- so a miss is a broken clustering. Never skipped: dropping an
/// id here would quietly shrink the abstraction, and a query with fewer
/// hypotheses than intended reports its counterexample as conclusive.
fn circuit_of<'a>(circuit_by_id: &HashMap<usize, &'a NodeInfo>, id: &usize) -> &'a NodeInfo {
    circuit_by_id.get(id).copied().unwrap_or_else(|| {
        unreachable!(
            "Cluster {} has no counterpart on the circuit side. The hybrid clustering is \
             supposed to keep one id set for both sides -- this is a bug in \
             clustering::smt_hybrid, not in the input.",
            id
        )
    })
}

/// The same, on the specification side. See [`circuit_of`].
fn spec_of<'a>(spec_by_id: &HashMap<usize, &'a NodeInfo>, id: &usize) -> &'a NodeInfo {
    spec_by_id.get(id).copied().unwrap_or_else(|| {
        unreachable!(
            "Cluster {} has no counterpart on the specification side. The hybrid clustering is \
             supposed to keep one id set for both sides -- this is a bug in \
             clustering::smt_hybrid, not in the input.",
            id
        )
    })
}

/// Runs one cluster's query, widening the asserted region while the verdict is
/// inconclusive and `--extra_rounds` allows it.
///
/// Mirrors `correctness::modular_reasoning::check_node`: not a different
/// encoding, the same obligation with fewer abstractions in front of it. Round N
/// asserts every cluster within N hops — strictly stronger, strictly slower.
///
/// Stops when the verdict cannot improve: VERIFIED, or a counterexample with
/// nothing left abstracted (the query is the whole story), or no neighbours left.
fn verify_cluster_with_refinement(
    pair: &ClusterPair,
    circuit_by_id: &HashMap<usize, &NodeInfo>,
    spec_by_id: &HashMap<usize, &NodeInfo>,
    interface: &InstanceInterface,
    catalogue: &Catalogue,
    ctx: &VerificationContext,
) -> ClusterVerdict {

    // Two phases, in this order:
    //
    //  1. roll outwards over the SIBLING clusters: each round asserts in full the
    //     ring that was abstracted in the previous one, and abstracts the next
    //     ring beyond it;
    //  2. once every sibling is asserted, start asserting the CHILD INSTANCES in
    //     full, one level per round, with the level below them abstracted.
    //
    // The child instances abstracted in either phase are those of everything
    // asserted so far, not just of the cluster being verified: a sibling that has
    // been pulled in brings its own calls with it.
    let mut asserted: BTreeSet<usize> = BTreeSet::from([pair.spec.node_id]);
    let mut depth: usize = 0;
    let mut round: usize = 0;

    loop {
        // Everything bordering the asserted region, minus the region itself.
        //
        // The SPECIFICATION's edges, and only those. The two clusterings share ids
        // but not edge sets: a pair joined only on the circuit side shares a signal
        // the specification never names, and `bound_boundary` drops unbound signals,
        // so no implication about that wire could be built anyway -- abstracting
        // such a neighbour would add hypotheses about OTHER signals, not about what
        // makes them neighbours.
        //
        // Which DIRECTION is read comes from the same two flags the template-level
        // modes use, with the same defaults: successors, unless told otherwise.
        let take_successors = !ctx.apply_predecessors || ctx.apply_bidirectional;
        let take_predecessors = ctx.apply_predecessors || ctx.apply_bidirectional;
        // The ring just beyond what is asserted: abstracted now, asserted next round.
        let abstracted_ids = ring(spec_by_id, &asserted, take_successors, take_predecessors,
                                  ctx.instance_adjacency);
        // The SPECIFICATION node of each neighbour: its abstraction has to be the
        // obligation its own query discharges, and that query states it over the
        // specification's split into inputs and outputs, not the circuit's.
        let abstracted: Vec<&NodeInfo> = abstracted_ids
            .iter()
            .map(|id| spec_of(spec_by_id, id))
            .collect();
        // Every sibling asserted so far, paired with its specification counterpart
        // by the shared id.
        let inlined: Vec<(&NodeInfo, &NodeInfo)> = asserted
            .iter()
            .filter(|id| **id != pair.spec.node_id)
            .map(|id| (circuit_of(circuit_by_id, id), spec_of(spec_by_id, id)))
            .collect();
        // Phase 2's contribution: the child instances down to `depth`, asserted in
        // full, with the level below them abstracted.
        let instances = collect_inlined(catalogue, ctx.table, pair.instance, depth);
        // A child of THIS instance that phase 2 has not reached yet is still an
        // implication, and so is every instance below an inlined one.
        let children_abstracted = interface
            .children
            .iter()
            .any(|c| !instances.names.contains(&c.instance));
        let nothing_approximated = abstracted.is_empty()
            && !children_abstracted
            && instances.implications.is_empty();

        let (result, logs) = check_cluster(pair, &abstracted, &inlined, &instances, interface, ctx);
        for log in logs {
            println!("{}", log);
        }

        let verdict = match result {
            PossibleResult::VERIFIED => ClusterVerdict::Verified,
            // Conclusive only when there was nothing left to abstract -- the region
            // borders no other cluster, either because it never did or because the
            // refinement rounds swallowed them all.
            PossibleResult::FAILED if nothing_approximated => ClusterVerdict::Failed,
            PossibleResult::FAILED => ClusterVerdict::LocalCounterexample,
            _ => ClusterVerdict::Unknown,
        };

        // What is left to try: assert the ring that is currently abstracted, and
        // once there is none, one more level of child instances.
        let can_roll = !abstracted_ids.is_empty();
        let can_deepen = has_instances_at(catalogue, pair.instance, depth);

        let settled = matches!(verdict, ClusterVerdict::Verified | ClusterVerdict::Failed);
        if settled || round >= ctx.extra_rounds || (!can_roll && !can_deepen) {
            if round > 0 {
                println!(
                    "LOG: cluster {} settled as {} after {} refinement round(s): {} sibling(s) \
                     asserted in full, {} abstracted, {} child instance(s) asserted in full",
                    pair.spec.node_id,
                    verdict.as_str(),
                    round,
                    inlined.len(),
                    abstracted.len(),
                    instances.names.len()
                );
            }
            return verdict;
        }

        round += 1;
        if can_roll {
            println!(
                "LOG: cluster {} came back {}; refinement round {} of {}: asserting {} \
                 sibling(s) in full and abstracting the ring beyond them",
                pair.spec.node_id, verdict.as_str(), round, ctx.extra_rounds, abstracted_ids.len()
            );
            asserted.extend(abstracted_ids.into_iter());
        } else {
            depth += 1;
            println!(
                "LOG: cluster {} came back {}; refinement round {} of {}: every sibling is \
                 asserted, now asserting the child instances at depth {} in full",
                pair.spec.node_id, verdict.as_str(), round, ctx.extra_rounds, depth
            );
        }
    }
}

/// The clusters bordering `asserted` in the specification dag, minus `asserted`
/// itself: what the next query abstracts, and what the round after that asserts.
fn ring(
    spec_by_id: &HashMap<usize, &NodeInfo>,
    asserted: &BTreeSet<usize>,
    take_successors: bool,
    take_predecessors: bool,
    instance_adjacency: bool,
) -> BTreeSet<usize> {
    if instance_adjacency {
        // The complete graph over the instance: adjacency stops meaning anything.
        return spec_by_id.keys().copied().filter(|id| !asserted.contains(id)).collect();
    }
    let mut out: BTreeSet<usize> = BTreeSet::new();
    for id in asserted.iter() {
        let node = spec_of(spec_by_id, id);
        let sucs = if take_successors { node.successors.as_slice() } else { &[] };
        let preds = if take_predecessors { node.predecessors.as_slice() } else { &[] };
        for adjacent in sucs.iter().chain(preds.iter()) {
            if !asserted.contains(adjacent) {
                out.insert(*adjacent);
            }
        }
    }
    out
}

/// Aborts unless the two clusterings really are partitions of what they were
/// built from.
///
/// The clustering gives up when a round places nothing, and whatever it could not
/// place is simply absent from the result. An absent ATOM is a piece of the
/// specification no query ever asserts, so every cluster could come back VERIFIED
/// while it was never looked at; an absent r1cs constraint is one whose
/// contribution to the outputs is never asserted. Either way the run is refused,
/// not qualified.
fn check_partition_coverage(
    instance: &str,
    node: &NodeInfo,
    circuit_clusters: &StructureReader,
    spec_clusters: &StructureReader,
    atom_range: Option<std::ops::Range<usize>>,
) -> Result<(), String> {
    let covered_constraints: HashSet<usize> = circuit_clusters
        .nodes
        .iter()
        .flat_map(|n| n.constraints.iter().copied())
        .collect();
    let missing: Vec<usize> = node
        .constraints
        .iter()
        .copied()
        .filter(|c| !covered_constraints.contains(c))
        .collect();
    if !missing.is_empty() {
        return Err(format!(
            "The clustering of instance '{}' covers only {} of its {} r1cs constraints: {:?}{} were left \
             out, so a verdict on it would ignore them. Refusing to verify.",
            instance,
            node.constraints.len() - missing.len(),
            node.constraints.len(),
            missing.iter().take(10).collect::<Vec<_>>(),
            if missing.len() > 10 { format!(" (and {} more)", missing.len() - 10) } else { String::new() }
        ));
    }

    let atom_range = match atom_range {
        Some(r) => r,
        // An instance the specification says nothing about: build_atoms would
        // already have complained, and there is no coverage to check.
        None => return Ok(()),
    };
    let covered_atoms: HashSet<usize> = spec_clusters
        .nodes
        .iter()
        .flat_map(|n| n.constraints.iter().copied())
        .collect();
    let missing_atoms: Vec<usize> = atom_range
        .clone()
        .filter(|a| !covered_atoms.contains(a))
        .collect();
    if !missing_atoms.is_empty() {
        return Err(format!(
            "The clustering of instance '{}' covers only {} of its {} specification atoms: {:?}{} were \
             left out, so every cluster of it could be VERIFIED without those atoms ever being \
             asserted. Refusing to verify.",
            instance,
            atom_range.len() - missing_atoms.len(),
            atom_range.len(),
            missing_atoms.iter().take(10).collect::<Vec<_>>(),
            if missing_atoms.len() > 10 { format!(" (and {} more)", missing_atoms.len() - 10) } else { String::new() }
        ));
    }

    Ok(())
}

/// The ports of each structure node's children, read straight off the structure.
/// See [`InstanceInterface`] for why the `DAGNode`s cannot supply them.
fn instance_interfaces(
    structure: &StructureInfo,
    prefixes: &HashMap<usize, String>,
) -> HashMap<usize, InstanceInterface> {
    let nodeid2pos: HashMap<usize, usize> = structure
        .nodes
        .iter()
        .enumerate()
        .map(|(pos, node)| (node.node_id, pos))
        .collect();

    structure
        .nodes
        .iter()
        .map(|node| {
            let mut interface = InstanceInterface::default();
            for child_id in node.successors.iter() {
                if let Some(pos) = nodeid2pos.get(child_id) {
                    let child = &structure.nodes[*pos];
                    interface.children.push(ChildPorts {
                        node_id: *child_id,
                        instance: prefixes
                            .get(child_id)
                            .cloned()
                            .unwrap_or_else(|| child.component_name.clone()),
                        inputs: child.input_signals.clone(),
                        outputs: child.output_signals.clone(),
                    });
                }
            }
            (node.node_id, interface)
        })
        .collect()
}

/// The same walk the preprocessor and the clustering do: root is `"main"`,
/// every child appends `.component_name`.
fn instance_prefixes(structure: &StructureInfo) -> HashMap<usize, String> {
    let nodeid2pos: HashMap<usize, usize> = structure
        .nodes
        .iter()
        .enumerate()
        .map(|(pos, node)| (node.node_id, pos))
        .collect();

    let mut prefixes: HashMap<usize, String> = HashMap::new();
    let mut stack = vec![(0usize, "main".to_string())];
    while let Some((node_id, prefix)) = stack.pop() {
        prefixes.insert(node_id, prefix.clone());
        if let Some(pos) = nodeid2pos.get(&node_id) {
            for child in structure.nodes[*pos].successors.iter() {
                if let Some(cpos) = nodeid2pos.get(child) {
                    let child_prefix =
                        format!("{}.{}", prefix, structure.nodes[*cpos].component_name);
                    stack.push((*child, child_prefix));
                }
            }
        }
    }
    prefixes
}

/// The preconditions `smt_hybrid`'s structure-driven mode asserts with
/// `panic!`, checked here so the user gets a message instead of a stack trace.
fn check_structure_is_usable(reader: &StructureReader) -> Result<(), String> {
    if reader.nodes.is_empty() {
        return Err("The circuit structure has no nodes".to_string());
    }
    if reader.nodes[0].node_id != 0 {
        return Err("The circuit structure's first node is not node 0 (the root)".to_string());
    }
    if !reader.nodes[0].component_name.is_empty()
        && reader.nodes[0].component_name != "main"
    {
        return Err(format!(
            "Node 0 of the structure is not the main component (component_name is '{}')",
            reader.nodes[0].component_name
        ));
    }
    let mut seen: HashSet<usize> = HashSet::new();
    for node in reader.nodes.iter() {
        if !seen.insert(node.node_id) {
            return Err(format!("The structure repeats node id {}", node.node_id));
        }
    }
    // The structure-driven clustering requires a TREE: every node reachable
    // from the root exactly once. A node with two parents makes it panic with
    // "Given circuit structure is not a tree".
    let mut parents: HashMap<usize, usize> = HashMap::new();
    for node in reader.nodes.iter() {
        for child in node.successors.iter() {
            *parents.entry(*child).or_insert(0) += 1;
        }
    }
    if let Some((child, count)) = parents.iter().find(|(_, c)| **c > 1) {
        return Err(format!(
            "The circuit structure is not a tree: node {} has {} parents",
            child, count
        ));
    }
    Ok(())
}

/// `StructureReader` is not `Clone`, and both the clustering (which wants the
/// reader) and `transform_structure_reader` (which consumes one) need it.
fn clone_reader(reader: &StructureReader) -> StructureReader {
    StructureReader {
        timing: reader.timing.clone(),
        nodes: reader.nodes.clone(),
        equivalency_local: reader.equivalency_local.clone(),
        equivalency_structural: reader.equivalency_structural.clone(),
    }
}

/// Both sides must be over the same field, or the equalities the query builds
/// between a circuit signal and a spec variable are meaningless.
fn reconcile_prime(
    spec: &utils::read_specification::SpecificationInfo,
    cli_prime: &BigInt,
) -> Result<BigInt, String> {
    match spec.prime_as_bigint() {
        Ok(spec_prime) => {
            if &spec_prime != cli_prime {
                return Err(format!(
                    "The specification's prime ({}) differs from the one given with --prime ({}). \
                     Both sides have to be over the same field, or every circuit-signal = \
                     spec-variable equality the queries build would compare values from two \
                     different fields.",
                    spec_prime, cli_prime
                ));
            }
            Ok(spec_prime)
        }
        Err(e) => {
            println!(
                "WARNING: could not read the prime from the specification ({}); \
                 using --prime instead",
                e
            );
            Ok(cli_prime.clone())
        }
    }
}

fn build_semantic_equivalence_report(
    input: &crate::Input,
    results: &ResultInfoSemanticEquivalence,
) -> report::VerificationReport {
    // A local counterexample is inconclusive, not a failure: it counts as a
    // node we could not verify, the same bucket as a timeout.
    let overall = report::compute_overall(
        results.count(ClusterVerdict::Failed) == 0,
        results.count(ClusterVerdict::Unknown) == 0
            && results.count(ClusterVerdict::LocalCounterexample) == 0,
    );

    let summary = report::ReportSummary {
        total_nodes: results.clusters.len(),
        verified_nodes: results.count(ClusterVerdict::Verified),
        previously_verified_nodes: None,
        failed_nodes: results.count(ClusterVerdict::Failed),
        timeout_nodes: results.count(ClusterVerdict::Unknown)
            + results.count(ClusterVerdict::LocalCounterexample),
        total_constraints: Some(results.cluster_size.values().sum()),
        verified_constraints: Some(
            results
                .clusters
                .iter()
                .filter(|(_, v)| **v == ClusterVerdict::Verified)
                .map(|(id, _)| results.cluster_size.get(id).copied().unwrap_or(0))
                .sum(),
        ),
        verified_constraints_pct: None,
    };

    let mut nodes: Vec<report::NodeResult> = results
        .clusters
        .iter()
        .map(|(id, verdict)| report::NodeResult {
            seconds: results.cluster_seconds.get(id).map(|s| (s * 1000.0).round() / 1000.0),
            node_id: *id,
            node_name: format!(
                "{}#c{}",
                results
                    .cluster_instance
                    .get(id)
                    .cloned()
                    .unwrap_or_else(|| "?".to_string()),
                id
            ),
            result: verdict.as_str().to_string(),
            num_constraints: results.cluster_size.get(id).copied(),
            previously_verified: None,
        })
        .collect();
    nodes.sort_by_key(|n| n.node_id);

    report::VerificationReport {
        check_type: report::CheckType::SemanticEquivalence,
        input_circuit: input.input_r1cs.display().to_string(),
        second_circuit: input
            .check_semantic_equivalence
            .as_ref()
            .map(|p| p.display().to_string()),
        solver: report::solver_to_str(input.solver_option).to_string(),
        timeout_ms: input.timeout,
        overall_result: overall,
        summary,
        nodes,
        failed_templates: None,
    }
}

/// Laid out like the other modes' `print_pretty_results`: banner, headline, one
/// list per non-empty bucket, counters. The buckets stay apart on purpose —
/// FAILED and a local counterexample are two different things (see
/// [`ClusterVerdict`]).
fn print_pretty_results(results: &ResultInfoSemanticEquivalence) {
    let verified = results.count(ClusterVerdict::Verified);
    let failed = results.count(ClusterVerdict::Failed);
    let local = results.count(ClusterVerdict::LocalCounterexample);
    let unknown = results.count(ClusterVerdict::Unknown);

    println!();

    println!("--------------------------------------------");
    println!("--------------------------------------------");
    println!("-- ZK-GENVER SEMANTIC EQUIVALENCE RESULTS --");
    println!("--------------------------------------------");
    println!("--------------------------------------------\n");

    if results.clusters.is_empty() {
        println!("-> There was no cluster pair to verify");
    } else if failed == 0 && local == 0 && unknown == 0 {
        println!("-> All cluster pairs are semantically equivalent to their specification :)");
        // Saying "the circuit is equivalent" needs the per-cluster results to
        // compose, which nothing here establishes -- see the assumption recorded
        // after the clustering.
        println!("   (per cluster pair.)");
    } else {
        println!("-> ZK-GENVER could not verify the semantic equivalence of all cluster pairs");
        print_cluster_list(
            results,
            ClusterVerdict::Failed,
            "Cluster pairs that disagree with the specification (nothing was left abstracted to find it): ",
        );
        print_cluster_list(
            results,
            ClusterVerdict::LocalCounterexample,
            "Cluster pairs whose counterexample is local to their own boundary (inconclusive, not a failure): ",
        );
        print_cluster_list(
            results,
            ClusterVerdict::Unknown,
            "Cluster pairs that timeout when checking semantic equivalence: ",
        );
    }
    println!("  * Number of verified cluster pairs (semantic equivalence): {}", verified);
    println!("  * Number of failed cluster pairs (semantic equivalence): {}", failed);
    println!("  * Number of inconclusive cluster pairs (local counterexample): {}", local);
    println!("  * Number of timeout cluster pairs (semantic equivalence): {}", unknown);
    if !results.unbound_signals.is_empty() {
        println!(
            "  * Number of cluster pairs with boundary signals the specification never names: {} (a VERIFIED verdict says nothing about those signals)",
            results.unbound_signals.len()
        );
    }
}

/// The clusters holding one verdict, in the `    - Node {id}: {name}, ` shape
/// the other modes use: here the cluster id plays the node id and the instance
/// it belongs to plays the name. Sorted, because `clusters` is a `HashMap` and
/// an unordered list of ids is unreadable across runs.
fn print_cluster_list(
    results: &ResultInfoSemanticEquivalence,
    verdict: ClusterVerdict,
    header: &str,
) {
    let mut ids: Vec<usize> = results
        .clusters
        .iter()
        .filter(|(_, v)| **v == verdict)
        .map(|(id, _)| *id)
        .collect();
    if ids.is_empty() {
        return;
    }
    ids.sort();
    println!("{}", header);
    for id in ids {
        println!(
            "    - Cluster {}: {}, ",
            id,
            results.cluster_instance.get(&id).cloned().unwrap_or_default()
        );
    }
}

#[cfg(test)]
mod tests {
    //! The refinement decides two things: which SIBLING clusters come in, and
    //! which CHILD INSTANCES do. Both are pure functions of the two clusterings,
    //! so both can be pinned down without a solver.

    use super::*;
    use crate::semantic_equivalence::atoms::InstanceInfo;
    use utils::structure::TimingInfo;

    fn node(id: usize, inputs: &[usize], outputs: &[usize], preds: &[usize], sucs: &[usize]) -> NodeInfo {
        let mut signals: Vec<usize> = inputs.iter().chain(outputs.iter()).copied().collect();
        signals.sort();
        signals.dedup();
        NodeInfo {
            node_id: id,
            node_name: format!("cluster_{}", id),
            component_name: String::new(),
            constraints: vec![id],
            input_signals: inputs.to_vec(),
            output_signals: outputs.to_vec(),
            signals,
            is_custom: false,
            is_deterministic: false,
            predecessors: preds.to_vec(),
            successors: sucs.to_vec(),
        }
    }

    fn reader(nodes: Vec<NodeInfo>) -> StructureReader {
        StructureReader { timing: TimingInfo::new(), nodes, equivalency_local: None, equivalency_structural: None }
    }

    fn by_id(nodes: &[NodeInfo]) -> HashMap<usize, &NodeInfo> {
        index_by_id(nodes)
    }

    /// `0 -> 1 -> 2`, plus an isolated `3`.
    fn chain() -> Vec<NodeInfo> {
        vec![
            node(0, &[], &[10], &[], &[1]),
            node(1, &[10], &[11], &[0], &[2]),
            node(2, &[11], &[12], &[1], &[]),
            node(3, &[], &[], &[], &[]),
        ]
    }

    fn set(ids: &[usize]) -> BTreeSet<usize> {
        ids.iter().copied().collect()
    }

    // ---- siblings ---------------------------------------------------------

    #[test]
    fn the_ring_rolls_outwards_one_step_at_a_time() {
        let nodes = chain();
        let map = by_id(&nodes);
        // Successors only, which is the default.
        assert_eq!(ring(&map, &set(&[0]), true, false, false), set(&[1]));
        // Next round: what was abstracted is now asserted, and the ring moves on.
        assert_eq!(ring(&map, &set(&[0, 1]), true, false, false), set(&[2]));
        // And stops when the region has swallowed everything reachable.
        assert_eq!(ring(&map, &set(&[0, 1, 2]), true, false, false), set(&[]));
    }

    #[test]
    fn the_direction_flags_pick_which_way_the_ring_grows() {
        let nodes = chain();
        let map = by_id(&nodes);
        // --apply_predecessors: upstream instead of downstream.
        assert_eq!(ring(&map, &set(&[2]), false, true, false), set(&[1]));
        assert_eq!(ring(&map, &set(&[2]), true, false, false), set(&[]));
        // --apply_bidirectional: both at once.
        assert_eq!(ring(&map, &set(&[1]), true, true, false), set(&[0, 2]));
    }

    #[test]
    fn instance_adjacency_ignores_the_edges_entirely() {
        let nodes = chain();
        let map = by_id(&nodes);
        // Cluster 3 has no edge to anything, so no direction ever reaches it...
        assert!(!ring(&map, &set(&[0]), true, true, false).contains(&3));
        // ...until every cluster of the instance counts as a neighbour.
        assert_eq!(ring(&map, &set(&[0]), true, false, true), set(&[1, 2, 3]));
    }

    #[test]
    fn a_cluster_with_no_edges_has_nothing_to_roll_into() {
        let nodes = chain();
        let map = by_id(&nodes);
        assert_eq!(ring(&map, &set(&[3]), true, true, false), set(&[]));
    }

    // ---- child instances --------------------------------------------------

    struct Hierarchy {
        main_c: StructureReader,
        main_s: StructureReader,
        lt_c: StructureReader,
        lt_s: StructureReader,
        n2b_c: StructureReader,
        n2b_s: StructureReader,
        main_i: InstanceInterface,
        lt_i: InstanceInterface,
        n2b_i: InstanceInterface,
        table: AtomTable,
    }

    /// `main` calls `main.lt` (ports 5,6 in / 4 out), which calls `main.lt.n2b`
    /// (ports 7 in / 8 out). One cluster each, one constraint and one atom each.
    fn hierarchy() -> Hierarchy {
        let child = |id: usize, ins: &[usize], outs: &[usize], instance: &str| ChildPorts {
            node_id: id,
            instance: instance.to_string(),
            inputs: ins.to_vec(),
            outputs: outs.to_vec(),
        };
        let info = |pairs: &[(usize, &str)]| InstanceInfo {
            signal_to_spec_var: pairs.iter().map(|(s, v)| (*s, v.to_string())).collect(),
            spec_vars: pairs.iter().map(|(_, v)| v.to_string()).collect(),
        };
        let mut table = AtomTable::default();
        // The same wires, named differently by each instance: that is what the
        // port equalities have to bridge.
        table.instances.insert("main".to_string(),
            info(&[(1, "spec_main_out"), (4, "spec_main_lt_out"), (5, "spec_main_lt_in0"), (6, "spec_main_lt_in1")]));
        table.instances.insert("main.lt".to_string(),
            info(&[(4, "spec_lt_out"), (5, "spec_lt_a"), (6, "spec_lt_b"), (7, "spec_lt_n2b_in"), (8, "spec_lt_n2b_out")]));
        table.instances.insert("main.lt.n2b".to_string(),
            info(&[(7, "spec_n2b_in"), (8, "spec_n2b_out")]));
        Hierarchy {
            main_c: reader(vec![node(0, &[2], &[1], &[], &[])]),
            main_s: reader(vec![node(0, &[2], &[1], &[], &[])]),
            lt_c: reader(vec![node(1, &[5, 6], &[4], &[], &[])]),
            lt_s: reader(vec![node(1, &[5, 6], &[4], &[], &[])]),
            n2b_c: reader(vec![node(2, &[7], &[8], &[], &[])]),
            n2b_s: reader(vec![node(2, &[7], &[8], &[], &[])]),
            main_i: InstanceInterface { children: vec![child(1, &[5, 6], &[4], "main.lt")] },
            lt_i: InstanceInterface { children: vec![child(2, &[7], &[8], "main.lt.n2b")] },
            n2b_i: InstanceInterface { children: vec![] },
            table,
        }
    }

    fn catalogue(h: &Hierarchy) -> Catalogue<'_> {
        let mut c: Catalogue = HashMap::new();
        c.insert("main".to_string(), InstanceEntry { circuit: &h.main_c, spec: &h.main_s, interface: &h.main_i });
        c.insert("main.lt".to_string(), InstanceEntry { circuit: &h.lt_c, spec: &h.lt_s, interface: &h.lt_i });
        c.insert("main.lt.n2b".to_string(), InstanceEntry { circuit: &h.n2b_c, spec: &h.n2b_s, interface: &h.n2b_i });
        c
    }

    #[test]
    fn depth_zero_asserts_no_call_at_all() {
        // Phase 1 runs at depth 0 throughout: every child is an implication, which
        // `check_cluster` adds from the interface, not from here.
        let h = hierarchy();
        let out = collect_inlined(&catalogue(&h), &h.table, "main", 0);
        assert!(out.names.is_empty());
        assert!(out.constraints.is_empty());
        assert!(out.atoms.is_empty());
        assert!(out.implications.is_empty());
    }

    #[test]
    fn depth_one_asserts_the_direct_call_and_abstracts_the_next() {
        let h = hierarchy();
        let out = collect_inlined(&catalogue(&h), &h.table, "main", 1);

        assert_eq!(out.names, vec!["main.lt".to_string()]);
        assert_eq!(out.constraints, vec![1], "the child's r1cs constraints come in");
        assert_eq!(out.atoms, vec![1], "and its atoms");
        assert!(out.signals.contains(&4) && out.signals.contains(&5));
        assert!(out.spec_vars.contains(&"spec_lt_out".to_string()));
        // Its own call is what takes its place as an approximation.
        assert_eq!(out.implications.len(), 1, "the grandchild is abstracted, not asserted");
        let (antecedent, consequent) = &out.implications[0];
        assert_eq!(antecedent.iter().map(|(s, _)| *s).collect::<Vec<_>>(), vec![7]);
        assert_eq!(consequent.iter().map(|(s, _)| *s).collect::<Vec<_>>(), vec![8]);
        // And the grandchild's ports are named through the instance that CALLS it.
        assert_eq!(consequent[0].1, "spec_lt_n2b_out");
    }

    #[test]
    fn the_ports_of_an_asserted_call_are_tied_to_the_callers_names() {
        // Without this the child's formula constrains symbols nothing else mentions.
        let h = hierarchy();
        let out = collect_inlined(&catalogue(&h), &h.table, "main", 1);
        let mut eqs = out.port_equalities.clone();
        eqs.sort();
        assert_eq!(eqs, vec![
            "(= spec_lt_a spec_main_lt_in0)".to_string(),
            "(= spec_lt_b spec_main_lt_in1)".to_string(),
            "(= spec_lt_out spec_main_lt_out)".to_string(),
        ]);
    }

    #[test]
    fn depth_two_keeps_the_first_level_and_asserts_the_second() {
        let h = hierarchy();
        let out = collect_inlined(&catalogue(&h), &h.table, "main", 2);

        let mut names = out.names.clone();
        names.sort();
        assert_eq!(names, vec!["main.lt".to_string(), "main.lt.n2b".to_string()],
                   "deepening keeps what was already asserted");
        assert_eq!(out.constraints, vec![1, 2]);
        assert_eq!(out.atoms, vec![1, 2]);
        // Nothing below n2b, so nothing is left approximated.
        assert!(out.implications.is_empty());
        assert!(out.port_equalities.iter().any(|e| e == "(= spec_n2b_in spec_lt_n2b_in)"));
    }

    #[test]
    fn deepening_stops_when_there_are_no_more_calls() {
        let h = hierarchy();
        let cat = catalogue(&h);
        assert!(has_instances_at(&cat, "main", 0), "main calls main.lt");
        assert!(has_instances_at(&cat, "main", 1), "and main.lt calls n2b");
        assert!(!has_instances_at(&cat, "main", 2), "n2b calls nothing");
        assert!(!has_instances_at(&cat, "main.lt.n2b", 0), "a leaf has nothing to deepen into");
    }
}
