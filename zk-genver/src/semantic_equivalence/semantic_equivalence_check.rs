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
use clustering::smt_hybrid::{
    structure_driven_circuit_and_smt_hybrid_clustering_into_structurereader,
    HybridClusteringMethodOptions, HybridClusteringMethods, HybridClusteringOptions,
    TiebreakingStrategy,
};
use serde::Serialize;
use solvers_interface::{PossibleResult, PossibleSolver};
use utils::read_correspondence::read_signal_correspondence;
use utils::read_specification::read_smt_specification;
use utils::small_utilities::DecomposeOptions;
use utils::structure::{transform_structure_reader, NodeInfo, StructureInfo, StructureReader};
use crate::semantic_equivalence::structure_from_spec::derive_structure;
use circuits_constraints_and_algebra::constraint::Constraint as _;

use crate::processing_utils::process_constraints;
use crate::report;
use crate::semantic_equivalence::atoms::{build_atoms, required_macro_definitions};
use crate::semantic_equivalence::modular_reasoning::{
    check_cluster, index_by_id, unbound_boundary_signals, ChildPorts,
    ClusterPair, InstanceInterface, VerificationContext,
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
    /// The cluster has no output signal that the specification names, so there
    /// is no equality to refute and any query would be vacuously `unsat`.
    /// Counted apart from VERIFIED, because it establishes nothing.
    NothingToVerify,
}

impl ClusterVerdict {
    fn as_str(&self) -> &'static str {
        match self {
            ClusterVerdict::Verified => "VERIFIED",
            ClusterVerdict::Failed => "FAILED",
            ClusterVerdict::LocalCounterexample => "INCONCLUSIVE_LOCAL_COUNTEREXAMPLE",
            ClusterVerdict::Unknown => "UNKNOWN",
            ClusterVerdict::NothingToVerify => "NOTHING_TO_VERIFY",
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
    // writes: macro -> [ { instance, tag: [signals] } ]. Avazar builds this
    // itself with `build_atoms`, so the two can drift; this makes them
    // comparable.
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
            by_macro
                .entry(info.macro_name.clone())
                .or_default()
                .entry(info.instance.clone())
                .or_default()
                .insert(info.tag.clone(), signals);
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
        guide_decompose_options: decompose_options,
        hybrid_decompose_method: HybridClusteringMethods::default(),
        hybrid_decompose_options: HybridClusteringMethodOptions {
            // A soundness condition, not a preference: with the specification as
            // the guide it forces signals(circuit k) subset of signals(spec k),
            // which is what lets a cluster's interface be stated in spec
            // variables at all.
            recipient_requires_subsets: true,
            ..Default::default()
        },
        manually_check_acyclic: false,
    };

    println!("LOG: clustering circuit and specification together");
    let clusterings = structure_driven_circuit_and_smt_hybrid_clustering_into_structurereader(
        &circuit,
        &structure_reader,
        &formula,
        hybrid_options,
        if user_input.flag_verbose { 2 } else { 1 },
    );

    // ASSUMED FROM HERE ON: the clusters admit a single order in which every
    // hypothesis is discharged before it is used -- the union of both sides'
    // edges and the proves->assumes edges is acyclic. Nothing below establishes
    // it, and the per-cluster results only compose if it holds.
    //
    // Assumed rather than checked because the check that used to be here reported
    // cycles on runs that were fine (several clusters listing one signal as an
    // output put an edge from each, downstream ones included). What justifies it:
    // `guided_clustering` orients the recipient with the guide's own topological
    // order, so the two sides cannot disagree on a shared edge's direction, and
    // `agree_on_merge` keeps every merge acyclic on both sides.

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
    };

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
        let circuit_node = *circuit_by_id.get(&spec_node.node_id).unwrap_or_else(|| {
            // The two clusterings are built with the same id set by construction:
            // `dual_merge_until_property` merges the same ids on both sides and
            // asserts the keysets match. A missing counterpart is a broken
            // clustering, not a specification the tool should try to work around.
            unreachable!(
                "Cluster {} of instance {} exists on the specification side but not on the \
                 circuit side. The hybrid clustering is supposed to keep one id set for both \
                 sides -- this is a bug in clustering::smt_hybrid, not in the input.",
                spec_node.node_id, instance
            )
        });

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
        let unbound = unbound_boundary_signals(spec_node, instance_info);
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

        let outcome = verify_cluster_with_refinement(&pair, &circuit_by_id, &spec_by_id, interface, ctx);
        let verdict = match outcome {
            Some(verdict) => verdict,
            None => {
                println!(
                    "NOTE: cluster {} has no output signal the specification names, so there is \
                     nothing to verify for it (a query would be vacuously unsat).",
                    spec_node.node_id
                );
                results
                    .clusters
                    .insert(spec_node.node_id, ClusterVerdict::NothingToVerify);
                results
                    .cluster_instance
                    .insert(spec_node.node_id, instance.to_string());
                results
                    .cluster_size
                    .insert(spec_node.node_id, circuit_node.constraints.len());
                record_cluster(results, instance, circuit_node, spec_node,
                               ClusterVerdict::NothingToVerify);
                continue;
            }
        };

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
/// `None` when there is nothing to verify, which refinement cannot change.
fn verify_cluster_with_refinement(
    pair: &ClusterPair,
    circuit_by_id: &HashMap<usize, &NodeInfo>,
    spec_by_id: &HashMap<usize, &NodeInfo>,
    interface: &InstanceInterface,
    ctx: &VerificationContext,
) -> Option<ClusterVerdict> {

    let mut asserted: BTreeSet<usize> = BTreeSet::from([pair.spec.node_id]);
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
        let mut abstracted_ids: BTreeSet<usize> = BTreeSet::new();
        // Everything the region borders in the specification dag, both ways,
        // whatever the direction flags say. Kept apart from `abstracted_ids` because
        // the two answer different questions: that one is what this query abstracts,
        // this one is whether there was anything to abstract at all -- which is what
        // makes a counterexample conclusive or not.
        let mut bordering_ids: BTreeSet<usize> = BTreeSet::new();
        for id in asserted.iter() {
            let node = spec_of(spec_by_id, id);
            for adjacent in node.successors.iter().chain(node.predecessors.iter()) {
                if !asserted.contains(adjacent) {
                    bordering_ids.insert(*adjacent);
                }
            }
            if take_successors {
                for adjacent in node.successors.iter() {
                    if !asserted.contains(adjacent) {
                        abstracted_ids.insert(*adjacent);
                    }
                }
            }
            if take_predecessors {
                for adjacent in node.predecessors.iter() {
                    if !asserted.contains(adjacent) {
                        abstracted_ids.insert(*adjacent);
                    }
                }
            }
            if ctx.instance_adjacency {
                // Every cluster here belongs to the instance being verified:
                // `verify_instance` is called once per structure node.
                for other in spec_by_id.keys() {
                    if !asserted.contains(other) {
                        abstracted_ids.insert(*other);
                        bordering_ids.insert(*other);
                    }
                }
            }
        }
        // The SPECIFICATION node of each neighbour: its abstraction has to be the
        // obligation its own query discharges, and that query states it over the
        // specification's split into inputs and outputs, not the circuit's.
        let abstracted: Vec<&NodeInfo> = abstracted_ids
            .iter()
            .map(|id| spec_of(spec_by_id, id))
            .collect();
        // Every cluster asserted on top of this one, paired with its
        // specification counterpart by the shared id.
        let inlined: Vec<(&NodeInfo, &NodeInfo)> = asserted
            .iter()
            .filter(|id| **id != pair.spec.node_id)
            .map(|id| (circuit_of(circuit_by_id, id), spec_of(spec_by_id, id)))
            .collect();

        let (result, logs) = check_cluster(pair, &abstracted, &inlined, interface, ctx)?;
        for log in logs {
            println!("{}", log);
        }

        let verdict = match result {
            PossibleResult::VERIFIED => ClusterVerdict::Verified,
            // Conclusive only when there was nothing left to abstract -- the region
            // borders no other cluster, either because it never did or because the
            // refinement rounds swallowed them all.
            PossibleResult::FAILED if bordering_ids.is_empty() => ClusterVerdict::Failed,
            PossibleResult::FAILED => ClusterVerdict::LocalCounterexample,
            _ => ClusterVerdict::Unknown,
        };

        let settled = matches!(verdict, ClusterVerdict::Verified | ClusterVerdict::Failed);
        if settled || round >= ctx.extra_rounds || abstracted.is_empty() {
            if round > 0 {
                println!(
                    "LOG: cluster {} settled as {} after {} refinement round(s), with {} \
                     neighbouring cluster(s) asserted",
                    pair.spec.node_id,
                    verdict.as_str(),
                    round,
                    inlined.len()
                );
            }
            return Some(verdict);
        }

        round += 1;
        println!(
            "LOG: cluster {} came back {}; refinement round {} of {}: asserting {} neighbouring \
             cluster(s) in full instead of abstracting them",
            pair.spec.node_id,
            verdict.as_str(),
            round,
            ctx.extra_rounds,
            abstracted_ids.len()
        );
        asserted.extend(abstracted_ids.into_iter());
    }
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
            && results.count(ClusterVerdict::LocalCounterexample) == 0
            && results.count(ClusterVerdict::NothingToVerify) == 0,
    );

    let summary = report::ReportSummary {
        total_nodes: results.clusters.len(),
        verified_nodes: results.count(ClusterVerdict::Verified),
        previously_verified_nodes: None,
        failed_nodes: results.count(ClusterVerdict::Failed),
        timeout_nodes: results.count(ClusterVerdict::Unknown)
            + results.count(ClusterVerdict::LocalCounterexample)
            + results.count(ClusterVerdict::NothingToVerify),
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
/// FAILED, a local counterexample and "nothing to verify" are three different
/// things (see [`ClusterVerdict`]).
fn print_pretty_results(results: &ResultInfoSemanticEquivalence) {
    let verified = results.count(ClusterVerdict::Verified);
    let failed = results.count(ClusterVerdict::Failed);
    let local = results.count(ClusterVerdict::LocalCounterexample);
    let unknown = results.count(ClusterVerdict::Unknown);
    let vacuous = results.count(ClusterVerdict::NothingToVerify);

    println!();

    println!("--------------------------------------------");
    println!("--------------------------------------------");
    println!("-- ZK-GENVER SEMANTIC EQUIVALENCE RESULTS --");
    println!("--------------------------------------------");
    println!("--------------------------------------------\n");

    if results.clusters.is_empty() {
        println!("-> There was no cluster pair to verify");
    } else if failed == 0 && local == 0 && unknown == 0 && vacuous == 0 {
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
        print_cluster_list(
            results,
            ClusterVerdict::NothingToVerify,
            "Cluster pairs with nothing to verify, no output of theirs is named by the specification (skipped, NOT verified): ",
        );
    }
    println!("  * Number of verified cluster pairs (semantic equivalence): {}", verified);
    println!("  * Number of failed cluster pairs (semantic equivalence): {}", failed);
    println!("  * Number of inconclusive cluster pairs (local counterexample): {}", local);
    println!("  * Number of timeout cluster pairs (semantic equivalence): {}", unknown);
    println!("  * Number of skipped cluster pairs (nothing to verify): {}", vacuous);
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
