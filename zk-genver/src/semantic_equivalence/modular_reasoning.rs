//! Builds and discharges the per-cluster verification query.
//!
//! One cluster pair (same id on both sides — that shared id IS the semantic
//! link the hybrid clustering establishes) becomes one solver call:
//!
//! ```text
//!   r1cs constraints of the circuit cluster
//! ∧ SMT-LIB formulas of the atoms of the spec cluster
//! ∧ abstraction of every adjacent cluster        (see `neighbour_implication`)
//! ∧ inputs(circuit cluster) = the spec vars bound to them
//! ∧ ¬( outputs(circuit cluster) = the spec vars bound to them )
//! ```
//!
//! `unsat` means the cluster cannot disagree with its specification, i.e.
//! VERIFIED.
//!
//! ## Abstracting a neighbour, and inlining it instead
//!
//! A cluster's inputs come from sibling clusters. Asserting their constraints
//! would grow every query back towards the whole template, so each is summed up
//! by `inputs ⇒ outputs` — the same device
//! `correctness::modular_reasoning::generate_implications_safety` uses for
//! subcomponents, except that a cluster has no macro of its own (its boundary
//! was chosen by Leiden), so the pairing goes straight from the r1cs signal id
//! to the spec variable bound to it in the enclosing instance.
//!
//! When that abstraction is too weak to close the proof, `--extra_rounds`
//! asserts the neighbour in full instead: its r1cs constraints on one side, its
//! spec atoms on the other. An inlined neighbour loses its implication — that
//! implication is the hypothesis "this neighbour agrees with the spec", which is
//! what is in question — and that is what makes a counterexample found with
//! nothing left abstracted a real one.

use std::collections::{BTreeMap, HashMap, HashSet, LinkedList};

use circuits_constraints_and_algebra::num_bigint::BigInt;
use circuits_constraints_and_algebra::r1cs::R1CSConstraint as Constraint;
use indexmap::IndexMap;

use solvers_interface::sanitize_symbol;
use solvers_interface::{
    cvc5_interface, ffsol_interface, nia_z3_interface, parallel_interface, yices_interface,
    CorrectnessVerification, PossibleResult, PossibleSolver, ProblemAnnotations,
};
use utils::structure::NodeInfo;

use crate::semantic_equivalence::atoms::{AtomTable, InstanceInfo};

/// The ports of one subcomponent instance, read straight off `structure.json`.
pub struct ChildPorts {
    /// The structure node id of the child, for the annotations.
    pub node_id: usize,
    /// Its dotted instance prefix, for the annotations.
    pub instance: String,
    pub inputs: Vec<usize>,
    pub outputs: Vec<usize>,
}

/// The subcomponents of one instance, each with its own ports.
///
/// A node in `structure.json` declares only its OWN ports, so the wires crossing
/// down to a subcomponent are invisible to the per-template subcircuit and the
/// `DAGNode` classifies them as neither input nor output. Left like that, a
/// cluster reading a child's output has no hypothesis about that wire and its
/// query is trivially satisfiable. They enter as one implication per child
/// instead — see [`child_implication`] — the way the template-level modes do it.
#[derive(Default)]
pub struct InstanceInterface {
    pub children: Vec<ChildPorts>,
}

/// A cluster pair to verify: the same node id on the circuit side and on the
/// specification side.
pub struct ClusterPair<'a> {
    /// Dotted instance prefix both clusters live in.
    pub instance: &'a str,
    /// The cluster on the circuit side (its `constraints` are indices into
    /// the global r1cs constraint list).
    pub circuit: &'a NodeInfo,
    /// The cluster on the specification side (its `constraints` are atom
    /// indices into the `Formula`, hence into [`AtomTable::atoms`]).
    pub spec: &'a NodeInfo,
}

/// Everything the query needs that is fixed for the whole run.
pub struct VerificationContext<'a> {
    pub constraints: &'a Vec<Constraint<usize>>,
    pub table: &'a AtomTable,
    /// Every macro of the specification, rendered as a `define-fun`. Narrowed
    /// per query by [`narrow_macros`], never by omission here: `build_macros`
    /// renders a macro left out as `true`, which frees that call's output.
    pub macros: &'a IndexMap<String, String>,
    pub field: &'a BigInt,
    /// Every cluster of the instance counts as a neighbour, edge or no edge —
    /// the complete graph over the instance, beyond what either side's edges say.
    ///
    /// Where an instance gets split is the algorithm's choice, not a semantic
    /// boundary: the constraints feeding a child's inputs can land in one cluster
    /// while the constraint consuming its output lands in another, leaving the
    /// second with a child implication whose antecedent nothing in its own query
    /// discharges. Only ever ADDS hypotheses, each of them some cluster's own
    /// obligation, so it cannot turn a real counterexample into a proof; it costs
    /// query size.
    pub instance_adjacency: bool,
    /// Which way to look for the neighbours to abstract, exactly as
    /// `correctness::modular_reasoning` and `determinism::modular_reasoning` read
    /// the same two flags: successors by default, predecessors instead under
    /// `--apply_predecessors`, both under `--apply_bidirectional`.
    pub apply_predecessors: bool,
    pub apply_bidirectional: bool,
    pub timeout: u64,
    pub solver: PossibleSolver,
    pub verbose: bool,
    pub original_file: &'a str,
    /// How many times a cluster with an inconclusive verdict may be retried with
    /// its neighbours asserted instead of abstracted (`--extra_rounds`, the same
    /// knob the template-level modes use for their own retries).
    pub extra_rounds: usize,
    /// r1cs signal id -> its name in the circom program, straight from
    /// `--correspondence`. Only used to annotate the generated `.smt2`.
    pub signal_names: &'a BTreeMap<usize, String>,
}

/// The `inputs ⇒ outputs` abstraction of one adjacent cluster: **that cluster's
/// own obligation, written as a formula**.
///
/// `node` must be the neighbour's SPECIFICATION node, through the same
/// [`bound_boundary`] its own query goes through, or the abstraction concludes
/// something other than what that query proves. Synthetic ids are dropped by the
/// caller: they have no circuit wire to be equated to.
fn neighbour_implication(
    node: &NodeInfo,
    instance: &InstanceInfo,
) -> (Vec<(usize, String)>, Vec<(usize, String)>) {
    bound_boundary(node, instance)
}

/// The same abstraction for one CHILD INSTANCE, paired through the ENCLOSING
/// instance's bindings: the child's ports are named in the parent's spec too
/// (`lt.in`, `lt.out`), and those are the variables the parent's atoms talk
/// about. Mirrors `generate_implications_safety`, which goes through the father
/// macro for the same reason.
fn child_implication(
    child: &ChildPorts,
    instance: &InstanceInfo,
) -> (Vec<(usize, String)>, Vec<(usize, String)>) {
    let bind = |signals: &Vec<usize>| -> Vec<(usize, String)> {
        signals
            .iter()
            .filter_map(|s| instance.signal_to_spec_var.get(s).map(|v| (*s, v.clone())))
            .collect()
    };
    (bind(&child.inputs), bind(&child.outputs))
}

/// Assembles the query for one cluster pair and hands it to the solver.
///
/// `adjacent` are abstracted by an implication; `inlined` are asserted in full
/// (empty unless `--extra_rounds` asked for them). The two must be disjoint.
/// Either way the obligation never moves: it is always about THIS cluster's
/// boundary, and inlining only adds hypotheses on the left of it.
///
/// `None` when there is nothing to verify (the vacuity guard below).
pub fn check_cluster(
    pair: &ClusterPair,
    adjacent: &[&NodeInfo],
    inlined: &[(&NodeInfo, &NodeInfo)],
    interface: &InstanceInterface,
    ctx: &VerificationContext,
) -> Option<(PossibleResult, Vec<String>)> {
    let instance = ctx.table.instance(pair.instance);
    // The ids the preprocessor invented for specification variables with no r1cs
    // wire behind them. Needed early: the boundary and the neighbour abstractions
    // are read off SPECIFICATION nodes now, whose ports can include one of these,
    // and there is no circuit signal to equate it to -- declaring `s_<id>` for it
    // would invent a wire and hand the solver a free variable.
    let synthetic: HashSet<usize> = ctx.table.unresolved_ids.values().copied().collect();
    let drop_synthetic = |bound: Vec<(usize, String)>| -> Vec<(usize, String)> {
        bound.into_iter().filter(|(s, _)| !synthetic.contains(s)).collect()
    };

    // ---- circuit side ----------------------------------------------------
    // Deduplicated: one `declare-fun` per entry of `signals_1`, and a cluster's
    // signals overlap its neighbours' by definition. A redeclaration is rejected
    // by the solver, which reads back as a timeout.
    let mut declared: HashSet<usize> = HashSet::new();
    let mut signals_1: LinkedList<usize> = LinkedList::new();
    for signal in pair.circuit.signals.iter().copied() {
        if declared.insert(signal) {
            signals_1.push_back(signal);
        }
    }
    let mut constraints_1: Vec<Constraint<usize>> = pair
        .circuit
        .constraints
        .iter()
        .map(|c| ctx.constraints[*c].clone())
        .collect();
    // Parallel to `constraints_1`: which r1cs constraint, and whose.
    let mut constraint_notes: Vec<String> = pair
        .circuit
        .constraints
        .iter()
        .map(|c| format!("r1cs constraint {} of cluster {}", c, pair.spec.node_id))
        .collect();
    for (circuit_node, _) in inlined.iter() {
        for signal in circuit_node.signals.iter().copied() {
            if declared.insert(signal) {
                signals_1.push_back(signal);
            }
        }
        constraints_1.extend(circuit_node.constraints.iter().map(|c| ctx.constraints[*c].clone()));
        constraint_notes.extend(circuit_node.constraints.iter().map(|c| {
            format!(
                "r1cs constraint {} of cluster {}, asserted in full by --extra_rounds",
                c, circuit_node.node_id
            )
        }));
    }

    // ---- specification side ---------------------------------------------
    let mut constraints_2: Vec<String> = pair
        .spec
        .constraints
        .iter()
        .map(|atom| ctx.table.atom(*atom).formula.clone())
        .collect();
    // Parallel to `constraints_2`: which tag of which macro each assertion is.
    let atom_note = |atom: &usize, cluster: usize| {
        let info = ctx.table.atom(*atom);
        format!(
            "atom {} of cluster {}: tag \"{}\" of {} in {}",
            atom, cluster, info.tag, info.macro_name, info.instance
        )
    };
    let mut atom_notes: Vec<String> = pair
        .spec
        .constraints
        .iter()
        .map(|atom| atom_note(atom, pair.spec.node_id))
        .collect();
    for (_, spec_node) in inlined.iter() {
        constraints_2.extend(
            spec_node
                .constraints
                .iter()
                .map(|atom| ctx.table.atom(*atom).formula.clone()),
        );
        atom_notes.extend(
            spec_node
                .constraints
                .iter()
                .map(|atom| atom_note(atom, spec_node.node_id)),
        );
    }

    // Every spec variable of the instance, narrowed below to the ones the query
    // mentions: a `declare-fun` with no assertion over it reads like a free
    // variable, which is the shape of the bug this mode keeps hitting.
    let mut signals_2: Vec<String> = instance.spec_vars.clone();

    // ---- interface -------------------------------------------------------
    let split = |bound: Vec<(usize, String)>| -> (Vec<usize>, Vec<String>) {
        (bound.iter().map(|(s, _)| *s).collect(), bound.into_iter().map(|(_, v)| v).collect())
    };
    // From the SPECIFICATION side. The two clusterings agree on which signals a
    // cluster holds but not on how they split into inputs and outputs, and the
    // circuit split leaves clusters with no output at all -- skipped as
    // NOTHING_TO_VERIFY -- while a sibling inherits the output without the
    // constraints producing it. Measured over circomlib: recovers four circuits,
    // removes a false FAILED, changes nothing in the ten that already worked.
    let (assumed, proved) = bound_boundary(pair.spec, instance);
    let (inputs_1, mut inputs_2) = split(drop_synthetic(assumed));
    let (outputs_1, mut outputs_2) = split(drop_synthetic(proved));

    // No output the spec names means a VACUOUS query: the disagreement clause
    // becomes `(assert (not true))` and is `unsat` whatever the circuit says.
    // Reporting that as VERIFIED would be a lie.
    if outputs_2.is_empty() {
        return None;
    }

    // ---- neighbours ------------------------------------------------------
    let mut implications = Vec::new();
    // Parallel to `implications`: what each one stands in for.
    let mut implication_notes: Vec<String> = Vec::new();
    let mut abstracted_ids: Vec<usize> = Vec::new();
    let mut seen: HashSet<usize> = inlined.iter().map(|(c, _)| c.node_id).collect();
    for node in adjacent {
        if node.node_id == pair.spec.node_id || !seen.insert(node.node_id) {
            continue;
        }
        let implication = {
            let (ins, outs) = neighbour_implication(node, instance);
            (drop_synthetic(ins), drop_synthetic(outs))
        };
        // Declare exactly what the implication mentions, taken from it rather
        // than from the node's ports: no longer the same set.
        for (signal, _) in implication.0.iter().chain(implication.1.iter()) {
            if declared.insert(*signal) {
                signals_1.push_back(*signal);
            }
        }
        implications.push(implication);
        implication_notes.push(format!(
            "sibling cluster {} abstracted: assumed to agree on its outputs given its inputs, \
             which is what its own query proves",
            node.node_id
        ));
        abstracted_ids.push(node.node_id);
    }

    // ---- child instances -------------------------------------------------
    // Only the children this region touches: one whose ports appear nowhere here
    // would add an implication over signals no constraint mentions.
    let mut abstracted_children: Vec<String> = Vec::new();
    for child in interface.children.iter() {
        let touches = child
            .inputs
            .iter()
            .chain(child.outputs.iter())
            .any(|s| declared.contains(s));
        if !touches {
            continue;
        }
        let implication = child_implication(child, instance);
        if implication.0.is_empty() && implication.1.is_empty() {
            // The specification names none of that child's ports: nothing to
            // relate, and asserting `true => true` only adds noise.
            continue;
        }
        // If everything the implication concludes is already an assumed input of
        // this cluster, it concludes nothing new while its antecedent names the
        // child's inputs, which nothing here binds. Harmless, but the exact shape
        // of the undischarged premise that is not.
        if !implication.1.is_empty()
            && implication.1.iter().all(|(s, _)| inputs_1.contains(s))
        {
            continue;
        }
        for (signal, _) in implication.0.iter().chain(implication.1.iter()) {
            if declared.insert(*signal) {
                signals_1.push_back(*signal);
            }
        }
        implications.push(implication);
        implication_notes.push(format!(
            "child instance {} (cluster {}) abstracted: its formula is left out of this query \
             because its own query proves this implication",
            child.instance, child.node_id
        ));
        abstracted_children.push(format!("{} (node {})", child.instance, child.node_id));
    }

    let mut dropped_atoms: Vec<usize> = Vec::new();
    // A child's macro call is redundant once the child is abstracted: the
    // implication already ties its spec-side output to the circuit's, so dropping
    // the call takes the child's whole formula out of the query.
    //
    // Guarded, because the call also binds the child's internal spec variables:
    // it goes only when everything it binds beyond the implication's own
    // variables is unused here. Otherwise removing it would free a variable.
    {
        let covered: HashSet<&str> = implications
            .iter()
            .flat_map(|(ins, outs)| ins.iter().chain(outs.iter()))
            .map(|(_, var)| var.as_str())
            .collect();
        let own = pair.spec.constraints.len();
        let mut drop: Vec<bool> = vec![false; constraints_2.len()];
        for i in 0..constraints_2.len() {
            if !constraints_2[i].contains(":meta-data \"call ") {
                continue;
            }
            let bound = spec_variables(&constraints_2[i]);
            let uncovered: Vec<&String> = bound
                .iter()
                .filter(|v| !covered.contains(v.as_str()))
                .collect();
            let read_elsewhere = constraints_2.iter().enumerate().any(|(j, other)| {
                j != i && uncovered.iter().any(|v| mentions_identifier(other, v))
            });
            if !read_elsewhere {
                drop[i] = true;
                // Atom ids are the circuit's, so a silent gap reads like a loss.
                if i < own {
                    dropped_atoms.push(pair.spec.constraints[i]);
                }
            }
        }
        if drop.iter().any(|d| *d) {
            let mut k = 0;
            constraints_2.retain(|_| { k += 1; !drop[k - 1] });
            let mut k = 0;
            atom_notes.retain(|_| { k += 1; !drop[k - 1] });
        }
    }

    // Always `cluster_N`, never the DAGNode's own `node_name`: that one defaults
    // to `node_N`, which reads on disk like a circom template rather than a
    // cluster the algorithm chose.
    let node_name = format!("cluster_{}", pair.spec.node_id);

    // ---- annotations -----------------------------------------------------
    // Everything a person needs to read this query without the correspondence
    // file and the structure open beside it.
    let mut annotations = ProblemAnnotations::default();
    annotations.header.push(format!(
        "semantic equivalence: cluster {} of instance {}",
        pair.spec.node_id, pair.instance
    ));
    let kept_atoms = pair.spec.constraints.len() - dropped_atoms.len();
    annotations.header.push(format!(
        "{} r1cs constraint(s) vs {} specification atom(s)",
        pair.circuit.constraints.len(),
        kept_atoms
    ));
    // Atom ids are the circuit's, not the cluster's, so a file that starts at
    // atom 2 is normal and worth saying out loud.
    if let (Some(first), Some(last)) = (
        pair.spec.constraints.iter().min(),
        pair.spec.constraints.iter().max(),
    ) {
        annotations.header.push(format!(
            "specification atoms {}-{} of the circuit's {}; ids are the circuit's, so they do \
             not start at 0",
            first,
            last,
            ctx.table.atoms.len()
        ));
    }
    if !dropped_atoms.is_empty() {
        annotations.header.push(format!(
            "atom(s) {:?} dropped: a call into an abstracted child, already covered by that \
             child's implication below",
            dropped_atoms
        ));
    }
    annotations.header.push(format!(
        "assumed to agree (inputs): {:?}",
        inputs_1.iter().map(|s| signal_label(s, ctx, &synthetic)).collect::<Vec<_>>()
    ));
    annotations.header.push(format!(
        "to be proved to agree (outputs): {:?}",
        outputs_1.iter().map(|s| signal_label(s, ctx, &synthetic)).collect::<Vec<_>>()
    ));
    if !inlined.is_empty() {
        annotations.header.push(format!(
            "asserted in full alongside it (--extra_rounds): cluster(s) {:?}",
            inlined.iter().map(|(c, _)| c.node_id).collect::<Vec<_>>()
        ));
    }
    if !abstracted_children.is_empty() {
        annotations.header.push(format!(
            "child instance(s) abstracted by an implication: {}",
            abstracted_children.join(", ")
        ));
    }
    // Sibling clusters only, and only when there are any: the old wording said
    // "nothing abstracted" on queries that abstract a child two lines above.
    if !abstracted_ids.is_empty() {
        annotations.header.push(format!(
            "sibling cluster(s) abstracted by an implication: {:?} -- a counterexample may be spurious",
            abstracted_ids
        ));
    }
    annotations.signals = signals_1
        .iter()
        .filter_map(|s| ctx.signal_names.get(s).map(|name| (*s, name.clone())))
        .collect();
    // A spec variable on its own says nothing; what it is bound to does.
    for (signal, var) in instance.signal_to_spec_var.iter() {
        let entry = annotations
            .spec_vars
            .entry(var.clone())
            .or_insert_with(String::new);
        let label = signal_label(signal, ctx, &synthetic);
        if entry.is_empty() {
            *entry = format!("= {}", label);
        } else {
            // A tie: the specification says these signals are the same wire.
            entry.push_str(&format!(" = {}", label));
        }
    }
    annotations.constraints = constraint_notes;
    annotations.atoms = atom_notes;
    annotations.implications = implication_notes;

    // `spec_main_isz_out` rather than `spec_main_v_14`, for variables tied to a
    // real wire (synthetic ones name nothing and keep their `v_N`). Textual,
    // because the atoms carry the old names inside their formulas; longest first,
    // or `spec_main_v_1` would corrupt every `spec_main_v_14`.
    {
        // A variable covering several signals is the spec saying they are the
        // same wire: name it after all of them, sorted. Picking one arbitrarily
        // named consecutive elements of one bus after different components.
        let mut wires_of: BTreeMap<&String, Vec<String>> = BTreeMap::new();
        for (signal, var) in instance.signal_to_spec_var.iter() {
            if synthetic.contains(signal) {
                continue;
            }
            if let Some(wire) = ctx.signal_names.get(signal) {
                wires_of.entry(var).or_default().push(sanitize_symbol(wire));
            }
        }
        let mut rename: Vec<(String, String)> = Vec::new();
        let mut taken: HashSet<String> = HashSet::new();
        for (var, mut wires) in wires_of {
            wires.sort();
            wires.dedup();
            let candidate = format!("spec_{}", wires.join("__"));
            if candidate == *var || !taken.insert(candidate.clone()) {
                continue;
            }
            rename.push((var.clone(), candidate));
        }
        rename.sort_by(|a, b| b.0.len().cmp(&a.0.len()));

        if !rename.is_empty() {
            let apply = |text: &str| -> String {
                let mut out = text.to_string();
                for (from, to) in rename.iter() {
                    out = replace_identifier(&out, from, to);
                }
                out
            };
            for c in constraints_2.iter_mut() {
                *c = apply(c);
            }
            for v in signals_2.iter_mut() {
                *v = apply(v);
            }
            for v in inputs_2.iter_mut() {
                *v = apply(v);
            }
            for v in outputs_2.iter_mut() {
                *v = apply(v);
            }
            for (ins, outs) in implications.iter_mut() {
                for (_, v) in ins.iter_mut().chain(outs.iter_mut()) {
                    *v = apply(v);
                }
            }
            annotations.spec_vars = annotations
                .spec_vars
                .iter()
                .map(|(k, v)| (apply(k), v.clone()))
                .collect();
        }
    }

    // `required_macro_definitions` computes reachability over every atom of the
    // run, so its set is global: two thirds of a query's definitions are never
    // called by it. Cheap for the solver, noise for the reader.
    let macros_for_query = narrow_macros(ctx.macros, &constraints_2);

    // Declare only what is left. After the call removal and `narrow_macros`, so
    // it sees the final assertions. The interface variables are added by name:
    // the hypothesis and the goal are built downstream, not from any text here.
    {
        let mut used: HashSet<String> = HashSet::new();
        for text in constraints_2.iter().chain(macros_for_query.values()) {
            used.extend(spec_variables(text));
        }
        for (ins, outs) in implications.iter() {
            used.extend(ins.iter().chain(outs.iter()).map(|(_, v)| v.clone()));
        }
        used.extend(inputs_2.iter().cloned());
        used.extend(outputs_2.iter().cloned());
        signals_2.retain(|v| used.contains(v));
        // Drop the notes for what is no longer declared.
        annotations.spec_vars.retain(|v, _| used.contains(v));
    }

    // After the sweep, or the count would predate it. Against the circuit's and
    // the instance's totals, so the ratio shows how much this query carries.
    let header_pos = annotations.header.len().min(2);
    annotations.header.insert(
        header_pos,
        format!(
            "declares {} of the circuit's {} signal(s) and {} of the instance's {} \
             specification variable(s)",
            signals_1.len(),
            ctx.signal_names.len(),
            signals_2.len(),
            instance.spec_vars.len()
        ),
    );

    let verification = CorrectnessVerification::new(
        &node_name,
        &ctx.original_file.to_string(),
        signals_1,
        signals_2,
        inputs_1,
        inputs_2,
        outputs_1,
        outputs_2,
        constraints_1,
        constraints_2,
        implications,
        ctx.field,
        ctx.timeout,
        ctx.verbose,
        macros_for_query,
    )
    // So a semantic-equivalence run's .smt2 files are told apart from a
    // correctness run's over the same circuit.
    .with_file_prefix("semantic")
    .with_annotations(annotations);

    Some(run_solver(&verification, ctx.solver))
}




/// Whole-identifier replacement: `spec_main_v_1` must not be rewritten inside
/// `spec_main_v_14`.
fn replace_identifier(text: &str, from: &str, to: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let bytes = text.as_bytes();
    let mut i = 0;
    while i < text.len() {
        if text[i..].starts_with(from) {
            let end = i + from.len();
            let before_ok = i == 0 || {
                let c = bytes[i - 1] as char;
                !(c.is_alphanumeric() || c == '_')
            };
            let after_ok = end >= bytes.len() || {
                let c = bytes[end] as char;
                !(c.is_alphanumeric() || c == '_')
            };
            if before_ok && after_ok {
                out.push_str(to);
                i = end;
                continue;
            }
        }
        let ch = text[i..].chars().next().unwrap();
        out.push(ch);
        i += ch.len_utf8();
    }
    out
}

/// Every specification variable an assertion mentions (`spec_main_v_14` and the
/// like), leaving out the `spec_macro_*` symbols, which are functions.
fn spec_variables(text: &str) -> HashSet<String> {
    let mut out = HashSet::new();
    let bytes = text.as_bytes();
    let mut i = 0;
    while let Some(p) = text[i..].find("spec_") {
        let start = i + p;
        // Mid-identifier match: not the start of a name.
        if start > 0 {
            let prev = bytes[start - 1] as char;
            if prev.is_alphanumeric() || prev == '_' {
                i = start + 5;
                continue;
            }
        }
        let mut end = start;
        while end < bytes.len() {
            let c = bytes[end] as char;
            if c.is_alphanumeric() || c == '_' {
                end += 1;
            } else {
                break;
            }
        }
        let ident = &text[start..end];
        if !ident.starts_with("spec_macro_") {
            out.insert(ident.to_string());
        }
        i = end.max(start + 5);
    }
    out
}

/// Whole-identifier search: `spec_main_v_1` must not match inside `spec_main_v_14`.
fn mentions_identifier(text: &str, ident: &str) -> bool {
    let bytes = text.as_bytes();
    let mut from = 0;
    while let Some(p) = text[from..].find(ident) {
        let start = from + p;
        let end = start + ident.len();
        let before_ok = start == 0 || {
            let c = bytes[start - 1] as char;
            !(c.is_alphanumeric() || c == '_')
        };
        let after_ok = end >= bytes.len() || {
            let c = bytes[end] as char;
            !(c.is_alphanumeric() || c == '_')
        };
        if before_ok && after_ok {
            return true;
        }
        from = start + 1;
    }
    false
}

/// The macros a query invokes, in `ctx.macros`'s order (SMT-LIB wants a
/// `define-fun` before its callers; `required_macro_definitions` worked that out
/// already). Only the spec assertions are scanned — the implications are plain
/// `signal = spec-var` pairs and call nothing.
///
/// Exactness matters more than size: a macro left out renders as `true`, which
/// frees that call's output. So the scan closes over the bodies it finds and then
/// checks nothing invoked went missing.
fn narrow_macros(
    all: &IndexMap<String, String>,
    assertions: &[String],
) -> IndexMap<String, String> {
    fn calls_in(text: &str, all: &IndexMap<String, String>, needed: &mut HashSet<String>) {
        for name in all.keys() {
            if !needed.contains(name) && text.contains(&format!("({} ", name)) {
                needed.insert(name.clone());
            }
        }
    }

    let mut needed: HashSet<String> = HashSet::new();
    for text in assertions.iter() {
        calls_in(text, all, &mut needed);
    }
    // A macro's own body can call another one.
    loop {
        let before = needed.len();
        for name in needed.iter().cloned().collect::<Vec<_>>() {
            if let Some(body) = all.get(&name) {
                calls_in(body, all, &mut needed);
            }
        }
        if needed.len() == before {
            break;
        }
    }

    let kept: IndexMap<String, String> = all
        .iter()
        .filter(|(name, _)| needed.contains(*name))
        .map(|(n, b)| (n.clone(), b.clone()))
        .collect();

    // `(name ` is an application; `(define-fun name ` does not match it.
    for text in assertions.iter().chain(kept.values()) {
        let mut rest = text.as_str();
        while let Some(i) = rest.find("(spec_macro_") {
            rest = &rest[i + 1..];
            let end = rest
                .find(|c: char| c.is_whitespace() || c == ')' || c == '(')
                .unwrap_or(rest.len());
            let symbol = &rest[..end];
            if all.contains_key(symbol) && !kept.contains_key(symbol) {
                panic!(
                    "Query invokes macro '{}' but the narrowed set does not define it. \
                     Emitting it would render as `true` and free that call's output, so the \
                     query would report a counterexample that is not there.",
                    symbol
                );
            }
        }
    }

    kept
}

/// The boundary the obligation is stated over: the signals of
/// [`classify_boundary`] the spec binds, paired with their variable. `.0` is what
/// the query ASSUMES, `.1` what it PROVES. Unbound signals drop out — nothing to
/// equate them to. Single definition of a cluster's interface, on purpose.
pub fn bound_boundary(
    node: &NodeInfo,
    instance: &InstanceInfo,
) -> (Vec<(usize, String)>, Vec<(usize, String)>) {
    let bind = |signals: Vec<usize>| -> Vec<(usize, String)> {
        signals
            .into_iter()
            .filter_map(|s| instance.signal_to_spec_var.get(&s).map(|v| (s, v.clone())))
            .collect()
    };
    let (inputs, outputs) = classify_boundary(node);
    (bind(inputs), bind(outputs))
}

/// `12 (main.lt.in[0])`, `8 (synthetic: no r1cs wire)` for an invented id, bare
/// `12` for a real signal the correspondence does not name. The synthetic ones
/// are never equated to anything circuit-side, so a plain number would read like
/// a wire whose name is merely missing.
fn signal_label(signal: &usize, ctx: &VerificationContext, synthetic: &HashSet<usize>) -> String {
    match ctx.signal_names.get(signal) {
        Some(name) => format!("{} ({})", signal, name),
        None if synthetic.contains(signal) => format!("{} (synthetic: no r1cs wire)", signal),
        None => format!("{}", signal),
    }
}

/// The ports the `DAGNode` gives a cluster, and nothing else: a subcomponent's
/// wires are NOT folded in, they enter as [`child_implication`].
///
/// Inputs win a tie. A signal on both sides of `in = ... ∧ ¬(out = ...)` is
/// unsatisfiable on the spot — a VERIFIED that checked nothing.
pub fn classify_boundary(node: &NodeInfo) -> (Vec<usize>, Vec<usize>) {
    let mut inputs: Vec<usize> = node.input_signals.clone();
    inputs.sort();
    inputs.dedup();

    let input_set: HashSet<usize> = inputs.iter().copied().collect();
    let mut outputs: Vec<usize> = node
        .output_signals
        .iter()
        .copied()
        .filter(|s| !input_set.contains(s))
        .collect();
    outputs.sort();
    outputs.dedup();

    (inputs, outputs)
}

/// Which signals of a cluster the specification says nothing about. Reported,
/// not tolerated: an unbound OUTPUT is one the query never constrains, so a
/// VERIFIED verdict says nothing about it.
pub fn unbound_boundary_signals(node: &NodeInfo, instance: &InstanceInfo) -> Vec<usize> {
    let (inputs, outputs) = classify_boundary(node);
    inputs
        .into_iter()
        .chain(outputs.into_iter())
        .filter(|s| !instance.signal_to_spec_var.contains_key(s))
        .collect()
}

fn run_solver(
    problem: &CorrectnessVerification,
    solver: PossibleSolver,
) -> (PossibleResult, Vec<String>) {
    match solver {
        PossibleSolver::FFSOL => ffsol_interface::study_correctness(
            problem,
            &ffsol_interface::FfsolConfig::default(problem.verification_timeout, problem.verbose),
        ),
        PossibleSolver::CVC5 => cvc5_interface::study_correctness(problem),
        PossibleSolver::YICES => yices_interface::study_correctness(problem),
        PossibleSolver::NIAZ3 => nia_z3_interface::study_correctness(problem),
        PossibleSolver::ALL => parallel_interface::study_correctness(problem),
        _ => unreachable!("solver rejected earlier by prove_semantic_equivalence"),
    }
}

/// Index of a structure's nodes by id, for the adjacency lookups.
pub fn index_by_id(nodes: &[NodeInfo]) -> HashMap<usize, &NodeInfo> {
    nodes.iter().map(|n| (n.node_id, n)).collect()
}

#[cfg(test)]
mod tests {
    //! The boundary arithmetic: which signal ends up on which side.

    use super::*;

    fn node(inputs: &[usize], outputs: &[usize], extra: &[usize]) -> NodeInfo {
        let mut signals: Vec<usize> = inputs
            .iter()
            .chain(outputs.iter())
            .chain(extra.iter())
            .copied()
            .collect();
        signals.sort();
        signals.dedup();
        NodeInfo {
            node_id: 7,
            node_name: "cluster_7".to_string(),
            component_name: String::new(),
            constraints: vec![0],
            input_signals: inputs.to_vec(),
            output_signals: outputs.to_vec(),
            signals,
            is_custom: false,
            is_deterministic: false,
            predecessors: Vec::new(),
            successors: Vec::new(),
        }
    }

    /// Everything listed is bound, so the boundary rules are what is observed.
    fn instance(signals: &[usize]) -> InstanceInfo {
        InstanceInfo {
            signal_to_spec_var: signals.iter().map(|s| (*s, format!("spec_v_{}", s))).collect(),
            spec_vars: signals.iter().map(|s| format!("spec_v_{}", s)).collect(),
        }
    }

    fn child(inputs: &[usize], outputs: &[usize]) -> ChildPorts {
        ChildPorts {
            node_id: 1,
            instance: "main.lt".to_string(),
            inputs: inputs.to_vec(),
            outputs: outputs.to_vec(),
        }
    }

    fn ids(pairs: &[(usize, String)]) -> Vec<usize> {
        pairs.iter().map(|(s, _)| *s).collect()
    }

    #[test]
    fn the_boundary_is_the_clusters_own_ports_only() {
        // 4 is a child's output, 5 a child's input: neither becomes a port here.
        let cluster = node(&[2], &[3], &[4, 5]);
        let (assumed, proved) = bound_boundary(&cluster, &instance(&[2, 3, 4, 5]));

        assert_eq!(ids(&assumed), vec![2]);
        assert_eq!(ids(&proved), vec![3]);
    }
}
