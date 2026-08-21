//! Turns the specification into the atoms the clustering works on.
//!
//! The chain is:
//!
//! ```text
//! spec.json ──llzk_smt_preprocessor──> ResolvedMacroEntry (one per INSTANCE)
//!                                          │  tags: signals + SMT-LIB text
//!                                          ▼
//!                                     Formula  (atoms = top-level tags)
//!                                     AtomTable (what each atom index means)
//! ```
//!
//! One atom = **one top-level tag** of a macro instance, because that is the
//! only level that partitions the formula: a macro body is
//! `(and branch0 branch1 ...)` and each top-level tag is exactly one branch, so
//! the atoms cover it without overlapping. Nested tags overlap (a parent's text
//! contains its children's) and the leaves lose the structure holding them
//! together (the `ite` of an `if`).

use std::collections::{BTreeMap, HashMap, HashSet};

use circuits_constraints_and_algebra::num_bigint::BigInt;
use circuits_constraints_and_algebra::smt_formula::{Formula, FormulaAtom};
use indexmap::IndexMap;
use llzk_smt_preprocessor::graph::resolve_full;
use llzk_smt_preprocessor::resolve::{aggregate_resolved, ResolvedMacroEntry, ResolvedVar};
use utils::read_specification::MacroDef;
use utils::structure::StructureInfo;

/// What an atom of the [`Formula`] is, kept alongside it so a verification step
/// can go from "atom 17 landed in cluster 3" to the SMT-LIB it must assert.
/// Everything beyond `formula` is diagnostics: what makes a solver log traceable
/// back to a place in the specification.
#[derive(Clone, Debug)]
#[allow(dead_code)]
pub struct AtomInfo {
    /// Dotted instance prefix this atom belongs to (`"main"`, `"main.sub3"`).
    pub instance: String,
    /// Name of the macro the atom came from (`"@IsZero_0"`).
    pub macro_name: String,
    /// The `:meta-data` value, or the synthetic `"andN"` for a branch of the
    /// top-level `and` that llzk didn't annotate.
    pub tag: String,
    /// The atom's SMT-LIB text, **already rewritten** into the shared
    /// namespace: the macro's own `v_k` have been replaced by the
    /// `spec_{instance}_v_k` names declared for this instance.
    pub formula: String,
}

/// Everything the verification side needs about one macro instance beyond the
/// atoms themselves.
#[derive(Clone, Debug, Default)]
pub struct InstanceInfo {
    /// r1cs signal id -> the spec variable bound to it in this instance: what
    /// makes an `input = spec var` equality expressible at all.
    pub signal_to_spec_var: HashMap<usize, String>,
    /// Every spec variable declared for this instance, in a stable order.
    /// These have to be `declare-fun`'d before any atom that mentions them.
    pub spec_vars: Vec<String>,
}

/// The side table that goes with the [`Formula`]: indexed exactly like its
/// atoms.
#[derive(Clone, Debug, Default)]
pub struct AtomTable {
    pub atoms: Vec<AtomInfo>,
    pub instances: BTreeMap<String, InstanceInfo>,
    /// Instances that had loose variables outside every tag (`level0`
    /// non-empty). That means part of the macro body is NOT covered by any
    /// atom, so the atoms no longer add up to the whole specification and any
    /// verdict built on them is against a weaker spec than intended.
    pub instances_with_uncovered_body: Vec<String>,
    /// Synthetic id for each `(instance, variable)` the preprocessor could not
    /// tie to an r1cs signal: llzk's temporaries (`%1`, `%felt_const_2`).
    ///
    /// Without an id they would contribute nothing to the clustering, and since
    /// the chain computing an output runs through temporaries, the atoms doing
    /// the work would look signal-less and land in unrelated clusters. Each gets
    /// an id above every r1cs signal id, so they only ever add edges to the
    /// specification-side graph — which is the point. Per instance: `v_3` of
    /// `main.a` and of `main.b` are different variables.
    pub unresolved_ids: HashMap<(String, String), usize>,
    /// Next synthetic id to hand out.
    next_synthetic_id: usize,
}

impl AtomTable {
    /// Starts the synthetic ids above every r1cs signal id, so they can never
    /// be confused with a real signal.
    fn with_signal_base(base: usize) -> AtomTable {
        AtomTable {
            next_synthetic_id: base,
            ..AtomTable::default()
        }
    }

    /// The synthetic id of an unresolved variable, allocating it on first use.
    /// Stable per `(instance, variable)`, so the same temporary in two atoms
    /// of the same instance is the same "signal" and the clustering sees the
    /// edge between them.
    fn synthetic_id(&mut self, instance: &str, var: &str) -> usize {
        let key = (instance.to_string(), var.to_string());
        if let Some(id) = self.unresolved_ids.get(&key) {
            return *id;
        }
        let id = self.next_synthetic_id;
        self.next_synthetic_id += 1;
        self.unresolved_ids.insert(key, id);
        id
    }

    pub fn atom(&self, index: usize) -> &AtomInfo {
        &self.atoms[index]
    }

    pub fn instance(&self, name: &str) -> &InstanceInfo {
        self.instances
            .get(name)
            .unwrap_or_else(|| panic!("No instance info recorded for '{}'", name))
    }
}

/// Sanitises an instance prefix into something usable inside an SMT-LIB
/// symbol: `"main.sub[0]"` -> `"main_sub_0_"`.
fn sanitise(prefix: &str) -> String {
    prefix
        .chars()
        .map(|c| if c.is_alphanumeric() || c == '_' { c } else { '_' })
        .collect()
}

/// The shared-namespace name for one instance's spec variable. Two instances of
/// the same macro use the SAME local names, so the prefix is what keeps them
/// apart; `spec_` keeps them clear of the circuit's `s_{id}`.
fn spec_var_name(instance: &str, var: &str) -> String {
    format!("spec_{}_{}", sanitise(instance), var)
}

/// Rewrites the macro's own variable names into the shared namespace. Same
/// word-boundary technique as `build_call_macro`, for the same reason: `v_1` must
/// not match inside `v_10`.
fn rewrite_formula(formula: &str, instance: &str, vars: &[String]) -> String {
    use regex::{escape, Regex};

    let mut out = formula.to_string();
    for var in vars {
        let re = Regex::new(&format!(r"\b{}\b", escape(var))).unwrap();
        out = re
            .replace_all(&out, spec_var_name(instance, var).as_str())
            .into_owned();
    }
    out
}

/// Replaces every standalone occurrence of `from` with `to` — standalone meaning
/// the next character does not continue an identifier, so `@Foo` is not replaced
/// inside `@Foo_2`. Hand-written because `\b@Foo\b` never matches: `@` is not a
/// word character.
fn replace_token(text: &str, from: &str, to: &str) -> String {
    let bytes = text.as_bytes();
    let mut out = String::with_capacity(text.len());
    let mut cursor = 0;
    while let Some(pos) = text[cursor..].find(from) {
        let start = cursor + pos;
        let after = start + from.len();
        let standalone = bytes
            .get(after)
            .map(|c| !(c.is_ascii_alphanumeric() || *c == b'_'))
            .unwrap_or(true);
        out.push_str(&text[cursor..start]);
        if standalone {
            out.push_str(to);
        } else {
            out.push_str(from);
        }
        cursor = after;
    }
    out.push_str(&text[cursor..]);
    out
}

/// The name a specification macro is emitted under. llzk names them `@BinSub_0`,
/// but SMT-LIB reserves every symbol starting with `@` or `.` and cvc5 rejects
/// them outright — quoting as `|@BinSub_0|` does not help, it checks the prefix
/// after unquoting. Rewritten consistently at the definition and every call.
pub fn macro_symbol(name: &str) -> String {
    let cleaned: String = name
        .chars()
        .map(|c| if c.is_alphanumeric() || c == '_' { c } else { '_' })
        .collect();
    format!("spec_macro_{}", cleaned)
}

/// Rewrites every macro call in `formula` to the emitted symbol name.
fn rename_macro_calls(formula: &str, macro_names: &[String]) -> String {
    let mut out = formula.to_string();
    for name in macro_names {
        out = replace_token(&out, name, &macro_symbol(name));
    }
    out
}

/// All the r1cs signal ids a resolved variable stands for. A tie contributes ALL
/// of them: the specification is saying they are the same wire, so they belong in
/// one cluster. `Unresolved` gets a synthetic id — see `unresolved_ids`.
fn resolved_signals(table: &mut AtomTable, instance: &str, var: &ResolvedVar) -> Vec<usize> {
    match var {
        ResolvedVar::Signal(ids) => ids.clone(),
        ResolvedVar::Unresolved(name) => vec![table.synthetic_id(instance, name)],
    }
}

/// Builds the [`Formula`] the clustering consumes plus its [`AtomTable`].
///
/// `structure` is the circom component structure: the preprocessor needs it
/// to know which macro and which dotted instance prefix each node gets.
pub fn build_atoms(
    macro_defs: &IndexMap<String, MacroDef>,
    structure: &StructureInfo,
    name_to_signal: &BTreeMap<String, usize>,
    prime: &BigInt,
    circuit_inputs: HashSet<usize>,
    circuit_outputs: HashSet<usize>,
    // One past the largest r1cs signal id: where the synthetic ids for
    // unresolved variables start.
    synthetic_id_base: usize,
    debug: usize,
) -> Result<(Formula, AtomTable), String> {
    let resolved = resolve_full(macro_defs, structure, name_to_signal)?;
    let macro_names: Vec<String> = macro_defs.keys().cloned().collect();

    let mut table = AtomTable::with_signal_base(synthetic_id_base);
    let mut trivial_atoms = 0usize;
    // Instance -> its atoms, in the order the atoms were built. Kept as a
    // Vec of pairs (not a map) because `Formula::from_atoms` lays the atoms
    // out in this order and each instance must end up contiguous.
    let mut by_instance: Vec<(String, Vec<FormulaAtom>)> = Vec::new();
    // Buffered per instance and flattened in the same order, so
    // `formula.atoms[i]` and `table.atoms[i]` are the same atom by CONSTRUCTION.
    // Pushing straight into `table.atoms` would order by encounter while
    // `from_atoms` orders by instance -- identical until one prefix appears in
    // two entries of `resolved`, and then every cluster gets somebody else's
    // SMT-LIB.
    let mut infos_by_instance: Vec<Vec<AtomInfo>> = Vec::new();
    let mut instance_position: HashMap<String, usize> = HashMap::new();

    for entry in resolved.iter() {
        // The "main" macro is only a wrapper whose body is the `@Root` call
        // that binds the root instance's parameters; the root's own macro
        // carries the actual specification, and is resolved with the same
        // prefix. Keeping both would assert the root twice and drag in a
        // macro call for no gain.
        if entry.name == "main" {
            continue;
        }

        register_instance(&mut table, entry);

        if !entry.level0.is_empty() {
            table
                .instances_with_uncovered_body
                .push(entry.instance_prefix.clone());
        }

        // The names to rewrite are the macro's OWN variable names (the keys
        // of `bindings`, i.e. `v_0`), not the renamed ones: `rewrite_formula`
        // searches the formula, and the formula is written in the former.
        let local_vars: Vec<String> = entry.bindings.keys().cloned().collect();

        let position = match instance_position.get(&entry.instance_prefix) {
            Some(p) => *p,
            None => {
                by_instance.push((entry.instance_prefix.clone(), Vec::new()));
                infos_by_instance.push(Vec::new());
                instance_position.insert(entry.instance_prefix.clone(), by_instance.len() - 1);
                by_instance.len() - 1
            }
        };

        for node in entry.tree.iter() {
            // A tag whose whole body is `true` asserts nothing: llzk emits
            // these to document an alias or a constant, and in a real
            // specification they are the majority. Dropping them is sound —
            // `true` is the identity of conjunction — and it avoids handing
            // the clustering atoms with no content to cluster.
            if node.formula.trim() == "true" {
                trivial_atoms += 1;
                continue;
            }

            let resolved_vars = aggregate_resolved(node);
            let mut signals: Vec<usize> = Vec::new();
            for var in resolved_vars.iter() {
                for id in resolved_signals(&mut table, &entry.instance_prefix, var) {
                    if !signals.contains(&id) {
                        signals.push(id);
                    }
                }
            }

            by_instance[position].1.push(FormulaAtom {
                name: node.tag.clone(),
                signals,
            });

            infos_by_instance[position].push(AtomInfo {
                instance: entry.instance_prefix.clone(),
                macro_name: entry.name.clone(),
                tag: node.tag.clone(),
                formula: rename_macro_calls(
                    &rewrite_formula(&node.formula, &entry.instance_prefix, &local_vars),
                    &macro_names,
                ),
            });
        }
    }

    // Flattened in the order `from_atoms` will lay the FormulaAtoms out in.
    for infos in infos_by_instance.into_iter() {
        table.atoms.extend(infos);
    }
    // What the layout is supposed to be, kept before `by_instance` is moved.
    let layout: Vec<(String, usize)> = by_instance
        .iter()
        .map(|(instance, atoms)| (instance.clone(), atoms.len()))
        .collect();

    if debug > 0 {
        println!(
            "LOG: built {} atoms over {} instances",
            table.atoms.len(),
            by_instance.len()
        );
        println!(
            "LOG: dropped {} tag(s) whose body is just `true`, and gave synthetic ids to {} \
             variable(s) with no r1cs signal",
            trivial_atoms,
            table.unresolved_ids.len()
        );
    }
    if !table.instances_with_uncovered_body.is_empty() {
        println!(
            "WARNING: {} instance(s) have specification content outside every :meta-data tag, \
             so the atoms do NOT cover their whole formula: {:?}",
            table.instances_with_uncovered_body.len(),
            table.instances_with_uncovered_body
        );
    }

    let formula = Formula::from_atoms(prime, by_instance, circuit_inputs, circuit_outputs);

    // The verification maps an atom index coming out of the clustering to its
    // SMT-LIB through `table.atoms[i]`, so the two indexings agreeing is not a
    // detail -- a mismatch would assert the wrong formula for a cluster and say
    // nothing about the misplacement. Cheap enough to check outright.
    let mut cursor = 0usize;
    for (instance, count) in layout.into_iter() {
        let range = formula
            .get_atomrange_for_component(&instance)
            .ok_or_else(|| format!("Internal: no atom range recorded for instance '{}'", instance))?;
        if range != (cursor..cursor + count) {
            return Err(format!(
                "Internal: instance '{}' occupies atoms {:?} in the formula but {:?} in the atom \
                 table",
                instance,
                range,
                cursor..cursor + count
            ));
        }
        if let Some(wrong) = range.clone().find(|i| table.atoms[*i].instance != instance) {
            return Err(format!(
                "Internal: atom {} is '{}' in the formula's range for instance '{}' but belongs to \
                 '{}' in the atom table",
                wrong, instance, instance, table.atoms[wrong].instance
            ));
        }
        cursor += count;
    }
    if cursor != table.atoms.len() {
        return Err(format!(
            "Internal: the instances account for {} atoms but the atom table holds {}",
            cursor,
            table.atoms.len()
        ));
    }

    Ok((formula, table))
}

/// Records an instance's spec variables and their binding to r1cs signals.
///
/// Called once per resolved entry; several entries can share an instance
/// prefix, in which case their variables accumulate.
fn register_instance(table: &mut AtomTable, entry: &ResolvedMacroEntry) {
    // Resolved first, then inserted: allocating a synthetic id needs `table`
    // mutably, and so does the instance entry.
    let mut bindings: Vec<(String, Vec<usize>)> = Vec::new();
    for (var, resolved) in entry.bindings.iter() {
        let ids = resolved_signals(table, &entry.instance_prefix, resolved);
        bindings.push((spec_var_name(&entry.instance_prefix, var), ids));
    }

    let info = table
        .instances
        .entry(entry.instance_prefix.clone())
        .or_default();

    for (name, ids) in bindings.into_iter() {
        if !info.spec_vars.contains(&name) {
            info.spec_vars.push(name.clone());
        }
        // A tie binds the spec variable to several signals at once. All of
        // them get the same spec-side name, which is exactly right: the
        // specification is asserting they hold the same value.
        for signal in ids {
            info.signal_to_spec_var.insert(signal, name.clone());
        }
    }
}

/// Whether `formula` calls the macro `name`. Deliberately loose — literal match,
/// checking only that what follows is not part of a longer identifier. A false
/// positive emits one extra `define-fun`; a false negative would leave a call
/// undefined and the query unparseable.
fn references_macro(formula: &str, name: &str) -> bool {
    let bytes = formula.as_bytes();
    let mut from = 0;
    while let Some(pos) = formula[from..].find(name) {
        let start = from + pos;
        let after = start + name.len();
        let boundary = bytes
            .get(after)
            .map(|c| !(c.is_ascii_alphanumeric() || *c == b'_'))
            .unwrap_or(true);
        if boundary {
            return true;
        }
        from = after;
    }
    false
}

/// The macro definitions the atoms need, ordered so every macro comes after the
/// ones it calls.
///
/// Two jobs: keep only what is reachable from the atoms (a large specification
/// would otherwise carry hundreds of unused `define-fun`s into every query), and
/// fix the order, since SMT-LIB wants a definition before its callers and the
/// JSON is in no particular order — `build_macros` preserves the map's.
pub fn required_macro_definitions(
    table: &AtomTable,
    macro_defs: &IndexMap<String, MacroDef>,
) -> IndexMap<String, String> {
    use crate::correctness::processing_correctness_utils::build_call_macro;

    // Reachability: start from the macros the atoms call, close transitively.
    let mut needed: Vec<String> = Vec::new();
    let mut frontier: Vec<String> = Vec::new();
    for atom in table.atoms.iter() {
        for name in macro_defs.keys() {
            // The atom's text has already been through `rename_macro_calls`,
            // so it is the emitted symbol that appears in it, not the original
            // `@Name`.
            if references_macro(&atom.formula, &macro_symbol(name)) && !needed.contains(name) {
                needed.push(name.clone());
                frontier.push(name.clone());
            }
        }
    }
    while let Some(current) = frontier.pop() {
        let Some(def) = macro_defs.get(&current) else { continue };
        for name in macro_defs.keys() {
            if name != &current && references_macro(&def.formula, name) && !needed.contains(name) {
                needed.push(name.clone());
                frontier.push(name.clone());
            }
        }
    }

    // Dependency order: a macro is emitted once every macro it calls is out.
    let mut ordered: Vec<String> = Vec::new();
    let mut remaining = needed.clone();
    while !remaining.is_empty() {
        let ready: Vec<String> = remaining
            .iter()
            .filter(|name| {
                let Some(def) = macro_defs.get(*name) else { return true };
                !remaining
                    .iter()
                    .any(|other| other != *name && references_macro(&def.formula, other))
            })
            .cloned()
            .collect();

        if ready.is_empty() {
            // A cycle among the macros: SMT-LIB would need `define-funs-rec`
            // for that, which is not what `build_call_macro` emits. Emit the
            // rest in the order they came and say so, rather than looping.
            println!(
                "WARNING: the specification's macros call each other cyclically ({:?}); \
                 emitting them unordered, the solver may reject the query",
                remaining
            );
            ordered.extend(remaining.into_iter());
            break;
        }
        for name in ready {
            ordered.push(name.clone());
            remaining.retain(|n| n != &name);
        }
    }

    ordered
        .into_iter()
        .filter_map(|name| {
            macro_defs.get(&name).map(|def| {
                let symbol = macro_symbol(&name);
                let body = rename_macro_calls(&def.formula, &macro_defs.keys().cloned().collect::<Vec<_>>());
                (symbol.clone(), build_call_macro(&symbol, &def.params, body))
            })
        })
        .collect()
}
