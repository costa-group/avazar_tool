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
//!
//! Two things happen to a tag's SIGNAL FOOTPRINT that do not happen to its text,
//! both so that the atoms of one circom line stay connected once llzk has split
//! it into several operations:
//!
//! - it is closed over the temporaries it mentions, transitively, so an atom
//!   reading a value with no r1cs wire behind it inherits the wires that value
//!   was computed from (see `real_signals_reachable`);
//! - the instance's tie groups become atoms of their own, asserting `true`,
//!   because two signals bound to one specification variable are the same wire
//!   and no tag says so on its own.

use std::collections::{BTreeMap, HashMap, HashSet};

use circuits_constraints_and_algebra::num_bigint::BigInt;
use circuits_constraints_and_algebra::smt_formula::{Formula, FormulaAtom};
use indexmap::IndexMap;
use llzk_smt_preprocessor::graph::resolve_full;
use llzk_smt_preprocessor::resolve::{
    aggregate_resolved, equality_groups, ResolvedMacroEntry, ResolvedTagNode, ResolvedVar,
};
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

    /// The same table with a different atom list and a different instance map,
    /// keeping the synthetic-id bookkeeping. What the flat mode needs: its atoms
    /// are the resolved file's, in the clustering's order, and its instances are
    /// the one merged instance. See `flat_mode::align_atoms`.
    pub fn recast(
        &self,
        atoms: Vec<AtomInfo>,
        instances: BTreeMap<String, InstanceInfo>,
    ) -> AtomTable {
        AtomTable {
            atoms,
            instances,
            instances_with_uncovered_body: self.instances_with_uncovered_body.clone(),
            unresolved_ids: self.unresolved_ids.clone(),
            next_synthetic_id: self.next_synthetic_id,
        }
    }

    pub fn instance(&self, name: &str) -> &InstanceInfo {
        self.instances
            .get(name)
            .unwrap_or_else(|| panic!("No instance info recorded for '{}'", name))
    }
}

/// Sanitises an instance prefix into something usable inside an SMT-LIB
/// symbol: `"main.sub[0]"` -> `"main_sub_0_"`.
pub(crate) fn sanitise(prefix: &str) -> String {
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

/// Whether a tag's body asserts nothing: a conjunction of `true`s, however
/// deeply nested and however many `:meta-data` annotations hang off it.
///
/// llzk emits such a body for a whole `repeat_exp` loop that turned out to be
/// pure bookkeeping -- `array.read`/`array.write` over indices that constant
/// tracking already resolved to literals, so not one leaf of it reaches the
/// field. `mux1` has two, of 20 and 32 leaves each. The textual test this
/// replaces (`body == "true"`) only caught the single-alias tag llzk writes as
/// literally `true`.
///
/// Keeping them is not harmless. Such a body names no `v_k` either, so its atom
/// has an EMPTY signal footprint and is an isolated vertex of the specification
/// graph -- no edge, hence no merge can absorb it at any `--clustering_size`. It
/// comes out of the clustering as a cluster of its own, holding no r1cs
/// constraint and no output the specification names, and that is the vacuous
/// pair `check_cluster` refuses to report on: it panics and the run dies.
///
/// The test is over the SYMBOLS, not the tree: a body is a conjunction of
/// `true`s exactly when every symbol in it is structural (`and`, `!`, an
/// annotation keyword) or `true` itself. Anything that asserts something --
/// `=`, `ff.mul`, `ff.range`, `ite`, a variable, a numeral -- brings a symbol
/// of its own, and so does anything that could turn a `true` into something
/// else (`not`, `or`), which is why those are not on the list and a body using
/// them is kept. Linear rather than recursive on purpose: these bodies nest one
/// level per conjunct, thousands deep on a real circuit.
fn asserts_nothing(formula: &str) -> bool {
    let bytes = formula.as_bytes();
    let mut i = 0usize;
    while i < bytes.len() {
        match bytes[i] {
            b'(' | b')' => i += 1,
            c if c.is_ascii_whitespace() => i += 1,
            // A `:meta-data` payload is prose -- `"%10_aft62 := %arg1_w62"` --
            // and its words are not symbols of the formula.
            b'"' => {
                i += 1;
                while i < bytes.len() {
                    if bytes[i] == b'"' {
                        // SMT-LIB escapes a quote by doubling it.
                        if bytes.get(i + 1) == Some(&b'"') {
                            i += 2;
                            continue;
                        }
                        i += 1;
                        break;
                    }
                    i += 1;
                }
            }
            _ => {
                let start = i;
                while i < bytes.len()
                    && !bytes[i].is_ascii_whitespace()
                    && !matches!(bytes[i], b'(' | b')' | b'"')
                {
                    i += 1;
                }
                let symbol = &formula[start..i];
                let structural = symbol == "and"
                    || symbol == "!"
                    || symbol == "true"
                    || symbol.starts_with(':');
                if !structural {
                    return false;
                }
            }
        }
    }
    true
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
    // Of those, the ones the literal test would have missed: a whole nested
    // conjunction of `true`s rather than a bare `true`. Reported separately
    // because a run that drops one of these is a run that used to die.
    let mut trivial_conjunctions = 0usize;
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
    // Parallel to the atoms of `by_instance[position]`, flattened the same way:
    // the variables each atom defines, for the transitive closure below.
    let mut defines_by_instance: Vec<Vec<Vec<String>>> = Vec::new();
    // `(tag, macro, signals)` per instance for the tie groups, appended as atoms
    // AFTER the closure so they never get out of step with `defines_by_instance`.
    let mut equalities_by_instance: Vec<Vec<(String, String, Vec<usize>)>> = Vec::new();

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
                defines_by_instance.push(Vec::new());
                equalities_by_instance.push(Vec::new());
                instance_position.insert(entry.instance_prefix.clone(), by_instance.len() - 1);
                by_instance.len() - 1
            }
        };

        for node in entry.tree.iter() {
            // A tag that asserts nothing: llzk emits these to document an
            // alias or a constant, and in a real specification they are the
            // majority. Dropping them is sound — `true` is the identity of
            // conjunction — and it avoids handing the clustering atoms with no
            // content to cluster. See `asserts_nothing` for why the whole
            // conjunction has to be looked at and not just the literal `true`.
            if node.formula.trim() == "true" {
                trivial_atoms += 1;
                continue;
            }
            if asserts_nothing(&node.formula) {
                trivial_atoms += 1;
                trivial_conjunctions += 1;
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
            // Which llzk variable, if any, this tag DEFINES: the left of its
            // `:=`. Recorded now, while the macro is in hand; `close_over_
            // synthetics` needs it to walk back from a temporary to the atom
            // that produced it.
            defines_by_instance[position]
                .push(defined_vars_deep(node, macro_defs.get(&entry.name)));

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

        // Every variable the instance mentions anywhere, tags and loose ones
        // alike, so a tie is caught wherever it shows up. Same rule and the same
        // first-seen order as the preprocessor's own view, which is what keeps
        // the two files comparable.
        let mut mentioned: Vec<ResolvedVar> = entry.level0.clone();
        for node in entry.tree.iter() {
            mentioned.extend(aggregate_resolved(node));
        }
        for ids in equality_groups(&mentioned).into_iter() {
            // An instance can come from several entries; a group already found
            // in one of them is the same group, not a second one.
            if equalities_by_instance[position].iter().any(|(_, _, seen)| *seen == ids) {
                continue;
            }
            let name = format!("equality{}", equalities_by_instance[position].len() + 1);
            equalities_by_instance[position].push((name, entry.name.clone(), ids));
        }
    }

    // ---- transitive closure over the temporaries -------------------------
    // An atom's footprint is one llzk OPERATION, not the circom line it came
    // from: `n2b_in <== lt_in[0] + 4 - lt_in[1]` is split into `%8 := add ...`
    // and `%11 := sub %8 ...`, and `%8` is a temporary with no r1cs wire, so
    // the second op never mentions `lt_in[0]`. Two atoms that share a wire in
    // the circuit end up sharing nothing here, and the clustering separates
    // what belongs together.
    //
    // So: a variable standing for a real signal is left alone -- there is no
    // walking backwards from it -- and a temporary is REPLACED by the signals
    // of the atom that defined it, transitively. Replaced, not added to: the
    // footprint is then r1cs wires and nothing else. The cost is that an atom
    // whose every variable is a temporary with no real ancestor comes out with
    // no signals at all, and joins nothing.
    let synthetic: HashSet<usize> = table.unresolved_ids.values().copied().collect();
    let mut atoms_without_signals = 0usize;
    for (position, (instance, atoms)) in by_instance.iter_mut().enumerate() {
        // Temporary id -> the atom that defines it. A tag whose body is `true`
        // was dropped above, so some temporaries have no definer at all; those
        // contribute nothing, which is the same as not being there.
        // EVERY atom that pins a temporary down, not just the first: one can
        // compute it with a `:=` while another equates it to a real signal, and
        // keeping only whichever came first drops the other. `Num2Bits` loses a
        // bit that way -- the loop defines all three, and the tag equating them
        // to the output port is a different atom.
        let mut definer: HashMap<usize, Vec<usize>> = HashMap::new();
        for (index, vars) in defines_by_instance[position].iter().enumerate() {
            for var in vars.iter() {
                if let Some(id) = table.unresolved_ids.get(&(instance.clone(), var.clone())) {
                    let seen = definer.entry(*id).or_default();
                    if !seen.contains(&index) {
                        seen.push(index);
                    }
                }
            }
        }
        let closed: Vec<Vec<usize>> = (0..atoms.len())
            .map(|index| real_signals_reachable(index, atoms, &definer, &synthetic))
            .collect();
        for (atom, signals) in atoms.iter_mut().zip(closed.into_iter()) {
            if signals.is_empty() && !atom.signals.is_empty() {
                atoms_without_signals += 1;
            }
            atom.signals = signals;
        }
    }
    if atoms_without_signals > 0 && debug > 0 {
        println!(
            "LOG: {} atom(s) mention only temporaries with no r1cs wire behind them, so their \
             footprint closed to nothing and they join no cluster of their own accord",
            atoms_without_signals
        );
    }

    // ---- the tie groups, as atoms ----------------------------------------
    // Two r1cs signals bound to one specification variable are the same wire,
    // and nothing else in the formula says so: a tag lists the variable once,
    // and which signals it stands for is not recoverable from the tag alone.
    // They enter as atoms asserting `true` -- the same idiom `flat_mode` uses
    // for the resolved file's `equalityN` keys -- so they shape the partition
    // without adding anything to a query.
    for (position, groups) in equalities_by_instance.into_iter().enumerate() {
        for (name, macro_name, ids) in groups.into_iter() {
            by_instance[position].1.push(FormulaAtom { name: name.clone(), signals: ids });
            infos_by_instance[position].push(AtomInfo {
                instance: by_instance[position].0.clone(),
                macro_name,
                tag: name,
                formula: "true".to_string(),
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
            "LOG: dropped {} tag(s) whose body asserts nothing ({} of them a whole conjunction \
             of `true`s), and gave synthetic ids to {} variable(s) with no r1cs signal",
            trivial_atoms,
            trivial_conjunctions,
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

/// The variables a tag DEFINES: the left-hand side of its `:=`, resolved through
/// the macro's `vars_info`.
///
/// llzk names a tag after the operation it encloses (`%8 := felt.add %7
/// %felt_const_4`), so the name itself says what the operation produces. The
/// left side is an llzk local (`%8`); `vars_info` maps it to the SMT variable
/// the formula is written in (`v_14`), which is the name a temporary is filed
/// under in [`AtomTable::unresolved_ids`].
///
/// Empty for a tag that defines nothing -- `and0`, `repeat_exp 3`, `if (%3 ==
/// 1)`, a `call ... to ...` -- and for one whose left side is a constant rather
/// than a variable, which `vars_info` records as a number.
/// Both sides of every BARE equality in a tag's text: `(= v_117 v_74)`.
///
/// llzk ties a component's output port to the temporary that computed it with a
/// loose `=`, not with a `:=`, and it writes the real signal on the LEFT and the
/// variable that has no value of its own on the right. The closure walks from a
/// user of a temporary to whatever DEFINES it, so that direction is the wrong
/// way round: nothing defines `v_117`, it is merely equated to `v_74`, and the
/// atom that computes the bits never reaches the signals they land on.
///
/// Recording both sides as definitions of the tag asserting the equality makes
/// the relation symmetric for these, and ONLY these -- a `:=` keeps its
/// direction, so the closure stays a walk back along the computation rather
/// than a free propagation through every variable in sight.
fn equated_vars(formula: &str) -> Vec<String> {
    let mut out = Vec::new();
    let bytes = formula.as_bytes();
    let mut i = 0;
    while i + 2 < bytes.len() {
        if bytes[i] == b'(' && bytes[i + 1] == b'=' && bytes[i + 2] == b' ' {
            let rest = &formula[i + 3..];
            if let Some(end) = rest.find(')') {
                let inside = &rest[..end];
                let parts: Vec<&str> = inside.split_whitespace().collect();
                // Exactly two operands, both plain variables: anything else is a
                // real assertion about a term, not an alias.
                if parts.len() == 2
                    && parts.iter().all(|p| {
                        p.starts_with("v_") && p[2..].chars().all(|c| c.is_ascii_digit())
                    })
                {
                    out.push(parts[0].to_string());
                    out.push(parts[1].to_string());
                }
            }
        }
        i += 1;
    }
    out
}

/// Every variable the tag and its NESTED tags define, in subtree order.
///
/// The `:=` that matter are usually not the top-level tag's: an unrolled loop
/// comes out as one atom tagged `repeat_exp 3` whose own text defines nothing,
/// while every `%2_aft11 := bit.and ...` inside it does. Reading only the top
/// tag left those definitions unrecorded, so the closure below had nowhere to
/// jump to and an atom that computes a component's outputs came out mentioning
/// only its input. Mirrors `aggregate_resolved`, which already walks the whole
/// subtree for the VARIABLES; this is the same walk for the DEFINITIONS.
fn defined_vars_deep(node: &ResolvedTagNode, macro_def: Option<&MacroDef>) -> Vec<String> {
    let mut out = defined_vars(&node.tag, macro_def);
    out.extend(equated_vars(&node.formula));
    for child in node.children.iter() {
        out.extend(defined_vars_deep(child, macro_def));
    }
    out
}

fn defined_vars(tag: &str, macro_def: Option<&MacroDef>) -> Vec<String> {
    let Some(def) = macro_def else { return Vec::new() };
    let Some((left, _)) = tag.split_once(":=") else { return Vec::new() };
    match def.vars_info.get(left.trim()) {
        Some(serde_json::Value::String(var)) => vec![var.clone()],
        // A tuple-valued op (`%12#0`, `%12#1`, ...) is recorded as a list, and
        // the op defines all of them at once.
        Some(serde_json::Value::Array(items)) => items
            .iter()
            .filter_map(|item| item.as_str().map(|s| s.to_string()))
            .collect(),
        _ => Vec::new(),
    }
}

/// The r1cs signals atom `start` reaches: its own, plus -- for every temporary
/// it mentions -- those of the atom that defined that temporary, transitively.
///
/// Temporaries are followed, real signals are not: reaching `lt_in[0]` is the
/// end of the walk, not an invitation to pull in whatever computed `lt_in[0]`.
/// That is what keeps the closure from collapsing into "every atom touches
/// everything".
///
/// `visited` is over ATOMS, so the loop variables llzk emits (`%arg1_w38 :=
/// %24_aft38` and back) terminate instead of spinning.
fn real_signals_reachable(
    start: usize,
    atoms: &[FormulaAtom],
    definer: &HashMap<usize, Vec<usize>>,
    synthetic: &HashSet<usize>,
) -> Vec<usize> {
    let mut real: Vec<usize> = Vec::new();
    let mut visited: HashSet<usize> = HashSet::new();
    let mut pending: Vec<usize> = vec![start];
    while let Some(index) = pending.pop() {
        if !visited.insert(index) {
            continue;
        }
        for signal in atoms[index].signals.iter().copied() {
            if synthetic.contains(&signal) {
                if let Some(next) = definer.get(&signal) {
                    pending.extend(next.iter().copied());
                }
            } else if !real.contains(&signal) {
                real.push(signal);
            }
        }
    }
    real.sort_unstable();
    real
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

#[cfg(test)]
mod tests {
    //! The closure is what makes two atoms of the same circom line share a
    //! wire again, so what it must and must not follow is worth pinning down.

    use super::*;

    fn synthetics(ids: &[usize]) -> HashSet<usize> {
        ids.iter().copied().collect()
    }

    /// `(temporary, atom)` pairs as the map the closure takes. A temporary can
    /// be pinned down by several atoms, so the value is a list; these cases
    /// give one definer each.
    fn definers(pairs: &[(usize, usize)]) -> HashMap<usize, Vec<usize>> {
        let mut map: HashMap<usize, Vec<usize>> = HashMap::new();
        for (temporary, atom) in pairs.iter().copied() {
            map.entry(temporary).or_default().push(atom);
        }
        map
    }

    fn atom(name: &str, signals: &[usize]) -> FormulaAtom {
        FormulaAtom { name: name.to_string(), signals: signals.to_vec() }
    }

    fn macro_def(vars: &[(&str, serde_json::Value)]) -> MacroDef {
        MacroDef {
            params: Vec::new(),
            vars_info: vars.iter().map(|(k, v)| (k.to_string(), v.clone())).collect(),
            components_info: HashMap::new(),
            formula: String::new(),
        }
    }

    #[test]
    fn the_left_of_an_assignment_is_what_the_tag_defines() {
        let def = macro_def(&[
            ("%8", serde_json::json!("v_14")),
            ("%12", serde_json::json!(["v_125", "v_124"])),
            ("%9", serde_json::json!(1)),
        ]);
        assert_eq!(defined_vars("%8 := felt.add %7 %felt_const_4", Some(&def)), vec!["v_14"]);
        // A tuple-valued op defines all of its components at once.
        assert_eq!(defined_vars("%12 := call @F ()", Some(&def)), vec!["v_125", "v_124"]);
        // A constant is not a variable, and these tags define nothing at all.
        assert!(defined_vars("%9 := felt.const 1", Some(&def)).is_empty());
        assert!(defined_vars("and0", Some(&def)).is_empty());
        assert!(defined_vars("call @IsZero_0 (a) to oa", Some(&def)).is_empty());
        assert!(defined_vars("%8 := felt.add %7", None).is_empty());
    }

    #[test]
    fn a_temporary_is_followed_back_to_the_signals_that_defined_it() {
        // The case this exists for: circom's `n2b_in <== lt_in[0] + 4 - lt_in[1]`
        // becomes two llzk ops, and `%8` is a temporary with no r1cs wire, so
        // the second op never mentions lt_in[0] (5) or in[1] (3).
        let atoms = vec![
            atom("%8 := felt.add %7 %felt_const_4", &[3, 5, 17]),
            atom("%11 := felt.sub %8 %10", &[2, 6, 10, 17]),
        ];
        let synthetic = synthetics(&[17]);
        let definer = definers(&[(17, 0)]);

        assert_eq!(real_signals_reachable(0, &atoms, &definer, &synthetic), vec![3, 5]);
        assert_eq!(real_signals_reachable(1, &atoms, &definer, &synthetic), vec![2, 3, 5, 6, 10]);
    }

    #[test]
    fn a_real_signal_is_not_walked_back_through() {
        // Atom 1 reads signal 4, which atom 0 produces. That is NOT a reason to
        // pull atom 0's inputs into atom 1: chase real wires and every atom ends
        // up touching everything.
        let atoms = vec![atom("produces 4", &[7, 8, 4]), atom("reads 4", &[4, 9])];
        let definer: HashMap<usize, Vec<usize>> = HashMap::new();
        assert_eq!(
            real_signals_reachable(1, &atoms, &definer, &HashSet::new()),
            vec![4, 9]
        );
    }

    #[test]
    fn a_temporary_nobody_defines_simply_drops_out() {
        // A tag whose body is `true` is not an atom, so the temporary it would
        // have defined has no definer. Nothing to add, and no panic.
        let atoms = vec![atom("only a temporary", &[20])];
        let synthetic = synthetics(&[20]);
        assert!(real_signals_reachable(0, &atoms, &HashMap::new(), &synthetic).is_empty());
    }

    #[test]
    fn two_temporaries_defining_each_other_terminate() {
        // llzk's loop variables do this: `%arg1_w38 := %24_aft38` on one side
        // and `%24_aft38 := ... %arg1_w38` on the other.
        let atoms = vec![atom("a", &[1, 31, 30]), atom("b", &[2, 30, 31])];
        let synthetic = synthetics(&[30, 31]);
        let definer = definers(&[(30, 0), (31, 1)]);

        assert_eq!(real_signals_reachable(0, &atoms, &definer, &synthetic), vec![1, 2]);
        assert_eq!(real_signals_reachable(1, &atoms, &definer, &synthetic), vec![1, 2]);
    }

    #[test]
    fn the_closure_reaches_through_a_chain_of_temporaries() {
        let atoms = vec![
            atom("first", &[3, 40]),
            atom("second", &[40, 41]),
            atom("third", &[41, 9]),
        ];
        let synthetic = synthetics(&[40, 41]);
        let definer = definers(&[(40, 0), (41, 1)]);

        assert_eq!(real_signals_reachable(2, &atoms, &definer, &synthetic), vec![3, 9]);
    }

    #[test]
    fn a_bare_true_asserts_nothing() {
        assert!(asserts_nothing("true"));
        assert!(asserts_nothing("  true  "));
    }

    #[test]
    fn a_conjunction_of_nothing_but_true_asserts_nothing() {
        // The shape `mux1`'s two `repeat_exp 2` tags have: every leaf `true`,
        // the whole loop recorded in the annotations. This is the case the
        // literal test missed, and the one that used to kill the run.
        assert!(asserts_nothing(
            r#" (and  (and  (! true :meta-data "%10_aft62 := %arg1_w62") (and  (! true :meta-data "array.read %nondet_1[%10_aft62] %11_aft62") (! true :meta-data "%5 := %arg1_w62"))) true) "#
        ));
    }

    #[test]
    fn an_annotation_payload_is_not_read_as_symbols() {
        // `ff.mul` inside the prose of a `:meta-data` string must not make the
        // body look like it computes something.
        assert!(asserts_nothing(
            r#"(! true :meta-data "%11_aft77_t0 := felt.mul %12_aft77 %11_aft77_s0")"#
        ));
    }

    #[test]
    fn a_body_with_one_equation_asserts_something() {
        // `and0` of `mux1`: a single `(= v_178 v_167)` buried under `true`s is
        // still content, and dropping it would weaken the specification.
        assert!(!asserts_nothing(
            r#" (and  (! true :meta-data "%9 := %21_aft95") (= v_178 v_167)) "#
        ));
        assert!(!asserts_nothing("(ff.range v_20 (as ff0 FFp) (as ff1 FFp))"));
    }

    #[test]
    fn anything_that_could_falsify_a_true_is_kept() {
        // `(not true)` is `false`, not nothing: the token test leaves `not`
        // and `or` off the structural list precisely so these are not dropped.
        assert!(!asserts_nothing("(not true)"));
        assert!(!asserts_nothing("(or true true)"));
    }
}
