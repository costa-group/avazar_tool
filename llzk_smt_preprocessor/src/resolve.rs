// Copyright Costa Group UCM.
// SPDX-License-Identifier: Apache-2.0

//! Resolves the SMT variable names (`v_12`, `s_4`, ...) that [`crate::analyze`]
//! produces to the numeric signal identifiers used throughout the rest of
//! `avazar_tool` (the same `usize` that appears in the r1cs).
//!
//! It's the same problem that
//! `zk-genver::correctness::processing_correctness_utils` solves for the
//! circom-side macros, but in the opposite direction: there, you start from
//! an r1cs signal id and look up the matching SMT variable inside
//! `MacroDef::vars_info`; here, you start from the SMT variable (already
//! extracted from llzk's `.smt2`) and look up which r1cs signal id it
//! corresponds to.
//!
//! `vars_info` associates a "local" name for the macro (e.g. `"out"`, or
//! `"sub.out"` for a subcomponent's port) with the SMT variable name used in
//! the formula. To reconstruct the global signal id you also need that
//! specific macro's instance prefix (e.g. `"main"` or `"main.sub3"`), which
//! the caller must supply (it's the same information
//! `correctness_check`/`modular_reasoning` use while walking the component
//! graph).

use std::collections::{BTreeMap, HashMap, HashSet};

use utils::read_specification::MacroDef;

use crate::{MacroEntry, TagNode};

/// An already-resolved variable: either the r1cs signal id(s) it corresponds
/// to, or the original SMT name if no correspondence was found (e.g.
/// internal temporaries introduced by llzk that don't represent any r1cs
/// signal).
///
/// There can be more than one id because `vars_info` isn't injective: two
/// well-named, distinct ports (e.g. `"mux.c[0]"` and `"cst.out[0]"`) can
/// point to the exact same `v_i` (the wire connecting both), each with its
/// own r1cs id — there's no way to tell which one "is the right one", so
/// all of them are returned.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResolvedVar {
    Signal(Vec<usize>),
    Unresolved(String),
}

impl ResolvedVar {
    pub fn is_signal(&self) -> bool {
        matches!(self, ResolvedVar::Signal(_))
    }
}

/// Same as [`TagNode`] but with the variables already resolved.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResolvedTagNode {
    pub tag: String,
    pub own: Vec<ResolvedVar>,
    pub children: Vec<ResolvedTagNode>,
    /// The literal SMT-LIB text of the term this tag encloses, carried over
    /// unchanged from [`TagNode::formula`]. Still written in the macro's own
    /// variables (`v_12`, ...): resolving turns the variable LIST into signal
    /// ids but does not rewrite the formula, so a consumer that wants to
    /// assert it has to substitute the names itself.
    pub formula: String,
}

/// Same as [`MacroEntry`] but with the variables already resolved for ONE
/// specific instance of that macro. The same macro (`name`) can be
/// instantiated at several places in the circuit (e.g. `@Num2Bits_0` called
/// twice, once per `Num2Bits` component in the circuit) — each instance
/// produces its own `ResolvedMacroEntry`, distinguishable by
/// `instance_prefix` (see [`crate::graph::resolve_all_macros`], which groups
/// every instance of the same macro together before printing them).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResolvedMacroEntry {
    pub name: String,
    pub instance_prefix: String,
    pub level0: Vec<ResolvedVar>,
    pub tree: Vec<ResolvedTagNode>,
    /// Every formal parameter of the macro, resolved. The tags carry their
    /// formula in the macro's own variable names (`v_12`), so anyone wanting
    /// to ASSERT one of those formulas next to the r1cs constraints needs to
    /// substitute those names; this is the map to do it with.
    ///
    /// Keyed by the SMT variable name exactly as it appears in the formula.
    /// A parameter absent from `vars_info` maps to
    /// [`ResolvedVar::Unresolved`], same as anywhere else.
    pub bindings: BTreeMap<String, ResolvedVar>,
}

/// Local key within `vars_info`, plus the array index if the associated
/// value was an array (a vector signal).
type LocalKey = (String, Option<usize>);

/// `vars_info` isn't injective: the same SMT value can appear under several
/// local keys at once. Three distinct kinds of collision:
/// - `"isz.in"`, `"%4"` and `"%12"` can all three be the same `v_9` (one
///   real name and two internal operation labels).
/// - `"%1"` and `"%arg0"[1]` can both be the same `v_1` (an internal
///   operation label AND input argument number 1, at the same time).
/// - `"mux.c[0]"` and `"cst.out[0]"` can both be the same `v_4`: two real
///   and DISTINCT names (the wire connects two ports, each with its own,
///   different r1cs id) — here there's no choosing to do, both must be
///   returned (see [`resolve_var`]).
/// To know which candidates are "the best" (and therefore which ones need
/// to all be returned together) it's prioritized:
/// 1. real name (doesn't start with `%`) — resolvable by name in `signals.json`.
/// 2. `"%argN"` — resolvable by position against `node.input_signals`.
/// 3. any other internal label (`"%N"`, `"%felt_const_N"`, ...) — never
///    resolvable, it's the last resort.
fn is_internal_label(local_name: &str) -> bool {
    local_name.starts_with('%')
}

fn is_arg_label(local_name: &str) -> bool {
    local_name
        .strip_prefix("%arg")
        .is_some_and(|rest| !rest.is_empty() && rest.chars().all(|c| c.is_ascii_digit()))
}

fn resolution_priority(local_name: &str) -> u8 {
    if !is_internal_label(local_name) {
        1
    } else if is_arg_label(local_name) {
        1
    } else {
        0
    }
}

/// Inverts `MacroDef::vars_info`: from SMT variable name to ALL the local
/// keys (and, if applicable, the position within the array) that produce
/// it — there can be more than one (see above).
fn build_reverse_index(vars_info: &HashMap<String, serde_json::Value>) -> HashMap<String, Vec<LocalKey>> {
    let mut reverse: HashMap<String, Vec<LocalKey>> = HashMap::new();
    // A single pass over all of vars_info; each entry contributes one or
    // more (smt_var -> local_key) pairs depending on whether its value is...
    for (local_name, value) in vars_info {
        match value {
            // ...a scalar: "out": "v_13" -> reverse["v_13"] += ("out", None).
            serde_json::Value::String(smt_var) => {
                reverse.entry(smt_var.clone()).or_default().push((local_name.clone(), None));
            }
            // ...an array: "in": ["v_8","v_9"] -> reverse["v_8"] += ("in", Some(0)),
            // reverse["v_9"] += ("in", Some(1)). The index is kept so that
            // "in[0]"/"in[1]" can later be reconstructed when resolving by name.
            serde_json::Value::Array(items) => {
                for (idx, item) in items.iter().enumerate() {
                    if let Some(smt_var) = item.as_str() {
                        reverse
                            .entry(smt_var.to_string())
                            .or_default()
                            .push((local_name.clone(), Some(idx)));
                    }
                }
            }
            // ...a number (a constant folded at compile time, e.g.
            // "%felt_const_1": 1): it's not an SMT variable, so it
            // contributes no correspondence — it's ignored.
            _ => {}
        }
    }
    reverse
}

/// `vars_info`'s `"%argN"` entries have no real name (they aren't
/// `"instance.port"`, so they'll never show up in `signals.json`): they're
/// the macro's input parameters, and are resolved by **position**, just
/// like `get_input_signals_macro` does in `processing_correctness_utils.rs`
/// with `node.input_signals`. Here we precompute, for each `"%argN"` (and
/// each element if it's an array), which flattened position it occupies:
/// `%arg0` takes position 0 (or the first `len` if it's an array), `%arg1`
/// follows right after, etc.
fn build_arg_positions(vars_info: &HashMap<String, serde_json::Value>) -> HashMap<LocalKey, usize> {
    let mut positions = HashMap::new();
    // Position already assigned (counts how many "slots" of
    // node.input_signals have been handed out so far); it accumulates
    // according to whether the "%argN"s seen so far were scalars (1 slot)
    // or arrays (as many slots as elements).
    let mut flattened = 0usize;
    let mut n = 0usize;
    // %arg0, %arg1, %arg2, ... in order — stops at the first N that
    // doesn't exist in vars_info (that's where the macro's arguments end).
    loop {
        let arg_name = format!("%arg{}", n);
        let Some(value) = vars_info.get(&arg_name) else {
            break;
        };
        match value {
            // %argN is an array: it occupies `items.len()` consecutive
            // positions (e.g. %arg0 = ["v_0","v_1"] occupies positions 0
            // and 1, and the next %arg starts at 2, not 1).
            serde_json::Value::Array(items) => {
                for idx in 0..items.len() {
                    positions.insert((arg_name.clone(), Some(idx)), flattened);
                    flattened += 1;
                }
            }
            // Scalar %argN: occupies a single position.
            _ => {
                positions.insert((arg_name.clone(), None), flattened);
                flattened += 1;
            }
        }
        n += 1;
    }
    positions
}

/// Parses a string of concatenated array indices (e.g. `"[0][18]"` ->
/// `[0, 18]`); `None` if it isn't exactly that (something's missing or left over).
fn parse_bracket_indices(mut suffix: &str) -> Option<Vec<usize>> {
    let mut indices = Vec::new();
    // Consume "[N]" repeatedly while there's one at the start of `suffix`.
    while let Some(rest) = suffix.strip_prefix('[') {
        let end = rest.find(']')?; // no closing ']' -> not a valid index, None.
        indices.push(rest[..end].parse().ok()?); // what's inside isn't a number -> None.
        suffix = &rest[end + 1..];
    }
    // If there's leftover text that wasn't consumed (e.g. "[0]rest") or
    // there wasn't any bracket at all, it isn't "just concatenated indices"
    // and gets rejected.
    if suffix.is_empty() && !indices.is_empty() {
        Some(indices)
    } else {
        None
    }
}

/// `vars_info` flattens a signal array into a single JSON array, never
/// saying anywhere how many dimensions it really had (`BinSum`'s
/// `in[nInputs][nBits]`, e.g., shows up as a flat array of
/// `nInputs * nBits` elements). Always assuming a single dimension
/// (`name[idx]`) fails as soon as the real signal is 2D or more
/// (`main.sum.in[0][18]`, not `main.sum.in[18]`).
///
/// Instead of guessing the shape, we search `name_to_signal` for everything
/// hanging off `"{prefix}.{local_name}["` (with however many brackets),
/// sort it numerically by its index tuple, and take the `idx`-th element —
/// that order has to match the order in which `vars_info` flattened the
/// original array, whatever its real shape.
fn resolve_array_element_by_search(
    instance_prefix: &str,
    local_name: &str,
    idx: usize,
    name_to_signal: &BTreeMap<String, usize>,
) -> Option<usize> {
    let prefix = format!("{}.{}", instance_prefix, local_name);
    let bracket_prefix = format!("{}[", prefix);

    // 1. Collect ALL signals in signals.json that hang off this base name,
    //    whatever their real shape ("main.sum.in[0][3]",
    //    "main.sum.in[7]", ...) — no dimensionality is assumed.
    // 2. Keep only the ones that parse as pure indices after the prefix
    //    (filter_map discards the ones that don't).
    let mut matches: Vec<(Vec<usize>, usize)> = name_to_signal
        .iter()
        .filter(|(key, _)| key.starts_with(&bracket_prefix))
        .filter_map(|(key, &signal_id)| {
            parse_bracket_indices(&key[prefix.len()..]).map(|indices| (indices, signal_id))
        })
        .collect();
    // 3. Sort by the index tuple (numeric order: [0,0] < [0,1] < ... <
    //    [0,31] < [1,0] < ...) — this is the same "row-major" order in
    //    which vars_info flattened the original array, whatever its real shape.
    matches.sort_by(|a, b| a.0.cmp(&b.0));

    // 4. Position `idx` in THIS order is the signal that corresponds to
    //    vars_info's flat index `idx`.
    matches.get(idx).map(|(_, signal_id)| *signal_id)
}

/// Inverse of `graph::hashify_brackets`: `vars_info` names a
/// subcomponent-array instance with `#N` (`"sub#0.port"`), but
/// `signals.json` (just like `component_name` in `structure.json`) uses
/// real brackets (`"sub[0].port"`). Used as a fallback when the literal
/// name doesn't show up in `name_to_signal`.
fn bracketify_hashes(name: &str) -> String {
    let mut out = String::with_capacity(name.len());
    let mut chars = name.chars().peekable();
    while let Some(c) = chars.next() {
        // Normal character: copied as-is.
        if c != '#' {
            out.push(c);
            continue;
        }
        // It's a '#': check whether digits follow (a real "#N") or not.
        let mut digits = String::new();
        while let Some(&c2) = chars.peek() {
            if !c2.is_ascii_digit() {
                break;
            }
            digits.push(c2);
            chars.next(); // consume the digit already peeked at.
        }
        if digits.is_empty() {
            // A lone '#' with no digits after it (shouldn't happen in
            // practice, but there's nothing to translate) is left as-is.
            out.push('#');
        } else {
            // "#0" -> "[0]".
            out.push('[');
            out.push_str(&digits);
            out.push(']');
        }
    }
    out
}

/// Tries to resolve `local_name` (already a specific name to try) against
/// `name_to_signal`, with or without an array index.
fn resolve_by_name(
    instance_prefix: &str,
    local_name: &str,
    array_idx: Option<usize>,
    name_to_signal: &BTreeMap<String, usize>,
) -> Option<usize> {
    let Some(idx) = array_idx else {
        return name_to_signal.get(&format!("{}.{}", instance_prefix, local_name)).copied();
    };

    // Fast path: the signal is 1D, the name is literally "name[idx]".
    let flat_name = format!("{}.{}[{}]", instance_prefix, local_name, idx);
    if let Some(&signal_id) = name_to_signal.get(&flat_name) {
        return Some(signal_id);
    }
    // The signal has more than one dimension: it needs to be searched for.
    resolve_array_element_by_search(instance_prefix, local_name, idx, name_to_signal)
}

/// Resolves a single local key (name + optional array index) to a signal
/// id, either by position (`"%argN"`) or by name.
fn resolve_local_key(
    local_key: &LocalKey,
    arg_positions: &HashMap<LocalKey, usize>,
    input_signals: &[usize],
    instance_prefix: &str,
    name_to_signal: &BTreeMap<String, usize>,
) -> Option<usize> {
    // 1. Is it a "%argN"? Then it's resolved by position against
    //    node.input_signals, without touching signals.json at all.
    if let Some(&pos) = arg_positions.get(local_key) {
        if let Some(&signal_id) = input_signals.get(pos) {
            return Some(signal_id);
        }
    }
    let (local_name, array_idx) = local_key;

    // 2. Try the local name as it arrives (the normal case).
    if let Some(id) = resolve_by_name(instance_prefix, local_name, *array_idx, name_to_signal) {
        return Some(id);
    }
    // 3. If it contains "#N" (an array subcomponent, named that way by
    //    llzk), also try the real-bracket form, which is what
    //    signals.json uses (see `bracketify_hashes`).
    if local_name.contains('#') {
        let bracketed = bracketify_hashes(local_name);
        if let Some(id) = resolve_by_name(instance_prefix, &bracketed, *array_idx, name_to_signal) {
            return Some(id);
        }
    }
    None
}

fn resolve_var(
    var_name: &str,
    reverse_index: &HashMap<String, Vec<LocalKey>>,
    arg_positions: &HashMap<LocalKey, usize>,
    input_signals: &[usize],
    instance_prefix: &str,
    name_to_signal: &BTreeMap<String, usize>,
) -> ResolvedVar {
    // No local_name in vars_info produces this SMT var -> nothing to
    // resolve, it's a purely internal llzk temporary.
    let Some(candidates) = reverse_index.get(var_name) else {
        return ResolvedVar::Unresolved(var_name.to_string());
    };

    // Only the candidates at the highest priority level present are
    // considered (see `resolution_priority`); if that level is "just an
    // internal label" (0), none of them is resolvable (neither by name nor
    // by position), so we stop here without further work.
    let max_priority = candidates.iter().map(|(name, _)| resolution_priority(name)).max().unwrap_or(0);
    if max_priority == 0 {
        return ResolvedVar::Unresolved(var_name.to_string());
    }

    // Try to resolve EVERY candidate at the winning level (not just the
    // first): if two real, distinct names point to the same v_i (e.g.
    // "mux.c[0]" and "cst.out[0]", the wire connecting both), they're
    // equally valid and both must show up in the result.
    let mut signals = Vec::new();
    for local_key in candidates {
        if resolution_priority(&local_key.0) != max_priority {
            continue; // lower-priority candidate: doesn't compete with the winner.
        }
        if let Some(signal_id) =
            resolve_local_key(local_key, arg_positions, input_signals, instance_prefix, name_to_signal)
        {
            if !signals.contains(&signal_id) {
                signals.push(signal_id); // avoids duplicating the same id if two candidates resolve to the same thing.
            }
        }
    }

    if signals.is_empty() {
        // All the winning-level candidates had, in theory, the "correct"
        // name, but none of them appears in signals.json (or in
        // node.input_signals) — there's no id to return.
        ResolvedVar::Unresolved(var_name.to_string())
    } else {
        // Stable order (tied candidates are visited in vars_info's
        // HashMap's non-deterministic iteration order): without this, the
        // same v_i could come out as [3, 20] or [20, 3] depending on the run.
        signals.sort_unstable();
        ResolvedVar::Signal(signals)
    }
}

#[allow(clippy::too_many_arguments)]
fn resolve_node(
    node: &TagNode,
    reverse_index: &HashMap<String, Vec<LocalKey>>,
    arg_positions: &HashMap<LocalKey, usize>,
    input_signals: &[usize],
    instance_prefix: &str,
    name_to_signal: &BTreeMap<String, usize>,
) -> ResolvedTagNode {
    ResolvedTagNode {
        tag: node.tag.clone(),
        formula: node.formula.clone(),
        own: node
            .own
            .iter()
            .map(|v| resolve_var(v, reverse_index, arg_positions, input_signals, instance_prefix, name_to_signal))
            .collect(),
        children: node
            .children
            .iter()
            .map(|c| resolve_node(c, reverse_index, arg_positions, input_signals, instance_prefix, name_to_signal))
            .collect(),
    }
}

/// Resolves a [`MacroEntry`] (already extracted from an llzk `.smt2` by
/// [`crate::analyze`]) using the corresponding `MacroDef` in the
/// specification JSON (the same one `processing_correctness_utils`
/// consumes) and the r1cs signal correspondence map (`name_to_signal`, as
/// returned by `utils::read_correspondence::read_signal_correspondence`).
///
/// `instance_prefix` is the dotted path down to the specific instance this
/// macro corresponds to (e.g. `"main"` or `"main.sub3"`); the same macro
/// definition can be instantiated at several places in the circuit, so the
/// caller must fix this prefix (it's the same information
/// `zk-genver::correctness::modular_reasoning` uses while walking the
/// component graph).
///
/// `input_signals` are that same instance's r1cs input ids, in order
/// (`NodeInfo::input_signals`); used to resolve `"%argN"` by position
/// instead of by name (see [`build_arg_positions`]).
pub fn resolve_macro_entry(
    entry: &MacroEntry,
    macro_def: &MacroDef,
    instance_prefix: &str,
    input_signals: &[usize],
    name_to_signal: &BTreeMap<String, usize>,
) -> ResolvedMacroEntry {
    let reverse_index = build_reverse_index(&macro_def.vars_info);
    let arg_positions = build_arg_positions(&macro_def.vars_info);
    let bindings = macro_def
        .params
        .iter()
        .map(|p| {
            (
                p.name.clone(),
                resolve_var(&p.name, &reverse_index, &arg_positions, input_signals, instance_prefix, name_to_signal),
            )
        })
        .collect();
    ResolvedMacroEntry {
        name: entry.name.clone(),
        instance_prefix: instance_prefix.to_string(),
        bindings,
        level0: entry
            .level0
            .iter()
            .map(|v| resolve_var(v, &reverse_index, &arg_positions, input_signals, instance_prefix, name_to_signal))
            .collect(),
        tree: entry
            .tree
            .iter()
            .map(|n| resolve_node(n, &reverse_index, &arg_positions, input_signals, instance_prefix, name_to_signal))
            .collect(),
    }
}

/// A single id is printed as a bare number (the normal case); if there were
/// several equally-good candidates for the same `v_i` (see
/// [`ResolvedVar::Signal`]), they're all printed together as a nested array.
fn resolved_var_json(v: &ResolvedVar) -> String {
    match v {
        ResolvedVar::Signal(ids) if ids.len() == 1 => ids[0].to_string(),
        ResolvedVar::Signal(ids) => {
            let parts: Vec<String> = ids.iter().map(|id| id.to_string()).collect();
            format!("[{}]", parts.join(", "))
        }
        ResolvedVar::Unresolved(name) => crate::json_string(name),
    }
}

/// All of a node's already-resolved variables, recursively aggregating its
/// children (flat view). Analogous to [`crate::aggregate`] for
/// [`ResolvedTagNode`].
pub fn aggregate_resolved(node: &ResolvedTagNode) -> Vec<ResolvedVar> {
    let mut out = Vec::new();
    for v in &node.own {
        if !out.contains(v) {
            out.push(v.clone());
        }
    }
    for c in &node.children {
        for v in aggregate_resolved(c) {
            if !out.contains(&v) {
                out.push(v);
            }
        }
    }
    out
}

fn merge_pair_resolved(into: &mut Vec<(String, Vec<ResolvedVar>)>, tag: String, vars: Vec<ResolvedVar>) {
    match into.iter_mut().find(|(t, _)| *t == tag) {
        Some((_, existing)) => {
            for v in vars {
                if !existing.contains(&v) {
                    existing.push(v);
                }
            }
        }
        None => into.push((tag, vars)),
    }
}

/// [`merge_pair_resolved`] over ids instead of variables: what the `single` mode
/// needs once its values are resolved. Same rule -- a tag seen twice adds only
/// the ids it brings that are not there yet.
fn merge_pair_ids(into: &mut Vec<(String, Vec<usize>)>, tag: String, ids: Vec<usize>) {
    match into.iter_mut().find(|(t, _)| *t == tag) {
        Some((_, existing)) => {
            for id in ids {
                if !existing.contains(&id) {
                    existing.push(id);
                }
            }
        }
        None => into.push((tag, ids)),
    }
}

/// Groups the resolved instances by macro name, preserving the order in
/// which each name first appears. Necessary because the same macro can be
/// instantiated several times (e.g. `@Num2Bits_0` called twice in the same
/// circuit, each call with its own signals): if one JSON entry were printed
/// per instance, keyed by the macro name, two instances of the same macro
/// would produce the SAME key twice — invalid JSON, and any real parser
/// (`json.load`, `JSON.parse`) would just keep the last one, silently
/// dropping the other. That's why each macro name maps to a LIST of instances.
fn group_by_name(macros: &[ResolvedMacroEntry]) -> Vec<(&str, Vec<&ResolvedMacroEntry>)> {
    let mut groups: Vec<(&str, Vec<&ResolvedMacroEntry>)> = Vec::new();
    // Simple linear scan (no HashMap): with few macro names per circuit the
    // cost doesn't matter, and this way the first-appearance order is kept
    // without having to sort anything at the end.
    for m in macros {
        match groups.iter_mut().find(|(name, _)| *name == m.name) {
            Some((_, instances)) => instances.push(m), // there was already a group for this name: add this instance.
            None => groups.push((&m.name, vec![m])),   // first time this name is seen: new group.
        }
    }
    groups
}

/// Like [`resolved_var_json`], but a tied [`ResolvedVar::Signal`] (more than
/// one candidate r1cs id for the same SMT variable) only shows its smallest
/// id instead of the whole group — the group as a whole is printed once per
/// instance by [`equality_groups_json`], under an `"equalityN"` key, so no
/// information is lost, it's just not repeated at every occurrence.
///
/// `ids` is always sorted ascending by [`resolve_var`], so "smallest id" is
/// deterministic and the same across every occurrence of that same tied
/// group — which is what lets a reader go from an id seen inline back to
/// its `"equalityN"` entry.
/// EVERY id a variable is tied to, not just the smallest.
///
/// A variable tied to several r1cs signals -- `main.lt.out` and the parent's
/// `lt.out` are one variable and two ids -- names all of them, so an atom that
/// mentions it depends on all of them. Printing one representative and leaving
/// the rest to the `equalityN` entries loses that for anyone reading the array
/// on its own, and the clustering reads exactly these arrays: fewer ids means
/// fewer edges in the shared-signal graph and a different partition. This is
/// what `zk-genver`'s `build_atoms` does with the same data, and the two have to
/// agree or the same circuit gets clustered two ways.
fn resolved_first_var_json(v: &ResolvedVar) -> String {
    match v {
        ResolvedVar::Signal(ids) if !ids.is_empty() => ids
            .iter()
            .map(|id| id.to_string())
            .collect::<Vec<_>>()
            .join(", "),
        // Unreachable in practice: resolve_var never returns an empty Signal.
        ResolvedVar::Signal(_) => resolved_var_json(v),
        ResolvedVar::Unresolved(_) => resolved_var_json(v),
    }
}

/// `show_unresolved = false` (the normal case) omits from the array the
/// `v_i`s that couldn't be tied to any r1cs signal: in a large macro these
/// are the majority, and mixed in with the already-resolved ids they make
/// it very hard to eyeball that everything is correct.
fn resolved_first_var_array_json(items: &[ResolvedVar], show_unresolved: bool) -> String {
    let parts: Vec<String> = items
        .iter()
        .filter(|v| show_unresolved || v.is_signal())
        .map(resolved_first_var_json)
        .collect();
    format!("[{}]", parts.join(", "))
}

/// Every DISTINCT tied group (two or more r1cs ids sharing the same SMT
/// variable) referenced anywhere in `items`, in first-seen order. See
/// [`resolved_first_var_json`]: only the smallest id of each such group is
/// printed inline, so this is what lets a reader recover the rest.
pub fn equality_groups(items: &[ResolvedVar]) -> Vec<Vec<usize>> {
    let mut seen = HashSet::new();
    let mut groups = Vec::new();
    for var in items {
        if let ResolvedVar::Signal(ids) = var {
            if ids.len() > 1 && seen.insert(ids.clone()) {
                groups.push(ids.clone());
            }
        }
    }
    groups
}

/// Renders `groups` (see [`equality_groups`]) as one `"equalityN": [...]`
/// JSON line per group, indented with `pad`. Callers append `",\n"` after
/// each line themselves, same convention as every other key in this module.
///
/// [`resolved_first_var_json`] only prints a tied group's smallest id
/// inline, relying on that id being unique among this instance's groups so
/// it can be traced back to exactly one `"equalityN"` entry. That's true of
/// every real circuit checked so far (r1cs ids are assigned sequentially,
/// so two unrelated wires landing on the same minimum is astronomically
/// unlikely), but it's not something the code actually enforces anywhere
/// else — so it's checked here, once per instance, right before printing.
fn equality_groups_json(groups: &[Vec<usize>], pad: &str) -> Vec<String> {
    let mut seen_firsts = HashMap::new();
    for ids in groups {
        let first = *ids.first().expect("equality_groups never produces empty groups");
        if let Some(previous) = seen_firsts.insert(first, ids) {
            panic!(
                "two different groups of equality share the same minimum id ({first}): {:?} and {:?} -- can't tell which one the {first} in \"vars\" belongs to",
                previous, ids
            );
        }
    }

    groups
        .iter()
        .enumerate()
        .map(|(idx, ids)| {
            let ids_str: Vec<String> = ids.iter().map(|id| id.to_string()).collect();
            format!("{}\"equality{}\": [{}]", pad, idx + 1, ids_str.join(", "))
        })
        .collect()
}


/// Flat view of already-resolved macros (signal ids instead of SMT names).
/// Analogous to [`crate::to_json_flat`]: for each top-level tag, all the
/// variables it touches (aggregating nested tags). Always includes `level0`.
///
/// Each macro name maps to an ARRAY of instances (one per place in the
/// circuit where that macro is used; see [`group_by_name`]); each instance
/// carries its `"instance"` (the dotted prefix, e.g. `"main.n2ba"`) so they
/// can be told apart.
///
/// `show_unresolved = false` (the CLI default) omits the `v_i`s with no
/// r1cs signal associated; see [`resolved_first_var_array_json`].

/// The r1cs signals a tag reaches: its own, plus -- for every UNRESOLVED
/// variable it mentions -- those of the tag that defined that variable,
/// transitively.
///
/// llzk writes a chain of temporaries: `%8 := add %7 %felt_const_4` and
/// `%11 := sub %8 %10`, where `%8` has no r1cs wire, so the second op never
/// mentions the signal the first one landed on. Two tags that share a wire in
/// the circuit would share nothing here, and anything clustering on these lists
/// would separate what belongs together.
///
/// A variable that already IS a signal is left alone -- reaching `lt_in[0]` ends
/// the walk rather than inviting whatever computed it -- which is what keeps the
/// closure from collapsing into "every tag touches everything".
///
/// `visited` is over TAGS, so llzk's loop variables (`%arg1_w38 := %24_aft38`
/// and back) terminate instead of spinning.
///
/// Duplicated from `zk-genver`'s `real_signals_reachable`: the two have to agree
/// on what a tag's signals are, or the same circuit gets clustered two ways
/// depending on which of them produced the file.
fn signals_reachable(
    start: usize,
    per_tag: &[Vec<ResolvedVar>],
    definer: &HashMap<String, Vec<usize>>,
) -> Vec<usize> {
    let mut real: Vec<usize> = Vec::new();
    let mut visited: HashSet<usize> = HashSet::new();
    let mut pending: Vec<usize> = vec![start];
    while let Some(index) = pending.pop() {
        if !visited.insert(index) {
            continue;
        }
        for var in per_tag[index].iter() {
            match var {
                ResolvedVar::Signal(ids) => {
                    for id in ids.iter().copied() {
                        if !real.contains(&id) {
                            real.push(id);
                        }
                    }
                }
                ResolvedVar::Unresolved(name) => {
                    if let Some(next) = definer.get(name) {
                        pending.extend(next.iter().copied());
                    }
                }
            }
        }
    }
    real.sort_unstable();
    real
}

/// Which macro variable a tag DEFINES: the left of its `:=`, translated through
/// `vars_info` into the name the formulas use. A tuple-valued op records a list
/// and defines all of them at once.
/// Every variable the tag and its NESTED tags define. The `:=` that matter are
/// usually not the top-level tag's: an unrolled loop is one tag whose own text
/// defines nothing while every `%2_aft11 := ...` inside it does.
fn tag_defines_deep(node: &ResolvedTagNode, macro_def: Option<&MacroDef>) -> Vec<String> {
    let mut out = tag_defines(&node.tag, macro_def);
    out.extend(equated_vars(&node.formula));
    for child in node.children.iter() {
        out.extend(tag_defines_deep(child, macro_def));
    }
    out
}

/// Both sides of every BARE equality `(= v_117 v_74)`. llzk ties an output port
/// to the temporary that computed it with a loose `=`, real signal on the LEFT,
/// which is the wrong way round for a closure that walks from a user to a
/// definer. Recording both sides makes the relation symmetric for these and only
/// these: a `:=` keeps its direction.
fn equated_vars(formula: &str) -> Vec<String> {
    let bytes = formula.as_bytes();
    let mut out = Vec::new();
    for i in 0..bytes.len().saturating_sub(2) {
        if bytes[i] == b'(' && bytes[i + 1] == b'=' && bytes[i + 2] == b' ' {
            if let Some(end) = formula[i + 3..].find(')') {
                let parts: Vec<&str> = formula[i + 3..i + 3 + end].split_whitespace().collect();
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
    }
    out
}

fn tag_defines(tag: &str, macro_def: Option<&MacroDef>) -> Vec<String> {
    let Some(def) = macro_def else { return Vec::new() };
    let Some((left, _)) = tag.split_once(":=") else { return Vec::new() };
    match def.vars_info.get(left.trim()) {
        Some(serde_json::Value::String(var)) => vec![var.clone()],
        Some(serde_json::Value::Array(items)) => items
            .iter()
            .filter_map(|item| item.as_str().map(|s| s.to_string()))
            .collect(),
        _ => Vec::new(),
    }
}

/// One instance's tags, already resolved to r1cs signal ids.
///
/// The single place the per-instance view is COMPUTED; both output modes format
/// what this returns. `single` used to do its own resolution, with its own rules,
/// and drifted from `flat` every time one of them was fixed -- it kept only the
/// smallest id of a tie, emitted `main`, and gave temporaries synthetic ids
/// instead of closing over them. Sharing the computation is what keeps a fix in
/// one from having to be made twice.
pub struct ResolvedInstance {
    pub macro_name: String,
    pub instance_prefix: String,
    /// `("equality1", ids)` per tie group, in first-seen order.
    pub equalities: Vec<(String, Vec<usize>)>,
    /// `(tag, ids)`, `level0` first, in the order the tags appear.
    pub tags: Vec<(String, Vec<usize>)>,
}

/// Resolves every instance, skipping the `main` wrapper.
///
/// `main`'s body is the call binding the root instance's parameters, and the
/// root's own macro carries the specification under the same prefix, so keeping
/// both states the root twice. `zk-genver`'s `build_atoms` skips it for the same
/// reason and the two outputs are meant to be comparable.
pub fn resolved_instances(
    macros: &[ResolvedMacroEntry],
    macro_defs: &indexmap::IndexMap<String, MacroDef>,
) -> Vec<ResolvedInstance> {
    let mut out = Vec::new();
    for (name, instances) in group_by_name(macros).into_iter() {
        if name == "main" {
            continue;
        }
        let def = macro_defs.get(name);
        for m in instances.iter() {
            // `level0` has no tag node of its own: loose variables, nothing to
            // walk into.
            let mut nodes: Vec<Option<&ResolvedTagNode>> = vec![None];
            let mut pairs: Vec<(String, Vec<ResolvedVar>)> =
                vec![("level0".to_string(), m.level0.clone())];
            for node in &m.tree {
                let before = pairs.len();
                merge_pair_resolved(&mut pairs, node.tag.clone(), aggregate_resolved(node));
                // `merge_pair_resolved` appends OR merges into an existing tag of
                // the same name; only track a node when it actually appended.
                if pairs.len() > before {
                    nodes.push(Some(node));
                }
            }

            let mut v_acum: Vec<ResolvedVar> = Vec::new();
            for (_, v) in &pairs {
                v_acum.extend_from_slice(v);
            }
            let equalities: Vec<(String, Vec<usize>)> = equality_groups(&v_acum)
                .into_iter()
                .enumerate()
                .map(|(i, ids)| (format!("equality{}", i + 1), ids))
                .collect();

            let per_tag: Vec<Vec<ResolvedVar>> = pairs.iter().map(|(_, v)| v.clone()).collect();
            // EVERY tag that pins a variable down, not just the first: one can
            // compute it with a `:=` while another equates it to a real signal,
            // and keeping only whichever came first drops the other. The two
            // relate the same variable and both have to be followed.
            let mut definer: HashMap<String, Vec<usize>> = HashMap::new();
            for (index, node) in nodes.iter().enumerate() {
                if let Some(node) = node {
                    for var in tag_defines_deep(node, def) {
                        let seen = definer.entry(var).or_default();
                        if !seen.contains(&index) {
                            seen.push(index);
                        }
                    }
                }
            }

            let tags: Vec<(String, Vec<usize>)> = pairs
                .iter()
                .enumerate()
                .map(|(i, (tag, _))| (tag.clone(), signals_reachable(i, &per_tag, &definer)))
                .collect();

            out.push(ResolvedInstance {
                macro_name: name.to_string(),
                instance_prefix: m.instance_prefix.clone(),
                equalities,
                tags,
            });
        }
    }
    out
}

fn ids_json(ids: &[usize]) -> String {
    format!(
        "[{}]",
        ids.iter().map(|id| id.to_string()).collect::<Vec<_>>().join(", ")
    )
}

pub fn to_json_flat_resolved(
    macros: &[ResolvedMacroEntry],
    macro_defs: &indexmap::IndexMap<String, MacroDef>,
    _show_unresolved: bool,
) -> String {
    // Grouped back by macro: one key per macro, one object per instance of it.
    let resolved = resolved_instances(macros, macro_defs);
    let mut by_macro: Vec<(String, Vec<&ResolvedInstance>)> = Vec::new();
    for r in resolved.iter() {
        match by_macro.iter_mut().find(|(name, _)| *name == r.macro_name) {
            Some((_, v)) => v.push(r),
            None => by_macro.push((r.macro_name.clone(), vec![r])),
        }
    }

    let mut out = String::from("{\n");
    for (gi, (name, instances)) in by_macro.iter().enumerate() {
        out.push_str(&format!("  {}: [\n", crate::json_string(name)));
        for (ii, r) in instances.iter().enumerate() {
            out.push_str(&format!(
                "    {{\n      \"instance\": {},\n",
                crate::json_string(&r.instance_prefix)
            ));
            for (tag, ids) in r.equalities.iter() {
                out.push_str(&format!(
                    "      {}: {},\n",
                    crate::json_string(tag),
                    ids_json(ids)
                ));
            }
            for (pi, (tag, ids)) in r.tags.iter().enumerate() {
                out.push_str(&format!(
                    "      {}: {}",
                    crate::json_string(tag),
                    ids_json(ids)
                ));
                if pi + 1 < r.tags.len() {
                    out.push(',');
                }
                out.push('\n');
            }
            out.push_str("    }");
            if ii + 1 < instances.len() {
                out.push(',');
            }
            out.push('\n');
        }
        out.push_str("  ]");
        if gi + 1 < by_macro.len() {
            out.push(',');
        }
        out.push('\n');
    }
    out.push('}');
    out
}

/// Single-dictionary view: EVERY instance's tags in one map, each tag prefixed
/// with the instance it belongs to.
///
/// The per-macro view ([`to_json_flat_resolved`]) keeps one entry per macro and,
/// inside it, one object per instance. That shape is what the structure-driven
/// clustering wants, because it looks the atoms of each component up by name.
/// The PLAIN hybrid clustering wants the opposite: one global formula to pair
/// against the whole r1cs, with no component decomposition at all -- and for
/// that the instances have to be merged into a single map.
///
/// Merging them needs the prefix, or two instances of the same template would
/// collide on every tag they share (`"if (%6 == 1)"` appears once per instance).
/// So the key becomes `main.lt.if (%6 == 1)`.
///
/// Built on top of [`resolved_instances`], the same resolution `flat` uses, and
/// differing from it ONLY in the envelope. It used to resolve on its own -- ties
/// collapsed to their smallest id, `main` emitted, temporaries given synthetic
/// ids instead of being closed over -- and drifted apart every time one of the
/// two was fixed. Now a fix in the shared core reaches both.
///
/// The envelope is the one `parse_formula` reads (`{ name: [ { "instance": ...,
/// tag: [...] } ] }`), with a single outer key and a single instance, so the
/// clustering takes the file as it stands. That also means this file must NOT be
/// passed with `--circuit-structure`: the structure-driven mode looks every
/// component up by name and only the root is there.
pub fn to_json_single_resolved(
    macros: &[ResolvedMacroEntry],
    macro_defs: &indexmap::IndexMap<String, MacroDef>,
) -> String {
    let resolved = resolved_instances(macros, macro_defs);
    let root = resolved
        .first()
        .map(|r| r.instance_prefix.clone())
        .unwrap_or_else(|| "main".to_string());

    let mut entries: Vec<(String, Vec<usize>)> = Vec::new();
    for r in resolved.iter() {
        let prefixed = |tag: &str| format!("{}.{}", r.instance_prefix, tag);
        for (tag, ids) in r.equalities.iter().chain(r.tags.iter()) {
            entries.push((prefixed(tag), ids.clone()));
        }
    }

    let mut out = String::from("{\n");
    out.push_str(&format!("  {}: [\n", crate::json_string("all")));
    out.push_str(&format!(
        "    {{\n      \"instance\": {},\n",
        crate::json_string(&root)
    ));
    for (ei, (tag, ids)) in entries.iter().enumerate() {
        out.push_str(&format!(
            "      {}: {}",
            crate::json_string(tag),
            ids_json(ids)
        ));
        if ei + 1 < entries.len() {
            out.push(',');
        }
        out.push('\n');
    }
    out.push_str("    }\n  ]\n}");
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn macro_def(vars_info: HashMap<String, serde_json::Value>) -> MacroDef {
        MacroDef {
            params: Vec::new(),
            vars_info,
            components_info: HashMap::new(),
            formula: String::new(),
        }
    }

    // ---- the single-dictionary mode --------------------------------------

    fn resolved_entry(name: &str, prefix: &str, tags: &[(&str, &[usize])]) -> ResolvedMacroEntry {
        ResolvedMacroEntry {
            name: name.to_string(),
            instance_prefix: prefix.to_string(),
            level0: Vec::new(),
            tree: tags
                .iter()
                .map(|(tag, ids)| ResolvedTagNode {
                    tag: tag.to_string(),
                    own: ids.iter().map(|id| ResolvedVar::Signal(vec![*id])).collect(),
                    children: Vec::new(),
                    formula: String::new(),
                })
                .collect(),
            bindings: BTreeMap::new(),
        }
    }

    /// No macro definitions: with none, `tag_defines` finds no `:=` to follow and
    /// the closure is a no-op, so a fixture's footprints stay exactly as written.
    fn no_macro_defs() -> indexmap::IndexMap<String, MacroDef> {
        indexmap::IndexMap::new()
    }

    /// The written JSON, parsed back: what the clustering will actually see.
    fn single_json(entries: &[ResolvedMacroEntry]) -> serde_json::Value {
        serde_json::from_str(&to_json_single_resolved(entries, &no_macro_defs()))
            .expect("the single mode has to emit valid JSON")
    }

    #[test]
    fn every_instance_lands_in_one_dictionary_under_the_envelope_parse_formula_reads() {
        let entries = vec![
            resolved_entry("@Main_0", "main", &[("step0", &[1, 2])]),
            resolved_entry("@Lt_0", "main.lt", &[("step0", &[3])]),
        ];
        let v = single_json(&entries);

        // One outer key, one instance object: a single global formula, which is
        // what the plain hybrid clustering pairs against the whole r1cs.
        let obj = v.as_object().unwrap();
        assert_eq!(obj.len(), 1);
        let instances = obj["all"].as_array().unwrap();
        assert_eq!(instances.len(), 1);
        assert_eq!(instances[0]["instance"], "main", "the root prefix names the lot");
    }

    #[test]
    fn the_same_tag_in_two_instances_does_not_collide() {
        // Both instances of the same template carry a tag called "step0". Without
        // the prefix one would overwrite the other and half the specification
        // would vanish from the file.
        let entries = vec![
            resolved_entry("@Lt_0", "main.a", &[("step0", &[1])]),
            resolved_entry("@Lt_0", "main.b", &[("step0", &[2])]),
        ];
        let v = single_json(&entries);
        let inst = v["all"][0].as_object().unwrap();

        assert_eq!(inst["main.a.step0"], json!([1]));
        assert_eq!(inst["main.b.step0"], json!([2]));
        assert!(inst.get("step0").is_none(), "no tag is left unprefixed");
    }

    #[test]
    fn the_value_is_the_same_as_the_per_macro_view() {
        // The only difference between the two views is the key. A tie prints
        // EVERY id it holds inline, and its group still comes out as an
        // `equality` entry -- prefixed too, or the instances would collide there.
        let mut entry = resolved_entry("@Main_0", "main", &[("step0", &[4])]);
        entry.tree[0].own.push(ResolvedVar::Signal(vec![7, 9]));
        let v = single_json(&[entry]);
        let inst = v["all"][0].as_object().unwrap();

        assert_eq!(inst["main.step0"], json!([4, 7, 9]), "the tie shows every id");
        assert_eq!(inst["main.equality1"], json!([7, 9]), "and the group is listed apart");
    }

    #[test]
    fn a_temporary_with_no_definer_contributes_no_id() {
        // No invented id stands in for it any more. A temporary is meant to be
        // replaced by the signals of the tag that DEFINED it (`signals_reachable`);
        // with no macro definition there is no `:=` to follow, nothing is reachable
        // from it, and it adds nothing rather than an id of its own. A footprint is
        // then r1cs wires and nothing else, in every view alike.
        let mut entry = resolved_entry("@Main_0", "main", &[("step0", &[4])]);
        entry.tree[0].own.push(ResolvedVar::Unresolved("v_9".to_string()));
        let v = single_json(std::slice::from_ref(&entry));

        assert_eq!(v["all"][0]["main.step0"], json!([4]));
    }

    #[test]
    fn temporaries_do_not_tie_tags_together_by_themselves() {
        // `v_9` in two tags of one instance used to share an invented id and so
        // connect them. It no longer does: what connects two tags is a real
        // signal, or the closure over the tag that defines the temporary.
        let mut a = resolved_entry("@Lt_0", "main.a", &[("step0", &[1]), ("step1", &[2])]);
        a.tree[0].own.push(ResolvedVar::Unresolved("v_9".to_string()));
        a.tree[1].own.push(ResolvedVar::Unresolved("v_9".to_string()));
        let mut b = resolved_entry("@Lt_0", "main.b", &[("step0", &[3])]);
        b.tree[0].own.push(ResolvedVar::Unresolved("v_9".to_string()));
        let v = single_json(&[a, b]);
        let inst = v["all"][0].as_object().unwrap();

        assert_eq!(inst["main.a.step0"], json!([1]));
        assert_eq!(inst["main.a.step1"], json!([2]));
        assert_eq!(inst["main.b.step0"], json!([3]));
    }

    #[test]
    fn resolves_scalar_signal() {
        let entry = MacroEntry {
            name: "main".to_string(),
            level0: vec!["v_4".to_string(), "v_3".to_string()],
            tree: Vec::new(),
        };
        let mut vars_info = HashMap::new();
        vars_info.insert("out".to_string(), json!("v_4"));
        let def = macro_def(vars_info);

        let mut name_to_signal = BTreeMap::new();
        name_to_signal.insert("main.out".to_string(), 7usize);

        let resolved = resolve_macro_entry(&entry, &def, "main", &[], &name_to_signal);
        assert_eq!(resolved.level0[0], ResolvedVar::Signal(vec![7]));
        assert_eq!(resolved.level0[1], ResolvedVar::Unresolved("v_3".to_string()));
    }

    #[test]
    fn resolves_array_signal() {
        let entry = MacroEntry {
            name: "main".to_string(),
            level0: vec!["v_9".to_string()],
            tree: Vec::new(),
        };
        let mut vars_info = HashMap::new();
        vars_info.insert("in".to_string(), json!(["v_8", "v_9"]));
        let def = macro_def(vars_info);

        let mut name_to_signal = BTreeMap::new();
        name_to_signal.insert("main.in[1]".to_string(), 3usize);

        let resolved = resolve_macro_entry(&entry, &def, "main", &[], &name_to_signal);
        assert_eq!(resolved.level0[0], ResolvedVar::Signal(vec![3]));
    }

    #[test]
    fn resolves_subcomponent_signal() {
        let entry = MacroEntry {
            name: "main".to_string(),
            level0: vec!["v_2".to_string()],
            tree: Vec::new(),
        };
        let mut vars_info = HashMap::new();
        vars_info.insert("sub.out".to_string(), json!("v_2"));
        let def = macro_def(vars_info);

        let mut name_to_signal = BTreeMap::new();
        name_to_signal.insert("main.sub.out".to_string(), 11usize);

        let resolved = resolve_macro_entry(&entry, &def, "main", &[], &name_to_signal);
        assert_eq!(resolved.level0[0], ResolvedVar::Signal(vec![11]));
    }

    #[test]
    fn prefers_named_key_over_internal_label_on_collision() {
        // Mirrors results/isequal.json's @IsEqual_1: vars_info is not
        // injective, "isz.in", "%4" and "%12" are all "v_9". Whichever
        // gets inverted last must not shadow the real name.
        let entry = MacroEntry {
            name: "main".to_string(),
            level0: vec!["v_9".to_string()],
            tree: Vec::new(),
        };
        let mut vars_info = HashMap::new();
        vars_info.insert("isz.in".to_string(), json!("v_9"));
        vars_info.insert("%4".to_string(), json!("v_9"));
        vars_info.insert("%12".to_string(), json!("v_9"));
        let def = macro_def(vars_info);

        let mut name_to_signal = BTreeMap::new();
        name_to_signal.insert("main.isz.in".to_string(), 5usize);

        let resolved = resolve_macro_entry(&entry, &def, "main", &[], &name_to_signal);
        assert_eq!(resolved.level0[0], ResolvedVar::Signal(vec![5]));
    }

    #[test]
    fn prefers_arg_label_over_other_internal_label_on_collision() {
        // Mirrors results/isequal.json's @IsEqual_1: "%1" (a dead-end
        // internal op-label) and "%arg0"[1] (resolvable positionally) are
        // both "v_1". Both are "internal" (start with '%'), so the plain
        // named-vs-internal check from the test above can't tell them
        // apart — this must always prefer "%argN" regardless of HashMap
        // iteration order.
        let entry = MacroEntry {
            name: "@IsEqual_1".to_string(),
            level0: vec!["v_1".to_string(), "v_0".to_string()],
            tree: Vec::new(),
        };
        let mut vars_info = HashMap::new();
        vars_info.insert("%1".to_string(), json!("v_1"));
        vars_info.insert("%3".to_string(), json!("v_0"));
        vars_info.insert("%arg0".to_string(), json!(["v_0", "v_1"]));
        let def = macro_def(vars_info);

        let name_to_signal = BTreeMap::new();
        let input_signals = [2usize, 3usize];

        let resolved = resolve_macro_entry(&entry, &def, "main", &input_signals, &name_to_signal);
        assert_eq!(resolved.level0[0], ResolvedVar::Signal(vec![3]));
        assert_eq!(resolved.level0[1], ResolvedVar::Signal(vec![2]));
    }

    #[test]
    fn resolves_scalar_arg_by_position() {
        // Mirrors @IsZero_0: vars_info["%arg0"] = "v_0" has no real name, so
        // it must resolve positionally against node.input_signals, not
        // against `signals.json`.
        let entry = MacroEntry {
            name: "@IsZero_0".to_string(),
            level0: vec!["v_0".to_string()],
            tree: Vec::new(),
        };
        let mut vars_info = HashMap::new();
        vars_info.insert("%arg0".to_string(), json!("v_0"));
        let def = macro_def(vars_info);

        let name_to_signal = BTreeMap::new();
        let input_signals = [5usize];

        let resolved = resolve_macro_entry(&entry, &def, "main.isz", &input_signals, &name_to_signal);
        assert_eq!(resolved.level0[0], ResolvedVar::Signal(vec![5]));
    }

    #[test]
    fn resolves_array_arg_by_flattened_position() {
        // Mirrors @IsEqual_1: vars_info["%arg0"] = ["v_0", "v_1"] (two
        // scalar inputs packed into one array argument).
        let entry = MacroEntry {
            name: "@IsEqual_1".to_string(),
            level0: vec!["v_1".to_string(), "v_0".to_string()],
            tree: Vec::new(),
        };
        let mut vars_info = HashMap::new();
        vars_info.insert("%arg0".to_string(), json!(["v_0", "v_1"]));
        let def = macro_def(vars_info);

        let name_to_signal = BTreeMap::new();
        let input_signals = [2usize, 3usize];

        let resolved = resolve_macro_entry(&entry, &def, "main", &input_signals, &name_to_signal);
        assert_eq!(resolved.level0[0], ResolvedVar::Signal(vec![3]));
        assert_eq!(resolved.level0[1], ResolvedVar::Signal(vec![2]));
    }

    #[test]
    fn later_arg_accounts_for_earlier_array_width() {
        // %arg0 is a 2-wide array (occupies flattened positions 0 and 1),
        // so %arg1 must land on position 2, not 1.
        let entry = MacroEntry {
            name: "main".to_string(),
            level0: vec!["v_2".to_string()],
            tree: Vec::new(),
        };
        let mut vars_info = HashMap::new();
        vars_info.insert("%arg0".to_string(), json!(["v_0", "v_1"]));
        vars_info.insert("%arg1".to_string(), json!("v_2"));
        let def = macro_def(vars_info);

        let name_to_signal = BTreeMap::new();
        let input_signals = [7usize, 8usize, 9usize];

        let resolved = resolve_macro_entry(&entry, &def, "main", &input_signals, &name_to_signal);
        assert_eq!(resolved.level0[0], ResolvedVar::Signal(vec![9]));
    }

    #[test]
    fn returns_all_tied_named_candidates() {
        // Mirrors results/mux4_1.json's @Main_4: "mux.c[0]" and "cst.out[0]"
        // are both real, distinct port names for the exact same v_4 (the
        // wire connecting a Constants subcomponent's output straight into a
        // Mux's input) — each has its own, different r1cs id, and there's no
        // way to tell which one is "the right one", so both must come back.
        let entry = MacroEntry {
            name: "@Main_4".to_string(),
            level0: vec!["v_4".to_string()],
            tree: Vec::new(),
        };
        let mut vars_info = HashMap::new();
        vars_info.insert("mux.c".to_string(), json!(["v_4"]));
        vars_info.insert("cst.out".to_string(), json!(["v_4"]));
        let def = macro_def(vars_info);

        let mut name_to_signal = BTreeMap::new();
        name_to_signal.insert("main.mux.c[0]".to_string(), 20usize);
        name_to_signal.insert("main.cst.out[0]".to_string(), 3usize);

        let resolved = resolve_macro_entry(&entry, &def, "main", &[], &name_to_signal);
        match &resolved.level0[0] {
            ResolvedVar::Signal(ids) => {
                let mut sorted = ids.clone();
                sorted.sort();
                assert_eq!(sorted, vec![3, 20]);
            }
            other => panic!("expected Signal(_), got {other:?}"),
        }
    }

    #[test]
    fn tied_internal_labels_stay_unresolved_not_multi_valued() {
        // Two dead-end internal labels colliding on the same var must NOT
        // produce a spurious multi-value result — there's nothing to
        // resolve either of them to.
        let entry = MacroEntry {
            name: "main".to_string(),
            level0: vec!["v_9".to_string()],
            tree: Vec::new(),
        };
        let mut vars_info = HashMap::new();
        vars_info.insert("%4".to_string(), json!("v_9"));
        vars_info.insert("%12".to_string(), json!("v_9"));
        let def = macro_def(vars_info);

        let resolved = resolve_macro_entry(&entry, &def, "main", &[], &BTreeMap::new());
        assert_eq!(resolved.level0[0], ResolvedVar::Unresolved("v_9".to_string()));
    }

    #[test]
    fn resolves_2d_array_element_by_searching_signal_names() {
        // Mirrors results/sum_test.json's @sum_test_3: vars_info["sum.in"]
        // is a flat 64-element array, but the real signal is 2D
        // (BinSum's in[2][32]): "main.sum.in[0][18]", never
        // "main.sum.in[18]". Flat index 18 must land on [0][18]; flat
        // index 32 (start of the second row) must land on [1][0].
        let entry = MacroEntry {
            name: "@sum_test_3".to_string(),
            level0: vec!["v_first_row".to_string(), "v_second_row".to_string()],
            tree: Vec::new(),
        };
        let mut sum_in = vec![serde_json::Value::Null; 64];
        sum_in[18] = json!("v_first_row");
        sum_in[32] = json!("v_second_row");
        let mut vars_info = HashMap::new();
        vars_info.insert("sum.in".to_string(), serde_json::Value::Array(sum_in));
        let def = macro_def(vars_info);

        let mut name_to_signal = BTreeMap::new();
        for i in 0..32 {
            name_to_signal.insert(format!("main.sum.in[0][{}]", i), 100 + i);
            name_to_signal.insert(format!("main.sum.in[1][{}]", i), 200 + i);
        }

        let resolved = resolve_macro_entry(&entry, &def, "main", &[], &name_to_signal);
        assert_eq!(resolved.level0[0], ResolvedVar::Signal(vec![118])); // [0][18]
        assert_eq!(resolved.level0[1], ResolvedVar::Signal(vec![200])); // [1][0]
    }

    #[test]
    fn prefers_1d_fast_path_when_it_matches() {
        // If the flat "name[idx]" form is directly present, use it — don't
        // fall back to the search just because the array happens to have
        // several elements.
        let entry = MacroEntry {
            name: "main".to_string(),
            level0: vec!["v_5".to_string()],
            tree: Vec::new(),
        };
        let mut vars_info = HashMap::new();
        vars_info.insert("in".to_string(), json!(["v_4", "v_5"]));
        let def = macro_def(vars_info);

        let mut name_to_signal = BTreeMap::new();
        name_to_signal.insert("main.in[1]".to_string(), 42usize);

        let resolved = resolve_macro_entry(&entry, &def, "main", &[], &name_to_signal);
        assert_eq!(resolved.level0[0], ResolvedVar::Signal(vec![42]));
    }

    #[test]
    fn same_macro_at_two_instances_produces_one_array_not_duplicate_keys() {
        // Mirrors results/sum_test.json: "@Num2Bits_0" is instantiated at
        // both "n2ba" and "n2bb". Printing one JSON object per instance,
        // both keyed by the macro name, would be two identical keys in the
        // same object — invalid, and any real JSON parser silently drops
        // the first. Grouping into one array under the shared name avoids
        // that.
        let entry = MacroEntry {
            name: "@Num2Bits_0".to_string(),
            level0: vec!["v_arg".to_string()],
            tree: Vec::new(),
        };
        let mut vars_info = HashMap::new();
        vars_info.insert("%arg0".to_string(), json!("v_arg"));
        let def = macro_def(vars_info);

        let name_to_signal = BTreeMap::new();
        let first = resolve_macro_entry(&entry, &def, "main.n2ba", &[69], &name_to_signal);
        let second = resolve_macro_entry(&entry, &def, "main.n2bb", &[102], &name_to_signal);

        assert_eq!(first.level0[0], ResolvedVar::Signal(vec![69]));
        assert_eq!(second.level0[0], ResolvedVar::Signal(vec![102]));

        let json = to_json_flat_resolved(&[first, second], &no_macro_defs(), false);
        // Exactly one "@Num2Bits_0" key...
        assert_eq!(json.matches("\"@Num2Bits_0\"").count(), 1);
        // ...mapping to an array holding both instances' data.
        assert!(json.contains("\"instance\": \"main.n2ba\""));
        assert!(json.contains("\"instance\": \"main.n2bb\""));
        assert!(json.contains("[69]"));
        assert!(json.contains("[102]"));
    }

    #[test]
    fn resolves_subcomponent_key_when_vars_info_uses_hash_but_signals_uses_brackets() {
        // Mirrors results/ternary.json's @Num2Ternary_1: vars_info keys the
        // subcomponent-array port as "Num2Bits_16_325#0.in", but
        // signals.json (like component_name in structure.json) names it
        // "main.Num2Bits_16_325[0].in" — real brackets, not '#'.
        let entry = MacroEntry {
            name: "@Num2Ternary_1".to_string(),
            level0: vec!["v_24".to_string()],
            tree: Vec::new(),
        };
        let mut vars_info = HashMap::new();
        vars_info.insert("Num2Bits_16_325#0.in".to_string(), json!("v_24"));
        let def = macro_def(vars_info);

        let mut name_to_signal = BTreeMap::new();
        name_to_signal.insert("main.Num2Bits_16_325[0].in".to_string(), 10usize);

        let resolved = resolve_macro_entry(&entry, &def, "main", &[], &name_to_signal);
        assert_eq!(resolved.level0[0], ResolvedVar::Signal(vec![10]));
    }

    #[test]
    fn bracketify_hashes_converts_each_hash_group() {
        assert_eq!(bracketify_hashes("Num2Bits_16_325#0"), "Num2Bits_16_325[0]");
        assert_eq!(bracketify_hashes("Num2Bits_16_325#0.in"), "Num2Bits_16_325[0].in");
        assert_eq!(bracketify_hashes("isz.in"), "isz.in");
    }

    /// Same mux4_1 collision as `returns_all_tied_named_candidates` (v_4 ==
    /// {mux.c[0]=20, cst.out[0]=3}), but checking the printed JSON itself:
    /// only the smallest id (3) should show up where the tied variable is
    /// used, and the full group should be recorded once, under an
    /// "equalityN" key, so the printed output doesn't silently drop that 20
    /// is tied to it too.
    fn mux4_1_collision_resolved() -> ResolvedMacroEntry {
        let entry = MacroEntry {
            name: "@Main_4".to_string(),
            level0: vec!["v_4".to_string()],
            tree: Vec::new(),
        };
        let mut vars_info = HashMap::new();
        vars_info.insert("mux.c".to_string(), json!(["v_4"]));
        vars_info.insert("cst.out".to_string(), json!(["v_4"]));
        let def = macro_def(vars_info);

        let mut name_to_signal = BTreeMap::new();
        name_to_signal.insert("main.mux.c[0]".to_string(), 20usize);
        name_to_signal.insert("main.cst.out[0]".to_string(), 3usize);

        resolve_macro_entry(&entry, &def, "main", &[], &name_to_signal)
    }

    #[test]
    fn flat_json_lists_every_tied_id_inline_and_the_group_as_an_equality() {
        let text = to_json_flat_resolved(&[mux4_1_collision_resolved()], &no_macro_defs(), true);
        // Every id, not just the smallest: the clustering reads these arrays, and
        // one representative would cost it the edges to the rest of the group.
        assert!(text.contains("\"level0\": [3, 20]"), "{text}");
        assert!(text.contains("\"equality1\": [3, 20]"), "{text}");
    }

    #[test]
    fn equality_groups_ignores_singletons_and_dedupes_repeats() {
        let items = vec![
            ResolvedVar::Signal(vec![1]),          // not tied: excluded.
            ResolvedVar::Signal(vec![3, 20]),       // tied: included once...
            ResolvedVar::Signal(vec![3, 20]),       // ...even though it repeats here.
            ResolvedVar::Unresolved("v_9".to_string()), // excluded.
        ];
        assert_eq!(equality_groups(&items), vec![vec![3, 20]]);
    }

    #[test]
    #[should_panic(expected = "two different groups of equality share the same minimum id (3)")]
    fn equality_groups_json_panics_if_two_groups_share_their_smallest_id() {
        // Contrived on purpose: two DISTINCT tied groups ([3, 20] and [3,
        // 45]) that happen to share their minimum id (3). Real circuits
        // checked so far never hit this (r1cs ids are assigned
        // sequentially), but if it ever did, resolved_first_var_json's "3"
        // in the printed JSON would be impossible to trace back to the
        // right group -- this must fail loudly instead of silently
        // producing ambiguous output.
        equality_groups_json(&[vec![3, 20], vec![3, 45]], "      ");
    }
}
