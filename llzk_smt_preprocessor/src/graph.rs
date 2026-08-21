// Copyright Costa Group UCM.
// SPDX-License-Identifier: Apache-2.0

//! Walks the circuit's component graph (the same `StructureInfo` that
//! `zk-genver` uses) to figure out, for each node, which llzk macro it
//! corresponds to and what its instance prefix is (the dotted path down to
//! that specific instance, e.g. `"main.sub3"`, the same format
//! [`crate::resolve::resolve_macro_entry`] expects).
//!
//! It's the same walk that
//! `zk-genver::correctness::processing_correctness_utils::process_correspondence_node_macro`
//! does over `MacroDef::components_info` (same `structure: &StructureInfo`,
//! same `nodeid2pos`, same use of the successors' `component_name`) — the
//! only difference is that here, in that same walk, the dotted prefix of
//! each node is also being accumulated, which
//! `process_correspondence_node_macro` doesn't need because in `zk-genver`
//! signal translation always uses the global id (`signal_to_name`), not a
//! name reconstructed by hand.

use std::collections::{BTreeMap, HashMap};

use indexmap::IndexMap;
use utils::read_specification::MacroDef;
use utils::structure::StructureInfo;

use crate::resolve::{resolve_macro_entry, ResolvedMacroEntry};
use crate::{analyze_specification, MacroEntry};

/// `component_name` (in `structure.json`, and therefore in `signals.json`)
/// uses real brackets for a component array (`"Foo[0]"`); llzk, on the
/// other hand, names that same instance in `components_info`/`vars_info`
/// with `#N` (`"Foo#0"`) — same component, two different naming
/// conventions depending on the file. For the instance PREFIX (which ends
/// up being compared against `signals.json`) the bracket form has to be
/// kept as-is; this only converts a key to try it against
/// `components_info`, which is the only place that uses `#N`.
fn hashify_brackets(name: &str) -> String {
    let mut out = String::with_capacity(name.len());
    let mut chars = name.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '[' {
            // "[N]" -> "#N": the '[' becomes '#' and the digits are copied
            // up to the closing ']' (which is discarded, not copied).
            out.push('#');
            for c2 in chars.by_ref() {
                if c2 == ']' {
                    break;
                }
                out.push(c2);
            }
        } else {
            // Any other character (letters, dots, other '#'s...) is copied
            // as-is.
            out.push(c);
        }
    }
    out
}

/// Walks `structure` starting at `node_id` and fills in, for each node
/// visited, the macro it corresponds to (`correspondence`) and its dotted
/// instance prefix (`instance_prefixes`).
///
/// `macro_name`/`prefix` are the macro and prefix of `node_id` itself (for
/// the initial call from the root node: the macro that instantiates the
/// main circuit and `"main"`).
pub fn build_correspondence_and_prefixes(
    structure: &StructureInfo,
    nodeid2pos: &HashMap<usize, usize>,
    macros: &IndexMap<String, MacroDef>,
    node_id: usize,
    macro_name: &str,
    prefix: &str,
    correspondence: &mut HashMap<usize, String>,
    instance_prefixes: &mut HashMap<usize, String>,
) {
    // Register this node before descending into its children (so that, if
    // the walk ends here — a node with no successors —, it's already registered).
    correspondence.insert(node_id, macro_name.to_string());
    instance_prefixes.insert(node_id, prefix.to_string());

    let pos = nodeid2pos.get(&node_id).unwrap();
    let node_studied = &structure.nodes[*pos];
    // `macro_name` is fixed by the caller (for the root node) or computed
    // in the previous recursive call (for the rest) — if it isn't in the
    // specification JSON, the JSON itself is inconsistent.
    let macro_studied = macros.get(macro_name).unwrap_or_else(|| {
        panic!(
            "macro '{}' does not appear in the specification JSON",
            macro_name
        )
    });

    // Walk every subcomponent (child in the graph) of this node.
    for suc in &node_studied.successors {
        let pos_suc = nodeid2pos.get(suc).unwrap();
        let suc_name = &structure.nodes[*pos_suc].component_name;
        // Which macro corresponds to this subcomponent? The PARENT's
        // (macro_studied) components_info translates its local instance
        // name ("isz", "mux", "Foo#0", ...) into the macro that implements
        // it. The name is tried as-is first (the normal case), and if that
        // fails, the "#N" variant (see `hashify_brackets` and its doc).
        let macro_suc = macro_studied
            .components_info
            .get(suc_name)
            .or_else(|| macro_studied.components_info.get(&hashify_brackets(suc_name)))
            .unwrap_or_else(|| {
                panic!(
                    "subcomponent '{}' does not appear in the components_info of macro '{}'",
                    suc_name, macro_name
                )
            });
        // The instance prefix later gets compared against signals.json,
        // which uses `component_name`'s bracket form — not the "#N" one
        // that components_info needed to find the macro. That's why
        // `suc_name` is concatenated here WITHOUT going through
        // `hashify_brackets`.
        let suc_prefix = format!("{}.{}", prefix, suc_name);
        // Recursion: the child becomes the "root" of its own subtree, with
        // its own macro and its own already-accumulated prefix.
        build_correspondence_and_prefixes(
            structure,
            nodeid2pos,
            macros,
            *suc,
            macro_suc,
            &suc_prefix,
            correspondence,
            instance_prefixes,
        );
    }
}

/// The `@Name` call of a wrapper formula: how the macro that instantiates the
/// circuit's root node is identified, from the `"main"` macro of the
/// specification JSON.
///
/// There must be EXACTLY one. `main` carries no specification of its own — its
/// whole body is the call to the macro that does — so:
///
/// - none means there is nothing to check the circuit against (a circuit that
///   imposes no constraint comes out as `main = true`);
/// - two or more means the walk would follow the first and silently never map
///   whatever the rest reach, which reads as a verified run over a
///   specification that was only half consumed.
///
/// Both are the specification's problem, not an impossible state, so both come
/// back as `Err` with the names found.
pub fn find_call_target(formula: &str) -> Result<String, String> {
    let calls = macro_calls(formula);
    match calls.len() {
        1 => Ok(calls.into_iter().next().unwrap()),
        0 => Err("no '@...' call found in the 'main' macro of the specification JSON: there is \
                  no template to check the circuit against"
            .to_string()),
        n => Err(format!(
            "the 'main' macro of the specification JSON makes {} '@...' calls ({}), and it must \
             make exactly one: it is a wrapper around the macro that carries the specification, \
             so only the first would ever be followed",
            n,
            calls.join(", ")
        )),
    }
}

/// Every `@Name` token in a formula, in the order they appear. A macro name
/// carries its `@` only at the front, so one occurrence is one call.
///
/// Occurrences inside a double-quoted string are SKIPPED. Every call llzk emits
/// is wrapped in its own annotation — `(! (@Foo v_0 ...) :meta-data "call @Foo
/// (%arg0) to out")` — so the name appears a second time as documentation, and
/// counting that one made a one-call `main` look like a two-call one.
fn macro_calls(formula: &str) -> Vec<String> {
    let bytes = formula.as_bytes();
    let mut calls = Vec::new();
    let mut in_string = false;
    for idx in 0..bytes.len() {
        match bytes[idx] {
            // SMT-LIB escapes a quote by doubling it, so the two toggles of a
            // `""` cancel and the literal stays closed, as it should.
            b'"' => in_string = !in_string,
            b'@' if !in_string => {
                // `idx` is the offset of an ASCII byte, hence a char boundary.
                if let Some(token) = formula[idx..].split_whitespace().next() {
                    let name = token.trim_matches(|c| c == ')' || c == '(' || c == ' ');
                    if !name.is_empty() {
                        calls.push(name.to_string());
                    }
                }
            }
            _ => {}
        }
    }
    calls
}

/// Resolves, for every node in the graph reachable from `root_node_id`, the
/// macro it corresponds to (looked up among the `macros` already analyzed
/// with [`crate::analyze_specification`]) into r1cs signal ids, using the
/// same [`build_correspondence_and_prefixes`] walk to know which macro and
/// which instance prefix each node gets.
#[allow(clippy::too_many_arguments)]
pub fn resolve_all_macros(
    macros: &[MacroEntry],
    macro_defs: &IndexMap<String, MacroDef>,
    structure: &StructureInfo,
    nodeid2pos: &HashMap<usize, usize>,
    root_node_id: usize,
    root_macro_name: &str,
    root_prefix: &str,
    name_to_signal: &std::collections::BTreeMap<String, usize>,
) -> HashMap<usize, ResolvedMacroEntry> {
    // Step 1: walk the WHOLE graph once to know, for each node, which
    // macro it corresponds to and what its full instance prefix is.
    let mut correspondence = HashMap::new();
    let mut instance_prefixes = HashMap::new();
    build_correspondence_and_prefixes(
        structure,
        nodeid2pos,
        macro_defs,
        root_node_id,
        root_macro_name,
        root_prefix,
        &mut correspondence,
        &mut instance_prefixes,
    );

    // Quick index of MacroEntry (the already-analyzed, unresolved tag
    // tree) by name, so `macros` doesn't need a linear scan for every node
    // in step 2.
    let entries_by_name: HashMap<&str, &MacroEntry> =
        macros.iter().map(|e| (e.name.as_str(), e)).collect();

    // Step 2: for each node (regardless of whether other nodes share its
    // same macro), resolve its MacroEntry with ITS OWN prefix and ITS OWN
    // input signals — state is never shared between nodes even if they
    // share a macro.
    let mut resolved = HashMap::new();
    for (node_id, macro_name) in &correspondence {
        let entry = entries_by_name.get(macro_name.as_str()).unwrap_or_else(|| {
            panic!(
                "macro '{}' (node {}) could not be analyzed from the specification JSON",
                macro_name, node_id
            )
        });
        let macro_def = macro_defs.get(macro_name).unwrap();
        let prefix = &instance_prefixes[node_id];
        let pos = nodeid2pos[node_id];
        let input_signals = &structure.nodes[pos].input_signals;
        resolved.insert(
            *node_id,
            resolve_macro_entry(entry, macro_def, prefix, input_signals, name_to_signal),
        );
    }
    resolved
}

/// Full end-to-end flow: analyzes `macro_defs` (the same macro map from the
/// specification JSON), walks `structure`'s component graph starting at the
/// root node, and returns the list of every macro already resolved against
/// `name_to_signal` — including `"main"`, which directly wraps the root
/// instance and is therefore resolved with the same prefix/input signals as
/// it, even though it isn't a node in the component graph.
///
/// This is exactly what the CLI (`main.rs`) does when passed
/// `--correspondence` and `--structure`; it's exposed here so it can be
/// tested directly against the real files in `results/` without invoking
/// the binary (see `tests/real_circuits.rs`).
pub fn resolve_full(
    macro_defs: &IndexMap<String, MacroDef>,
    structure: &StructureInfo,
    name_to_signal: &BTreeMap<String, usize>,
) -> Result<Vec<ResolvedMacroEntry>, String> {
    let macros = analyze_specification(macro_defs)?;
    let nodeid2pos: HashMap<usize, usize> = structure
        .nodes
        .iter()
        .enumerate()
        .map(|(pos, node)| (node.node_id, pos))
        .collect();

    let main_macro = macro_defs
        .get("main")
        .ok_or_else(|| "the specification JSON has no 'main' macro".to_string())?;
    let root_macro_name = find_call_target(&main_macro.formula)?;

    let root_pos = *nodeid2pos
        .get(&0)
        .ok_or_else(|| "the structure has no node with node_id 0".to_string())?;
    let root_component_name = &structure.nodes[root_pos].component_name;
    let root_prefix = if root_component_name.is_empty() {
        "main".to_string()
    } else {
        root_component_name.clone()
    };

    let resolved_by_node = resolve_all_macros(
        &macros,
        macro_defs,
        structure,
        &nodeid2pos,
        0,
        &root_macro_name,
        &root_prefix,
        name_to_signal,
    );

    let mut resolved: Vec<_> = resolved_by_node.into_iter().collect();
    resolved.sort_by_key(|(node_id, _)| *node_id);
    let mut resolved: Vec<_> = resolved.into_iter().map(|(_, entry)| entry).collect();

    let main_entry = macros
        .iter()
        .find(|e| e.name == "main")
        .ok_or_else(|| "the 'main' macro could not be analyzed from the specification JSON".to_string())?;
    let main_input_signals = &structure.nodes[root_pos].input_signals;
    resolved.push(resolve_macro_entry(
        main_entry,
        main_macro,
        &root_prefix,
        main_input_signals,
        name_to_signal,
    ));

    Ok(resolved)
}

#[cfg(test)]
mod tests {
    use super::*;
    use utils::structure::{NodeInfo, TimingInfo};

    #[test]
    fn one_call_is_the_root_macro() {
        assert_eq!(
            find_call_target("(@IsZero_0 v_0 v_1 v_2)").unwrap(),
            "@IsZero_0"
        );
        // No arguments: the closing paren sticks to the token.
        assert_eq!(find_call_target("(@Foo)").unwrap(), "@Foo");
    }

    #[test]
    fn no_call_is_refused() {
        let err = find_call_target("true").unwrap_err();
        assert!(err.contains("no '@...' call found"), "{}", err);
    }

    #[test]
    fn more_than_one_call_is_refused() {
        // `main` is a wrapper: two calls mean only the first would be followed
        // and the rest of the specification would never be mapped.
        let err = find_call_target("(and (@A v_0) (@B v_1))").unwrap_err();
        assert!(err.contains("makes 2 '@...' calls"), "{}", err);
        assert!(err.contains("@A, @B"), "{}", err);
    }

    #[test]
    fn the_name_inside_a_meta_data_string_is_not_a_second_call() {
        // The shape llzk actually emits for the root call of `main`: one call,
        // annotated with a string that names it again.
        let formula = r#" (and  (! (@GreaterThan_2 v_0 v_1) :meta-data "call @GreaterThan_2 (%arg0) to out") (= v_236 v_2) ) "#;
        assert_eq!(find_call_target(formula).unwrap(), "@GreaterThan_2");
    }

    #[test]
    fn two_real_calls_are_still_refused_when_one_is_annotated() {
        let formula = r#"(and (! (@A v_0) :meta-data "call @A to out") (@B v_1))"#;
        let err = find_call_target(formula).unwrap_err();
        assert!(err.contains("makes 2 '@...' calls"), "{}", err);
        assert!(err.contains("@A, @B"), "{}", err);
    }

    #[test]
    fn hashify_brackets_converts_each_bracket_group() {
        assert_eq!(hashify_brackets("Foo[0]"), "Foo#0");
        assert_eq!(hashify_brackets("Foo[0][1]"), "Foo#0#1");
        assert_eq!(hashify_brackets("isz"), "isz");
    }

    fn node(node_id: usize, component_name: &str, successors: Vec<usize>) -> NodeInfo {
        NodeInfo {
            node_id,
            node_name: component_name.to_string(),
            component_name: component_name.to_string(),
            constraints: Vec::new(),
            input_signals: Vec::new(),
            output_signals: Vec::new(),
            signals: Vec::new(),
            is_custom: false,
            is_deterministic: false,
            predecessors: Vec::new(),
            successors,
        }
    }

    fn empty_macro_def(components_info: HashMap<String, String>) -> MacroDef {
        MacroDef {
            params: Vec::new(),
            vars_info: HashMap::new(),
            components_info,
            formula: String::new(),
        }
    }

    #[test]
    fn finds_child_macro_when_component_name_uses_brackets_but_components_info_uses_hash() {
        // Mirrors results/ternary.json: structure.json's component_name is
        // "Num2Bits_16_325[0]" (real brackets), but components_info's key
        // for that same subcomponent is "Num2Bits_16_325#0" (hash). The
        // lookup must still find it, without ever rewriting the prefix
        // itself (that still needs the bracket form to match signals.json).
        let structure = StructureInfo {
            timing: TimingInfo::new(),
            nodes: vec![
                node(0, "", vec![1]),
                node(1, "Num2Bits_16_325[0]", vec![]),
            ],
            local_equivalency: vec![vec![0], vec![1]],
            structural_equivalency: vec![vec![0], vec![1]],
        };
        let nodeid2pos: HashMap<usize, usize> = [(0, 0), (1, 1)].into_iter().collect();

        let mut components_info = HashMap::new();
        components_info.insert("Num2Bits_16_325#0".to_string(), "@Num2Bits_0".to_string());
        let mut macros = IndexMap::new();
        macros.insert("@Num2Ternary_1".to_string(), empty_macro_def(components_info));
        macros.insert("@Num2Bits_0".to_string(), empty_macro_def(HashMap::new()));

        let mut correspondence = HashMap::new();
        let mut instance_prefixes = HashMap::new();
        build_correspondence_and_prefixes(
            &structure,
            &nodeid2pos,
            &macros,
            0,
            "@Num2Ternary_1",
            "main",
            &mut correspondence,
            &mut instance_prefixes,
        );

        assert_eq!(correspondence[&1], "@Num2Bits_0");
        // The prefix keeps the bracket form (the one signals.json expects),
        // not the "#0" one that was needed to find the macro in
        // components_info.
        assert_eq!(instance_prefixes[&1], "main.Num2Bits_16_325[0]");
    }
}
