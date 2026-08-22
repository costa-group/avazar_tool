//! Builds the circuit structure out of the specification and the signal
//! correspondence.
//!
//! The structure is what says which component instances the circuit has, what
//! each one holds, and how they nest. Semantic equivalence needs it three times
//! over: to name every instance (`main.lt.n2b`), to slice the subcircuit each
//! instance is clustered from, and to know a child's ports so it can be
//! abstracted by an implication.
//!
//! All of that is already in the two files the check reads anyway:
//!
//! - the component TREE is `components_info`, which maps each macro's local
//!   subcomponent name to the macro implementing it;
//! - each child's PORTS are the `child.port` keys of the parent's `vars_info`,
//!   split by direction against the child macro's own output names, since only
//!   outputs get an entry of their own;
//! - the SIGNAL IDS behind those ports come from the correspondence, by dotted
//!   name;
//! - the root's own ports are the r1cs header's output/input counts.
//!
//! The one thing neither file records is which r1cs CONSTRAINT belongs to which
//! component, so it is inferred: a constraint belongs to the deepest instance
//! that contains every signal it mentions. A template may only touch its own
//! signals and its direct subcomponents' ports, so that deepest instance is the
//! template the constraint was written in -- the wiring constraints of a parent
//! mention the child's ports and stay in the parent, which is where they belong.
//!
//! Two things fall outside what the specification can describe, and both come
//! back as `Err` rather than as a half-built structure: a `main` that calls no
//! macro at all, which is a circuit with nothing to check against, and a
//! component array that `components_info` records unindexed, which leaves its
//! elements with no instance of their own.

use indexmap::IndexMap;
use std::collections::{BTreeMap, HashMap, HashSet};

use utils::read_specification::MacroDef;
use utils::structure::{NodeInfo, StructureReader, TimingInfo};

/// `S#0` is how `components_info` writes an array element; `S[0]` is how the
/// correspondence writes it. Same instance, two notations.
fn bracketify(name: &str) -> String {
    let mut out = String::with_capacity(name.len());
    let mut chars = name.chars().peekable();
    while let Some(c) = chars.next() {
        if c != '#' {
            out.push(c);
            continue;
        }
        out.push('[');
        while let Some(d) = chars.peek() {
            if d.is_ascii_digit() {
                out.push(*d);
                chars.next();
            } else {
                break;
            }
        }
        out.push(']');
    }
    out
}

/// The `@Name` tokens of a formula, ignoring the ones inside a `:meta-data`
/// string. Same rule as the preprocessor's `macro_calls`.
fn macro_calls(formula: &str) -> Vec<String> {
    let bytes = formula.as_bytes();
    let mut calls = Vec::new();
    let mut in_string = false;
    for idx in 0..bytes.len() {
        match bytes[idx] {
            b'"' => in_string = !in_string,
            b'@' if !in_string => {
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

/// A macro's OWN ports, as named in `vars_info`: the keys with no dot and no
/// `%`. llzk records only the outputs there -- inputs never get an entry -- so
/// this doubles as "which of a child's ports are its outputs".
fn own_output_names(macro_def: &MacroDef) -> HashSet<&str> {
    macro_def
        .vars_info
        .keys()
        .filter(|k| !k.starts_with('%') && !k.contains('.'))
        .map(|k| k.as_str())
        .collect()
}

/// Every signal id behind `<prefix>.<port>`, scalar or array, in index order.
fn signals_for(prefix: &str, port: &str, name_to_signal: &BTreeMap<String, usize>) -> Vec<usize> {
    let flat = bracketify(&format!("{}.{}", prefix, port));
    if let Some(id) = name_to_signal.get(&flat) {
        return vec![*id];
    }
    // An array port: `flat[0]`, `flat[0][1]`, ... Sorted by their indices so the
    // order matches the declaration, which is what the implications assume.
    let mut hits: Vec<(Vec<usize>, usize)> = Vec::new();
    let opening = format!("{}[", flat);
    for (name, id) in name_to_signal.range(opening.clone()..) {
        if !name.starts_with(&opening) {
            break;
        }
        let tail = &name[flat.len()..];
        if !tail.ends_with(']') {
            continue;
        }
        let indices: Vec<usize> = tail
            .split(|c| c == '[' || c == ']')
            .filter(|s| !s.is_empty())
            .filter_map(|s| s.parse().ok())
            .collect();
        // `foo[0].bar` is a subcomponent's signal, not an element of `foo`.
        if tail.contains('.') || indices.is_empty() {
            continue;
        }
        hits.push((indices, *id));
    }
    hits.sort();
    hits.into_iter().map(|(_, id)| id).collect()
}

/// One node under construction, before the ids are known.
struct Derived {
    node_id: usize,
    node_name: String,
    component_name: String,
    prefix: String,
    successors: Vec<usize>,
    input_signals: Vec<usize>,
    output_signals: Vec<usize>,
}

#[allow(clippy::too_many_arguments)]
fn walk(
    macros: &IndexMap<String, MacroDef>,
    macro_name: &str,
    prefix: &str,
    component_name: &str,
    name_to_signal: &BTreeMap<String, usize>,
    nodes: &mut Vec<Derived>,
) -> Result<usize, String> {
    let macro_def = macros
        .get(macro_name)
        .ok_or_else(|| format!("macro '{}' does not appear in the specification JSON", macro_name))?;

    let node_id = nodes.len();
    nodes.push(Derived {
        node_id,
        node_name: macro_name.to_string(),
        component_name: component_name.to_string(),
        prefix: prefix.to_string(),
        successors: Vec::new(),
        input_signals: Vec::new(),
        output_signals: Vec::new(),
    });

    // Sorted, so the ids a run hands out do not depend on HashMap iteration
    // order: the dumps and the .smt2 file names would move between runs.
    let mut children: Vec<(&String, &String)> = macro_def.components_info.iter().collect();
    children.sort();

    for (local, child_macro_name) in children {
        let child_macro = macros.get(child_macro_name).ok_or_else(|| {
            format!(
                "subcomponent '{}' of macro '{}' claims macro '{}', which is not in the \
                 specification JSON",
                local, macro_name, child_macro_name
            )
        })?;
        let child_prefix = bracketify(&format!("{}.{}", prefix, local));
        let child_id = walk(
            macros,
            child_macro_name,
            &child_prefix,
            local,
            name_to_signal,
            nodes,
        )?;
        nodes[node_id].successors.push(child_id);

        // A `local.port` key of THIS macro is one of the child's ports. It is an
        // output when the child's own macro lists that name among its outputs.
        let child_outputs = own_output_names(child_macro);
        let dotted = format!("{}.", local);
        let mut ins: Vec<&str> = Vec::new();
        let mut outs: Vec<&str> = Vec::new();
        for key in macro_def.vars_info.keys() {
            if key.starts_with('%') || !key.starts_with(&dotted) {
                continue;
            }
            let port = &key[dotted.len()..];
            if child_outputs.contains(port) {
                outs.push(port);
            } else {
                ins.push(port);
            }
        }
        ins.sort();
        outs.sort();
        for port in ins {
            let ids = signals_for(&child_prefix, port, name_to_signal);
            nodes[child_id].input_signals.extend(ids);
        }
        for port in outs {
            let ids = signals_for(&child_prefix, port, name_to_signal);
            nodes[child_id].output_signals.extend(ids);
        }
    }

    Ok(node_id)
}

/// Which instance each constraint belongs to: the deepest one holding every
/// signal it mentions.
///
/// This is the one field of the structure that has to be INFERRED rather than
/// read from the specification or the correspondence.
///
/// The rule holds because a template may only touch its own signals and its
/// direct subcomponents' ports, so the deepest instance holding every signal of
/// a constraint is the template it was written in -- a parent's wiring mentions
/// the child's ports and stays in the parent, which is where it belongs.
fn assign_constraints(
    nodes: &[Derived],
    name_to_signal: &BTreeMap<String, usize>,
    constraint_signals: &[Vec<usize>],
) -> Vec<Vec<usize>> {
    let signal_to_name: HashMap<usize, &str> = name_to_signal
        .iter()
        .map(|(name, id)| (*id, name.as_str()))
        .collect();
    let prefix_to_node: HashMap<&str, usize> =
        nodes.iter().map(|n| (n.prefix.as_str(), n.node_id)).collect();

    // The instance a signal lives in: the longest prefix of its dotted name that
    // is an instance. `main.lt.in[0]` -> `main.lt`.
    fn instance_of<'n>(name: &'n str, known: &HashMap<&str, usize>) -> Option<&'n str> {
        let mut cut = name.len();
        loop {
            let candidate = &name[..cut];
            if known.contains_key(candidate) {
                return Some(candidate);
            }
            match candidate.rfind('.') {
                Some(pos) => cut = pos,
                None => return None,
            }
        }
    }

    let mut per_node: Vec<Vec<usize>> = vec![Vec::new(); nodes.len()];
    for (idx, signals) in constraint_signals.iter().enumerate() {
        // Signal 0 is the r1cs constant and has no name; a constraint made only
        // of constants belongs to the root.
        let mut common: Option<&str> = None;
        for signal in signals {
            let name = match signal_to_name.get(signal) {
                Some(n) => *n,
                None => continue,
            };
            let instance = match instance_of(name, &prefix_to_node) {
                Some(i) => i,
                None => continue,
            };
            common = Some(match common {
                None => instance,
                Some(current) => {
                    // The longest common instance prefix of the two.
                    let mut best = current;
                    while !instance.starts_with(best) {
                        best = match best.rfind('.') {
                            Some(pos) => &best[..pos],
                            None => break,
                        };
                    }
                    if instance.len() < best.len() && best.starts_with(instance) {
                        instance
                    } else {
                        best
                    }
                }
            });
        }
        let node = common
            .and_then(|p| prefix_to_node.get(p).copied())
            .unwrap_or(0);
        per_node[node].push(idx);
    }
    per_node
}

/// The root's own ports, as `(inputs, outputs)`.
///
/// Every other node gets its ports from its parent, but nothing sits above
/// `main`, so the two files have to agree on them:
///
/// - the r1cs header numbers them, outputs `1..=n_outputs` and inputs the
///   `n_inputs` after them;
/// - the called macro's `vars_info` names the outputs, which the correspondence
///   turns into ids under the `main` prefix. Only outputs get a plain key of
///   their own, so the inputs are the r1cs's to give either way.
///
/// The two are CHECKED against each other rather than one being preferred. They
/// describe the same circuit, so a disagreement means the specification and the
/// r1cs were not built from the same source, and every signal-to-variable
/// equality the queries go on to build would be pairing the wrong things.
/// Returns `Err` in that case instead of picking a side.
///
/// When the correspondence resolves none of the names -- an older
/// correspondence, a specification with no ports of its own -- there is nothing
/// to check against and the r1cs's own numbering stands.
fn root_ports(
    root_macro: &str,
    macros: &IndexMap<String, MacroDef>,
    name_to_signal: &BTreeMap<String, usize>,
    n_outputs: usize,
    n_inputs: usize,
) -> Result<(Vec<usize>, Vec<usize>), String> {
    let from_r1cs: (Vec<usize>, Vec<usize>) = (
        (n_outputs + 1..=n_outputs + n_inputs).collect(),
        (1..=n_outputs).collect(),
    );

    let macro_def = match macros.get(root_macro) {
        Some(m) => m,
        None => return Ok(from_r1cs),
    };

    let mut port_names: Vec<&str> = macro_def
        .vars_info
        .keys()
        .filter(|k| !k.starts_with('%') && !k.contains('.'))
        .map(|s| s.as_str())
        .collect();
    port_names.sort();
    let mut from_spec: Vec<usize> = port_names
        .iter()
        .flat_map(|port| signals_for("main", port, name_to_signal))
        .collect();
    from_spec.sort_unstable();
    from_spec.dedup();

    if from_spec.is_empty() {
        return Ok(from_r1cs);
    }

    let (r1cs_inputs, r1cs_outputs) = from_r1cs;
    if from_spec != r1cs_outputs {
        return Err(format!(
            "the r1cs and the specification disagree on the circuit's outputs: the r1cs header              declares {} of them ({:?}), while '{}' names {} ({:?}, from the port(s) {:?}). Both              files have to describe the same circuit.",
            r1cs_outputs.len(),
            preview(&r1cs_outputs),
            root_macro,
            from_spec.len(),
            preview(&from_spec),
            port_names
        ));
    }
    Ok((r1cs_inputs, r1cs_outputs))
}

/// The first few ids of a list, so a mismatch message stays readable when the
/// circuit has hundreds of outputs.
fn preview(ids: &[usize]) -> String {
    const SHOWN: usize = 8;
    if ids.len() <= SHOWN {
        return format!("{:?}", ids);
    }
    format!("{:?} and {} more", &ids[..SHOWN], ids.len() - SHOWN)
}

/// The structure of the circuit the specification describes.
///
/// `constraint_signals[i]` lists the signals r1cs constraint `i` mentions;
/// `n_outputs`/`n_inputs` are the r1cs header's counts, which fix the root's
/// own ports (outputs are `1..=n_outputs`, inputs the `n_inputs` after them).
pub fn derive_structure(
    macros: &IndexMap<String, MacroDef>,
    name_to_signal: &BTreeMap<String, usize>,
    n_outputs: usize,
    n_inputs: usize,
    constraint_signals: &[Vec<usize>],
) -> Result<StructureReader, String> {
    let main = macros
        .get("main")
        .ok_or_else(|| "the specification JSON has no 'main' macro".to_string())?;
    let calls = macro_calls(&main.formula);
    let root_macro = match calls.len() {
        1 => calls[0].clone(),
        0 => {
            return Err("no '@...' call found in the 'main' macro of the specification JSON: \
                        there is no template to check the circuit against"
                .to_string())
        }
        n => {
            return Err(format!(
                "the 'main' macro of the specification JSON makes {} '@...' calls ({}), and it \
                 must make exactly one",
                n,
                calls.join(", ")
            ))
        }
    };

    let mut derived: Vec<Derived> = Vec::new();
    walk(macros, &root_macro, "main", "", name_to_signal, &mut derived)?;

    let (root_inputs, root_outputs) =
        root_ports(&root_macro, macros, name_to_signal, n_outputs, n_inputs)?;
    derived[0].input_signals = root_inputs;
    derived[0].output_signals = root_outputs;

    let constraints = assign_constraints(&derived, name_to_signal, constraint_signals);

    let mut predecessors: HashMap<usize, Vec<usize>> = HashMap::new();
    for node in derived.iter() {
        for child in node.successors.iter() {
            predecessors.entry(*child).or_default().push(node.node_id);
        }
    }

    let nodes = derived
        .into_iter()
        .zip(constraints)
        .map(|(node, constraints)| {
            let mut signals: Vec<usize> = node
                .input_signals
                .iter()
                .chain(node.output_signals.iter())
                .copied()
                .collect();
            for idx in constraints.iter() {
                signals.extend(constraint_signals[*idx].iter().copied());
            }
            signals.sort_unstable();
            signals.dedup();
            NodeInfo {
                node_id: node.node_id,
                node_name: node.node_name,
                component_name: node.component_name,
                constraints,
                input_signals: node.input_signals,
                output_signals: node.output_signals,
                signals,
                is_custom: false,
                is_deterministic: false,
                predecessors: predecessors.remove(&node.node_id).unwrap_or_default(),
                successors: node.successors,
            }
        })
        .collect();

    Ok(StructureReader {
        timing: TimingInfo::default(),
        nodes,
        equivalency_local: None,
        equivalency_structural: None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A macro with the given subcomponents and `vars_info` keys. The values do
    /// not matter here: the ports are found by KEY, and turned into signal ids
    /// through the correspondence, not through these.
    fn macro_def(children: &[(&str, &str)], vars: &[&str]) -> MacroDef {
        MacroDef {
            params: Vec::new(),
            vars_info: vars
                .iter()
                .map(|k| (k.to_string(), serde_json::Value::String("v".into())))
                .collect(),
            components_info: children
                .iter()
                .map(|(local, m)| (local.to_string(), m.to_string()))
                .collect(),
            formula: String::new(),
        }
    }

    fn names(pairs: &[(&str, usize)]) -> BTreeMap<String, usize> {
        pairs.iter().map(|(n, i)| (n.to_string(), *i)).collect()
    }

    fn run(macros: &IndexMap<String, MacroDef>, root: &str, n2s: &BTreeMap<String, usize>) -> Vec<Derived> {
        let mut nodes = Vec::new();
        walk(macros, root, "main", "", n2s, &mut nodes).expect("walk failed");
        nodes
    }

    /// THE case this module has to get right: one macro instantiated twice, each
    /// instance carrying its own child. The two must come out as separate nodes
    /// with separate prefixes and separate signals -- a node per CALL, not per
    /// macro.
    #[test]
    fn a_macro_used_twice_becomes_two_independent_subtrees() {
        let mut macros = IndexMap::new();
        macros.insert("@Root".to_string(), macro_def(&[("a", "@Mid"), ("b", "@Mid")], &["a.in", "a.out", "b.in", "b.out"]));
        macros.insert("@Mid".to_string(), macro_def(&[("leaf", "@Leaf")], &["out", "leaf.in", "leaf.out"]));
        macros.insert("@Leaf".to_string(), macro_def(&[], &["out"]));

        let n2s = names(&[
            ("main.a.in", 10), ("main.a.out", 11),
            ("main.a.leaf.in", 12), ("main.a.leaf.out", 13),
            ("main.b.in", 20), ("main.b.out", 21),
            ("main.b.leaf.in", 22), ("main.b.leaf.out", 23),
        ]);
        let nodes = run(&macros, "@Root", &n2s);

        let prefixes: Vec<&str> = nodes.iter().map(|n| n.prefix.as_str()).collect();
        assert_eq!(
            prefixes,
            vec!["main", "main.a", "main.a.leaf", "main.b", "main.b.leaf"],
            "one node per call, depth first"
        );
        // The two `@Mid` instances share a macro but nothing else.
        let a = nodes.iter().find(|n| n.prefix == "main.a").unwrap();
        let b = nodes.iter().find(|n| n.prefix == "main.b").unwrap();
        assert_eq!((a.input_signals.as_slice(), a.output_signals.as_slice()), (&[10][..], &[11][..]));
        assert_eq!((b.input_signals.as_slice(), b.output_signals.as_slice()), (&[20][..], &[21][..]));
        // ...and so do their children, which is what a per-macro walk would break.
        let al = nodes.iter().find(|n| n.prefix == "main.a.leaf").unwrap();
        let bl = nodes.iter().find(|n| n.prefix == "main.b.leaf").unwrap();
        assert_eq!(al.output_signals, vec![13]);
        assert_eq!(bl.output_signals, vec![23]);
        assert_eq!(nodes[0].successors, vec![1, 3], "the root's two children");
    }

    /// A port is an output because the CHILD's macro lists it, not because it is
    /// spelled "out": circomlib has components whose outputs are `xout`/`yout`.
    #[test]
    fn direction_comes_from_the_child_macro_not_from_the_port_name() {
        let mut macros = IndexMap::new();
        macros.insert("@Root".to_string(), macro_def(&[("add", "@Adder")], &["add.x1", "add.y1", "add.xout", "add.yout"]));
        macros.insert("@Adder".to_string(), macro_def(&[], &["xout", "yout"]));

        let n2s = names(&[
            ("main.add.x1", 5), ("main.add.y1", 6),
            ("main.add.xout", 7), ("main.add.yout", 8),
        ]);
        let nodes = run(&macros, "@Root", &n2s);
        let add = &nodes[1];
        assert_eq!(add.input_signals, vec![5, 6], "x1/y1 are inputs");
        assert_eq!(add.output_signals, vec![7, 8], "xout/yout are outputs");
    }

    /// Array elements: `components_info` writes `S#0`, the correspondence writes
    /// `S[0]`, and an array port expands into one signal per index, in order.
    #[test]
    fn array_components_and_array_ports() {
        let mut macros = IndexMap::new();
        macros.insert("@Root".to_string(), macro_def(&[("S#0", "@Cell"), ("S#1", "@Cell")], &["S#0.in", "S#0.out", "S#1.in", "S#1.out"]));
        macros.insert("@Cell".to_string(), macro_def(&[], &["out"]));

        let n2s = names(&[
            ("main.S[0].in[0]", 1), ("main.S[0].in[1]", 2), ("main.S[0].out", 3),
            ("main.S[1].in[0]", 4), ("main.S[1].in[1]", 5), ("main.S[1].out", 6),
        ]);
        let nodes = run(&macros, "@Root", &n2s);
        assert_eq!(nodes[1].prefix, "main.S[0]");
        assert_eq!(nodes[1].input_signals, vec![1, 2], "expanded in index order");
        assert_eq!(nodes[1].output_signals, vec![3]);
        assert_eq!(nodes[2].prefix, "main.S[1]");
        assert_eq!(nodes[2].input_signals, vec![4, 5]);
    }

    /// `foo[0].bar` belongs to a subcomponent, not to the array port `foo`.
    #[test]
    fn a_childs_own_signals_are_not_elements_of_the_parents_port() {
        let mut macros = IndexMap::new();
        macros.insert("@Root".to_string(), macro_def(&[("c", "@Child")], &["c.out"]));
        macros.insert("@Child".to_string(), macro_def(&[], &["out"]));

        let n2s = names(&[("main.c.out", 1), ("main.c.out[0].inner", 2)]);
        let nodes = run(&macros, "@Root", &n2s);
        assert_eq!(nodes[1].output_signals, vec![1], "the nested name is not an element");
    }

    /// Ids must not depend on how the components map happens to iterate: they end
    /// up in the dump and in the .smt2 file names.
    #[test]
    fn ids_do_not_depend_on_the_insertion_order_of_the_components() {
        let n2s = names(&[("main.a.out", 1), ("main.b.out", 2), ("main.c.out", 3)]);
        let build = |order: &[&str]| {
            let mut macros = IndexMap::new();
            let children: Vec<(&str, &str)> = order.iter().map(|l| (*l, "@Leaf")).collect();
            let vars: Vec<String> = order.iter().map(|l| format!("{}.out", l)).collect();
            let vars_ref: Vec<&str> = vars.iter().map(|s| s.as_str()).collect();
            macros.insert("@Root".to_string(), macro_def(&children, &vars_ref));
            macros.insert("@Leaf".to_string(), macro_def(&[], &["out"]));
            run(&macros, "@Root", &n2s)
                .into_iter()
                .map(|n| (n.node_id, n.prefix))
                .collect::<Vec<_>>()
        };
        assert_eq!(build(&["a", "b", "c"]), build(&["c", "a", "b"]));
    }

    #[test]
    fn a_child_claiming_a_macro_that_is_not_there_is_an_error() {
        let mut macros = IndexMap::new();
        macros.insert("@Root".to_string(), macro_def(&[("c", "@Missing")], &["c.out"]));
        let mut nodes = Vec::new();
        let err = walk(&macros, "@Root", "main", "", &names(&[]), &mut nodes).unwrap_err();
        assert!(err.contains("@Missing"), "{}", err);
    }

    /// The shape of circomlib's `greaterthan`, end to end.
    #[test]
    fn greaterthan_comes_out_as_its_three_instances() {
        let mut macros = IndexMap::new();
        macros.insert("@GreaterThan_2".to_string(), macro_def(&[("lt", "@LessThan_1")], &["out", "lt.out", "lt.in"]));
        macros.insert("@LessThan_1".to_string(), macro_def(&[("n2b", "@Num2Bits_0")], &["out", "n2b.out", "n2b.in"]));
        macros.insert("@Num2Bits_0".to_string(), macro_def(&[], &["out"]));

        let mut pairs = vec![
            ("main.lt.in[0]".to_string(), 5usize),
            ("main.lt.in[1]".to_string(), 6),
            ("main.lt.out".to_string(), 4),
            ("main.lt.n2b.in".to_string(), 40),
        ];
        for i in 0..33 {
            pairs.push((format!("main.lt.n2b.out[{}]", i), 7 + i));
        }
        let n2s: BTreeMap<String, usize> = pairs.into_iter().collect();
        let nodes = run(&macros, "@GreaterThan_2", &n2s);

        assert_eq!(nodes.len(), 3);
        assert_eq!(nodes[1].prefix, "main.lt");
        assert_eq!(nodes[1].input_signals, vec![5, 6]);
        assert_eq!(nodes[1].output_signals, vec![4]);
        assert_eq!(nodes[2].prefix, "main.lt.n2b");
        assert_eq!(nodes[2].input_signals, vec![40]);
        assert_eq!(nodes[2].output_signals, (7..40).collect::<Vec<_>>(), "33 bits, in order");
    }
}
