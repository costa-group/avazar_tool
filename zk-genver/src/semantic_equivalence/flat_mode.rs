//! `--resolved_formula`: verifying against ONE flat formula instead of one per
//! component instance.
//!
//! The normal path clusters the circuit instance by instance, guided by the
//! component structure: each template gets its own pair of clusterings and its
//! own queries, and a subcomponent enters its parent's query as an abstraction.
//! This one drops the structure. `llzk_smt_preprocessor --mode single` writes
//! every instance's tags into a SINGLE dictionary, each key carrying the
//! instance it came from as a prefix (`main.lt.if (%6 == 1)`), and the whole
//! file is handed to the hybrid clustering as one formula against the whole
//! r1cs. The clusters that come out are free to cut across instances.
//!
//! Two things have to be rebuilt for that to work.
//!
//! The atoms' SMT-LIB text is not in the resolved file -- it only lists signals
//! -- so it still comes from [`build_atoms`](super::atoms::build_atoms) over the
//! specification. The two are lined up by `instance.tag`, which is exactly the
//! key the `single` mode writes, and [`align_atoms`] reports every key with no
//! atom behind it and every atom the file does not carry.
//!
//! The specification variables are per instance: the parent calls a wire
//! `spec_main_v_9` and the child calls the same wire `spec_main_lt_v_3`. Within
//! one instance that never mattered. In one flat query it does, so names bound
//! to a common signal are merged into one -- see [`canonical_vars`] -- and every
//! atom's text is rewritten into the merged name. That is what makes a single
//! `signal -> variable` map, and hence a single cluster interface, well defined.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::path::Path;

use circuits_constraints_and_algebra::circuit::Circuit;
use circuits_constraints_and_algebra::num_bigint::BigInt;
use circuits_constraints_and_algebra::smt_formula::{Formula, FormulaAtom};

use crate::semantic_equivalence::atoms::{AtomInfo, AtomTable, InstanceInfo};

/// The resolved file read back: one component, holding every instance's atoms.
pub struct FlatFormula {
    pub formula: Formula,
    /// The `"instance"` field of the single entry, which is also the component
    /// name the `Formula` is filed under and the name the merged instance takes.
    pub instance: String,
    /// Keys dropped for listing no signal at all: a tag with no variable in it,
    /// which in llzk means a body of `true`. They cannot take part in a
    /// clustering that works by shared ids, and `build_atoms` drops the same
    /// tags, so nothing is normally lost -- what would be lost is counted as
    /// [`FlatAlignment::absent`] instead.
    pub empty: Vec<String>,
}

/// Reads `llzk_smt_preprocessor --mode single` output.
///
/// The envelope is the one `parse_formula` reads, and that function would do
/// most of this; it is not used because it walks `HashMap`s, so the atom ORDER
/// it produces changes from run to run, and the greedy clustering that consumes
/// it is order-sensitive. Here the keys come out of `serde_json`'s map sorted,
/// which is stable and keeps an instance's tags together.
pub fn read_flat_formula(
    path: &Path,
    prime: &BigInt,
    inputs: HashSet<usize>,
    outputs: HashSet<usize>,
) -> Result<FlatFormula, String> {
    let text = std::fs::read_to_string(path)
        .map_err(|e| format!("could not read {}: {}", path.display(), e))?;
    let root: serde_json::Value = serde_json::from_str(&text)
        .map_err(|e| format!("could not parse {}: {}", path.display(), e))?;
    let root = root
        .as_object()
        .ok_or_else(|| format!("{}: the top level is not an object", path.display()))?;

    let mut instance: Option<String> = None;
    let mut atoms: Vec<FormulaAtom> = Vec::new();
    let mut empty: Vec<String> = Vec::new();

    for (macro_name, entries) in root.iter() {
        let entries = entries.as_array().ok_or_else(|| {
            format!("{}: the value of \"{}\" is not an array", path.display(), macro_name)
        })?;
        for entry in entries.iter() {
            let entry = entry.as_object().ok_or_else(|| {
                format!("{}: an entry of \"{}\" is not an object", path.display(), macro_name)
            })?;
            let name = entry
                .get("instance")
                .and_then(|v| v.as_str())
                .ok_or_else(|| format!("{}: an entry has no \"instance\" name", path.display()))?;
            // One instance, by construction of the `single` mode. A file with
            // several is one of the other modes, whose keys are NOT prefixed, so
            // two instances of the same template would collide on every shared
            // tag: refuse rather than silently merge them.
            match &instance {
                Some(first) if first != name => {
                    return Err(format!(
                        "{}: holds more than one instance ('{}' and '{}'), so it is not the \
                         output of `llzk_smt_preprocessor --mode single`. Re-run the \
                         preprocessor with `--mode single`.",
                        path.display(),
                        first,
                        name
                    ))
                }
                Some(_) => {}
                None => instance = Some(name.to_string()),
            }

            for (tag, value) in entry.iter() {
                if tag == "instance" {
                    continue;
                }
                let signals = signal_list(value).ok_or_else(|| {
                    format!(
                        "{}: the value of \"{}\" is not a list of signal ids. A file written \
                         with `--show-unresolved` carries variable names too, which the \
                         clustering cannot use.",
                        path.display(),
                        tag
                    )
                })?;
                if signals.is_empty() {
                    empty.push(tag.clone());
                    continue;
                }
                atoms.push(FormulaAtom { name: tag.clone(), signals });
            }
        }
    }

    let instance = instance
        .ok_or_else(|| format!("{}: holds no instance at all", path.display()))?;
    if atoms.is_empty() {
        return Err(format!("{}: holds no atom with any signal in it", path.display()));
    }

    let formula = Formula::from_atoms(prime, vec![(instance.clone(), atoms)], inputs, outputs);
    Ok(FlatFormula { formula, instance, empty })
}

/// A tag's value: `[1, 5]`, and also `[[1, 5], 2]` the way `parse_formula`
/// accepts it. `None` for anything else, a variable name included.
fn signal_list(value: &serde_json::Value) -> Option<Vec<usize>> {
    let items = value.as_array()?;
    let mut out = Vec::new();
    for item in items.iter() {
        match item {
            serde_json::Value::Number(n) => out.push(n.as_u64()? as usize),
            serde_json::Value::Array(inner) => {
                for one in inner.iter() {
                    out.push(one.as_u64()? as usize);
                }
            }
            _ => return None,
        }
    }
    Some(out)
}

/// Drops from the formula the keys that answer to no atom of the specification.
///
/// Such a key asserts `true` (see [`align_atoms`]), so it adds nothing to any
/// query -- but its signals still shape the partition, and one of them is
/// routinely the whole circuit. `main.call @Root (%arg0) to out` is the case
/// that matters: `build_atoms` skips the `main` macro, which is only the
/// wrapper around the root's call, so nothing supplies that tag's text; in the
/// resolved file it survives with every signal the root touches and glues the
/// lot into a single cluster. The `equalityN` tie groups are the same shape,
/// and their content is in the bindings already -- both signals of a tie carry
/// the same variable, so the interface equates them whether or not the group
/// is an atom.
///
/// The `equalityN` tie groups are the ONE exception, and they are kept. They
/// assert nothing either, but they are the only place the file says that two
/// signals are the same wire: a tag's value carries just the smallest id of each
/// tie (`resolved_first_var_json`), while `build_atoms` puts all of them in the
/// atom. Dropped, the flat clustering would see strictly fewer connections than
/// avazar's own formula has.
///
/// The rule, then: the partition is over what the queries assert, plus what the
/// file says about signals being the same wire. Returns the restricted formula
/// and the keys it let go.
pub fn restrict_to_asserted(flat: FlatFormula, table: &AtomTable) -> (FlatFormula, Vec<String>) {
    let asserted: BTreeSet<String> = table
        .atoms
        .iter()
        .map(|info| format!("{}.{}", info.instance, info.tag))
        .collect();

    let mut kept: Vec<FormulaAtom> = Vec::new();
    let mut dropped: Vec<String> = Vec::new();
    for atom in flat.formula.atoms().iter() {
        if asserted.contains(&atom.name) || is_tie_group(&atom.name) {
            kept.push(atom.clone());
        } else {
            dropped.push(atom.name.clone());
        }
    }
    if kept.is_empty() {
        // Nothing matched at all: leave the formula alone rather than hand the
        // clustering an empty one. `align_atoms` reports the mismatch, and an
        // empty formula would only turn it into a panic further down.
        return (flat, Vec::new());
    }

    let formula = Formula::from_atoms(
        flat.formula.prime(),
        vec![(flat.instance.clone(), kept)],
        flat.formula.get_input_signals().collect(),
        flat.formula.get_output_signals().collect(),
    );
    (FlatFormula { formula, instance: flat.instance, empty: flat.empty }, dropped)
}

/// Whether a key is one of the preprocessor's tie groups: the instance prefix
/// followed by `equality` and a number, which is how `to_json_single_resolved`
/// names them. Matched on the name because that is all the file gives -- the
/// value is a plain signal list like any other key's.
fn is_tie_group(key: &str) -> bool {
    let tail = match key.rsplit_once('.') {
        Some((_, tail)) => tail,
        None => key,
    };
    match tail.strip_prefix("equality") {
        Some(rest) => !rest.is_empty() && rest.chars().all(|c| c.is_ascii_digit()),
        None => false,
    }
}

/// What [`align_atoms`] produced, and what it could not.
pub struct FlatAlignment {
    /// Aligned with the flat `Formula`: `table.atoms[i]` is the atom the
    /// clustering indexes as `i`, which is what every query relies on.
    pub table: AtomTable,
    /// How many atoms of the specification a key of the file claimed. Several
    /// can share one key -- the file merges same-tag entries and this table does
    /// not -- so this is not the number of keys.
    pub matched: usize,
    /// Keys of the file that no atom of the specification answers to. The
    /// `single` mode writes two of these per instance by design -- `level0` and
    /// the `equalityN` tie groups -- and they are asserted as `true`.
    pub unmatched: Vec<String>,
    /// Atoms of the specification the file does not carry, whose text no query
    /// will ever assert. Every verdict is then against a weaker specification.
    pub absent: Vec<String>,
}

/// Builds the [`AtomTable`] the flat formula needs: one entry per atom of the
/// formula, in its order, plus a single merged instance.
///
/// `synthetic_base` is one past the largest r1cs signal id. The `single` mode
/// hands out ids of its own above that line for the specification variables with
/// no wire behind them, and they are NOT the ones `build_atoms` invented for the
/// same variables -- each allocates in its own order. Every id at or above the
/// line is recorded as synthetic here, whichever side made it up, which is what
/// keeps a cluster's interface from equating one to a circuit signal that does
/// not exist.
pub fn align_atoms(
    table: &AtomTable,
    formula: &Formula,
    instance: &str,
    synthetic_base: usize,
) -> FlatAlignment {
    let mut by_key: BTreeMap<String, Vec<usize>> = BTreeMap::new();
    for (index, info) in table.atoms.iter().enumerate() {
        by_key
            .entry(format!("{}.{}", info.instance, info.tag))
            .or_default()
            .push(index);
    }

    let (rename, signal_to_var, merged_vars) = canonical_vars(table);
    let rewrite = var_rewriter(&rename);

    let mut atoms: Vec<AtomInfo> = Vec::with_capacity(formula.atoms().len());
    let mut unmatched: Vec<String> = Vec::new();
    let mut used: HashSet<usize> = HashSet::new();

    for atom in formula.atoms().iter() {
        match by_key.get(&atom.name) {
            Some(indices) => {
                used.extend(indices.iter().copied());
                // A key the file merged from several same-tag entries: the
                // conjunction is what that key asserts.
                let parts: Vec<String> =
                    indices.iter().map(|i| rewrite(&table.atoms[*i].formula)).collect();
                let first = &table.atoms[indices[0]];
                atoms.push(AtomInfo {
                    instance: first.instance.clone(),
                    macro_name: first.macro_name.clone(),
                    tag: first.tag.clone(),
                    formula: if parts.len() == 1 {
                        parts.into_iter().next().unwrap()
                    } else {
                        format!("(and {})", parts.join(" "))
                    },
                });
            }
            None => {
                unmatched.push(atom.name.clone());
                // `true`, never the empty string: the text goes straight into an
                // `assert`. Nothing is lost by it -- a tie group's content is
                // already in the binding, where both signals carry the same
                // variable, so the interface equates them anyway.
                atoms.push(AtomInfo {
                    instance: instance.to_string(),
                    macro_name: String::new(),
                    tag: atom.name.clone(),
                    formula: "true".to_string(),
                });
            }
        }
    }

    let absent: Vec<String> = table
        .atoms
        .iter()
        .enumerate()
        .filter(|(index, _)| !used.contains(index))
        .map(|(_, info)| format!("{}.{}", info.instance, info.tag))
        .collect();

    let merged = InstanceInfo { signal_to_spec_var: signal_to_var, spec_vars: merged_vars };
    let mut instances: BTreeMap<String, InstanceInfo> = BTreeMap::new();
    instances.insert(instance.to_string(), merged);

    let mut recast = table.recast(atoms, instances);
    for atom in formula.atoms().iter() {
        for signal in atom.signals.iter().copied().filter(|s| *s >= synthetic_base) {
            recast
                .unresolved_ids
                .entry((instance.to_string(), format!("resolved_file_{}", signal)))
                .or_insert(signal);
        }
    }

    FlatAlignment { table: recast, matched: used.len(), unmatched, absent }
}

/// Merges the per-instance specification variables into one namespace.
///
/// Two names bound to a common r1cs signal denote the same wire -- that is what
/// a port IS -- so they are the same variable once the instances share a query.
/// Union-find over "binds a common signal", with the lexicographically smallest
/// name of each class as its representative so the result does not depend on
/// iteration order.
///
/// Returns the renaming (only the names that change), the merged
/// `signal -> variable` map, and every variable to declare: representatives,
/// plus the ones bound to no signal at all, which keep their own name because
/// nothing ties them to anything.
fn canonical_vars(
    table: &AtomTable,
) -> (BTreeMap<String, String>, HashMap<usize, String>, Vec<String>) {
    let mut all: BTreeSet<String> = BTreeSet::new();
    let mut vars_of_signal: BTreeMap<usize, BTreeSet<String>> = BTreeMap::new();
    for info in table.instances.values() {
        for var in info.spec_vars.iter() {
            all.insert(var.clone());
        }
        for (signal, var) in info.signal_to_spec_var.iter() {
            all.insert(var.clone());
            vars_of_signal.entry(*signal).or_default().insert(var.clone());
        }
    }

    let names: Vec<String> = all.into_iter().collect();
    let position: BTreeMap<&str, usize> =
        names.iter().enumerate().map(|(i, n)| (n.as_str(), i)).collect();

    // Root of a class is its smallest index, i.e. its smallest name.
    let mut parent: Vec<usize> = (0..names.len()).collect();
    fn find(parent: &mut Vec<usize>, mut x: usize) -> usize {
        while parent[x] != x {
            parent[x] = parent[parent[x]];
            x = parent[x];
        }
        x
    }
    for vars in vars_of_signal.values() {
        let mut members = vars.iter().filter_map(|v| position.get(v.as_str()).copied());
        if let Some(first) = members.next() {
            for other in members {
                let (a, b) = (find(&mut parent, first), find(&mut parent, other));
                if a != b {
                    if a < b {
                        parent[b] = a;
                    } else {
                        parent[a] = b;
                    }
                }
            }
        }
    }

    let mut rename: BTreeMap<String, String> = BTreeMap::new();
    let mut roots: BTreeSet<&str> = BTreeSet::new();
    for index in 0..names.len() {
        let root = find(&mut parent, index);
        if root != index {
            rename.insert(names[index].clone(), names[root].clone());
        }
        roots.insert(names[root].as_str());
    }
    // Sorted, as a `BTreeSet` gives them: the declarations of a query come out
    // in this order and two runs have to produce the same file.
    let declare: Vec<String> = roots.into_iter().map(|n| n.to_string()).collect();

    let mut signal_to_var: HashMap<usize, String> = HashMap::new();
    for (signal, vars) in vars_of_signal.iter() {
        if let Some(any) = vars.iter().next() {
            let root = find(&mut parent, position[any.as_str()]);
            signal_to_var.insert(*signal, names[root].clone());
        }
    }

    (rename, signal_to_var, declare)
}

/// Applies a renaming to an atom's text.
///
/// One pass over the whole text, matching a specification symbol and looking the
/// whole of it up: replacing name by name in sequence would let one rewrite feed
/// the next, and matching a name as a substring would turn `spec_main_v_1` into
/// a prefix of `spec_main_v_10`. A macro call is `spec_macro_...`, which the
/// pattern also matches and the map never contains, so it is left alone.
fn var_rewriter<'a>(rename: &'a BTreeMap<String, String>) -> impl Fn(&str) -> String + 'a {
    use regex::Regex;
    let pattern = Regex::new(r"\bspec_[A-Za-z0-9_]+").unwrap();
    move |text: &str| -> String {
        if rename.is_empty() {
            return text.to_string();
        }
        pattern
            .replace_all(text, |caps: &regex::Captures| match rename.get(&caps[0]) {
                Some(to) => to.clone(),
                None => caps[0].to_string(),
            })
            .into_owned()
    }
}

#[cfg(test)]
mod tests {
    //! Three things have to hold for a flat query to mean anything: the atom the
    //! clustering indexes as `i` is the atom whose text ends up in the query,
    //! the same wire under two instances' names becomes one variable, and what
    //! is lost is counted.

    use super::*;
    use crate::semantic_equivalence::atoms::AtomInfo;

    fn atom(instance: &str, tag: &str, formula: &str) -> AtomInfo {
        AtomInfo {
            instance: instance.to_string(),
            macro_name: "@M_0".to_string(),
            tag: tag.to_string(),
            formula: formula.to_string(),
        }
    }

    /// A table with the instances given as `(prefix, [(signal, var)])`; the
    /// variables of an instance become its `spec_vars` in the order given.
    fn table(atoms: Vec<AtomInfo>, instances: Vec<(&str, Vec<(usize, &str)>)>) -> AtomTable {
        let mut map: BTreeMap<String, InstanceInfo> = BTreeMap::new();
        for (prefix, bindings) in instances {
            let mut info = InstanceInfo::default();
            for (signal, var) in bindings {
                if !info.spec_vars.contains(&var.to_string()) {
                    info.spec_vars.push(var.to_string());
                }
                info.signal_to_spec_var.insert(signal, var.to_string());
            }
            map.insert(prefix.to_string(), info);
        }
        AtomTable::default().recast(atoms, map)
    }

    fn formula(atoms: Vec<(&str, Vec<usize>)>) -> Formula {
        Formula::from_atoms(
            &BigInt::from(7u32),
            vec![(
                "main".to_string(),
                atoms
                    .into_iter()
                    .map(|(name, signals)| FormulaAtom { name: name.to_string(), signals })
                    .collect(),
            )],
            HashSet::new(),
            HashSet::new(),
        )
    }

    #[test]
    fn a_key_of_the_file_carries_the_text_of_the_atom_it_names() {
        // The whole alignment: `main.lt.step` in the file is the atom tagged
        // `step` of instance `main.lt`, whatever position either gives it.
        let t = table(
            vec![atom("main", "step", "(= spec_main_v_0 1)"), atom("main.lt", "step", "(= spec_main_lt_v_0 2)")],
            vec![("main", vec![(1, "spec_main_v_0")]), ("main.lt", vec![(2, "spec_main_lt_v_0")])],
        );
        // Deliberately the other way round from the table's order.
        let f = formula(vec![("main.lt.step", vec![2]), ("main.step", vec![1])]);
        let aligned = align_atoms(&t, &f, "main", 100);

        assert_eq!(aligned.table.atom(0).formula, "(= spec_main_lt_v_0 2)");
        assert_eq!(aligned.table.atom(1).formula, "(= spec_main_v_0 1)");
        assert_eq!(aligned.matched, 2);
        assert!(aligned.absent.is_empty());
    }

    #[test]
    fn the_same_wire_under_two_names_becomes_one_variable() {
        // Signal 5 is the child's output and the parent's input, and each
        // instance calls it its own thing. In one query that has to be ONE
        // symbol, or the child's formula constrains something the parent's
        // never mentions and the query is trivially satisfiable.
        let t = table(
            vec![atom("main", "read", "(= spec_main_v_9 spec_main_v_1)"), atom("main.lt", "write", "(= spec_main_lt_v_3 0)")],
            vec![
                ("main", vec![(5, "spec_main_v_9"), (1, "spec_main_v_1")]),
                ("main.lt", vec![(5, "spec_main_lt_v_3")]),
            ],
        );
        let f = formula(vec![("main.read", vec![5, 1]), ("main.lt.write", vec![5])]);
        let aligned = align_atoms(&t, &f, "main", 100);

        let merged = aligned.table.instance("main");
        assert_eq!(merged.signal_to_spec_var[&5], "spec_main_lt_v_3", "the smaller name wins");
        assert_eq!(aligned.table.atom(0).formula, "(= spec_main_lt_v_3 spec_main_v_1)");
        assert_eq!(aligned.table.atom(1).formula, "(= spec_main_lt_v_3 0)");
        assert!(merged.spec_vars.contains(&"spec_main_lt_v_3".to_string()));
        assert!(
            !merged.spec_vars.contains(&"spec_main_v_9".to_string()),
            "the name that was merged away is not declared any more"
        );
    }

    #[test]
    fn a_longer_name_is_not_rewritten_as_a_prefix_of_itself() {
        // `spec_main_v_1` is a prefix of `spec_main_v_10`: a substring rewrite
        // would turn the second into `spec_main_lt_v_00`.
        let t = table(
            vec![atom("main", "step", "(= spec_main_v_1 spec_main_v_10)")],
            vec![("main", vec![(5, "spec_main_v_1"), (6, "spec_main_v_10")]), ("main.lt", vec![(5, "spec_main_lt_v_0")])],
        );
        let f = formula(vec![("main.step", vec![5, 6])]);
        let aligned = align_atoms(&t, &f, "main", 100);

        assert_eq!(aligned.table.atom(0).formula, "(= spec_main_lt_v_0 spec_main_v_10)");
    }

    #[test]
    fn a_macro_call_is_left_alone() {
        // `spec_macro_...` matches the same pattern the variables do and must
        // never be renamed: it is a `define-fun`, not a wire.
        let t = table(
            vec![atom("main", "call", "(spec_macro_IsZero_0 spec_main_v_1)")],
            vec![("main", vec![(5, "spec_main_v_1")]), ("main.a", vec![(5, "spec_main_a_v_0")])],
        );
        let f = formula(vec![("main.call", vec![5])]);
        let aligned = align_atoms(&t, &f, "main", 100);

        // The argument is renamed, the macro symbol beside it is not.
        assert_eq!(aligned.table.atom(0).formula, "(spec_macro_IsZero_0 spec_main_a_v_0)");
    }

    #[test]
    fn a_key_with_no_atom_is_asserted_as_true_and_an_atom_with_no_key_is_reported() {
        // `equalityN` and `level0` are written by the `single` mode itself and
        // answer to no atom; an atom the file does not carry is a hole in the
        // specification the queries assert, and has to be said out loud.
        let t = table(
            vec![atom("main", "kept", "(= spec_main_v_0 1)"), atom("main", "lost", "(= spec_main_v_1 2)")],
            vec![("main", vec![(1, "spec_main_v_0"), (2, "spec_main_v_1")])],
        );
        let f = formula(vec![("main.kept", vec![1]), ("main.equality1", vec![1, 2])]);
        let aligned = align_atoms(&t, &f, "main", 100);

        assert_eq!(aligned.table.atom(1).formula, "true");
        assert_eq!(aligned.unmatched, vec!["main.equality1".to_string()]);
        assert_eq!(aligned.absent, vec!["main.lost".to_string()]);
    }

    #[test]
    fn two_atoms_under_one_key_are_asserted_together() {
        // The file merges same-tag entries of an instance into one key; the
        // table keeps them apart. Dropping either would silently weaken the
        // specification, so the key asserts both.
        let t = table(
            vec![atom("main", "and0", "(= spec_main_v_0 1)"), atom("main", "and0", "(= spec_main_v_1 2)")],
            vec![("main", vec![(1, "spec_main_v_0"), (2, "spec_main_v_1")])],
        );
        let f = formula(vec![("main.and0", vec![1, 2])]);
        let aligned = align_atoms(&t, &f, "main", 100);

        assert_eq!(aligned.table.atom(0).formula, "(and (= spec_main_v_0 1) (= spec_main_v_1 2))");
        assert_eq!(aligned.matched, 2);
        assert!(aligned.absent.is_empty());
    }

    #[test]
    fn an_id_the_file_invented_is_recorded_as_synthetic() {
        // The `single` mode hands out ids above the last r1cs signal for the
        // variables with no wire. They are not the ids `build_atoms` invented
        // for the same variables, and nothing must equate one to a circuit
        // signal: the interface drops whatever is recorded here.
        let t = table(
            vec![atom("main", "step", "(= spec_main_v_0 1)")],
            vec![("main", vec![(1, "spec_main_v_0")])],
        );
        let f = formula(vec![("main.step", vec![1, 100, 101])]);
        let aligned = align_atoms(&t, &f, "main", 100);

        let synthetic: HashSet<usize> = aligned.table.unresolved_ids.values().copied().collect();
        assert!(synthetic.contains(&100) && synthetic.contains(&101));
        assert!(!synthetic.contains(&1), "a real signal is not made up");
    }

    #[test]
    fn a_key_that_asserts_nothing_does_not_shape_the_partition() {
        // `main.call @Root ...` has no atom behind it -- `build_atoms` skips the
        // `main` wrapper macro -- yet it carries every signal the root touches.
        // Left in, it is one atom joining the whole circuit; it asserts `true`,
        // so leaving it out costs no assertion at all.
        let t = table(
            vec![atom("main", "step", "(= spec_main_v_0 1)")],
            vec![("main", vec![(1, "spec_main_v_0")])],
        );
        let f = formula(vec![
            ("main.step", vec![1]),
            ("main.call @Root (%arg0) to out", vec![1, 2, 3, 4]),
            ("main.equality1", vec![1, 2]),
        ]);
        let (restricted, dropped) =
            restrict_to_asserted(FlatFormula { formula: f, instance: "main".to_string(), empty: vec![] }, &t);

        // The call tag goes; the tie group stays, because it is the only place
        // the file says signals 1 and 2 are the same wire.
        let names: Vec<&str> = restricted.formula.atoms().iter().map(|a| a.name.as_str()).collect();
        assert_eq!(names, vec!["main.step", "main.equality1"]);
        assert_eq!(dropped, vec!["main.call @Root (%arg0) to out".to_string()]);
    }

    #[test]
    fn only_a_real_tie_group_is_spared() {
        assert!(is_tie_group("main.equality1") && is_tie_group("main.mux.equality12"));
        assert!(!is_tie_group("main.equalityish") && !is_tie_group("main.equality"));
        assert!(!is_tie_group("main.call @Root (%arg0) to out"));
    }

    #[test]
    fn a_formula_matching_nothing_is_left_alone() {
        // Every key unmatched means the two sides disagree on the instance
        // prefixes. `align_atoms` says so; handing the clustering an empty
        // formula would turn that report into a panic further down.
        let t = table(vec![atom("main", "step", "true")], vec![("main", vec![(1, "spec_main_v_0")])]);
        let f = formula(vec![("other.step", vec![1])]);
        let (restricted, dropped) =
            restrict_to_asserted(FlatFormula { formula: f, instance: "main".to_string(), empty: vec![] }, &t);

        assert_eq!(restricted.formula.atoms().len(), 1);
        assert!(dropped.is_empty());
    }

    #[test]
    fn a_file_with_two_instances_is_refused() {
        // The other modes write one entry per instance and do NOT prefix the
        // tags, so two instances of the same template share every key. Merging
        // them would lose half the specification without a word.
        let dir = std::env::temp_dir().join("avazar_flat_mode_two_instances");
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("resolved.json");
        std::fs::write(
            &path,
            r#"{"@M_0": [{"instance": "main", "step": [1]}, {"instance": "main.lt", "step": [2]}]}"#,
        )
        .unwrap();

        let err = match read_flat_formula(&path, &BigInt::from(7u32), HashSet::new(), HashSet::new()) {
            Err(e) => e,
            Ok(_) => panic!("two instances have to be refused"),
        };
        assert!(err.contains("--mode single"), "the message says how to fix it: {}", err);
    }

    #[test]
    fn a_file_written_with_variable_names_is_refused() {
        let dir = std::env::temp_dir().join("avazar_flat_mode_names");
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("resolved.json");
        std::fs::write(&path, r#"{"all": [{"instance": "main", "main.step": [1, "v_9"]}]}"#).unwrap();

        let err = match read_flat_formula(&path, &BigInt::from(7u32), HashSet::new(), HashSet::new()) {
            Err(e) => e,
            Ok(_) => panic!("a variable name is not a signal id"),
        };
        assert!(err.contains("show-unresolved"), "the message names the flag: {}", err);
    }

    #[test]
    fn the_atoms_come_out_in_a_stable_order() {
        // The clustering is greedy and order-sensitive, so two runs over the
        // same file have to see the same formula.
        let dir = std::env::temp_dir().join("avazar_flat_mode_order");
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("resolved.json");
        std::fs::write(
            &path,
            r#"{"all": [{"instance": "main", "main.b": [2], "main.a": [1], "main.c": [3]}]}"#,
        )
        .unwrap();

        let first = read_flat_formula(&path, &BigInt::from(7u32), HashSet::new(), HashSet::new()).unwrap();
        let second = read_flat_formula(&path, &BigInt::from(7u32), HashSet::new(), HashSet::new()).unwrap();
        let names = |f: &FlatFormula| -> Vec<String> {
            f.formula.atoms().iter().map(|a| a.name.clone()).collect()
        };
        assert_eq!(names(&first), names(&second));
        assert_eq!(first.instance, "main");
    }
}
