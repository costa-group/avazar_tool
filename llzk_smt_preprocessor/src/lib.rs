// Copyright Costa Group UCM.
// SPDX-License-Identifier: Apache-2.0

//! # llzk_smt_preprocessor
//!
//! Groups each llzk macro's parameters by its `:meta-data` annotations, over
//! [`yaspar`](https://crates.io/crates/yaspar). Builds a TREE of tags that
//! respects the nesting of `!`, and flattens it: [`to_json_flat`] gives, per
//! top-level formula, every variable it touches. The tree itself is not emitted
//! -- nothing downstream consumed it.
//!
//! [`analyze`] takes a whole `.smt2`. In practice the input is the same
//! specification JSON `zk-genver` consumes, where each macro carries its
//! `formula` and `params`; [`analyze_specification`] wraps each one in a valid
//! `define-fun` and runs the same analysis:
//!
//! ```no_run
//! use utils::read_specification::read_smt_specification;
//!
//! let spec = read_smt_specification("results/iszero.json").unwrap();
//! let macros = llzk_smt_preprocessor::analyze_specification(&spec.macros).unwrap();
//! ```

use dashu::float::DBig;
use dashu::integer::UBig;

use yaspar::action::{
    ActionOnAttribute, ActionOnConstant, ActionOnIdentifier, ActionOnIndex, ActionOnSort,
    ActionOnString, ActionOnTerm, ParsingAction, ParsingResult, Pattern,
};
use yaspar::ast::{DatatypeDec, DatatypeDef, FunctionDef, Keyword};
use yaspar::position::Range;
use yaspar::smtlib2::ScriptParser;
use yaspar::{binary_to_string, hex_to_string, tokenize_str};

use indexmap::IndexMap;
use utils::read_specification::{MacroDef, VarInfo};

pub mod graph;
pub mod pretty;
pub mod resolve;

// ===========================================================================
// Public result types.
// ===========================================================================

/// Node of the `:meta-data` tag tree.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TagNode {
    /// The `:meta-data` value.
    pub tag: String,
    /// Direct parameters of this tag (the ones that don't fall into a child tag).
    pub own: Vec<String>,
    /// Tags nested within this one.
    pub children: Vec<TagNode>,
    /// Range of the term the tag encloses, WITHOUT the `(! ... :meta-data ...)`
    /// wrapper.
    pub range: Option<Range>,
    /// That term's literal SMT-LIB text, sliced from the source. Assertable on
    /// its own, which is what makes a tag a verification unit and not just a bag
    /// of variables.
    pub formula: String,
}

/// Result per macro (already filtered down to the formal parameters).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MacroEntry {
    /// Macro name.
    pub name: String,
    /// Parameters outside any `and`/tag. Usually empty: a loose branch of a
    /// top-level `and` becomes its own `"andN"` node in `tree` instead (see
    /// `on_term_app`).
    pub level0: Vec<String>,
    /// Top-level tag tree: real tags plus the synthetic `"andN"` ones.
    pub tree: Vec<TagNode>,
}

/// Analyzes an SMT-LIB script and returns one entry per macro defined in it.
///
/// `block_comments` enables SMT-LIB 2.7's `#| ... |#` comments.
/// Returns `Err` with the parse error message if the script is invalid.
pub fn analyze(source: &str, block_comments: bool) -> Result<Vec<MacroEntry>, String> {
    let mut col = MetaCollector::default();
    match ScriptParser::new().parse(&mut col, tokenize_str(source, block_comments)) {
        Ok(_) => {
            let chars: Vec<char> = source.chars().collect();
            let mut macros = col.macros;
            for m in macros.iter_mut() {
                for node in m.tree.iter_mut() {
                    fill_formulas(node, &chars);
                }
            }
            Ok(macros)
        }
        Err(e) => Err(format!("{}", e)),
    }
}

/// Slices each [`TagNode::formula`] out of the source at the node's range. A
/// post-pass because yaspar's callbacks see positions, never the text.
///
/// `chars` because [`yaspar::position::Position::char_num`] counts CHARACTERS,
/// so indexing a `&str` would be wrong — and would panic — on any non-ASCII.
fn fill_formulas(node: &mut TagNode, chars: &[char]) {
    if let Some(range) = &node.range {
        let (start, end) = (range.start.char_num, range.end.char_num);
        if start <= end && end <= chars.len() {
            node.formula = chars[start..end].iter().collect();
        }
    }
    for child in node.children.iter_mut() {
        fill_formulas(child, chars);
    }
}

/// Wraps a macro body in a valid `define-fun` so [`analyze`] can take it. Any
/// sort works: yaspar doesn't typecheck (see `parses_one_macro`, which uses the
/// undeclared sort `FFp`).
fn wrap_macro_formula(name: &str, params: &[VarInfo], formula: &str) -> String {
    let mut script = format!("(define-fun {} (", name);
    for par in params {
        script.push_str(&format!("({} FF0) ", par.name));
    }
    script.push_str(") Bool\n");
    script.push_str(formula);
    script.push_str(")\n");
    script
}

/// Analyzes a single macro from the specification JSON.
pub fn analyze_macro_def(name: &str, macro_def: &MacroDef) -> Result<MacroEntry, String> {
    let script = wrap_macro_formula(name, &macro_def.params, &macro_def.formula);
    let mut entries = analyze(&script, false)?;
    entries
        .pop()
        .ok_or_else(|| format!("macro '{}' produced no entry", name))
}

/// Analyzes every macro in the specification JSON (the same one
/// `zk-genver::correctness::processing_correctness_utils` consumes), instead
/// of a raw `.smt2` with several `define-fun`s.
pub fn analyze_specification(
    macros: &IndexMap<String, MacroDef>,
) -> Result<Vec<MacroEntry>, String> {
    macros
        .iter()
        .map(|(name, def)| analyze_macro_def(name, def))
        .collect()
}

/// All the variables of a node, recursively aggregating its children (flat view).
pub fn aggregate(node: &TagNode) -> Vec<String> {
    let mut out = Vec::new();
    for s in &node.own {
        push_unique(&mut out, s);
    }
    for c in &node.children {
        for s in aggregate(c) {
            push_unique(&mut out, &s);
        }
    }
    out
}

// ===========================================================================
// Internal representations built during parsing.
// ===========================================================================

#[derive(Clone)]
enum Attr {
    MetaData(String),
    Other,
}

#[derive(Clone, Default)]
struct MetaInfo {
    /// Direct symbols not yet enclosed in any inner tag.
    own: Vec<String>,
    /// Tags found in the subtree at the current level.
    children: Vec<TagNode>,
    /// Range of the term this was built from, so that when an enclosing
    /// `(! ... :meta-data ...)` closes a tag the [`TagNode`] knows where its
    /// formula is (see `on_term_annotated`).
    range: Option<Range>,
}

#[derive(Default)]
struct MetaCollector {
    macros: Vec<MacroEntry>,
}

// --- Helpers ---------------------------------------------------------------

fn is_meta(kw: &Keyword) -> bool {
    kw.symbol_of() == "meta-data"
}

fn push_unique(v: &mut Vec<String>, s: &str) {
    if !v.iter().any(|x| x == s) {
        v.push(s.to_string());
    }
}

// Keeps the symbols that are formal parameters, dropping the operator names
// ("=", "ff.mul", "ite") that `on_term_app` accumulates into `own` alongside
// them.
fn filter_params(syms: &[String], params: &[String]) -> Vec<String> {
    syms.iter()
        .filter(|s| params.iter().any(|p| p == *s))
        .cloned()
        .collect()
}

fn filter_node(node: TagNode, params: &[String]) -> TagNode {
    TagNode {
        tag: node.tag,
        own: filter_params(&node.own, params),
        children: node
            .children
            .into_iter()
            .map(|c| filter_node(c, params))
            .collect(),
        range: node.range,
        formula: node.formula,
    }
}

/// Builds a macro entry, filtering down to its parameters.
fn build_entry(name: String, params: &[String], body: MetaInfo) -> MacroEntry {
    let level0 = filter_params(&body.own, params);
    let tree = body
        .children
        .into_iter()
        .map(|c| filter_node(c, params))
        .collect();
    MacroEntry { name, level0, tree }
}

// ===========================================================================
// JSON output.
// ===========================================================================

pub(crate) fn json_string(s: &str) -> String {
    let mut r = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => r.push_str("\\\""),
            '\\' => r.push_str("\\\\"),
            '\n' => r.push_str("\\n"),
            '\r' => r.push_str("\\r"),
            '\t' => r.push_str("\\t"),
            c if (c as u32) < 0x20 => r.push_str(&format!("\\u{:04x}", c as u32)),
            c => r.push(c),
        }
    }
    r.push('"');
    r
}

fn json_array(items: &[String]) -> String {
    let parts: Vec<String> = items.iter().map(|s| json_string(s)).collect();
    format!("[{}]", parts.join(", "))
}

fn merge_pair(into: &mut Vec<(String, Vec<String>)>, tag: String, syms: Vec<String>) {
    match into.iter_mut().find(|(t, _)| *t == tag) {
        Some((_, existing)) => {
            for s in &syms {
                push_unique(existing, s);
            }
        }
        None => into.push((tag, syms)),
    }
}

/// Flat view: `{ macro: { "level0": [...], "<top-level tag>": [all...] } }`.
pub fn to_json_flat(macros: &[MacroEntry]) -> String {
    let mut out = String::from("{\n");
    for (mi, m) in macros.iter().enumerate() {
        let mut pairs: Vec<(String, Vec<String>)> = Vec::new();
        pairs.push(("level0".to_string(), m.level0.clone()));
        for node in &m.tree {
            merge_pair(&mut pairs, node.tag.clone(), aggregate(node));
        }
        out.push_str(&format!("  {}: {{\n", json_string(&m.name)));
        for (pi, (k, v)) in pairs.iter().enumerate() {
            out.push_str(&format!("    {}: {}", json_string(k), json_array(v)));
            if pi + 1 < pairs.len() {
                out.push(',');
            }
            out.push('\n');
        }
        out.push_str("  }");
        if mi + 1 < macros.len() {
            out.push(',');
        }
        out.push('\n');
    }
    out.push('}');
    out
}

// ===========================================================================
// Implementation of yaspar's trait hierarchy.
// ===========================================================================

impl ActionOnString for MetaCollector {
    type Str = String;

    fn on_string(&mut self, _range: Range, s: String) -> ParsingResult<Self::Str> {
        Ok(s)
    }
}

impl ActionOnConstant for MetaCollector {
    type Constant = String;

    fn on_constant_binary(
        &mut self,
        _range: Range,
        bytes: Vec<u8>,
        len: usize,
    ) -> ParsingResult<Self::Constant> {
        Ok(format!("#b{}", binary_to_string(&bytes, len)))
    }

    fn on_constant_hexadecimal(
        &mut self,
        _range: Range,
        bytes: Vec<u8>,
        len: usize,
    ) -> ParsingResult<Self::Constant> {
        Ok(format!("#x{}", hex_to_string(&bytes, len)))
    }

    fn on_constant_decimal(&mut self, _range: Range, decimal: DBig) -> ParsingResult<Self::Constant> {
        Ok(format!("{}", decimal))
    }

    fn on_constant_numeral(&mut self, _range: Range, numeral: UBig) -> ParsingResult<Self::Constant> {
        Ok(format!("{}", numeral))
    }

    fn on_constant_string(
        &mut self,
        _range: Range,
        string: Self::Str,
    ) -> ParsingResult<Self::Constant> {
        Ok(string)
    }

    fn on_constant_bool(&mut self, _range: Range, boolean: bool) -> ParsingResult<Self::Constant> {
        Ok((if boolean { "true" } else { "false" }).to_string())
    }
}

impl ActionOnIndex for MetaCollector {
    type Index = String;

    fn on_index_numeral(&mut self, _range: Range, index: UBig) -> ParsingResult<Self::Index> {
        Ok(format!("{}", index))
    }

    fn on_index_symbol(&mut self, _range: Range, index: Self::Str) -> ParsingResult<Self::Index> {
        Ok(index)
    }

    fn on_index_hexadecimal(
        &mut self,
        _range: Range,
        bytes: Vec<u8>,
        len: usize,
    ) -> ParsingResult<Self::Index> {
        Ok(format!("#x{}", hex_to_string(&bytes, len)))
    }
}

impl ActionOnIdentifier for MetaCollector {
    type Identifier = String;

    fn on_identifier(
        &mut self,
        _range: Range,
        symbol: Self::Str,
        _indices: Vec<Self::Index>,
    ) -> ParsingResult<Self::Identifier> {
        Ok(symbol)
    }
}

impl ActionOnAttribute for MetaCollector {
    type Term = MetaInfo;
    type Attribute = Attr;

    fn on_attribute_keyword(
        &mut self,
        _range: Range,
        _keyword: Keyword,
    ) -> ParsingResult<Self::Attribute> {
        Ok(Attr::Other)
    }

    fn on_attribute_constant(
        &mut self,
        _range: Range,
        keyword: Keyword,
        constant: Self::Constant,
    ) -> ParsingResult<Self::Attribute> {
        if is_meta(&keyword) {
            Ok(Attr::MetaData(constant))
        } else {
            Ok(Attr::Other)
        }
    }

    fn on_attribute_symbol(
        &mut self,
        _range: Range,
        keyword: Keyword,
        symbol: Self::Str,
    ) -> ParsingResult<Self::Attribute> {
        if is_meta(&keyword) {
            Ok(Attr::MetaData(symbol))
        } else {
            Ok(Attr::Other)
        }
    }

    fn on_attribute_named(&mut self, _range: Range, _name: Self::Str) -> ParsingResult<Self::Attribute> {
        Ok(Attr::Other)
    }

    fn on_attribute_pattern(
        &mut self,
        _range: Range,
        _patterns: Vec<Self::Term>,
    ) -> ParsingResult<Self::Attribute> {
        Ok(Attr::Other)
    }
}

impl ActionOnSort for MetaCollector {
    type Sort = ();

    fn on_sort(
        &mut self,
        _range: Range,
        _identifier: Self::Identifier,
        _args: Vec<Self::Sort>,
    ) -> ParsingResult<Self::Sort> {
        Ok(())
    }
}

impl ActionOnTerm for MetaCollector {
    fn on_term_constant(
        &mut self,
        range: Range,
        _constant: Self::Constant,
    ) -> ParsingResult<Self::Term> {
        Ok(MetaInfo {
            range: Some(range),
            ..MetaInfo::default()
        })
    }

    fn on_term_identifier(
        &mut self,
        range: Range,
        identifier: Self::Identifier,
        _sort: Option<Self::Sort>,
    ) -> ParsingResult<Self::Term> {
        Ok(MetaInfo {
            own: vec![identifier],
            children: Vec::new(),
            range: Some(range),
        })
    }

    fn on_term_app(
        &mut self,
        range: Range,
        identifier: Self::Identifier,
        _sort: Option<Self::Sort>,
        args: Vec<Self::Term>,
    ) -> ParsingResult<Self::Term> {
        if identifier == "and" {
            // Every branch of an "and" is an independent assertion, so each one
            // gets its own node rather than having their variables merged. An
            // untagged branch becomes a synthetic "andN", indistinguishable from
            // a real tag downstream.
            //
            // Arguments arrive already processed (the parser is bottom-up), and
            // both a real :meta-data and a nested "and" leave `own` empty. So a
            // non-empty `a.own` means exactly "this branch has no tag of its own".
            let mut children = Vec::new();
            let mut and_index = 0;
            for a in args {
                if !a.own.is_empty() {
                    children.push(TagNode {
                        tag: format!("and{}", and_index),
                        own: a.own,
                        children: Vec::new(),
                        range: a.range.clone(),
                        formula: String::new(),
                    });
                    and_index += 1;
                }
                children.extend(a.children);
            }
            return Ok(MetaInfo {
                own: Vec::new(), // an "and" leaves nothing in `own`
                children,
                range: Some(range),
            });
        }

        // Any other operator ("=", "ite", a macro call) is a SINGLE
        // assertion, so merging its arguments' `own` loses nothing.
        let mut own = Vec::new();
        push_unique(&mut own, &identifier);
        for a in &args {
            for s in &a.own {
                push_unique(&mut own, s);
            }
        }
        let mut children = Vec::new();
        for a in args {
            children.extend(a.children);
        }
        Ok(MetaInfo {
            own,
            children,
            range: Some(range),
        })
    }

    fn on_term_let(
        &mut self,
        range: Range,
        bindings: Vec<(Self::Str, Self::Term)>,
        body: Self::Term,
    ) -> ParsingResult<Self::Term> {
        let mut own = Vec::new();
        for (_, t) in &bindings {
            for s in &t.own {
                push_unique(&mut own, s);
            }
        }
        for s in &body.own {
            push_unique(&mut own, s);
        }
        let mut children = Vec::new();
        for (_, t) in bindings {
            children.extend(t.children);
        }
        children.extend(body.children);
        Ok(MetaInfo {
            own,
            children,
            range: Some(range),
        })
    }

    fn on_term_lambda(
        &mut self,
        _range: Range,
        _names: Vec<(Self::Str, Self::Sort)>,
        body: Self::Term,
    ) -> ParsingResult<Self::Term> {
        Ok(body)
    }

    fn on_term_exists(
        &mut self,
        _range: Range,
        _names: Vec<(Self::Str, Self::Sort)>,
        body: Self::Term,
    ) -> ParsingResult<Self::Term> {
        Ok(body)
    }

    fn on_term_forall(
        &mut self,
        _range: Range,
        _names: Vec<(Self::Str, Self::Sort)>,
        body: Self::Term,
    ) -> ParsingResult<Self::Term> {
        Ok(body)
    }

    fn on_term_match(
        &mut self,
        range: Range,
        scrutinee: Self::Term,
        cases: Vec<(Pattern<Self::Str>, Self::Term)>,
    ) -> ParsingResult<Self::Term> {
        let mut own = Vec::new();
        for s in &scrutinee.own {
            push_unique(&mut own, s);
        }
        for (_, body) in &cases {
            for s in &body.own {
                push_unique(&mut own, s);
            }
        }
        let mut children = Vec::new();
        children.extend(scrutinee.children);
        for (_, body) in cases {
            children.extend(body.children);
        }
        Ok(MetaInfo {
            own,
            children,
            range: Some(range),
        })
    }

    // `(! term :meta-data "...")`: where a term becomes a node of the tag tree.
    fn on_term_annotated(
        &mut self,
        range: Range,
        t: Self::Term,
        attributes: Vec<Self::Attribute>,
    ) -> ParsingResult<Self::Term> {
        // Among the annotations of this `(! ...)`, find a :meta-data.
        let meta = attributes.into_iter().find_map(|a| match a {
            Attr::MetaData(tag) => Some(tag),
            Attr::Other => None,
        });
        match meta {
            // Everything the term had accumulated is closed inside a new
            // TagNode, and propagated upward with `own` EMPTY: the parent sees
            // only the packaged node, not the loose variables.
            Some(tag) => {
                let node = TagNode {
                    tag,
                    own: t.own,
                    children: t.children,
                    // `t.range` is the term alone; `range` would include the
                    // `(! ... :meta-data ...)` wrapper. `formula` comes later,
                    // in `fill_formulas`.
                    range: t.range,
                    formula: String::new(),
                };
                Ok(MetaInfo {
                    own: Vec::new(),
                    children: vec![node],
                    // The whole `(! ...)`, so an enclosing tag still knows
                    // where this subterm was.
                    range: Some(range),
                })
            }
            // An annotation of another kind: the term passes through untouched.
            None => Ok(t),
        }
    }
}

impl ParsingAction for MetaCollector {
    type Command = ();

    fn on_command_assert(&mut self, _range: Range, _t: Self::Term) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_check_sat(&mut self, _range: Range) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_check_sat_assuming(
        &mut self,
        _range: Range,
        _terms: Vec<Self::Term>,
    ) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_declare_const(
        &mut self,
        _range: Range,
        _name: Self::Str,
        _sort: Self::Sort,
    ) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_declare_datatype(
        &mut self,
        _range: Range,
        _name: Self::Str,
        _datatype: DatatypeDec<Self::Str, Self::Sort>,
    ) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_declare_datatypes(
        &mut self,
        _range: Range,
        _defs: Vec<DatatypeDef<Self::Str, Self::Sort>>,
    ) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_declare_fun(
        &mut self,
        _range: Range,
        _name: Self::Str,
        _input_sorts: Vec<Self::Sort>,
        _out_sort: Self::Sort,
    ) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_declare_sort(
        &mut self,
        _range: Range,
        _name: Self::Str,
        _arity: UBig,
    ) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_declare_sort_parameter(
        &mut self,
        _range: Range,
        _name: Self::Str,
    ) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_define_const(
        &mut self,
        _range: Range,
        name: Self::Str,
        _sort: Self::Sort,
        term: Self::Term,
    ) -> ParsingResult<Self::Command> {
        let entry = build_entry(name, &[], term);
        self.macros.push(entry);
        Ok(())
    }

    fn on_command_define_fun(
        &mut self,
        _range: Range,
        definition: FunctionDef<Self::Str, Self::Sort, Self::Term>,
    ) -> ParsingResult<Self::Command> {
        let params: Vec<String> = definition.vars.iter().map(|(n, _)| n.clone()).collect();
        let entry = build_entry(definition.name, &params, definition.body);
        self.macros.push(entry);
        Ok(())
    }

    fn on_command_define_fun_rec(
        &mut self,
        _range: Range,
        definition: FunctionDef<Self::Str, Self::Sort, Self::Term>,
    ) -> ParsingResult<Self::Command> {
        let params: Vec<String> = definition.vars.iter().map(|(n, _)| n.clone()).collect();
        let entry = build_entry(definition.name, &params, definition.body);
        self.macros.push(entry);
        Ok(())
    }

    fn on_command_define_funs_rec(
        &mut self,
        _range: Range,
        definitions: Vec<FunctionDef<Self::Str, Self::Sort, Self::Term>>,
    ) -> ParsingResult<Self::Command> {
        for def in definitions {
            let params: Vec<String> = def.vars.iter().map(|(n, _)| n.clone()).collect();
            let entry = build_entry(def.name, &params, def.body);
            self.macros.push(entry);
        }
        Ok(())
    }

    fn on_command_define_sort(
        &mut self,
        _range: Range,
        _name: Self::Str,
        _params: Vec<Self::Str>,
        _sort: Self::Sort,
    ) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_echo(&mut self, _range: Range, _s: Self::Str) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_exit(&mut self, _range: Range) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_get_assertions(&mut self, _range: Range) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_get_assignment(&mut self, _range: Range) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_get_info(&mut self, _range: Range, _kw: Keyword) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_get_model(&mut self, _range: Range) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_get_option(&mut self, _range: Range, _kw: Keyword) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_get_proof(&mut self, _range: Range) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_get_unsat_assumptions(&mut self, _range: Range) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_get_unsat_core(&mut self, _range: Range) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_get_value(
        &mut self,
        _range: Range,
        _ts: Vec<Self::Term>,
    ) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_pop(&mut self, _range: Range, _lvl: UBig) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_push(&mut self, _range: Range, _lvl: UBig) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_reset(&mut self, _range: Range) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_reset_assertions(&mut self, _range: Range) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_set_info(
        &mut self,
        _range: Range,
        _attributes: Self::Attribute,
    ) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_set_logic(
        &mut self,
        _range: Range,
        _logic: Self::Str,
    ) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_set_option(
        &mut self,
        _range: Range,
        _attribute: Self::Attribute,
    ) -> ParsingResult<Self::Command> {
        Ok(())
    }
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    const EXAMPLE: &str = r#"
(define-fun main ((v_0 FFp) (v_4 FFp) (v_1 FFp) (v_2 FFp) (v_3 FFp)) Bool
  (and
    (and
      (! (ite (= v_0 1)
              (! (= v_1 (ff.mul v_0 1)) :meta-data "%z := felt.mul %x 1")
              (! (foo v_0 v_1 v_2) :meta-data "call foo (%x) to %z"))
         :meta-data "if (%x == 1)")
      (! (= v_3 (ff.add v_1 1)) :meta-data "%y := felt.add %z 1"))
    (= v_4 v_3)))
"#;

    #[test]
    fn parses_one_macro() {
        let macros = analyze(EXAMPLE, false).unwrap();
        assert_eq!(macros.len(), 1);
        assert_eq!(macros[0].name, "main");
    }

    #[test]
    fn untagged_top_level_conjunct_becomes_synthetic_and_tag() {
        let macros = analyze(EXAMPLE, false).unwrap();
        // "(= v_4 v_3)" has no :meta-data, so it becomes its own "and0" node
        // instead of being merged into level0.
        assert!(macros[0].level0.is_empty());
        let and0 = macros[0].tree.iter().find(|n| n.tag == "and0").unwrap();
        assert_eq!(and0.own, vec!["v_4".to_string(), "v_3".to_string()]);
        assert!(and0.children.is_empty());
    }

    #[test]
    fn if_aggregates_all_branch_vars() {
        let macros = analyze(EXAMPLE, false).unwrap();
        let if_node = macros[0]
            .tree
            .iter()
            .find(|n| n.tag == "if (%x == 1)")
            .unwrap();
        // Direct: only the condition.
        assert_eq!(if_node.own, vec!["v_0".to_string()]);
        // Aggregated (flat view).
        assert_eq!(
            aggregate(if_node),
            vec!["v_0".to_string(), "v_1".to_string(), "v_2".to_string()]
        );
        // then / else.
        assert_eq!(if_node.children.len(), 2);
    }
}
