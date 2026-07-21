// Copyright Costa Group UCM.
// SPDX-License-Identifier: Apache-2.0

//! # llzk_smt_preprocessor
//!
//! Preprocesado del SMT-LIB producido por llzk. Analiza cómo se agrupan los
//! parámetros de cada macro (`define-fun` y familia) según las anotaciones
//! `:meta-data`, usando la librería
//! [`yaspar`](https://crates.io/crates/yaspar).
//!
//! Construye un ÁRBOL de tags que respeta el anidamiento de los `!` y ofrece dos
//! vistas:
//!
//! - **plano** ([`to_json_flat`]): para cada fórmula del nivel superior, todas las
//!   variables accedidas (agregando los tags anidados). Siempre incluye `level0`.
//! - **anidado** ([`to_json_nested`]): respeta la estructura; cada tag es un nodo
//!   con sus variables directas y sus hijos.
//!
//! ## Uso como librería
//!
//! ```no_run
//! let source = std::fs::read_to_string("f.smt2").unwrap();
//! let macros = llzk_smt_preprocessor::analyze(&source, false).unwrap();
//! for m in &macros {
//!     println!("{}: level0 = {:?}", m.name, m.level0);
//! }
//! println!("{}", llzk_smt_preprocessor::to_json_nested(&macros));
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

// ===========================================================================
// Tipos públicos del resultado.
// ===========================================================================

/// Nodo del árbol de tags `:meta-data`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TagNode {
    /// Valor del `:meta-data`.
    pub tag: String,
    /// Parámetros directos de este tag (los que no caen en un tag hijo).
    pub own: Vec<String>,
    /// Tags anidados dentro de este.
    pub children: Vec<TagNode>,
}

/// Resultado por macro (ya filtrado a los parámetros formales).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MacroEntry {
    /// Nombre de la macro.
    pub name: String,
    /// Parámetros que aparecen fuera de cualquier tag.
    pub level0: Vec<String>,
    /// Árbol de tags de nivel superior.
    pub tree: Vec<TagNode>,
}

/// Analiza un script SMT-LIB y devuelve una entrada por cada macro definida.
///
/// `block_comments` habilita los comentarios `#| ... |#` de SMT-LIB 2.7.
/// Devuelve `Err` con el mensaje de error de parseo si el script es inválido.
pub fn analyze(source: &str, block_comments: bool) -> Result<Vec<MacroEntry>, String> {
    let mut col = MetaCollector::default();
    match ScriptParser::new().parse(&mut col, tokenize_str(source, block_comments)) {
        Ok(_) => Ok(col.macros),
        Err(e) => Err(format!("{}", e)),
    }
}

/// Todas las variables de un nodo, agregando recursivamente sus hijos (vista plana).
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
// Representaciones internas construidas durante el parseo.
// ===========================================================================

#[derive(Clone)]
enum Attr {
    MetaData(String),
    Other,
}

#[derive(Clone, Default)]
struct MetaInfo {
    /// Símbolos directos no encerrados aún en ningún tag interno.
    own: Vec<String>,
    /// Tags hallados en el subárbol al nivel actual.
    children: Vec<TagNode>,
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
    }
}

/// Construye la entrada de una macro filtrando a sus parámetros.
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
// Salida JSON.
// ===========================================================================

fn json_string(s: &str) -> String {
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

/// Vista plana: `{ macro: { "level0": [...], "<tag superior>": [todas...] } }`.
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

fn node_json(node: &TagNode, ind: usize) -> String {
    let pad = "  ".repeat(ind);
    let pad2 = "  ".repeat(ind + 1);
    let mut s = String::new();
    s.push_str(&format!("{}{{\n", pad));
    s.push_str(&format!("{}\"tag\": {},\n", pad2, json_string(&node.tag)));
    s.push_str(&format!("{}\"vars\": {},\n", pad2, json_array(&node.own)));
    if node.children.is_empty() {
        s.push_str(&format!("{}\"children\": []\n", pad2));
    } else {
        s.push_str(&format!("{}\"children\": [\n", pad2));
        for (i, c) in node.children.iter().enumerate() {
            s.push_str(&node_json(c, ind + 2));
            if i + 1 < node.children.len() {
                s.push(',');
            }
            s.push('\n');
        }
        s.push_str(&format!("{}]\n", pad2));
    }
    s.push_str(&format!("{}}}", pad));
    s
}

/// Vista anidada: respeta la estructura de tags.
pub fn to_json_nested(macros: &[MacroEntry]) -> String {
    let mut out = String::from("{\n");
    for (mi, m) in macros.iter().enumerate() {
        out.push_str(&format!("  {}: {{\n", json_string(&m.name)));
        out.push_str(&format!("    \"level0\": {},\n", json_array(&m.level0)));
        if m.tree.is_empty() {
            out.push_str("    \"tags\": []\n");
        } else {
            out.push_str("    \"tags\": [\n");
            for (i, node) in m.tree.iter().enumerate() {
                out.push_str(&node_json(node, 3));
                if i + 1 < m.tree.len() {
                    out.push(',');
                }
                out.push('\n');
            }
            out.push_str("    ]\n");
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
// Implementación de la jerarquía de traits de yaspar.
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
        _range: Range,
        _constant: Self::Constant,
    ) -> ParsingResult<Self::Term> {
        Ok(MetaInfo::default())
    }

    fn on_term_identifier(
        &mut self,
        _range: Range,
        identifier: Self::Identifier,
        _sort: Option<Self::Sort>,
    ) -> ParsingResult<Self::Term> {
        Ok(MetaInfo {
            own: vec![identifier],
            children: Vec::new(),
        })
    }

    fn on_term_app(
        &mut self,
        _range: Range,
        identifier: Self::Identifier,
        _sort: Option<Self::Sort>,
        args: Vec<Self::Term>,
    ) -> ParsingResult<Self::Term> {
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
        Ok(MetaInfo { own, children })
    }

    fn on_term_let(
        &mut self,
        _range: Range,
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
        Ok(MetaInfo { own, children })
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
        _range: Range,
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
        Ok(MetaInfo { own, children })
    }

    fn on_term_annotated(
        &mut self,
        _range: Range,
        t: Self::Term,
        attributes: Vec<Self::Attribute>,
    ) -> ParsingResult<Self::Term> {
        let meta = attributes.into_iter().find_map(|a| match a {
            Attr::MetaData(tag) => Some(tag),
            Attr::Other => None,
        });
        match meta {
            Some(tag) => {
                let node = TagNode {
                    tag,
                    own: t.own,
                    children: t.children,
                };
                Ok(MetaInfo {
                    own: Vec::new(),
                    children: vec![node],
                })
            }
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
    fn level0_is_v4_v3() {
        let macros = analyze(EXAMPLE, false).unwrap();
        assert_eq!(macros[0].level0, vec!["v_4".to_string(), "v_3".to_string()]);
    }

    #[test]
    fn if_aggregates_all_branch_vars() {
        let macros = analyze(EXAMPLE, false).unwrap();
        let if_node = macros[0]
            .tree
            .iter()
            .find(|n| n.tag == "if (%x == 1)")
            .unwrap();
        // Directo del if: solo v_0 (la condición).
        assert_eq!(if_node.own, vec!["v_0".to_string()]);
        // Agregado (modo plano): v_0, v_1, v_2.
        assert_eq!(
            aggregate(if_node),
            vec!["v_0".to_string(), "v_1".to_string(), "v_2".to_string()]
        );
        // Estructura: dos hijos (then / else).
        assert_eq!(if_node.children.len(), 2);
    }
}
