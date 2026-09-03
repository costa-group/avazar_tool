use serde::{Serialize,Deserialize};
use std::collections::HashMap;
use std::fs::File;
use std::io::BufReader;
use std::path::Path;
use std::error::Error;
use indexmap::IndexMap;
use num_bigint_dig::BigInt;




/// A single variable / parameter entry: `{ "name": "v_0", "type": "ff" }`.
#[derive(Deserialize, Serialize, Debug, Clone)]
pub struct VarInfo {
    pub name: String,
    #[serde(rename = "type")]
    pub var_type: String,
}

/// One entry in the `macros` map.
/// `vars_info` values may be a string, an integer, or an array of strings,
/// so they are kept as raw `serde_json::Value`.
#[derive(Deserialize, Serialize, Debug, Clone)]
pub struct MacroDef {
    pub params: Vec<VarInfo>,
    pub vars_info: HashMap<String, serde_json::Value>,
    pub components_info: HashMap<String, String>,
    pub formula: String,
}




fn value_to_strings(v: Option<&serde_json::Value>) -> Vec<String> {
    match v {
        Some(serde_json::Value::String(s)) => vec![s.clone()],
        Some(serde_json::Value::Array(arr)) => {
            arr.iter().filter_map(|v| v.as_str().map(str::to_string)).collect()
        }
        _ => vec![],
    }
}

/// The top-level `main` section (distinct from the `main` entry inside `macros`).
#[derive(Deserialize, Serialize, Debug, Clone)]
pub struct MainSection {
    pub vars: Vec<VarInfo>,
    pub formula: String,
}

/// Top-level structure of the concrete specification JSON.
#[derive(Deserialize, Serialize, Debug, Clone)]
pub struct SpecificationInfo {
    pub prime: serde_json::Value,
    pub macros: IndexMap<String, MacroDef>,
    pub main: MainSection,
}

impl SpecificationInfo {
    pub fn prime_as_bigint(&self) -> Result<BigInt, String> {
        let text = match &self.prime {
            serde_json::Value::String(s) => s.clone(),
            serde_json::Value::Number(n) => n.to_string(),
            other => return Err(format!("prime is neither a number nor a string: {}", other)),
        };
        text.parse::<BigInt>()
            .map_err(|e| format!("could not parse prime '{}': {}", text, e))
    }
}

/// Rewrites JSON escaping inside SMT-LIB string literals into the SMT-LIB one.
///
/// llzk writes some annotation values as JSON (`:in-vars-info "{\"%arg0\":
/// [\"v_0\"]}"`), escaping the inner quotes the JSON way. SMT-LIB has no
/// backslash escapes: a quote inside a string is written `""` and a backslash is
/// a plain character, so `\"` CLOSES the string and everything after it is
/// tokenized as if it were code — which is why one such annotation makes the
/// whole specification unparseable (`invalid token '"{\"%arg0\":'`).
///
/// Only the escaping changes, and only inside string literals; comments and
/// `|quoted symbols|` are skipped so a `"` in them doesn't open one. Idempotent:
/// text already in SMT-LIB form has no `\"` left to rewrite, and its `""` are
/// copied through as they are.
pub fn normalize_smt_string_escapes(source: &str) -> String {
    let mut out = String::with_capacity(source.len());
    let mut chars = source.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            // A comment runs to the end of the line: no string starts in it.
            ';' => {
                out.push(c);
                for c2 in chars.by_ref() {
                    out.push(c2);
                    if c2 == '\n' {
                        break;
                    }
                }
            }
            // A quoted symbol can hold a `"` without opening a string literal.
            '|' => {
                out.push(c);
                for c2 in chars.by_ref() {
                    out.push(c2);
                    if c2 == '|' {
                        break;
                    }
                }
            }
            // Inside a string literal, up to and including its closing quote.
            '"' => {
                out.push(c);
                while let Some(c2) = chars.next() {
                    match c2 {
                        '\\' => match chars.peek() {
                            // JSON's `\"` is SMT-LIB's `""`.
                            Some('"') => {
                                chars.next();
                                out.push_str("\"\"");
                            }
                            // JSON's `\\` is a single plain backslash.
                            Some('\\') => {
                                chars.next();
                                out.push('\\');
                            }
                            // Any other backslash is already a plain character
                            // for SMT-LIB, so it stays as it is.
                            _ => out.push('\\'),
                        },
                        // `""` is an escaped quote and the string goes on; a
                        // lone `"` is the end of it.
                        '"' => {
                            if chars.peek() == Some(&'"') {
                                chars.next();
                                out.push_str("\"\"");
                            } else {
                                out.push('"');
                                break;
                            }
                        }
                        _ => out.push(c2),
                    }
                }
            }
            _ => out.push(c),
        }
    }
    out
}

pub fn read_smt_specification<P: AsRef<Path>>(path: P) -> Result<SpecificationInfo, Box<dyn Error>> {
    let file = File::open(path)?;
    let reader = BufReader::new(file);
    let mut u: SpecificationInfo = serde_json::from_reader(reader)?;
    // Done here, once, because every consumer of a `formula` reads it as
    // SMT-LIB text — the preprocessor's parser and the solvers alike — and none
    // of them tolerates llzk's JSON escaping.
    for def in u.macros.values_mut() {
        def.formula = normalize_smt_string_escapes(&def.formula);
    }
    u.main.formula = normalize_smt_string_escapes(&u.main.formula);
    Ok(u)
}

#[cfg(test)]
mod tests {
    use super::normalize_smt_string_escapes;

    #[test]
    fn json_escaped_annotation_becomes_smtlib() {
        let source = r#"(! true :in-vars-info "{\"%arg0\": [\"v_0\", \"v_1\"]}")"#;
        assert_eq!(
            normalize_smt_string_escapes(source),
            r#"(! true :in-vars-info "{""%arg0"": [""v_0"", ""v_1""]}")"#
        );
    }

    #[test]
    fn smtlib_escaping_is_left_alone() {
        // Already valid: `""` is an escaped quote, so this must come out byte
        // for byte as it went in (the normalization runs on every formula,
        // including the ones that never needed it).
        let source = r#"(! true :meta-data "say ""hi""" ) (= v_0 1)"#;
        assert_eq!(normalize_smt_string_escapes(source), source);
    }

    #[test]
    fn normalizing_twice_changes_nothing() {
        let source = r#"(! true :in-vars-info "{\"out\": \"v_2\"}")"#;
        let once = normalize_smt_string_escapes(source);
        assert_eq!(normalize_smt_string_escapes(&once), once);
    }

    #[test]
    fn escaped_backslash_loses_its_escape() {
        // JSON's `\\` is one backslash, which SMT-LIB writes as itself.
        assert_eq!(normalize_smt_string_escapes(r#""a\\b""#), r#""a\b""#);
    }

    #[test]
    fn quotes_outside_string_literals_are_not_touched() {
        // A `"` in a comment or in a |quoted symbol| opens nothing, so the `\"`
        // after it is still outside any string and stays as it is.
        let source = "; a \" comment\n(= |a \" b| 1) \\\"";
        assert_eq!(normalize_smt_string_escapes(source), source);
    }
}

