// Copyright Costa Group UCM.
// SPDX-License-Identifier: Apache-2.0

//! Reformats a raw SMT-LIB formula (a single, extremely long line, as
//! `MacroDef::formula` in the specification JSON comes in) so it can be
//! read by eye: any sub-expression that doesn't fit on one line gets
//! opened up into several, indenting its children, so nested `and`/`ite`s
//! show up as blocks at the same indentation instead of getting lost in
//! the text. It's only for human inspection (checking that the tag tree
//! [`crate::analyze`] produces matches the real formula); it's never
//! parsed again.

#[derive(Debug)]
enum Sexpr {
    Atom(String),
    List(Vec<Sexpr>),
}

// Splits `source` into SMT-LIB tokens: lone parentheses, quoted strings
// (with the `""` escape) and "everything else" (identifiers, numbers,
// operators) cut at whitespace/parentheses. It doesn't understand types or
// syntax beyond this — it's deliberately simple, it's only needed to be
// able to reindent, not to re-interpret the formula.
fn tokenize(source: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let mut chars = source.chars().peekable();
    while let Some(&c) = chars.peek() {
        if c.is_whitespace() {
            chars.next(); // discarded, produces no token.
        } else if c == '(' || c == ')' {
            tokens.push(c.to_string());
            chars.next();
        } else if c == '"' {
            // SMT-LIB strings use `""` to escape a quote inside the string
            // (e.g. inside a :meta-data value).
            let mut tok = String::from("\"");
            chars.next();
            loop {
                match chars.next() {
                    Some('"') => {
                        tok.push('"');
                        if chars.peek() == Some(&'"') {
                            tok.push('"');
                            chars.next();
                        } else {
                            break;
                        }
                    }
                    Some(other) => tok.push(other),
                    None => break,
                }
            }
            tokens.push(tok);
        } else {
            let mut tok = String::new();
            while let Some(&c2) = chars.peek() {
                if c2.is_whitespace() || c2 == '(' || c2 == ')' {
                    break;
                }
                tok.push(c2);
                chars.next();
            }
            tokens.push(tok);
        }
    }
    tokens
}

// Classic recursive-descent parser over the token list: '(' opens a list
// and elements are read (possibly nested lists, via the recursive call)
// until the ')' that closes it; any other token is a lone atom. `pos`
// advances shared across calls (passed by `&mut`).
fn parse_one(tokens: &[String], pos: &mut usize) -> Sexpr {
    match tokens[*pos].as_str() {
        "(" => {
            *pos += 1; // consume '('
            let mut items = Vec::new();
            while tokens[*pos] != ")" {
                items.push(parse_one(tokens, pos));
            }
            *pos += 1; // consume ')'
            Sexpr::List(items)
        }
        atom => {
            *pos += 1;
            Sexpr::Atom(atom.to_string())
        }
    }
}

fn parse_all(tokens: &[String]) -> Vec<Sexpr> {
    let mut pos = 0;
    let mut out = Vec::new();
    while pos < tokens.len() {
        out.push(parse_one(tokens, &mut pos));
    }
    out
}

/// `(! true :meta-data "...")`: an annotation that only names an operation
/// (or documents an alias), without asserting anything — the body is
/// literally `true`. Pure noise to read by eye (in large formulas there are
/// vastly more of these than of the ones that actually assert something).
fn is_trivial_true_tag(expr: &Sexpr) -> bool {
    // Must be a list of at least 2 elements whose first atom is "!" (the
    // annotation operator) and whose second atom is literally "true" (the
    // annotated body). The rest (":meta-data", the string, other possible
    // annotations) doesn't matter here, which is why the pattern uses `..`.
    if let Sexpr::List(items) = expr {
        if let [Sexpr::Atom(head), Sexpr::Atom(body), ..] = items.as_slice() {
            return head == "!" && body == "true";
        }
    }
    false
}

fn is_and_head(items: &[Sexpr]) -> bool {
    matches!(items.first(), Some(Sexpr::Atom(head)) if head == "and")
}

/// Removes, from each `and`, the children that are exactly a trivial `true`
/// tag (see [`is_trivial_true_tag`]); it walks the whole formula, so it
/// also prunes `and`s nested inside an `ite`, etc.
///
/// If only one child is left after pruning, the `and` no longer groups
/// anything and gets discarded (that child is returned directly) so as not
/// to leave `(and (and X))` hanging; if none are left, an empty `and` is `true`.
fn prune_trivial_true_tags(expr: &Sexpr) -> Sexpr {
    match expr {
        Sexpr::Atom(a) => Sexpr::Atom(a.clone()),
        Sexpr::List(items) => {
            let and_head = is_and_head(items);
            // `items` is walked with its index so the head (index 0, the
            // "and"/operator itself — never pruned) can be told apart from
            // the arguments (index > 0). An argument is dropped IF AND
            // ONLY IF this list is an "and" AND that specific argument is
            // a trivial tag; in any other case (it isn't "and", or it is
            // "and" but the argument isn't trivial) it's kept and
            // processed recursively (to also prune inside it, e.g. an
            // "and" nested in an "ite" branch).
            let mut pruned: Vec<Sexpr> = items
                .iter()
                .enumerate()
                .filter(|(i, item)| !(and_head && *i > 0 && is_trivial_true_tag(item)))
                .map(|(_, item)| prune_trivial_true_tags(item))
                .collect();
            if and_head {
                match pruned.len() {
                    // Only the "and" head is left (ALL arguments were
                    // pruned): an empty "and" is equivalent to "true".
                    1 => return Sexpr::Atom("true".to_string()),
                    // Head + a single surviving argument: the "and" no
                    // longer groups anything, so the wrapper gets
                    // discarded and that argument is returned directly
                    // (avoids leaving "(and X)" hanging after pruning its siblings).
                    2 => return pruned.remove(1),
                    _ => {}
                }
            }
            Sexpr::List(pruned)
        }
    }
}

fn render_flat(expr: &Sexpr, out: &mut String) {
    match expr {
        Sexpr::Atom(a) => out.push_str(a),
        Sexpr::List(items) => {
            out.push('(');
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    out.push(' ');
                }
                render_flat(item, out);
            }
            out.push(')');
        }
    }
}

fn render_pretty(expr: &Sexpr, indent: usize, max_width: usize, out: &mut String) {
    match expr {
        Sexpr::Atom(a) => out.push_str(a),
        Sexpr::List(items) => {
            // First the single-line version (`render_flat`) is tried and,
            // if it fits within `max_width`, it's used as-is — so small
            // sub-expressions (e.g. "(ff.mul v_0 1)") don't get
            // unnecessarily fragmented even if the whole formula is huge.
            let mut flat = String::new();
            render_flat(expr, &mut flat);
            if flat.len() <= max_width {
                out.push_str(&flat);
                return;
            }
            if items.is_empty() {
                out.push_str("()");
                return;
            }
            // Doesn't fit on one line: it's opened up into several, one
            // element per line, indented one level more than the parent.
            out.push('(');
            // The head (the operator: "and", "ite", "=", ...) stays on the
            // same line as the opening parenthesis.
            render_pretty(&items[0], indent + 1, max_width, out);
            for item in &items[1..] {
                out.push('\n');
                out.push_str(&"  ".repeat(indent + 1));
                render_pretty(item, indent + 1, max_width, out);
            }
            out.push(')');
        }
    }
}

/// Reformats `source` (an SMT-LIB formula, typically `MacroDef::formula`)
/// into several lines indented by parenthesis depth, so it's easy to see
/// at a glance where the nested `and`/`ite`s are. Sub-expressions that
/// already fit within `max_width` characters are left on a single line.
///
/// `hide_trivial_true` (the normal case) strips out, before printing, the
/// `(! true :meta-data "...")`s that hang directly off an `and`: they're
/// pure aliases/names with no real assertion, and in large formulas they
/// vastly outnumber the tags that do assert something — eyeballing that
/// everything is correct is unfeasible if they all have to be read.
pub fn pretty_print_smt(source: &str, max_width: usize, hide_trivial_true: bool) -> String {
    let tokens = tokenize(source);
    let exprs = parse_all(&tokens);
    let exprs: Vec<Sexpr> = if hide_trivial_true {
        exprs.iter().map(prune_trivial_true_tags).collect()
    } else {
        exprs
    };
    let mut out = String::new();
    for (i, expr) in exprs.iter().enumerate() {
        if i > 0 {
            out.push('\n');
        }
        render_pretty(expr, 0, max_width, &mut out);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn keeps_short_expressions_on_one_line() {
        let formatted = pretty_print_smt("(= v_1 (ff.mul v_0 1))", 80, false);
        assert_eq!(formatted, "(= v_1 (ff.mul v_0 1))");
    }

    #[test]
    fn breaks_long_and_into_one_child_per_line() {
        let source = r#"(and (! true :meta-data "a") (and (! true :meta-data "b") (! true :meta-data "c")))"#;
        // Each "(! true :meta-data \"x\")" is 23 characters: with max_width
        // 30 they stay on one line, but the "and" wrapping them (53+
        // characters flat) is forced to split one per line.
        let formatted = pretty_print_smt(source, 30, false);
        let expected = "(and\n  (! true :meta-data \"a\")\n  (and\n    (! true :meta-data \"b\")\n    (! true :meta-data \"c\")))";
        assert_eq!(formatted, expected);
    }

    #[test]
    fn round_trips_escaped_quotes_in_meta_data() {
        let source = r#"(! true :meta-data "say ""hi""")"#;
        let formatted = pretty_print_smt(source, 80, false);
        assert_eq!(formatted, source);
    }

    #[test]
    fn hides_trivial_true_tags_by_default_when_requested() {
        let source = r#"(and (! true :meta-data "a") (and (! (= v_1 v_0) :meta-data "b") (! true :meta-data "c")))"#;
        let formatted = pretty_print_smt(source, 30, true);
        // After pruning "a" and "c" (the two "true"s), both the inner and
        // outer "and" are left with a single child and get discarded
        // entirely: only tag "b" survives, the only one that asserts anything.
        let expected = "(! (= v_1 v_0) :meta-data \"b\")";
        assert_eq!(formatted, expected);
    }

    #[test]
    fn keeps_true_tags_when_hide_trivial_true_is_false() {
        let source = r#"(and (! true :meta-data "a") (! (= v_1 v_0) :meta-data "b"))"#;
        let formatted = pretty_print_smt(source, 80, false);
        assert_eq!(formatted, source);
    }

    #[test]
    fn does_not_touch_true_outside_an_and() {
        // "true" that isn't hanging directly off an "and" (here, inside an
        // "ite") must not be touched: pruning only applies to "and" children.
        let source = r#"(ite (= v_0 1) true (= v_1 v_2))"#;
        let formatted = pretty_print_smt(source, 80, true);
        assert_eq!(formatted, source);
    }

    #[test]
    fn and_of_only_trivial_tags_collapses_to_true() {
        let source = r#"(and (! true :meta-data "a") (! true :meta-data "b"))"#;
        let formatted = pretty_print_smt(source, 80, true);
        assert_eq!(formatted, "true");
    }
}
