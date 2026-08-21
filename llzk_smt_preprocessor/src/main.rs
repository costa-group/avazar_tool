// Copyright Costa Group UCM.
// SPDX-License-Identifier: Apache-2.0

//! CLI for the `llzk_smt_preprocessor` crate: analyzes the grouping of
//! parameters by `:meta-data` into JSON (flat or nested mode).
//!
//! `file` accepts two formats:
//! - the specification JSON that `zk-genver` already consumes
//!   (`--check-correctness`, e.g. `results/iszero.json`): a map of macros,
//!   each already carrying its `formula` and its `vars_info`. This is the normal case.
//! - if it isn't a valid specification JSON, a raw `.smt2` with one or
//!   several `define-fun`s (the old mode, without `vars_info`).
//!
//! Resolving the variables to r1cs signal ids also requires
//! `--correspondence` (the `name_to_signal`, e.g. `results/iszero_signals.json`)
//! and `--structure` (the `StructureInfo`, e.g. `results/iszero_structure.json`):
//! with them, the component graph is walked exactly like
//! `zk-genver::correctness::processing_correctness_utils::process_correspondence_node_macro`
//! does, to know which macro and which dotted instance prefix (`"main"`,
//! `"main.sub3"`, ...) each node corresponds to.

use std::fs;

use clap::Parser as ClapParser;
use llzk_smt_preprocessor::graph::resolve_full;
use llzk_smt_preprocessor::pretty::pretty_print_smt;
use llzk_smt_preprocessor::resolve::{to_json_flat_resolved, to_json_nested_resolved};
use llzk_smt_preprocessor::{analyze, analyze_specification, to_json_flat, to_json_nested};
use utils::read_correspondence::read_signal_correspondence;
use utils::read_specification::read_smt_specification;
use utils::structure::read_structure;

#[derive(Clone, Debug, clap::ValueEnum)]
enum Mode {
    /// For each top-level formula, all the variables (aggregated).
    Flat,
    /// Preserves the nested tag structure.
    Nested,
}

#[derive(ClapParser, Debug)]
#[command(about = "Groups macro parameters by :meta-data (flat / nested modes)")]
struct Cli {
    /// Specification JSON (e.g. results/iszero.json), or failing that, a
    /// raw .smt2.
    file: String,
    /// Output mode (applies both to the raw and the already-resolved
    /// output, if --correspondence and --structure are passed)
    #[arg(long, value_enum, default_value = "flat")]
    mode: Mode,
    /// Enables SMT-LIB 2.7's `#| ... |#` block comments (only applies if
    /// `file` is a raw .smt2)
    #[arg(long)]
    block_comments: bool,
    /// r1cs signal correspondence JSON (dotted name -> id), e.g.
    /// results/iszero_signals.json.
    #[arg(long, requires = "structure")]
    correspondence: Option<String>,
    /// Circuit structure JSON (the same StructureInfo zk-genver uses), e.g.
    /// results/iszero_structure.json. Together with --correspondence, it's
    /// used to walk the component graph and know which macro and which
    /// instance prefix each node gets.
    #[arg(long, requires = "correspondence")]
    structure: Option<String>,
    /// Maximum line width when printing each macro's formula (to stderr)
    /// before the JSON, to eyeball that the tags match the real `and`/`ite`s.
    #[arg(long, default_value_t = 100)]
    formula_width: usize,
    /// When printing the formula (to stderr), don't hide the `(! true
    /// :meta-data "...")` tags (hidden by default: they're pure noise, they
    /// only document an alias/name without asserting anything, and in large
    /// formulas they're the majority compared to the ones that do assert something).
    #[arg(long)]
    show_trivial_tags: bool,
    /// In the already-resolved JSON, don't hide the `v_i`s that couldn't be
    /// tied to any r1cs signal (hidden by default: they're the majority in
    /// large macros and make it impossible to eyeball whether the ones that
    /// do matter are correct).
    #[arg(long)]
    show_unresolved: bool,
}

fn main() {
    let args = Cli::parse();

    let (macros, macro_defs) = match read_smt_specification(&args.file) {
        Ok(spec) => {
            let entries = analyze_specification(&spec.macros).unwrap_or_else(|e| {
                eprintln!("Error de parseo: {}", e);
                std::process::exit(1);
            });
            (entries, Some(spec.macros))
        }
        Err(_) => {
            let source =
                fs::read_to_string(&args.file).expect("could not read the input file");
            let entries = analyze(&source, args.block_comments).unwrap_or_else(|e| {
                eprintln!("Error de parseo: {}", e);
                std::process::exit(1);
            });
            (entries, None)
        }
    };

    // Dumps each reformatted formula (to stderr, so as not to pollute
    // stdout's JSON), so it's possible to eyeball that the tags/vars coming
    // out in the JSON match the formula's real `and`/`ite`s.
    if let Some(macro_defs) = &macro_defs {
        for (name, def) in macro_defs {
            eprintln!("=== {} ===", name);
            eprintln!(
                "{}",
                pretty_print_smt(&def.formula, args.formula_width, !args.show_trivial_tags)
            );
            eprintln!();
        }
    }

    match (&args.correspondence, &args.structure, &macro_defs) {
        // Normal case: --correspondence + --structure are present AND
        // `file` was the specification JSON (macro_defs = Some) -> resolve
        // everything to r1cs signal ids.
        (Some(correspondence_path), Some(structure_path), Some(macro_defs)) => {
            let (_, name_to_signal) = read_signal_correspondence(correspondence_path)
                .expect("could not read the signal correspondence JSON");
            let structure =
                read_structure(structure_path).expect("could not read the structure JSON");

            let resolved = resolve_full(macro_defs, &structure, &name_to_signal)
                .unwrap_or_else(|e| {
                    eprintln!("Error al resolver: {}", e);
                    std::process::exit(1);
                });

            let json = match args.mode {
                Mode::Flat => to_json_flat_resolved(&resolved, args.show_unresolved),
                Mode::Nested => to_json_nested_resolved(&resolved, args.show_unresolved),
            };
            println!("{}", json);
        }
        // Without --correspondence or --structure: dump the raw tag tree
        // (SMT names, without resolving to signal ids).
        (None, None, _) => {
            let json = match args.mode {
                Mode::Flat => to_json_flat(&macros),
                Mode::Nested => to_json_nested(&macros),
            };
            println!("{}", json);
        }
        // Any other combination (one of the two flags without the other,
        // or both but `file` was a raw .smt2 without vars_info): there's no
        // way to resolve anything, so warn and stop.
        _ => {
            eprintln!(
                "--correspondence and --structure only make sense together, and only when `file` is the specification JSON (the one with vars_info)"
            );
            std::process::exit(1);
        }
    }
}
