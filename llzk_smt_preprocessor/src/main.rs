// Copyright Costa Group UCM.
// SPDX-License-Identifier: Apache-2.0

//! CLI del crate `llzk_smt_preprocessor`: analiza un fichero SMT-LIB y vuelca el agrupado de
//! parámetros por `:meta-data` en JSON (modo plano o anidado).

use std::fs;

use clap::Parser as ClapParser;
use llzk_smt_preprocessor::{analyze, to_json_flat, to_json_nested};

#[derive(Clone, Debug, clap::ValueEnum)]
enum Mode {
    /// Por fórmula de nivel superior, todas las variables (agregadas).
    Flat,
    /// Respeta la estructura anidada de tags.
    Nested,
}

#[derive(ClapParser, Debug)]
#[command(about = "Agrupa parámetros de macro por :meta-data (modos flat / nested)")]
struct Cli {
    /// Fichero SMT-LIB de entrada
    file: String,
    /// Modo de salida
    #[arg(long, value_enum, default_value = "flat")]
    mode: Mode,
    /// Habilita los comentarios de bloque `#| ... |#` de SMT-LIB 2.7
    #[arg(long)]
    block_comments: bool,
}

fn main() {
    let args = Cli::parse();
    let source = fs::read_to_string(&args.file).expect("No se pudo leer el fichero de entrada");

    match analyze(&source, args.block_comments) {
        Ok(macros) => {
            let json = match args.mode {
                Mode::Flat => to_json_flat(&macros),
                Mode::Nested => to_json_nested(&macros),
            };
            println!("{}", json);
        }
        Err(e) => {
            eprintln!("Error de parseo: {}", e);
            std::process::exit(1);
        }
    }
}
