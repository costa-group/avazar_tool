/*
Bare Bones Version -- DONE

TODO: Equivalence Implementation
TODO: Implement Own Graph Version
TODO: Better Error Handling (using Result and the like)

*/
use ansi_term::Colour;
use std::fs::File;
use std::io::{BufWriter};
use std::path::Path;
use std::io::Write;
use std::error::Error;
use std::time::{Instant};
use clap::Parser;

mod leiden_clustering;
mod argument_parsing;
pub mod decompose_circuit;


use crate::decompose_circuit::{StructureReader, decompose_circuit};
use crate::argument_parsing::{Args};
use utils::read_r1cs::R1CSData;
use circuits_and_constraints::circuit::Circuit;

fn main() {
    let args = Args::parse();
    let result = start(args);
    if result.is_err() {
        eprintln!("{}", Colour::Red.paint("previous errors were found"));
        std::process::exit(1);
    } else {
        println!("{}", Colour::Green.paint("Everything went okay, clustered"));
        //std::process::exit(0);
    }
}

fn write_output_into_file<P: AsRef<Path>>(path: P, result: &StructureReader) -> Result<(), Box<dyn Error>> {
    // Open the file in read-only mode with buffer.

    let file = File::create(path)?;
    let mut writer = BufWriter::new(file);

    // Write the result.
    let value = serde_json::to_string_pretty(result)?;
    writer.write(value.as_bytes())?;
    writer.flush()?;
    Ok(())
}

fn start(args: Args) -> Result<(), Box<dyn Error>> {
    // Pass circuit
    let circuit_parsing_timer = Instant::now();
    
    let mut r1cs: R1CSData = R1CSData::new();
    r1cs.parse_file(&args.filepath);
    println!("Took {:?} to parse", circuit_parsing_timer.elapsed());
    
    let result = decompose_circuit(&r1cs, args.resolution, args.target_size, args.equivalence_mode, args.graph_backend, args.debug);

    let filepath_rev: String = args.filepath.chars().rev().collect();
    let circname: String = filepath_rev[filepath_rev.find('.').expect("filepath didn't have filetype period")+1..filepath_rev.find('/').unwrap_or(filepath_rev.len())].chars().rev().collect();
    
    let outfile: String = format!("{}/{}_{}_{}.json", args.out_directory, circname, args.graph_backend, args.equivalence_mode);

    write_output_into_file(outfile, &result)
}
