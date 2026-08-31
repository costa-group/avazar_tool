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
use mimalloc::MiMalloc;
use serde::{Serialize};

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

mod argument_parsing;
mod smt_hybrid;
pub mod decompose_circuit;


use utils::structure::StructureReader;
use crate::decompose_circuit::decompose_circuit;
use crate::argument_parsing::{Args};
use crate::smt_hybrid::{
    circuit_and_smt_hybrid_clustering_into_structurereader,
    structure_driven_circuit_and_smt_hybrid_clustering_into_structurereader};
use utils::small_utilities::{DecomposeOptions, FileType};
use circuits_constraints_and_algebra::r1cs::{R1CSData};
use circuits_constraints_and_algebra::generic::{AIRDataWrapper};
use circuits_constraints_and_algebra::acir::{ACIRCircuit};
use circuits_constraints_and_algebra::constraint::Constraint;
use circuits_constraints_and_algebra::circuit::Circuit;
use circuits_constraints_and_algebra::smt_formula::{Formula, parse_formula};

fn main() {
    let args = Args::parse();
    let result = start(args);
    if result.is_err() {
        eprintln!("{:?}", result);
        eprintln!("{}", Colour::Red.paint("previous errors were found"));
        std::process::exit(1);
    } else {
        println!("{}", Colour::Green.paint("Everything went okay, clustered"));
        //std::process::exit(0);
    }
}

fn write_output_into_file<P: AsRef<Path>>(path: P, result: &Output<StructureReader>) -> Result<(), Box<dyn Error>> {
    // Open the file in read-only mode with buffer.

    let file = File::create(path)?;
    let mut writer = BufWriter::new(file);

    // Write the result.
    let value = serde_json::to_string_pretty(result)?;
    writer.write(value.as_bytes())?;
    writer.flush()?;
    Ok(())
}

use crate::smt_hybrid::HybridClusteringOptions;
use crate::smt_hybrid::TiebreakingStrategy;
use crate::smt_hybrid::HybridClusteringMethodOptions;
use crate::smt_hybrid::HybridClusteringMethods;
use std::path::PathBuf;

#[derive(Serialize)]
#[serde(untagged)]
enum Output<T> {Single(T), Pair(T, T), StructuredPair(Vec<(T,T)>)}

fn start(args: Args) -> Result<(), Box<dyn Error>> {
    
    let existing_partition: Option<Vec<Vec<usize>>> =
     args.existing_partition.map(
        |path| serde_json::from_reader(
                std::fs::File::open(path).expect("Error when attempting to open file")
            ).expect("Error attempting to deserialize partition")
    );
    // Pass circuit
    let circuit_parsing_timer = Instant::now();

    let decompose_options = DecomposeOptions {
        resolution: args.resolution, 
        target_size: args.target_size, 
        leiden_max_iterations: args.leiden_max_iterations, 
        equivalence_mode: args.equivalence_mode, 
        graph_backend: args.graph_backend, preprocessing: args.preprocessing, 
        minimum_equivalence_size: args.minimum_equivalence_size, 
        hierarchy_mode: args.hierarchy_mode,
        equivalence_comparison_budget: args.equivalence_comparison_budget, 
        existing_partition: existing_partition, debug: args.debug,
        extract_raw_partition: args.extract_raw_partition,
        clique_cluster_size: args.clique_cluster_size,
        dead_ends_as_outputs: args.dead_ends_as_outputs,
        manually_check_acyclic: args.manually_check_acyclic,

        ..Default::default()
    };

    let hybrid_clustering_options = HybridClusteringOptions {
        guide_decompose_options: decompose_options.clone(),
        hybrid_decompose_method: HybridClusteringMethods::default(),
        hybrid_decompose_options: HybridClusteringMethodOptions {tiebreaking_strategy: TiebreakingStrategy::default(), recipient_requires_subsets: true} ,
        manually_check_acyclic: args.manually_check_acyclic,
    };
    
    let mut structure_info: Option<StructureReader> = None;
    if args.circuit_structure.is_some() {
        use std::io::BufReader;
        let file = File::open(args.circuit_structure.as_ref().unwrap())?;
        let reader = BufReader::new(file);
        structure_info = Some(serde_json::from_reader(reader).unwrap());
    }

    let selector: usize = if args.smt_formula.is_none() {0} else if args.smt_formula.is_some() && args.circuit_structure.is_none() {1} else if args.smt_formula.is_some() && args.circuit_structure.is_some() {2} else {3};

    fn circuit_to_output<'a, C: Constraint + 'a, S: Circuit<C> + 'a>(
        selector: usize, circuit: &S, smt_path: &Option<PathBuf>, structure_info: &Option<StructureReader>, decompose_options: DecomposeOptions<'a>, hybrid_clustering_options: HybridClusteringOptions<'a>, debug: usize
    ) -> Output<StructureReader> {
        let mut smt: Option<Formula> = None;
        if smt_path.is_some() {
            smt = Some(parse_formula(smt_path.as_ref().unwrap(), circuit.prime(), circuit.get_input_signals().collect(), circuit.get_output_signals().collect(), None).unwrap_or_else(|e| panic!("Error when parsing SMT {e}")));
        }

        match selector {
            0 => Output::Single(decompose_circuit(circuit, decompose_options)),
            1 => {
                let (smt_clustering, circ_clustering) = circuit_and_smt_hybrid_clustering_into_structurereader(smt.as_ref().unwrap(), circuit, hybrid_clustering_options, debug);
                Output::Pair(smt_clustering, circ_clustering)
            },
            2 => Output::StructuredPair(structure_driven_circuit_and_smt_hybrid_clustering_into_structurereader(circuit, structure_info.as_ref().unwrap(), smt.as_ref().unwrap(), hybrid_clustering_options, debug)),
            _ => unreachable!(),
        }
    }

    
    // TODO: refactor some code to make the dyn work -- hmm looks like dyn just won't work so its this bodge forever
    let result: Output<StructureReader> = match args.file_type {
        FileType::R1CS => {
            let circuit = R1CSData::parse_file(&args.filepath)?;
            if args.debug > 0 { println!("Took {:?} to parse", circuit_parsing_timer.elapsed()); }
            circuit_to_output(selector, &circuit, &args.smt_formula, &structure_info, decompose_options, hybrid_clustering_options, args.debug)
        },
        FileType::ACIR =>{
            let circuit = ACIRCircuit::parse_file(&args.filepath)?;
            if args.debug > 0 { println!("Took {:?} to parse", circuit_parsing_timer.elapsed()); }
            circuit_to_output(selector, &circuit, &args.smt_formula, &structure_info, decompose_options, hybrid_clustering_options, args.debug)
        },
        FileType::Generic =>{
            let circuit = AIRDataWrapper::parse_file(&args.filepath)?;
            if args.debug > 0 { println!("Took {:?} to parse", circuit_parsing_timer.elapsed()); }
            circuit_to_output(selector, &circuit, &args.smt_formula, &structure_info, decompose_options, hybrid_clustering_options, args.debug)
        }
    };
    
    let filepath_rev: String = args.filepath.chars().rev().collect();
    let circname: String = filepath_rev[filepath_rev.find('.').expect("filepath didn't have filetype period")+1..filepath_rev.find('/').unwrap_or(filepath_rev.len())].chars().rev().collect();
    
    use utils::small_utilities::{GraphBackend, EquivalenceMode};

    let mut outfile: String = format!("{}/{}", args.out_directory, circname);
    if args.graph_backend != GraphBackend::GraphRS {outfile.push_str(&format!("_{}", args.graph_backend));}
    if args.equivalence_mode != EquivalenceMode::None {outfile.push_str(&format!("_{}", args.equivalence_mode));}
    if args.target_size.is_some() {outfile.push_str(&format!("_t{}", args.target_size.unwrap()));}
    if args.clique_cluster_size.is_some() {outfile.push_str(&format!("_c{}", args.clique_cluster_size.unwrap()));}
    if args.dead_ends_as_outputs {outfile.push_str(&"_deadends");}
    outfile.push_str(&".json");

    write_output_into_file(outfile, &result)
}
