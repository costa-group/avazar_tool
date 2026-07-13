use ansi_term::Colour;
use clap::Parser;
use std::fs::File;
use std::io::{BufWriter};
use std::path::Path;
use std::io::Write;
use std::error::Error;
use std::time::{Instant};

use utils::small_utilities::{FileType, DecomposeOptions};
use circuits_constraints_and_algebra::r1cs::{R1CSData};
use circuits_constraints_and_algebra::generic::{AIRDataWrapper};
use circuits_constraints_and_algebra::acir::{ACIRCircuit};
use circuits_constraints_and_algebra::circuit::Circuit;
use zkgenver::determinism::determinism_check::{print_pretty_results, DeterminismOptions};

use crate::argument_parsing::{Args};
use crate::integrated_clustering::decompose_circuit_and_check_determinism;
use crate::hierarchy_solver::HierarchyOptions;

mod argument_parsing;
mod integrated_clustering;
mod hierarchy_solver;

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
        graph_backend: args.graph_backend, preprocessing: args.preprocessing, 
        existing_partition: existing_partition, debug: args.debug,
        extract_raw_partition: args.extract_raw_partition,
        clique_cluster_size: args.clique_cluster_size,

        ..Default::default()
    };

    let hierarchy_options = HierarchyOptions {
        property: args.property,
        preprocessing: args.hierarchy_preprocessing,
        solver_target: args.solver_target,
        solver_option: args.solver_option,
        dag_extension_method: args.dag_extension_method,
        num_cores: args.hierarchy_num_cores,
        timeout: args.hierarchy_timeout,
        debug: args.debug
    };

    let original_file = args.filepath
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("")
        .to_string();

    let determinism_options = DeterminismOptions {

        original_structure: args.original_structure,
        timeout: args.determinism_timeout,
        include_niaz3_in_all: args.include_niaz3_in_all,
        apply_deduction_assigned: args.apply_deduction_assigned,
        apply_predecessors: args.apply_predecessors,
        apply_bidirectional: args.apply_bidirectional,
        equivalence_mode: args.equivalence_mode,
        clustering_size: args.clustering_size,
        target_size: args.target_size.unwrap_or(0 as f64) as usize,
        solver_option: args.solver_option,
        extra_rounds: args.extra_rounds,
        limit_size: args.limit_size,
        verbose: args.debug > 1,
        original_file: &original_file
    };

    
    // TODO: refactor some code to make the dyn work
    let result = match args.file_type {
        FileType::R1CS => {
            let circuit = R1CSData::parse_file(&args.filepath.to_str().expect("not valid UTF-8 path"))?;
            if args.debug > 0 { println!("Took {:?} to parse", circuit_parsing_timer.elapsed()); }
            decompose_circuit_and_check_determinism(&circuit, decompose_options, hierarchy_options, determinism_options, args.extract_integrated_hierarchy)
            },
        FileType::ACIR =>{
            panic!("Encoding is not yet implemented for the Acir filetype");
            // let circuit = ACIRCircuit::parse_file(&args.filepath)?;
            // if args.debug > 0 { println!("Took {:?} to parse", circuit_parsing_timer.elapsed()); }
            // decompose_circuit_and_check_determinism(&circuit, decompose_options)
            }
        FileType::Generic =>{
            panic!("Encoding is not yet implemented for the Generic filetype");
            // let circuit = AIRDataWrapper::parse_file(&args.filepath)?;
            // if args.debug > 0 { println!("Took {:?} to parse", circuit_parsing_timer.elapsed()); }
            // decompose_circuit_and_check_determinism(&circuit, decompose_options)
            }
    };
    
    // let filepath_rev: String = args.filepath.chars().rev().collect();
    // let circname: String = filepath_rev[filepath_rev.find('.').expect("filepath didn't have filetype period")+1..filepath_rev.find('/').unwrap_or(filepath_rev.len())].chars().rev().collect();
    
    // use utils::small_utilities::{GraphBackend};

    // let mut outfile: String = format!("{}/{}", args.out_directory, circname);
    // if args.graph_backend != GraphBackend::GraphRS {outfile.push_str(&format!("_{}", args.graph_backend));}
    // if args.target_size.is_some() {outfile.push_str(&format!("_t{}", args.target_size.unwrap()));}
    // if args.clique_cluster_size.is_some() {outfile.push_str(&format!("_c{}", args.clique_cluster_size.unwrap()));}
    // outfile.push_str(&".json");

    print_pretty_results(&result);

    Ok(())
}