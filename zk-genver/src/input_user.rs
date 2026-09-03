use std::path::PathBuf;
use solvers_interface::PossibleSolver;

use crate::BigInt;


pub struct Input {
    pub input_r1cs: PathBuf,
    pub input_structure: Option<PathBuf>,
    pub input_correspondence: Option<PathBuf>,

    pub timeout: u64,
    pub original_structure: Option<PathBuf>,
    pub solver_option: PossibleSolver,
    pub flag_verbose: bool,
    pub apply_deduction_assigned: bool,
    pub include_niaz3_in_all: bool,
    pub apply_predecessors: bool,
    pub apply_bidirectional: bool,
    pub allow_empty_clusters: bool,
    pub smt_signal_names: bool,
    pub no_clustering: bool,
    pub prime: BigInt,
    pub clustering_size: usize,
    pub equivalence_mode: usize,
    pub target_size: usize,
    pub limit_size: usize,
    pub extra_rounds: usize,

    pub check_equivalence: Option<PathBuf>,
    pub check_correctness: Option<PathBuf>,
    pub check_semantic_equivalence: Option<PathBuf>,
    pub resolved_formula: Option<PathBuf>,
    pub report_output: Option<PathBuf>,
    pub dump_dir: Option<PathBuf>,
    pub instance_adjacency: bool,
}


impl Input {
    pub fn new() -> Result<Input, ()> {
        let matches = input_processing::view();
        let input_r1cs = input_processing::get_input_r1cs(&matches)?;
        let input_structure = input_processing::get_input_structure(&matches)?;
        let input_correspondence = input_processing::get_input_correspondence(&matches)?;
        let timeout =  input_processing::get_timeout(&matches)?;
        let original_structure = input_processing::get_original_structure(&matches)?;
        let solver_option = input_processing::get_solver(&matches)?;
        let flag_verbose =  input_processing::get_flag_verbose(&matches);
        let prime = input_processing::get_prime(&matches)?;
        let clustering_size = input_processing::get_clustering_size(&matches)?;
        let desactivate_deduction_assigned = input_processing::get_apply_deduction_assigned(&matches);
        let include_niaz3_in_all = input_processing::get_include_niaz3_in_all(&matches);
        let apply_predecessors = input_processing::get_apply_predecessors(&matches);
        let apply_bidirectional = input_processing::get_apply_bidirectional(&matches);
        let allow_empty_clusters = matches.is_present("allow_empty_clusters");
        let smt_signal_names = matches.is_present("smt_signal_names");
        let no_clustering = matches.is_present("no_clustering");

        let equivalence_mode = input_processing::get_equivalence_mode(&matches)?;
        let target_size = input_processing::get_target_size(&matches)?;
        let extra_rounds = input_processing::get_extra_rounds(&matches)?;
        let check_equivalence = input_processing::get_check_equivalence(&matches)?;
        let check_correctness = input_processing::get_check_correctness(&matches)?;
        let check_semantic_equivalence = input_processing::get_check_semantic_equivalence(&matches)?;
        let resolved_formula = input_processing::get_resolved_formula(&matches)?;

        let limit_size = input_processing::get_limit_size(&matches)?;
        let report_output = input_processing::get_report_output(&matches);
        let dump_dir = matches.value_of("dump_dir").map(PathBuf::from);
        let instance_adjacency = matches.is_present("instance_adjacency");

        Result::Ok(Input {
            input_r1cs,
            input_structure,
            input_correspondence,
            timeout,
            original_structure,
            solver_option,
            flag_verbose,
            prime,
            clustering_size,
            apply_deduction_assigned: !desactivate_deduction_assigned,
            include_niaz3_in_all,
            apply_predecessors,
            apply_bidirectional,
            allow_empty_clusters,
            smt_signal_names,
            no_clustering,
            equivalence_mode,
            target_size,
            extra_rounds,
            limit_size,
            check_equivalence,
            check_correctness,
            check_semantic_equivalence,
            resolved_formula,

            report_output,
            dump_dir,
            instance_adjacency,
        })
    }
}


mod input_processing {
    use ansi_term::Colour;
    use clap::{App, Arg, ArgMatches};
    use solvers_interface::PossibleSolver;
    use std::path::{Path, PathBuf};
    use crate::BigInt;

    pub fn get_input_r1cs(matches: &ArgMatches) -> Result<PathBuf, ()> {
        let route = Path::new(matches.value_of("input").unwrap()).to_path_buf();
        if route.is_file() {
            Result::Ok(route)
        } else {
            let route = if route.to_str().is_some() { ": ".to_owned() + route.to_str().unwrap()} else { "".to_owned() };
            Result::Err(eprintln!("{}", Colour::Red.paint("Input file does not exist".to_owned() + &route)))
        }
    }

    pub fn get_input_structure(matches: &ArgMatches) -> Result<Option<PathBuf>, ()> {
        if matches.is_present("input_structure"){
            let route = Path::new(matches.value_of("input_structure").unwrap()).to_path_buf();
            if route.is_file() {
                Result::Ok(Some(route))
            } else {
                Result::Err(eprintln!("{}", Colour::Red.paint("invalid input structure")))
            }
        } else{
            Ok(None)
        }
    }

    pub fn get_input_correspondence(matches: &ArgMatches) -> Result<Option<PathBuf>, ()> {
        if matches.is_present("correspondence"){
            let route = Path::new(matches.value_of("correspondence").unwrap()).to_path_buf();
            if route.is_file() {
                Result::Ok(Some(route))
            } else {
                Result::Err(eprintln!("{}", Colour::Red.paint("invalid input structure")))
            }
        } else{
            Ok(None)
        }
    }

    pub fn get_check_equivalence(matches: &ArgMatches) -> Result<Option<PathBuf>, ()> {
        if matches.is_present("check_equivalence"){
            let route = Path::new(matches.value_of("check_equivalence").unwrap()).to_path_buf();
            if route.is_file() {
                Result::Ok(Some(route))
            } else {
                Result::Err(eprintln!("{}", Colour::Red.paint("invalid file to check equivalence")))
            }
        } else{
            Ok(None)
        }
    }

    pub fn get_check_correctness(matches: &ArgMatches) -> Result<Option<PathBuf>, ()> {
        if matches.is_present("check_correctness"){
            let route = Path::new(matches.value_of("check_correctness").unwrap()).to_path_buf();
            if route.is_file() {
                Result::Ok(Some(route))
            } else {
                Result::Err(eprintln!("{}", Colour::Red.paint("invalid file to check correctness")))
            }
        } else{
            Ok(None)
        }
    }

    pub fn get_resolved_formula(matches: &ArgMatches) -> Result<Option<PathBuf>, ()> {
        if matches.is_present("resolved_formula") {
            let route = Path::new(matches.value_of("resolved_formula").unwrap()).to_path_buf();
            if route.is_file() {
                Result::Ok(Some(route))
            } else {
                Result::Err(eprintln!("{}", Colour::Red.paint("Resolved formula file does not exist: ".to_owned() + &route.display().to_string())))
            }
        } else {
            Result::Ok(None)
        }
    }

    pub fn get_check_semantic_equivalence(matches: &ArgMatches) -> Result<Option<PathBuf>, ()> {
        if matches.is_present("check_semantic_equivalence"){
            let route = Path::new(matches.value_of("check_semantic_equivalence").unwrap()).to_path_buf();
            if route.is_file() {
                Result::Ok(Some(route))
            } else {
                Result::Err(eprintln!("{}", Colour::Red.paint("invalid file to check semantic equivalence")))
            }
        } else{
            Ok(None)
        }
    }

    pub fn get_original_structure(matches: &ArgMatches) -> Result<Option<PathBuf>, ()> {
        if matches.is_present("original_structure"){
            let route = Path::new(matches.value_of("original_structure").unwrap()).to_path_buf();
            if route.is_file() {
                Result::Ok(Some(route))
            } else {
                Result::Err(eprintln!("{}", Colour::Red.paint("invalid original structure")))
            }
        } else{
            Ok(None)
        }
    }

    pub fn get_timeout(matches: &ArgMatches) -> Result<u64, ()> {
        let timeout_argument = matches.value_of("timeout").unwrap();
        let timeout = u64::from_str_radix(timeout_argument, 10);
        if let Result::Ok(time) = timeout { 
           Ok(time)
        }
        else { 
            Result::Err(eprintln!("{}", Colour::Red.paint("invalid timeout")))
        }
    }

    pub fn get_flag_verbose(matches: &ArgMatches) -> bool {
        matches.is_present("verbose")
    }

    pub fn get_apply_deduction_assigned(matches: &ArgMatches) -> bool {
        matches.is_present("desactivate_deduction_assigned")
    }

    pub fn get_include_niaz3_in_all(matches: &ArgMatches) -> bool {
        matches.is_present("include_niaz3_in_all")
    }
    
    pub fn get_apply_predecessors(matches: &ArgMatches) -> bool {
        matches.is_present("apply_predecessors")
    }

    pub fn get_apply_bidirectional(matches: &ArgMatches) -> bool {
        matches.is_present("apply_bidirectional")
    }

    pub fn get_prime(matches: &ArgMatches) -> Result<BigInt, ()>{
        let prime_argument = matches.value_of("prime").unwrap();
        let prime = prime_argument.parse::<BigInt>();
        if let Result::Ok(p) = prime { 
           Ok(p)
        }
        else { 
            Result::Err(eprintln!("{}", Colour::Red.paint("invalid prime")))
        }
    }

    pub fn get_clustering_size(matches: &ArgMatches) -> Result<usize, ()> {
        let timeout_argument = matches.value_of("clustering_size").unwrap();
        let timeout = usize::from_str_radix(timeout_argument, 10);
        if let Result::Ok(time) = timeout { 
           Ok(time)
        }
        else { 
            Result::Err(eprintln!("{}", Colour::Red.paint("invalid clustering size")))
        }
    }

    pub fn get_limit_size(matches: &ArgMatches) -> Result<usize, ()> {
        let limit_size_argument = matches.value_of("limit_size").unwrap();
        let limit_size = usize::from_str_radix(limit_size_argument, 10);
        if let Result::Ok(size) = limit_size { 
           Ok(size)
        }
        else { 
            Result::Err(eprintln!("{}", Colour::Red.paint("invalid limit size")))
        }
    }
    
    pub fn get_solver(matches: &ArgMatches) -> Result<PossibleSolver,()> {
        use solvers_interface::PossibleSolver::*;
        match matches.is_present("solver"){
            true => {
                let solver = matches.value_of("solver").unwrap().to_ascii_lowercase();
                let solver_enum = if solver == "civer" {
                    Ok(CIVER)
                } else if solver == "picus" {
                    Ok(PICUS)
                } else if solver == "ffsol" {
                    Ok(FFSOL)
                } else if solver == "cvc5" {
                    Ok(CVC5)
                } else if solver == "yices" {
                    Ok(YICES)
                } else if solver == "niaz3" || solver == "nia-z3" {
                    Ok(NIAZ3)
                } else if solver == "z3" {
                    Ok(Z3)
                } else if solver == "all" {
                    Ok(ALL)
                } else {
                    Result::Err(eprintln!("{}", Colour::Red.paint("invalid solver")))
                }?;

                if solver_enum != ALL && !solver_enum.is_available() {
                    let binary = solver_enum.required_binary().unwrap();
                    return Result::Err(eprintln!("{}", Colour::Red.paint(
                        format!("solver '{}' requires '{}' which was not found in PATH", solver, binary)
                    )));
                }
                Ok(solver_enum)
            }
            false => Ok(CIVER),
        }
    }

    pub fn get_equivalence_mode(matches: &ArgMatches) -> Result<usize,  ()> {
        
        match matches.is_present("equivalence"){
            true => 
               {
                   let solver = matches.value_of("equivalence").unwrap();
                   if solver == "none"{
                        Ok(0)
                    } else if solver == "local"{
                        Ok(1)
                    } else if solver == "structural"{
                        Ok(2)
                    } else{
                        Result::Err(eprintln!("{}", Colour::Red.paint("invalid equivalence mode")))
                    }
               }
               
            false => Ok(2),
        }
    }

    pub fn get_target_size(matches: &ArgMatches) -> Result<usize, ()> {
        let target_argument = matches.value_of("target_size").unwrap();
        let size = usize::from_str_radix(target_argument, 10);
        if let Result::Ok(size) = size { 
           Ok(size)
        }
        else { 
            Result::Err(eprintln!("{}", Colour::Red.paint("invalid target size")))
        }
    }

    pub fn get_extra_rounds(matches: &ArgMatches) -> Result<usize, ()> {
        let timeout_argument = matches.value_of("extra_rounds").unwrap();
        let timeout = usize::from_str_radix(timeout_argument, 10);
        if let Result::Ok(time) = timeout {
           Ok(time)
        }
        else {
            Result::Err(eprintln!("{}", Colour::Red.paint("invalid extra_rounds")))
        }
    }

    pub fn get_report_output(matches: &ArgMatches) -> Option<PathBuf> {
        matches.value_of("report").map(|s| PathBuf::from(s))
    }

    pub fn view() -> ArgMatches<'static> {
        App::new("ZK-GENVER")
            .about("General modular verifier for ZK-circuits")
            .arg(
                Arg::with_name("input")
                    .multiple(false)
                    .default_value("./circuit.circom")
                    .help("Path to the R1CS constraint system to be verified"),
            )
            .arg(
                Arg::with_name("original_structure")
                    .long("original_structure")
                    .hidden(false)
                    .takes_value(true)
                    .help("Original structure of the circuit. It can be used to return more significative errors")
                    .display_order(520)
            )
            .arg(
                Arg::with_name("input_structure")
                    .long("input_structure")
                    .hidden(false)
                    .takes_value(true)
                    .help("Structure in which the circuit is initially processed. If not given, the circuit is clusterized by ZK-GENVER; in --check_semantic_equivalence it is derived from the specification's components_info and vars_info instead")
                    .display_order(460)
            )
            .arg(
                Arg::with_name("correspondence")
                    .long("correspondence")
                    .hidden(false)
                    .takes_value(true)
                    .help("The correspondence between the witness signals and the original names in the circom program")
                    .display_order(460)
            )
            .arg(
                Arg::with_name("check_equivalence")
                    .long("check_equivalence")
                    .hidden(false)
                    .takes_value(true)
                    .help("Argument to activate the equivalence check mode. It check the equivalence between the input and the given file")
                    .display_order(130)
            )
            .arg(
                Arg::with_name("check_correctness")
                    .long("check_correctness")
                    .hidden(false)
                    .takes_value(true)
                    .help("Argument to activate the correctness check mode. It checks if the input is correct with respect to the given SMT2 formula")
                    .display_order(130)
            )
            .arg(
                Arg::with_name("check_semantic_equivalence")
                    .long("check_semantic_equivalence")
                    .hidden(false)
                    .takes_value(true)
                    .conflicts_with_all(&["check_correctness", "check_equivalence"])
                    .requires("correspondence")
                    .help("Argument to activate the semantic equivalence check mode. It checks the circuit against the given llzk specification (the same JSON --check_correctness takes), verifying one hybrid cluster pair at a time instead of one circom template at a time. Requires --correspondence; --input_structure is optional, and without it the structure is derived from the specification")
                    .display_order(131)
            )
            .arg(
                Arg::with_name("resolved_formula")
                    .long("resolved_formula")
                    .hidden(false)
                    .takes_value(true)
                    .requires("check_semantic_equivalence")
                    .help("--check_semantic_equivalence only: the specification already resolved to signal ids by `llzk_smt_preprocessor --mode single`, one flat dictionary whose tags carry the instance they belong to as a prefix. Given it, the circuit is clustered against that ONE formula instead of once per component instance, so a cluster may cut across instances; the specification passed to --check_semantic_equivalence is still needed, for the atoms' SMT-LIB text. --input_structure is then only used to build the atoms")
                    .display_order(132)
            )
            .arg(
                Arg::with_name("timeout")
                    .long("timeout")
                    .takes_value(true)
                    .hidden(false)
                    .default_value("5000")
                    .help("Timeout for the solvers")
                    .display_order(500)
            )
            .arg(
                Arg::with_name("limit_size")
                    .long("limit_size")
                    .takes_value(true)
                    .hidden(false)
                    .default_value("500000")
                    .help("Limit size of the nodes -> not sending to the solvers nodes with more than this limit. Decomposing instead.")
                    .display_order(876)
            )
            .arg(
                Arg::with_name("desactivate_deduction_assigned")
                    .long("desactivate_deduction_assigned")
                    .takes_value(false)
                    .hidden(false)
                    .help("Desactivate to apply the deduction rule for linear constraints")
                    .display_order(600)
            )
            .arg(
                Arg::with_name("verbose")
                    .long("verbose")
                    .takes_value(false)
                    .hidden(false)
                    .help("Activate to print debug messages and not remove intermediate files")
                    .display_order(600)
            )
            .arg(
                Arg::with_name("apply_predecessors")
                    .long("apply_predecessors")
                    .takes_value(false)
                    .hidden(false)
                    .help("Abstract/expand towards the predecessors instead of the successors. Read by --check_correctness, --check_equivalence, the determinism mode and --check_semantic_equivalence alike")
                    .display_order(600)
            )
            .arg(
                Arg::with_name("apply_bidirectional")
                    .long("apply_bidirectional")
                    .takes_value(false)
                    .hidden(false)
                    .help("Abstract/expand towards both the predecessors and the successors. Read by --check_correctness, --check_equivalence, the determinism mode and --check_semantic_equivalence alike")
                    .display_order(600)
            )
            .arg(
                Arg::with_name("no_clustering")
                    .long("no_clustering")
                    .takes_value(false)
                    .hidden(false)
                    .requires("check_semantic_equivalence")
                    .conflicts_with("resolved_formula")
                    .help("--check_semantic_equivalence only: do not cluster anything. Each template of the circuit structure -- the one --input_structure gives, or the one derived from the specification when it does not -- becomes ONE cluster pair holding all of its constraints and all of its atoms, so a verdict covers the whole template and nothing of it is ever abstracted away from its own query. The clustering algorithm does not run, which leaves --target_size and --skip_io_equivalence_merge with nothing to act on. Not available with --resolved_formula, which has no templates to keep whole")
                    .display_order(600)
            )
            .arg(
                Arg::with_name("smt_signal_names")
                    .long("smt_signal_names")
                    .takes_value(false)
                    .hidden(false)
                    .requires("check_semantic_equivalence")
                    .help("--check_semantic_equivalence only: name the symbols of the generated .smt2 after the circuit's own signals -- `r1cs_main_isz_in` for an r1cs wire and `spec_main_isz_out` for the specification variable bound to it -- so a query reads without the correspondence file at hand. Without it the .smt2 looks like --check_correctness's: `s_{id}` for an r1cs signal and the macro's own `v_j` for a specification variable, with the names kept in the trailing comments either way")
                    .display_order(600)
            )
            .arg(
                Arg::with_name("allow_empty_clusters")
                    .long("allow_empty_clusters")
                    .takes_value(false)
                    .hidden(false)
                    .requires("check_semantic_equivalence")
                    .help("--check_semantic_equivalence only: pass over a cluster pair with no output the specification names instead of aborting on it. Such a pair has nothing to prove -- its query would be vacuously unsat -- so by default it stops the run as a broken clustering; with this flag it is left unverified and unreported, and the rest of the clusters are checked as usual")
                    .display_order(600)
            )
            .arg(
                Arg::with_name("include_niaz3_in_all")
                    .long("include_niaz3_in_all")
                    .takes_value(false)
                    .hidden(false)
                    .help("When using --solver all, also run the NIA-Z3 backend")
                    .display_order(600)
            )
            .arg(
                Arg::with_name("solver")
                    .long("solver")
                    .takes_value(true)
                    .hidden(false)
                        .help("Solver to be used for the verification of the circuit. ZK-GENVER allows ffsol, cvc5, yices, niaz3, z3, picus, civer (default), and ALL")
                    .display_order(480)
            )
            .arg(
                Arg::with_name("equivalence")
                    .long("equivalence")
                    .takes_value(true)
                    .hidden(false)
                    .help("Select the equivalence between nodes that is going to be used by ZK-GENVER: none, local or structural. ZK-GENVER uses structural by default")
                    .display_order(620)
            )
            .arg (
                Arg::with_name("prime")
                    .short("prime")
                    .long("prime")
                    .takes_value(true)
                    .default_value("21888242871839275222246405745257275088548364400416034343698204186575808495617")
                    .display_order(600)
                    .help("To choose the prime number to use to verify the circuit"),
            )
            .arg (
                Arg::with_name("clustering_size")
                    .short("clustering_size")
                    .long("clustering_size")
                    .takes_value(true)
                    .default_value("200")
                    .display_order(600)
                    .help("To choose the size of the nodes that are considered for clustering. The default value is 200. In order to not apply clustering, use clustering_size 0"),
            )
            .arg (
                Arg::with_name("target_size")
                    .short("target_size")
                    .long("target_size")
                    .takes_value(true)
                    .default_value("0")
                    .display_order(600)
                    .help("To choose the target size of the nodes that is used in the clustering. In order to not apply target size, use target_size 0. The default value is 0."),
            )
            .arg (
                Arg::with_name("extra_rounds")
                    .short("extra_rounds")
                    .long("extra_rounds")
                    .takes_value(true)
                    .default_value("0")
                    .display_order(600)
                    .help("How many times a node whose query came back inconclusive is retried with more context. In --check_correctness, --check_equivalence and the determinism mode: rounds of adding successors/predecessors after a timeout. In --check_semantic_equivalence: rounds of asserting the neighbouring clusters in full instead of abstracting them, each round reaching one hop further. 0, the default, means one query per node"),
            )
            
            .arg(
                Arg::with_name("instance_adjacency")
                    .long("instance_adjacency")
                    .takes_value(false)
                    .help("Treat every cluster of the same instance as a neighbour. Splitting an instance across clusters is the clustering algorithm's choice, not a semantic boundary, and the split can leave one cluster holding the constraints that feed a child's inputs while another holds the constraint consuming its output -- the second then carries an implication whose antecedent nothing in its own query can discharge, and its counterexample is reported as conclusive")
                    .display_order(134)
            )
            .arg(
                Arg::with_name("dump_dir")
                    .long("dump_dir")
                    .takes_value(true)
                    .display_order(901)
                    .help("--check_semantic_equivalence only: directory to write the debug artefacts of the run into, created if missing. `structure.json` is the component structure the run used, derived from the specification unless --input_structure gave one, and is what `llzk_smt_preprocessor --structure` needs to write the file --resolved_formula reads; `resolved.json` is the specification as the clustering sees it (macro -> instance -> tag -> signals, the shape llzk_smt_preprocessor writes, so the two can be diffed); `raw_clustering.json` is the hybrid clustering exactly as the algorithm returned it, every instance including those no query was built for; `clusters.json` is one record per cluster pair actually verified, with its verdict, its interface and its atoms"),
            )
            .arg(
                Arg::with_name("report")
                    .long("report")
                    .takes_value(true)
                    .hidden(false)
                    .help("Path to write a JSON report with all results and statistics")
                    .display_order(900)
            )
            .get_matches()
    }

}