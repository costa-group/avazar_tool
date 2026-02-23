use std::path::PathBuf;
use crate::BigInt;


pub struct Input {
    pub input_r1cs: PathBuf,
    pub input_structure: Option<PathBuf>,
    pub timeout: u64,
    pub original_structure: Option<PathBuf>,
    pub use_picus: bool,
    pub use_civer: bool,
    pub _flag_verbose: bool,
    pub apply_deduction_assigned: bool,
    pub apply_predecessors: bool,
    pub apply_bidirectional: bool,
    pub prime: BigInt,
    pub clustering_size: usize,
    pub equivalence_mode: usize,
    pub target_size: usize,
    pub internal_solver: String,
    pub extra_rounds: usize
}


impl Input {
    pub fn new() -> Result<Input, ()> {
        let matches = input_processing::view();
        let input_r1cs = input_processing::get_input_r1cs(&matches)?;
        let input_structure = input_processing::get_input_structure(&matches)?;
        let timeout =  input_processing::get_timeout(&matches)?;
        let original_structure = input_processing::get_original_structure(&matches)?;
        let (use_civer, use_picus) = input_processing::get_solver(&matches)?;
        let _flag_verbose =  input_processing::get_flag_verbose(&matches);
        let prime = input_processing::get_prime(&matches)?;
        let clustering_size = input_processing::get_clustering_size(&matches)?;
        let apply_deduction_assigned = input_processing::get_apply_deduction_assigned(&matches);
        let apply_predecessors = input_processing::get_apply_predecessors(&matches);
        let apply_bidirectional = input_processing::get_apply_bidirectional(&matches);

        let equivalence_mode = input_processing::get_equivalence_mode(&matches)?;
        let target_size = input_processing::get_target_size(&matches)?;
        let internal_solver = input_processing::get_internal_solver(&matches)?;
        let extra_rounds = input_processing::get_extra_rounds(&matches)?;
       


        Result::Ok(Input {
            input_r1cs,
            input_structure,
            timeout,
            original_structure,
            use_picus,
            use_civer,
            _flag_verbose,
            prime,
            clustering_size,
            apply_deduction_assigned,
            apply_predecessors,
            apply_bidirectional,
            equivalence_mode,
            target_size,
            internal_solver,
            extra_rounds
        })
    }
}


mod input_processing {
    use ansi_term::Colour;
    use clap::{App, Arg, ArgMatches};
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
        matches.is_present("flag_verbose")
    }

    pub fn get_apply_deduction_assigned(matches: &ArgMatches) -> bool {
        matches.is_present("apply_deduction_assigned")
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
    
    pub fn get_solver(matches: &ArgMatches) -> Result<(bool, bool),  ()> {
        
        match matches.is_present("solver"){
            true => 
               {
                   let solver = matches.value_of("solver").unwrap();
                   if solver == "civer"
                      {
                        Ok((true, false))
                    } else if solver == "picus"{
                        Ok((false, true))
                    }
                    else{
                        Result::Err(eprintln!("{}", Colour::Red.paint("invalid solver")))
                    }
               }
               
            false => Ok((true, false)),
        }
    }

    pub fn get_internal_solver(matches: &ArgMatches) -> Result<String, ()> {
        let solver = matches.value_of("internal_solver").unwrap_or("z3");
        match solver {
            "z3" | "ffsol" | "cvc5" => Ok(solver.to_string()),
            _ => {
                Err(eprintln!("{}", Colour::Red.paint("invalid internal_solver. Must be one of: z3, ffsol, cvc5")))
            }
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
                    .help("Structure in which the circuit is initially processed. If not given, the circuit is clusterized by ZK-GENVER")
                    .display_order(460)
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
                Arg::with_name("apply_deduction_assigned")
                    .long("apply_deduction_assigned")
                    .takes_value(false)
                    .hidden(false)
                    .help("Activate to apply the deduction rule for linear constraints")
                    .display_order(600)
            )
            .arg(
                Arg::with_name("apply_predecessors")
                    .long("apply_predecessors")
                    .takes_value(false)
                    .hidden(false)
                    .help("Activate to start adding predecessors instead of childs")
                    .display_order(600)
            )
            .arg(
                Arg::with_name("apply_bidirectional")
                    .long("apply_bidirectional")
                    .takes_value(false)
                    .hidden(false)
                    .help("Activate to start adding predecessors and childs")
                    .display_order(600)
            )
            .arg(
                Arg::with_name("solver")
                    .long("solver")
                    .takes_value(true)
                    .hidden(false)
                    .help("Solver to be used for the verification of the circuit. ZK-GENVER allows picus and civer (default)")
                    .display_order(480)
            )
            .arg(
                Arg::with_name("internal_solver")
                    .long("internal_solver")
                    .takes_value(true)
                    .hidden(false)
                    .default_value("z3")
                    .help("Internal solver for CIVER: z3, ffsol, or cvc5 (default: z3)")
                    .display_order(485)
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
                    .help("To choose the number of extra rounds of adding successors/predecessors when a node makes timeout. The default value is 0."),
            )
            
            .get_matches()
    }

}