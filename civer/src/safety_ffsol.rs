use std::collections::HashMap;
use std::fs::File;
use std::io::{Read, Write};
use std::process::{Command, Stdio};
use std::thread;
use std::time::Duration;
use num_bigint_dig::BigInt;
use solvers_interface::PossibleResult;
use circom_algebra::algebra::Constraint;
use z3::Config;
use z3::Context;
use z3::Solver;
use z3::ast::Ast;
use z3::*;
use rand::Rng;
use std::os::unix::process::CommandExt;
use nix::unistd::Pid;
use nix::sys::signal::{killpg, Signal};
use wait_timeout::ChildExt;

//This function only works if 0 <= a <= field - 1
fn to_neg(a: &BigInt, field: &BigInt) -> BigInt{
    if a < &(field/BigInt::from(2)){
        a.clone()
    }
    else {
        a - field
    }
}

pub fn insert_constraint_in_smt(
    constraint: &Constraint<usize>,
    ctx: &Context,
    solver: &Solver,
    signals_to_smt_symbols: &HashMap<usize, z3::ast::Int>,
    field: &BigInt,
    num_k: usize,
    p: &z3::ast::Int,
    _verbose: bool,
) {
    let mut value_a = z3::ast::Int::from_u64(ctx, 0);
    let mut value_b = z3::ast::Int::from_u64(ctx, 0);
    let mut value_c = z3::ast::Int::from_u64(ctx, 0);


    for (signal, value) in constraint.a(){
        if *signal == 0{
            value_a += &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap()
        } else{
            value_a += signals_to_smt_symbols.get(signal).unwrap() *
                &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
        }
    }
    for (signal, value) in constraint.b(){
        if *signal == 0{
            value_b += &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap()
        } else{
            value_b += signals_to_smt_symbols.get(signal).unwrap() *
                &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
        }
    }
    for (signal, value) in constraint.c(){
        if *signal == 0{
            value_c += &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap()
        } else{
            value_c += signals_to_smt_symbols.get(signal).unwrap() *
                &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
        }
    }

    let pol = value_a * value_b;
    let c = pol._eq(&value_c);
    solver.assert(&c);
}

pub fn try_prove_safety_with_ffsol(
    inputs: &Vec<usize>,
    outputs: &Vec<usize>,
    signals: &Vec<usize>,
    constraints: &Vec<Constraint<usize>>,
    implications_safety: &Vec<(Vec<usize>, Vec<usize>)>,
    field: &BigInt,
    verification_timeout: u64,
    logs: &mut Vec<String>,
) -> PossibleResult {
        let mut cfg = Config::new();
        cfg.set_timeout_msec(verification_timeout);
        let ctx = Context::new(&cfg);
        let solver = Solver::new(&ctx);
        let zero = z3::ast::Int::from_i64(&ctx, 0);
        let field_z3 = z3::ast::Int::from_str(&ctx, &field.to_string()).unwrap();
        let mut aux_signals_to_smt_rep = HashMap::new();
        let mut aux_signals_to_smt_rep_aux = HashMap::new();
    
        println!("Number of signals: {}", signals.len());
        println!("Number of inputs: {}", inputs.len());
        println!("Number of outputs: {}", outputs.len());
        println!("Number of constraints: {}", constraints.len());
        for s in signals {
            let is_input = inputs.contains(s);

            let aux_signal_to_smt = z3::ast::Int::new_const(&ctx, format!("s_{}", s));
            let copy_aux_signal_to_smt = if !is_input {
                z3::ast::Int::new_const(&ctx, format!("saux_{}", s))
            } else {
                z3::ast::Int::new_const(&ctx, format!("s_{}", s))
            };
                aux_signals_to_smt_rep.insert(*s, aux_signal_to_smt.clone());
                aux_signals_to_smt_rep_aux.insert(*s, copy_aux_signal_to_smt.clone());

        }

        let mut i = 0;
        for constraint in constraints {
            insert_constraint_in_smt(
                constraint,
                &ctx,
                &solver,
                &aux_signals_to_smt_rep,
                &field,
                i,
                &field_z3,
                false,
            );
            i = i + 1;
            insert_constraint_in_smt(
                constraint,
                &ctx,
                &solver,
                &aux_signals_to_smt_rep_aux,
                &field,
                i,
                &field_z3,
                false,
            );
            i = i + 1;
        }


        for (inputs_i, outputs_o) in implications_safety{
            let mut implication_left = z3::ast::Bool::from_bool(&ctx, true);
            for s in inputs_i{
                let s_1 = aux_signals_to_smt_rep.get(s).unwrap();
                let s_2 = aux_signals_to_smt_rep_aux.get(s).unwrap();
                implication_left &= s_1._eq(s_2);
            }
            let mut implication_right = z3::ast::Bool::from_bool(&ctx, true);
            for s in outputs_o{
                let s_1 = aux_signals_to_smt_rep.get(s).unwrap();
                let s_2 = aux_signals_to_smt_rep_aux.get(s).unwrap();
                implication_right &= s_1._eq(s_2);
            }

            solver.assert(&implication_left.implies(&implication_right));
        }



        let mut all_outputs_equal = z3::ast::Bool::from_bool(&ctx, true);
        for s in outputs {
            let s_1 = aux_signals_to_smt_rep.get(s).unwrap();
            let s_2 = aux_signals_to_smt_rep_aux.get(s).unwrap();
            all_outputs_equal &= s_1._eq(s_2);
        }

        solver.assert(&!all_outputs_equal);

    
        let mut smt2_output = solver.to_string();
     
        //let start_time = std::time::Instant::now();
        //let result_sat = solver.check();
        //let elapsed_time = start_time.elapsed();

        //println!("### SMT Solver Execution Time: {:.2?}\n", elapsed_time);
        let prologue_str = format!("(set-info :smt-lib-version 2.6)\n(set-logic QF_FFA {})\n",field);
        let elapsed_time_str = format!("(check-sat)\n");
        smt2_output = format!("{}{}{}", prologue_str,smt2_output, elapsed_time_str);

        //produce a random number for the file name
        let mut rng = rand::thread_rng();
        let random_number: u32 = rng.gen();
        let new_file_name = format!("output_{}.smt2", random_number);
        // Ensure the SMT2 text is fully written and flushed to disk before continuing.
        {
            let mut file = File::create(&new_file_name).expect("Unable to create SMT2 file");
            file.write_all(smt2_output.as_bytes()).expect("Unable to write SMT2 file");
            file.sync_all().expect("Failed to sync SMT2 file to disk");
            file.flush().expect("Failed to flush SMT2 file");
            // `file` dropped here
            //esperar treinta segundoo
        }
    

    let mut command_args = Vec::new();
    command_args.push("-tlimit");
    let timeout_str = format!("{}",verification_timeout/1000);
    command_args.push(timeout_str.as_str());
    command_args.push("-using_cocoa");
    command_args.push("-file");
    command_args.push(&new_file_name);
    let mut child = unsafe { Command::new("/home/miguelis/Systems/poly-eqs/smtSystem/ffsol")
        .args(command_args)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .pre_exec(|| {
            // Crear un nuevo process group
            unsafe {
                libc::setsid();
            }
            Ok(())
        })
        .spawn()
        .expect("Failed to execute the command")};


    let mut stdout = child.stdout.take().expect("Failed to take stdout");
    let mut stderr = child.stderr.take().expect("Failed to take stderr");


    let stdout_handle = thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = stdout.read_to_end(&mut buf);
        buf
    });

    let stderr_handle = thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = stderr.read_to_end(&mut buf);
        buf
    });

// -------------------- timeout --------------------
    let timeout = Duration::from_millis(verification_timeout);

    let timed_out = match child.wait_timeout(timeout)
        .expect("Failed while waiting for the process")
    {
        Some(_status) => false, // terminó a tiempo
        None => {
            // Timeout: matar TODO el grupo de procesos
            let pgid = Pid::from_raw(child.id() as i32);
            let _ = killpg(pgid, Signal::SIGKILL);
            true
        }
    };

    // Esperar al proceso principal (NO wait_with_output)
    let status = child.wait().expect("Failed to wait on child");

    // Recoger stdout / stderr (ya no bloquea)
    let stdout = stdout_handle.join().expect("stdout thread panicked");
    let stderr = stderr_handle.join().expect("stderr thread panicked");

    // -------------------- output final --------------------
    let output = std::process::Output {
        status,
        stdout,
        stderr,
    };
    let stdout = String::from_utf8_lossy(&output.stdout);
    let mut result_solver = SatResult::Unknown;
    if let Some(ultima_linea) = stdout.lines().rev().find(|l| !l.trim().is_empty()) {
        if ultima_linea == "unsat" { 
		result_solver = SatResult::Unsat;
       	} else if ultima_linea == "sat" {
		result_solver = SatResult::Sat;
	}
    }
//     let num_calls = count_output_smt2_files(".");
//        logs.push(format!("Number of calls to NL Solver: {}", num_calls));
    match result_solver{
            SatResult::Sat =>{
                logs.push(format!("### THE TEMPLATE DOES NOT ENSURE SAFETY. FOUND COUNTEREXAMPLE USING SMT:\n"));

                /*let model = solver.get_model().unwrap();
                for s in 0..number_inputs{
                    let v = model.eval(aux_signals_to_smt_rep.get(&(initial_signal + number_outputs + s)).unwrap(), true).unwrap();
                    logs.push(format!("Input signal {}: {}\n", initial_signal + number_outputs + s, v.to_string()));

                }
                for s in 0..number_outputs{
                    let v = model.eval(aux_signals_to_smt_rep.get(&(initial_signal + s)).unwrap(), true).unwrap();
                    let v1 = model.eval(aux_signals_to_smt_rep_aux.get(&(initial_signal + s)).unwrap(), true).unwrap();

                    logs.push(format!("Output signal {}: values {} | {}\n", initial_signal + s, v.to_string(), v1.to_string()));

                }*/

                PossibleResult::FAILED
                //}
            },
            SatResult::Unsat =>{
                logs.push(format!("### WEAK SAFETY ENSURED BY THE TEMPLATE\n"));
                PossibleResult::VERIFIED
            },
            _=> {
                logs.push(format!("### UNKNOWN: VERIFICATION OF WEAK SAFETY USING THE SPECIFICATION TIMEOUT\n"));
                PossibleResult::UNKNOWN
            }
        }



    }

