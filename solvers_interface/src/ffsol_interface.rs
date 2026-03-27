use crate::{PossibleResult,SafetyVerification};
use std::process::Command;
use std::process::Stdio;
use std::time::Duration;
use std::collections::LinkedList;
use std::io::Read;
use crate::smt2_utils::safety_problem_to_smt2;
use wait_timeout::ChildExt;
use std::fs::File;
use std::io::Write;
use rand::Rng;
use std::os::unix::process::CommandExt;
use std::thread;
use nix::unistd::Pid;
use nix::sys::signal::Signal;
use nix::sys::signal::killpg;

pub fn deduce(problem: &SafetyVerification)-> (PossibleResult, Vec<String>){
    
    let mut logs = Vec::new();

    let smt2_problem: LinkedList<String> = safety_problem_to_smt2(problem);

       
    //produce a random number for the file name
    let mut rng = rand::thread_rng();
    let random_number: u32 = rng.gen();
    let new_file_name = format!("output_{}.smt2", random_number);

    // Ensure the SMT2 text is fully written and flushed to disk before continuing.
    {
        let mut file = File::create(&new_file_name).expect("Unable to create SMT2 file");
        for s in smt2_problem{
            file.write_all(format!("{}\n",s).as_bytes()).expect("Unable to write SMT2 file");
            
        }
        file.sync_all().expect("Failed to sync SMT2 file to disk");
        file.flush().expect("Failed to flush SMT2 file");
        // `file` dropped here
    }
    

    let mut command_args = Vec::new();
    command_args.push("-tlimit");
    let timeout_str = format!("{}",problem.verification_timeout);
    command_args.push(timeout_str.as_str());
    command_args.push("-using_cocoa");
    command_args.push("-file");
    command_args.push(&new_file_name);
    let mut child = unsafe { Command::new("/home/clara/circom/proving_unsat/copy_clean/src/ffsol")
        .args(command_args)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .pre_exec(|| {
            // Crear un nuevo process group
            libc::setsid();
            
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
    let timeout = Duration::from_millis(problem.verification_timeout);

    let _timed_out = match child.wait_timeout(timeout)
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

    let mut result_solver = PossibleResult::UNKNOWN;
    if let Some(ultima_linea) = stdout.lines().rev().find(|l| !l.trim().is_empty()) {
        if ultima_linea == "unsat" { 
            logs.push(format!("### THE TEMPLATE DOES NOT ENSURE SAFETY. FOUND COUNTEREXAMPLE USING SMT:\n"));
		    result_solver = PossibleResult::VERIFIED;
       	} else if ultima_linea == "sat" {
            logs.push(format!("### WEAK SAFETY ENSURED BY THE TEMPLATE\n"));
		    result_solver = PossibleResult::FAILED;
	    } else{
            logs.push("### UNKNOWN: VERIFICATION OF WEAK SAFETY USING THE SPECIFICATION TIMEOUT\n".to_string());
        }
    } else{
        logs.push("### UNKNOWN: VERIFICATION OF WEAK SAFETY USING THE SPECIFICATION TIMEOUT\n".to_string());
    }

    (result_solver, logs)
}

