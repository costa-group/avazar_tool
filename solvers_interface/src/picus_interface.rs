use crate::{PossibleResult,SafetyVerification};
use std::process::Command;
use std::process::Stdio;
use std::time::Duration;
use circom_algebra::algebra::Constraint;
use std::collections::{HashMap, LinkedList};
use std::io::Read;
use utils::write_r1cs::*;
use num_bigint_dig::BigInt;
use wait_timeout::ChildExt;
use std::fs;


pub fn deduce(problem: &SafetyVerification)-> (PossibleResult, Vec<String>){
    let  copy_inputs = problem.inputs.clone();
    let  copy_outputs = problem.outputs.clone();
    let  copy_signals = problem.signals.clone();
    let mut copy_constraints = problem.constraints.clone();
        
    // We need to rename the constraints to use the first numbers for the signals
    apply_renaming_signals(&mut copy_constraints, &copy_inputs, &copy_outputs, &copy_signals);

    //1. Generate r1cs file.
    let output_name = generate_r1cs_file(
        &problem.template_name, 
        copy_inputs.len(), 
        copy_outputs.len(), 
        copy_signals.len(), 
        copy_constraints, 
        &problem.field
    ).unwrap();
    
    //2. Create a process that calls to Picus
    println!("Running picus with output file: {}", output_name);
    let mut command_args = Vec::new();
    command_args.push("--timeout".to_string());
    let timeout = problem.verification_timeout;
    command_args.push(timeout.to_string());

    command_args.push(output_name.clone());
    let timeout = problem.verification_timeout;
    let mut cmd = Command::new("./Picus/run-picus")
        .args(command_args)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("Failed to start picus process");

    let mut stdout = String::new();
    let stderr = String::new();
    
    match cmd.wait_timeout(Duration::from_millis(timeout * 6)).unwrap() {
        Some(_) => {
            let _ = fs::remove_file(output_name);

            if let Some(mut out) = cmd.stdout.take() {
                let mut buf = Vec::new();
                out.read_to_end(&mut buf).ok();
                stdout = String::from_utf8_lossy(&buf).to_string();
            }
            //if stdout contains the line "The circuit is properly constrained"
            if stdout.contains("The circuit is properly constrained") {
                println!("VERIFIED: picus stdout:\n{}", stdout);
                (PossibleResult::VERIFIED, vec![stderr])
            }
            else if stdout.contains("underconstrained"){
                println!("FAILED: picus stdout:\n{}", stdout);
                (PossibleResult::FAILED, vec![stderr])
            } else{
                println!("TIMEOUT: picus stdout:\n{}", stdout);
                (PossibleResult::UNKNOWN, vec![stderr])
            }
        }
        None => {
            cmd.kill().ok();
            let _ = fs::remove_file(output_name);
            eprintln!("### PICUS: TIMED OUT\n");
            (PossibleResult::UNKNOWN, vec!["### PICUS: TIMED OUT\n".to_string()])
        }
    }
 
}


fn apply_renaming_signals(
    constraints: &mut Vec<Constraint<usize>>,
    inputs: &Vec<usize>,
    outputs: &Vec<usize>,
    signals: &LinkedList<usize>,
){
        // The needed renaming is outputs -> first positions
        // Inputs -> next positions
        // Auxiliar inputs (not for now) -> next

        //println!("Considering [{:?}] [{:?}] [{:?}]",self.outputs,self.inputs,self.signals);


        let mut renaming = HashMap::new();
        for s in outputs{
            renaming.insert(*s, renaming.len() + 1);
        }
        for s in inputs{
            renaming.insert(*s, renaming.len() + 1);
        }
        for s in signals{
            if !renaming.contains_key(s){
                renaming.insert(*s, renaming.len() + 1);
            }
        }

        for c in constraints{
            //c.print_pretty_constraint();
            *c = Constraint::<usize>::apply_correspondence(&c, &renaming);
        }
}


fn generate_r1cs_file(template_name: &String, n_inputs: usize, n_outputs: usize, n_signals: usize, constraints: Vec<Constraint<usize>>, field: &BigInt) -> Result<String,()>{
        // This function should generate the R1CS file based on the template verification data.
        // For now, we will return a placeholder string.

        //println!("Generating R1CS file for template: {}", template_name);
        let field_size = if field.bits() % 64 == 0 {
            field.bits() / 8
        } else{
            (field.bits() / 64 + 1) * 8
        };
        let output_name = format!("{}.r1cs", template_name);
        let r1cs = R1CSWriter::new( output_name.clone(), field_size, false)?;
        let mut header_section = R1CSWriter::start_header_section(r1cs)?;
        let header_data = HeaderData {
            field: field.clone(),
            public_outputs: n_outputs,
            public_inputs: 0,
            private_inputs: n_inputs,
            total_wires: n_signals+1, //he sumado uno por la zero wire
            number_of_labels: n_signals+1,
            number_of_constraints: constraints.len(),
        };
        // println!("Header data field: {:?}", header_data.field);
        // println!("Header data public outputs: {}", header_data.public_outputs);
        // println!("Header data public inputs: {}", header_data.public_inputs);
        // println!("Header data private inputs: {}", header_data.private_inputs);
        // println!("Header data total wires: {}", header_data.total_wires);
        // println!("Header data number of labels: {}", header_data.number_of_labels);
        // println!("Header data number of constraints: {}", header_data.number_of_constraints);
        header_section.write_section(header_data)?;
        let r1cs = header_section.end_section()?;

        let mut constraint_section = R1CSWriter::start_constraints_section(r1cs)?;
        
        for c in constraints{  
            ConstraintSection::write_constraint_usize(&mut constraint_section, c.a(), c.b(), c.c())?;
        }

            let r1cs = constraint_section.end_section()?;

        let mut signal_section = R1CSWriter::start_signal_section(r1cs)?;

        for id in 1..n_signals{
            SignalSection::write_signal_usize(&mut signal_section, id)?;
        }
        let r1cs = signal_section.end_section()?;
        R1CSWriter::finish_writing(r1cs)?;
        Ok(output_name)
}