
use std::collections::{HashMap, LinkedList};
use crate::{BigInt, SafetyVerification};


pub fn safety_problem_to_smt2(problem: &SafetyVerification)->LinkedList<String>{
    let mut smt2_problem = LinkedList::new();
    let mut header = declare_header(&problem.field);
    smt2_problem.append(&mut header);

    let mut signal_to_name = HashMap::new();
    let mut signal_to_name_aux = HashMap::new();
 
    for s in &problem.signals {
        let name = format!("s_{}",s);
        smt2_problem.push_back(declare_signal(&name)); 
        signal_to_name.insert(*s,name.clone());
        
        let name_aux = if problem.inputs.contains(&s){
            name
        }else{
            let aux = format!("s_{}_aux",s);
            smt2_problem.push_back(declare_signal(&aux)); 
            aux  
        };
        signal_to_name_aux.insert(*s,name_aux);  
    }

    for constraint in &problem.constraints {
        smt2_problem.push_back(
            format!("(assert {})",
                constraint.constraint_to_smt2(&signal_to_name)
            )
        );
        smt2_problem.push_back(
            format!("(assert {})",
                constraint.constraint_to_smt2(&signal_to_name_aux)
            )
        );
    }


    for imp in &problem.implications_safety{
        let new_imp = implication_to_smt2(imp,&signal_to_name,&signal_to_name_aux);
        smt2_problem.push_back(
            format!("(assert {})",
                new_imp
            )
        );
    }

    smt2_problem.push_back(
        format!("(assert (not {}))",
            declare_all_outputs_equal(&problem.outputs, &signal_to_name, &signal_to_name_aux)
        )
    );
    smt2_problem.push_back(format!("(check-sat)"));
    smt2_problem
    
}

pub fn declare_signal(signal_name: &String)->String{
    format!("(declare-fun {} () FF0)",signal_name)
}


pub fn declare_header(prime: &BigInt)->LinkedList<String>{
    let mut aux = LinkedList::new();
    aux.push_back("(set-logic QF_FF)".to_string());
    aux.push_back(format!("(define-sort FF0 () (_ FiniteField {}))", prime));
    aux
}

pub fn implication_to_smt2(imp: &(Vec<usize>, Vec<usize>), signal_to_names: &HashMap<usize,String>, signal_to_names_aux: &HashMap<usize,String>) -> String{
    let left: String = if imp.0.len() == 0{
        "true".to_string()
    } else if imp.0.len() == 1{
        let s = imp.0[0];
        format!("(= {} {})", signal_to_names[&s], signal_to_names_aux[&s])
    } else{
        let mut aux = "(and ".to_string();
        for s in &imp.0{
            aux = format!("{} (= {} {}) ", aux, signal_to_names[s], signal_to_names_aux[s]);
        }
        aux = format!("{})",aux);
        aux
    };

    let right = if imp.1.len() == 0{
        "true".to_string()
    } else if imp.1.len() == 1{
        let s = imp.1[0];
        format!("(= {} {})", signal_to_names[&s], signal_to_names_aux[&s])
    } else{
        let mut aux = "(and ".to_string();
        for s in &imp.1{
            aux = format!("{} (= {} {}) ", aux, signal_to_names[s], signal_to_names_aux[s]);
        }
        aux = format!("{})",aux);
        aux
    };

    format!("(=> {} {})", left, right)

}


pub fn declare_all_outputs_equal(outputs: &Vec<usize>, signal_to_names: &HashMap<usize,String>, signal_to_names_aux: &HashMap<usize,String>) -> String{
    if outputs.len() == 0{
        "true".to_string()
    } else if outputs.len() == 1{
        let s = outputs[0];
        format!("(= {} {})", signal_to_names[&s], signal_to_names_aux[&s])
    } else{
        let mut aux = "(and ".to_string();
        for s in outputs{
            aux = format!("{} (= {} {}) ", aux, signal_to_names[s], signal_to_names_aux[s]);
        }
        aux = format!("{})",aux);
        aux
    }
}