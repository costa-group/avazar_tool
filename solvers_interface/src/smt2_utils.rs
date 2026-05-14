
use std::collections::{HashMap, LinkedList};
use crate::{BigInt, SafetyVerification,EquivalenceVerification,CorrectnessVerification};
use circom_algebra::algebra::Constraint;

pub fn correctness_problem_to_smt2(problem: &CorrectnessVerification)->LinkedList<String>{
    let mut smt2_problem = LinkedList::new();
    let mut header = declare_header(&problem.field);
    smt2_problem.append(&mut header);

    let mut signal_to_name = HashMap::new();
 
    for s in &problem.signals_1 {
        let name = format!("s_{}",s);
        smt2_problem.push_back(declare_signal(&name)); 
        signal_to_name.insert(*s,name.clone());
    }

    for s in &problem.signals_2 {
        smt2_problem.push_back(declare_signal(s)); 
    }

    for constraint in &problem.constraints_1 {

        smt2_problem.push_back(
            format!("(assert {})",
                constraint.constraint_to_smt2(&signal_to_name)
            )
        );
        
    }

    for constraint in &problem.constraints_2 {

        smt2_problem.push_back(
            format!("{}",
                constraint
            )
        );
        
    }


    // for imp in &problem.implications_equivalence{
    //     let new_imp = implication_to_smt2(imp,&signal_to_name,&signal_to_name_aux);
    //     smt2_problem.push_back(
    //         format!("(assert {})",
    //             new_imp
    //         )
    //     );
    // }

    smt2_problem.push_back(
        format!("(assert {})",
            declare_all_signals_equal_2(&problem.inputs_1, &signal_to_name, &problem.inputs_2)
        )
    );

    smt2_problem.push_back(
        format!("(assert (not {}))",
            declare_all_signals_equal_2(&problem.outputs_1, &signal_to_name, &problem.outputs_2)
        )
    );
    smt2_problem.push_back(format!("(check-sat)"));
    smt2_problem
    
}


pub fn equivalence_problem_to_smt2(problem: &EquivalenceVerification,use_old_syntax:bool)->LinkedList<String>{
    let mut smt2_problem = LinkedList::new();
    let mut header = declare_header(&problem.field);
    smt2_problem.append(&mut header);

    let mut signal_to_name = HashMap::new();
    let mut signal_to_name_aux = HashMap::new();
 
    for s in &problem.signals_1 {
        let name = format!("s_{}",s);
        smt2_problem.push_back(declare_signal(&name)); 
        signal_to_name.insert(*s,name.clone());
    }

    for s in &problem.signals_2 {
        let name = format!("saux_{}",s);
        smt2_problem.push_back(declare_signal(&name)); 
        signal_to_name_aux.insert(*s,name.clone());
    }

    for constraint in &problem.constraints_1 {
        if use_old_syntax{
            smt2_problem.push_back(
               format!("(assert {})",
                  constraint.constraint_to_smt2_old(&signal_to_name)
                )
            );
        }else{
            smt2_problem.push_back(
               format!("(assert {})",
                  constraint.constraint_to_smt2(&signal_to_name)
                )
            );
        }
        
    }

    for constraint in &problem.constraints_2 {
        if use_old_syntax{
            smt2_problem.push_back(
               format!("(assert {})",
                  constraint.constraint_to_smt2_old(&signal_to_name_aux)
                )
            );
        }else{
            smt2_problem.push_back(
               format!("(assert {})",
                  constraint.constraint_to_smt2(&signal_to_name_aux)
                )
            );
        }
    }


    for imp in &problem.implications_equivalence{
        let new_imp = equivalence_implication_to_smt2(imp,&signal_to_name,&signal_to_name_aux);
        smt2_problem.push_back(
            format!("(assert {})",
                new_imp
            )
        );
    }

    smt2_problem.push_back(
        format!("(assert {})",
            declare_all_signals_equal(&problem.inputs_1, &signal_to_name, &problem.inputs_2,&signal_to_name_aux)
        )
    );

    smt2_problem.push_back(
        format!("(assert (not {}))",
            declare_all_signals_equal(&problem.outputs_1, &signal_to_name, &problem.outputs_2,&signal_to_name_aux)
        )
    );
    smt2_problem.push_back(format!("(check-sat)"));
    smt2_problem
    
}


pub fn safety_problem_to_smt2(problem: &SafetyVerification)->LinkedList<String>{
    let mut smt2_problem = LinkedList::new();
    let mut header = declare_header(&problem.field);
    smt2_problem.append(&mut header);

    let mut signal_to_name = HashMap::new();
    let mut signal_to_name_aux = HashMap::new();
    for s in &problem.signals {
        // if already declared do not insert 
        if !signal_to_name.contains_key(s){
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

        if problem.apply_deduction_assigned{
            let deductions_uniqueness = apply_deduction_assigned(constraint,&signal_to_name,&signal_to_name_aux);
            for imp in deductions_uniqueness{
                smt2_problem.push_back(
                    format!("(assert {})", imp)
                );
            } 
        }
    }


    for imp in &problem.implications_safety{
        let new_imp = safety_implication_to_smt2(imp,&signal_to_name,&signal_to_name_aux);
        smt2_problem.push_back(
            format!("(assert {})",
                new_imp
            )
        );
    }



    smt2_problem.push_back(
        format!("(assert (not {}))",
            declare_all_signals_equal(&problem.outputs, &signal_to_name, &problem.outputs,&signal_to_name_aux)
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

pub fn safety_implication_to_smt2(imp: &(Vec<usize>, Vec<usize>), signal_to_names: &HashMap<usize,String>, signal_to_names_aux: &HashMap<usize,String>) -> String{
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

pub fn equivalence_implication_to_smt2(imp: &(Vec<(usize, usize)>, Vec<(usize, usize)>), signal_to_names: &HashMap<usize,String>, signal_to_names_aux: &HashMap<usize,String>) -> String{
    let left: String = if imp.0.len() == 0{
        "true".to_string()
    } else if imp.0.len() == 1{
        let (s1, s2) = imp.0[0];
        format!("(= {} {})", signal_to_names[&s1], signal_to_names_aux[&s2])
    } else{
        let mut aux = "(and ".to_string();
        for (s1, s2) in &imp.0{
            aux = format!("{} (= {} {}) ", aux, signal_to_names[s1], signal_to_names_aux[s2]);
        }
        aux = format!("{})",aux);
        aux
    };

    let right = if imp.1.len() == 0{
        "true".to_string()
    } else if imp.1.len() == 1{
        let (s1, s2) = imp.1[0];
        format!("(= {} {})", signal_to_names[&s1], signal_to_names_aux[&s2])
    } else{
        let mut aux = "(and ".to_string();
        for (s_1, s_2) in &imp.1{
            aux = format!("{} (= {} {}) ", aux, signal_to_names[s_1], signal_to_names_aux[s_2]);
        }
        aux = format!("{})",aux);
        aux
    };

    format!("(=> {} {})", left, right)

}

pub fn apply_deduction_assigned(
    c: &Constraint<usize>,
    signals_to_names: &HashMap<usize,String>,
    signals_to_names_aux: &HashMap<usize,String>,
)->Vec<String> {

    let all_signals = c.take_signals();
    let only_linear_signals = c.take_only_linear_signals();

    let mut uniqueness_implications = Vec::new();
    // in case there are signals that are only_linear
    for s_deduced in only_linear_signals {
        // Generate the implication all signals in C are deterministic
        //  => s_deduced is deterministic

        let value_right_1 = signals_to_names.get(s_deduced).unwrap();
        let value_right_2 = signals_to_names_aux.get(s_deduced).unwrap();
        let right_side = format!("(= {} {})",
            value_right_1,
            value_right_2
        );

        let left_side = if all_signals.len() == 1{
            "true".to_string()
        } else {
            let mut new_left_side = if all_signals.len() > 2{
                "(and ".to_string()
            }else{
                "".to_string()
            };
            for s in &all_signals {
                if *s != s_deduced {
                    let value_s_1 = signals_to_names.get(s).unwrap();
                    let value_s_2 = signals_to_names_aux.get(s).unwrap();
                    new_left_side = format!("{}(= {} {}) ",
                        new_left_side,
                        value_s_1,
                        value_s_2
                    );
    
                }
            }

            if all_signals.len() > 2{
                new_left_side = format!("{})", new_left_side);
            }

            new_left_side
        };

        uniqueness_implications.push(
            format!("(=> {} {})",
                left_side,
                right_side
            )
        );  

    }
    uniqueness_implications
}


pub fn declare_all_signals_equal(signals: &Vec<usize>, signal_to_names: &HashMap<usize,String>, signals_aux:&Vec<usize>,signal_to_names_aux: &HashMap<usize,String>) -> String{
    if signals.len() == 0{
        "true".to_string()
    } else if signals.len() == 1{
        let s = signals[0];
        let s_aux = signals_aux[0];
        format!("(= {} {})", signal_to_names[&s], signal_to_names_aux[&s_aux])
    } else{
        let mut aux = "(and ".to_string();
        for i in 0..signals.len(){
            aux = format!("{} (= {} {}) ", aux, signal_to_names[&signals[i]], signal_to_names_aux[&signals_aux[i]]);
        }
        aux = format!("{})",aux);
        aux
    }
}

pub fn declare_all_signals_equal_2(signals: &Vec<usize>, signal_to_names: &HashMap<usize,String>, signals_aux:&Vec<String>) -> String{
    if signals.len() == 0{
        "true".to_string()
    } else if signals.len() == 1{
        let s = signals[0];
        let s_aux = &signals_aux[0];
        format!("(= {} {})", signal_to_names[&s], s_aux)
    } else{
        let mut aux = "(and ".to_string();
        for i in 0..signals.len(){
            aux = format!("{} (= {} {}) ", aux, signal_to_names[&signals[i]], signals_aux[i]);
        }
        aux = format!("{})",aux);
        aux
    }
}