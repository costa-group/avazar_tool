use std::str::FromStr;
use std::cmp::max;
use std::collections::{HashMap, HashSet};
use num_bigint::BigInt;
use z3::ast;

use crate::{modular_arithmetic, algebra::{EncodableConstraint, Constraint, ExecutedInequation}};

pub type Signal2Bounds = HashMap<usize, ExecutedInequation<usize>>;

pub fn is_positive(a: &BigInt, field: &BigInt) -> bool{
    a <= &(field / BigInt::from(2))
}

//This function only works if 0 <= a <= field - 1
pub fn to_neg(a: &BigInt, field: &BigInt) -> BigInt{
    if a < &(field/BigInt::from(2)){
        a.clone()
    }
    else {
        a - field
    }
}

fn solve_signal_plus_coef(a: &HashMap<usize, BigInt>, field: &BigInt) -> Option<(usize,BigInt)> {

    if (a.len() == 1 && !a.contains_key(&0)) || (a.len() == 2 && a.contains_key(&0)){
        let mut to_solve_signal = 0;
        let mut coef_indep = &BigInt::from(0);
        let mut coef_signal =  &BigInt::from(0);
        for (signal, coef) in a{
            if *signal == 0 {
                coef_indep = coef;
            } else{
                to_solve_signal = *signal;
                coef_signal = coef;
            }
        }
        match modular_arithmetic::div(&modular_arithmetic::prefix_sub(coef_indep, field), coef_signal, field){
            Ok(value) => Some((to_solve_signal, value)),
            Err(_) => None
        }
    } else{
        Option::None
    }
}

fn update_bounds_signal(deductions: &mut Signal2Bounds, signal: usize, min: BigInt, max: BigInt, field: &BigInt) -> bool{
    let pos_bounds = deductions.get_mut(&signal);

    if &min >= &BigInt::from(0) && &max <= &(field - &BigInt::from(1)){
        match pos_bounds{
            Option::None => {
    
                deductions.insert(
                    signal,
                    ExecutedInequation{signal, min, max}
                );
                true
            }
            
    
            Option::Some(bounds) => {
                if !(&bounds.min <= &BigInt::from(0) && &max >= &(field - &BigInt::from(1))){
                    bounds.update_bounds(min, max)
                } else{
                    false
                }
            }
       }
    } else{
        false
    }
}

fn check_consecutive_field_round(min: &BigInt, max: &BigInt, field: &BigInt)-> bool{
    // queremos que acepte cosas como [-1, 1] y lo guarde --> ahora mismo no funciona
    let zero = &BigInt::from(0);
    let two = &BigInt::from(2);
    if min < zero && max >= zero{
        min > &(- field / two) && max <= &(field / two) // o quiza solo que este entro (-field, field)
    } else if min < max{
        min / field == field / field - 1
    } else{
        false
    }
}

fn check_correct_signs(a: &BigInt, b: &BigInt)-> bool{
    // revisar esta también
    let zero = &BigInt::from(0);
    !(a >= zero && b < zero) && !(b >= zero && a < zero) 
}

fn check_same_field_round(a: &BigInt, b: &BigInt, field: &BigInt)-> bool{
    check_correct_signs(a, b) && (a / field == b / field)
}

fn compute_bounds_linear_expression(deductions: &Signal2Bounds, le: &HashMap<usize, BigInt>, field: &BigInt) -> (BigInt, BigInt){
    let mut lower_limit = BigInt::from(0);
    let mut upper_limit = BigInt::from(0);
    for (signal, coef) in le{
        let (min, max) = if deductions.contains_key(&signal){
            let bounds = deductions.get(&signal).unwrap();
            (bounds.min.clone(), bounds.max.clone())
        } else{
            (BigInt::from(0), field - &BigInt::from(1))
        };
        if is_positive(coef, field){
            upper_limit = upper_limit + coef * max;
            lower_limit = lower_limit + coef * min;
        } else{
            let neg_coef = field - coef;
            upper_limit = upper_limit - &neg_coef * min;
            lower_limit = lower_limit - &neg_coef * max;
        }
    }
    (lower_limit, upper_limit)
}

fn compute_bounds_linear_expression_strict(deductions: &Signal2Bounds, le: &HashMap<usize, BigInt>, field: &BigInt) -> (BigInt, BigInt){
    let mut lower_limit = BigInt::from(0);
    let mut upper_limit = BigInt::from(0);
    for (signal, coef) in le{
        let (min, max) = if deductions.contains_key(&signal){
            let bounds = deductions.get(&signal).unwrap();
            if bounds.min >= BigInt::from(0){
                (bounds.min.clone(), bounds.max.clone())
            }
            else {
                (BigInt::from(0), field - &BigInt::from(1))
            }
        } else{
            (BigInt::from(0), field - &BigInt::from(1))
        };
        if is_positive(coef, field){
            upper_limit = upper_limit + coef * max;
            lower_limit = lower_limit + coef * min;
        } else{
            let neg_coef = field - coef;
            upper_limit = upper_limit - &neg_coef * min;
            lower_limit = lower_limit - &neg_coef * max;
        }
    }
    (lower_limit, upper_limit)
}

fn compute_bounds_product(min_1: &BigInt, max_1: &BigInt, min_2: &BigInt, max_2: &BigInt)-> (BigInt, BigInt){
    let zero = &BigInt::from(0);
    if min_1 >= zero{ // bounds_1 are positive
        if min_2 >= zero{ // bounds_2 are two-positive
            (min_1 * min_2, max_1 * max_2)
        } else if max_2 >= zero{ // bounds_2 are neg/pos
            (max_1 * min_2, max_1 * max_2)
        } else{ // bounds_2 are two_negative
            (max_1 * min_2, min_1 * max_2)
        }
    } else if max_1 >= zero{ // bounds_1 are neg/pos
        if min_2 >= zero{ // bounds_2 are two-positive
            (min_1 * max_2, max_1 * max_2)
        } else if max_2 >= zero{ // bounds_2 are neg/pos
            (max(min_1 * max_2, min_2 * max_1), max(min_1 * min_2, max_1 * max_2))
        } else{ // bounds_2 are two_negative
            (max_1 * min_2, min_1 * min_2)
        }
    } else{ // bounds_1 are negative
        if min_2 >= zero{ // bounds_2 are two-positive
            (min_1 * max_2, max_1 * min_2)
        } else if max_2 >= zero{ // bounds_2 are neg/pos
            (min_1 * max_2, min_1 * min_2)
        } else{ // bounds_2 are two_negative
            (max_1 * max_2, min_1 * min_2)
        }
    }
}

impl EncodableConstraint for Constraint<usize> {
    fn constraint_to_smt2(&self, signal_to_name: &HashMap<usize, String>) -> String {Self::constraint_to_smt2(self, signal_to_name)}
    fn take_signals(&self) -> HashSet<&usize> {Self::take_signals(self)}
    fn take_only_linear_signals(&self) -> HashSet<&usize> {Self::take_only_linear_signals(self)}
    fn fix_constraint(&mut self, field: &BigInt) -> () {Constraint::fix_constraint(self, field);}

    fn declare_constraint_z3(&self, solver: &z3::Solver, signals_to_z3: &HashMap<usize, z3::ast::Int>, field: &BigInt) -> () {
        let mut value_a = z3::ast::Int::from_u64(0);
        let mut value_b = z3::ast::Int::from_u64(0);
        let mut value_c = z3::ast::Int::from_u64(0);

        for (signal, value) in self.a() {
            if *signal == 0 {
                value_a += &z3::ast::Int::from_str(&value.to_string()).unwrap()
            } else {
                value_a += signals_to_z3.get(signal).unwrap()
                    * &z3::ast::Int::from_str(&value.to_string()).unwrap();
            }
        }
        for (signal, value) in self.b() {
            if *signal == 0 {
                value_b += &z3::ast::Int::from_str(&value.to_string()).unwrap()
            } else {
                value_b += signals_to_z3.get(signal).unwrap()
                    * &z3::ast::Int::from_str(&value.to_string()).unwrap();
            }
        }
        for (signal, value) in self.c() {
            if *signal == 0 {
                value_c += &z3::ast::Int::from_str(&value.to_string()).unwrap()
            } else {
                value_c += signals_to_z3.get(signal).unwrap()
                    * &z3::ast::Int::from_str(&value.to_string()).unwrap();
            }
        }

        let prime = z3::ast::Int::from_str(&field.to_string()).unwrap();
        let value_left = (value_c - (value_a * value_b)).modulo(&prime);
        let value_right = z3::ast::Int::from_i64(0);
        solver.assert(&value_left.eq(&value_right));

    }

    fn constraint_to_mod0_assert(&self, signal_to_name: &HashMap<usize, String>, prime: &BigInt) -> String {

        fn sum_terms(terms: Vec<String>) -> String {
            if terms.is_empty() {
                return "0".to_string();
            }
            if terms.len() == 1 {
                return terms[0].clone();
            }
            format!("(+ {})", terms.join(" "))
        }

        fn linear_expr_to_int(coeffs: &HashMap<usize, BigInt>, signal_to_name: &HashMap<usize, String>) -> String {
            let mut terms = Vec::new();

            for (signal, value) in coeffs {
                if value == &BigInt::from(0) {
                    continue;
                }

                if *signal == 0 {
                    terms.push(value.to_string());
                    continue;
                }

                let s = signal_to_name.get(signal).unwrap();
                if value == &BigInt::from(1) {
                    terms.push(s.clone());
                } else {
                    terms.push(format!("(* {} {})", s, value));
                }
            }

            sum_terms(terms)
        }

        let a = linear_expr_to_int(self.a(), signal_to_name);
        let b = linear_expr_to_int(self.b(), signal_to_name);
        let c = linear_expr_to_int(self.c(), signal_to_name);

        let product = if self.a().is_empty() || self.b().is_empty() {
            "0".to_string()
        } else {
            format!("(* {} {})", a, b)
        };

        format!("(assert (= (mod (- {} {}) {}) 0))", c, product, prime)
    }

    fn insert_constraint_in_smt_z3(&self,
        solver: &z3::Solver,
        signals_to_smt_symbols: &HashMap<usize, z3::ast::Int>,
        field: &BigInt,
        deductions: &Signal2Bounds,
        num_k: usize,
        p: &z3::ast::Int,
        _verbose: bool,
    ) -> () {
        let mut value_a = z3::ast::Int::from_u64(0);
        let mut value_b = z3::ast::Int::from_u64(0);
        let mut value_c = z3::ast::Int::from_u64(0);

        for (signal, value) in self.a() {
            if *signal == 0 {
                value_a += &z3::ast::Int::from_str(&to_neg(value, field).to_string()).unwrap()
            } else {
                value_a += signals_to_smt_symbols.get(signal).unwrap()
                    * &z3::ast::Int::from_str(&to_neg(value, field).to_string()).unwrap();
            }
        }
        for (signal, value) in self.b() {
            if *signal == 0 {
                value_b += &z3::ast::Int::from_str(&to_neg(value, field).to_string()).unwrap()
            } else {
                value_b += signals_to_smt_symbols.get(signal).unwrap()
                    * &z3::ast::Int::from_str(&to_neg(value, field).to_string()).unwrap();
            }
        }
        for (signal, value) in self.c() {
            if *signal == 0 {
                value_c += &z3::ast::Int::from_str(&to_neg(value, field).to_string()).unwrap()
            } else {
                value_c += signals_to_smt_symbols.get(signal).unwrap()
                    * &z3::ast::Int::from_str(&to_neg(value, field).to_string()).unwrap();
            }
        }

        let a = self.a();
        let b = self.b();
        let c = self.c();
        let (lower_limit_a, upper_limit_a) =
            compute_bounds_linear_expression_strict(deductions, &a, field);
        let (lower_limit_b, upper_limit_b) =
            compute_bounds_linear_expression_strict(deductions, &b, field);

        let (lower_limit_ab, upper_limit_ab) = compute_bounds_product(
            &lower_limit_a,
            &upper_limit_a,
            &lower_limit_b,
            &upper_limit_b,
        );

        let (lower_limit_c, upper_limit_c) =
            compute_bounds_linear_expression_strict(deductions, &c, field);

        let lower_limit_k = (&lower_limit_c - &upper_limit_ab) / field;
        let upper_limit_k = if (&upper_limit_c - &lower_limit_ab) / field > BigInt::from(0)
            && (&upper_limit_c - &lower_limit_ab) % field != BigInt::from(0)
        {
            (&upper_limit_c - &lower_limit_ab) / field + BigInt::from(1)
        } else {
            (&upper_limit_c - &lower_limit_ab) / field
        };

        let lower_limit_k_a = &lower_limit_a / field;
        let upper_limit_k_a = if &upper_limit_a / field > BigInt::from(0)
            && &upper_limit_a % field != BigInt::from(0)
        {
            &upper_limit_a / field + BigInt::from(1)
        } else {
            &upper_limit_a / field
        };

        let lower_limit_k_b = &lower_limit_b / field;
        let upper_limit_k_b = if &upper_limit_b / field > BigInt::from(0)
            && &upper_limit_b % field != BigInt::from(0)
        {
            &upper_limit_b / field + BigInt::from(1)
        } else {
            &upper_limit_b / field
        };

        let lower_limit_k_c = &lower_limit_c / field;
        let upper_limit_k_c = if &upper_limit_c / field > BigInt::from(0)
            && &upper_limit_c % field != BigInt::from(0)
        {
            &upper_limit_c / field + BigInt::from(1)
        } else {
            &upper_limit_c / field
        };

        // Apply transformation rule A * B = 0 => (A = 0) \/ (B = 0)
        if &upper_limit_c == &lower_limit_c && &upper_limit_c == &BigInt::from(0) {
            let mut value_or = z3::ast::Bool::from_bool(false);

            let value_or_a = if upper_limit_k_a == lower_limit_k_a {
                let value_right =
                    z3::ast::Int::from_str(&lower_limit_k_a.to_string()).unwrap() * p;
                value_a.eq(&value_right)
            } else {
                let k = z3::ast::Int::new_const(format!("k_{}_a", num_k));

                let value_right = &k * p;
                solver.assert(&k.ge(&z3::ast::Int::from_str(&lower_limit_k_a.to_string()).unwrap()));
                solver.assert(
                    &k.le(&z3::ast::Int::from_str(&upper_limit_k_a.to_string()).unwrap()),
                );

                value_a.eq(&value_right)
            };

            let value_or_b = if upper_limit_k_b == lower_limit_k_b {
                let value_right =
                    z3::ast::Int::from_str(&lower_limit_k_b.to_string()).unwrap() * p;
                value_b.eq(&value_right)
            } else {
                let k = z3::ast::Int::new_const(format!("k_{}_b", num_k));

                let value_right = &k * p;
                solver.assert(&k.ge(&z3::ast::Int::from_str(&lower_limit_k_b.to_string()).unwrap()));
                solver.assert(
                    &k.le(&z3::ast::Int::from_str(&upper_limit_k_b.to_string()).unwrap()),
                );

                value_b.eq(&value_right)
            };

            value_or |= value_or_a;
            value_or |= value_or_b;
            solver.assert(&value_or);
        } else {
            // Apply deduction rule A * B = C => (C != 0) \/ (A = 0) \/ (B = 0)

            let condition_c = if upper_limit_k_c == lower_limit_k_c {
                let value_right =
                    z3::ast::Int::from_str(&lower_limit_k_c.to_string()).unwrap() * p;
                value_c.eq(&value_right)
            } else {
                let k = z3::ast::Int::new_const(format!("k_{}_c", num_k));

                let value_right = &k * p;
                solver.assert(&k.ge(&z3::ast::Int::from_str(&lower_limit_k_c.to_string()).unwrap()));
                solver.assert(
                    &k.le(&z3::ast::Int::from_str(&upper_limit_k_c.to_string()).unwrap()),
                );
                value_c.eq(&value_right)
            };

            let condition_a: ast::Bool = if upper_limit_k_a == lower_limit_k_a {
                let value_right =
                    z3::ast::Int::from_str(&lower_limit_k_a.to_string()).unwrap() * p;
                value_a.eq(&value_right)
            } else {
                let k = z3::ast::Int::new_const(format!("k_{}_a", num_k));

                let value_right = &k * p;
                solver.assert(&k.ge(&z3::ast::Int::from_str(&lower_limit_k_a.to_string()).unwrap()));
                solver.assert(
                    &k.le(&z3::ast::Int::from_str(&upper_limit_k_a.to_string()).unwrap()),
                );

                value_a.eq(&value_right)
            };

            let condition_b = if upper_limit_k_b == lower_limit_k_b {
                let value_right =
                    z3::ast::Int::from_str(&lower_limit_k_b.to_string()).unwrap() * p;
                value_b.eq(&value_right)
            } else {
                let k = z3::ast::Int::new_const(format!("k_{}_b", num_k));

                let value_right = &k * p;
                solver.assert(&k.ge(&z3::ast::Int::from_str(&lower_limit_k_b.to_string()).unwrap()));
                solver.assert(
                    &k.le(&z3::ast::Int::from_str(&upper_limit_k_b.to_string()).unwrap()),
                );

                value_b.eq(&value_right)
            };

            let mut value_or = z3::ast::Bool::from_bool(false);
            value_or |= !condition_c;
            value_or |= condition_a;
            value_or |= condition_b;
            solver.assert(&value_or);

            // APPLY TRANSFORMATION RULE REMOVE MOD
            if lower_limit_k == upper_limit_k {
                let value_left = value_c - (value_a * value_b);
                let value_right =
                    z3::ast::Int::from_str(&lower_limit_k.to_string()).unwrap() * p;
                solver.assert(&value_left.eq(&value_right));
            } else {
                let k = z3::ast::Int::new_const(format!("k_{}", num_k));

                let value_left = value_c - (value_a * value_b);
                let value_right = &k * p;
                solver.assert(&k.ge(&z3::ast::Int::from_str(&lower_limit_k.to_string()).unwrap()));
                solver.assert(
                    &k.le(&z3::ast::Int::from_str(&upper_limit_k.to_string()).unwrap()),
                );
                solver.assert(&value_left.eq(&value_right));
            }
        }
    }

    fn apply_deduction_assigned(&self, solver: &z3::Solver, signals_to_smt_symbols_1: &HashMap<usize, z3::ast::Int>, signals_to_smt_symbols_2: &HashMap<usize, z3::ast::Int>) -> () {
        let all_signals = self.take_signals();
        let only_linear_signals = self.take_only_linear_signals();

        // in case there are signals that are only_linear
        for s_deduced in only_linear_signals {
            // Generate the implication all signals in C are deterministic
            //  => s_deduced is deterministic

            let value_right_1 = signals_to_smt_symbols_1.get(s_deduced).unwrap();
            let value_right_2 = signals_to_smt_symbols_2.get(s_deduced).unwrap();
            let right_side = value_right_1.eq(value_right_2);

            let mut left_side = z3::ast::Bool::from_bool(true);

            for s in &all_signals {
                if *s != s_deduced {
                    let value_s_1 = signals_to_smt_symbols_1.get(s).unwrap();
                    let value_s_2 = signals_to_smt_symbols_2.get(s).unwrap();
                    let new_left_side = value_s_1.eq(value_s_2);

                    left_side &= new_left_side;
                }
            }

            let mut value_cond = !left_side;
            value_cond |= &right_side;
            solver.assert(&value_cond);
        }
    }

    fn apply_deduction_rule_homologues(&self, solver: &z3::Solver, signals_to_smt_symbols_1: &HashMap<usize, z3::ast::Int>, signals_to_smt_symbols_2: &HashMap<usize, z3::ast::Int>, deductions: &Signal2Bounds, field: &BigInt, p: &z3::ast::Int) -> () {
        let mut value_a = z3::ast::Int::from_u64(0);
        let mut value_b = z3::ast::Int::from_u64(0);
        let mut value_c = z3::ast::Int::from_u64(0);

        let mut value_a1 = z3::ast::Int::from_u64(0);
        let mut value_b1 = z3::ast::Int::from_u64(0);
        let mut value_c1 = z3::ast::Int::from_u64(0);

        for (signal, value) in self.a() {
            if *signal == 0 {
                value_a += &z3::ast::Int::from_str(&to_neg(value, field).to_string()).unwrap();
                value_a1 += &z3::ast::Int::from_str(&to_neg(value, field).to_string()).unwrap();
            } else {
                value_a += signals_to_smt_symbols_1.get(signal).unwrap()
                    * &z3::ast::Int::from_str(&to_neg(value, field).to_string()).unwrap();
                value_a1 += signals_to_smt_symbols_2.get(signal).unwrap()
                    * &z3::ast::Int::from_str(&to_neg(value, field).to_string()).unwrap();
            }
        }
        for (signal, value) in self.b() {
            if *signal == 0 {
                value_b += &z3::ast::Int::from_str(&to_neg(value, field).to_string()).unwrap();
                value_b1 += &z3::ast::Int::from_str(&to_neg(value, field).to_string()).unwrap();
            } else {
                value_b += signals_to_smt_symbols_1.get(signal).unwrap()
                    * &z3::ast::Int::from_str(&to_neg(value, field).to_string()).unwrap();
                value_b1 += signals_to_smt_symbols_2.get(signal).unwrap()
                    * &z3::ast::Int::from_str(&to_neg(value, field).to_string()).unwrap();
            }
        }
        for (signal, value) in self.c() {
            if *signal == 0 {
                value_c += &z3::ast::Int::from_str(&to_neg(value, field).to_string()).unwrap();
                value_c1 += &z3::ast::Int::from_str(&to_neg(value, field).to_string()).unwrap();
            } else {
                value_c += signals_to_smt_symbols_1.get(signal).unwrap()
                    * &z3::ast::Int::from_str(&to_neg(value, field).to_string()).unwrap();
                value_c1 += signals_to_smt_symbols_2.get(signal).unwrap()
                    * &z3::ast::Int::from_str(&to_neg(value, field).to_string()).unwrap();
            }
        }

        let c_a = self.a();
        let c_b = self.b();
        let c_c = self.c();
        let (lower_limit_a, upper_limit_a) =
            compute_bounds_linear_expression_strict(deductions, &c_a, field);
        let (lower_limit_b, upper_limit_b) =
            compute_bounds_linear_expression_strict(deductions, &c_b, field);
        let (lower_limit_c, upper_limit_c) =
            compute_bounds_linear_expression_strict(deductions, &c_c, field);

        let lower_limit_k_aa = (&lower_limit_a - &upper_limit_a) / field;
        let upper_limit_k_aa = if (&upper_limit_a - &lower_limit_a) / field > BigInt::from(0)
            && (&upper_limit_a - &lower_limit_a) % field != BigInt::from(0)
        {
            (&upper_limit_a - &lower_limit_a) / field + BigInt::from(1)
        } else {
            (&upper_limit_a - &lower_limit_a) / field
        };

        let lower_limit_k_bb = (&lower_limit_b - &upper_limit_b) / field;
        let upper_limit_k_bb = if (&upper_limit_b - &lower_limit_b) / field > BigInt::from(0)
            && (&upper_limit_b - &lower_limit_b) % field != BigInt::from(0)
        {
            (&upper_limit_b - &lower_limit_b) / field + BigInt::from(1)
        } else {
            (&upper_limit_b - &lower_limit_b) / field
        };

        let lower_limit_k_cc = (&lower_limit_c - &upper_limit_c) / field;
        let upper_limit_k_cc = if (&upper_limit_c - &lower_limit_c) / field > BigInt::from(0)
            && (&upper_limit_c - &lower_limit_c) % field != BigInt::from(0)
        {
            (&upper_limit_c - &lower_limit_c) / field + BigInt::from(1)
        } else {
            (&upper_limit_c - &lower_limit_c) / field
        };

        let zero = z3::ast::Int::from_u64(0);

        let condition_aa = if lower_limit_k_aa == upper_limit_k_aa {
            let value_left = &value_a - &value_a1;
            let value_right =
                z3::ast::Int::from_str(&lower_limit_k_aa.to_string()).unwrap() * p;
            value_left.eq(&value_right)
        } else {
            (&value_a - &value_a1).modulo(p).eq(&zero)
        };
        let condition_bb = if lower_limit_k_bb == upper_limit_k_bb {
            let value_left = &value_b - &value_b1;
            let value_right =
                z3::ast::Int::from_str(&lower_limit_k_bb.to_string()).unwrap() * p;
            value_left.eq(&value_right)
        } else {
            (&value_b - &value_b1).modulo(p).eq(&zero)
        };
        let condition_cc = if lower_limit_k_cc == upper_limit_k_cc {
            let value_left = &value_c - &value_c1;
            let value_right =
                z3::ast::Int::from_str(&lower_limit_k_cc.to_string()).unwrap() * p;
            value_left.eq(&value_right)
        } else {
            (&value_c - &value_c1).modulo(p).eq(&zero)
        };

        let mut value_cond = z3::ast::Bool::from_bool(false);
        value_cond |= !&condition_aa;
        value_cond |= !&condition_bb;
        value_cond |= &condition_cc;
        solver.assert(&value_cond);

        let lower_limit_k_a = &lower_limit_a / field;
        let upper_limit_k_a = if &upper_limit_a / field > BigInt::from(0)
            && &upper_limit_a % field != BigInt::from(0)
        {
            &upper_limit_a / field + BigInt::from(1)
        } else {
            &upper_limit_a / field
        };

        let condition_a_not_zero = if lower_limit_k_a == upper_limit_k_a {
            let value_left = &value_a;
            let value_right =
                z3::ast::Int::from_str(&lower_limit_k_a.to_string()).unwrap() * p;
            !value_left.eq(&value_right)
        } else {
            !&value_a.modulo(p).eq(&zero)
        };

        let mut value_cond = z3::ast::Bool::from_bool(false);
        value_cond |= !(&condition_aa & &condition_a_not_zero);
        value_cond |= !&condition_cc;
        value_cond |= &condition_bb;
        solver.assert(&value_cond);

        let lower_limit_k_b = &lower_limit_b / field;
        let upper_limit_k_b = if &upper_limit_b / field > BigInt::from(0)
            && &upper_limit_b % field != BigInt::from(0)
        {
            &upper_limit_b / field + BigInt::from(1)
        } else {
            &upper_limit_b / field
        };

        let condition_b_not_zero = if lower_limit_k_b == upper_limit_k_b {
            let value_left = &value_b;
            let value_right =
                z3::ast::Int::from_str(&lower_limit_k_b.to_string()).unwrap() * p;
            !value_left.eq(&value_right)
        } else {
            !&value_b.modulo(p).eq(&zero)
        };
        let mut value_cond = z3::ast::Bool::from_bool(false);
        value_cond |= !(&condition_bb & condition_b_not_zero);
        value_cond |= !&condition_cc;
        value_cond |= &condition_aa;
        solver.assert(&value_cond);
    }

    fn deduction_rule_apply_bounds_constraint(
        &self,
        deductions: &mut Signal2Bounds,
        field: &BigInt, 
        _verbose: bool,
    )-> Vec<usize> {
        let mut updated_signals = Vec::new();

        let a = self.a();
        let b = self.b();
        let c = self.c();

        let (lower_limit_a, upper_limit_a) = compute_bounds_linear_expression(deductions, &a, field);
        let (lower_limit_b, upper_limit_b) = compute_bounds_linear_expression(deductions, &b, field);

        let (lower_limit_ab, upper_limit_ab) = compute_bounds_product(
            &lower_limit_a, 
            &upper_limit_a, 
            &lower_limit_b, 
            &upper_limit_b
        );

        
        let (lower_limit_c, upper_limit_c) = compute_bounds_linear_expression(deductions, &c, field);

        let lower_limit = lower_limit_c - upper_limit_ab;
        let upper_limit = upper_limit_c - lower_limit_ab;

        for (signal, coef) in c{
            if coef == &BigInt::from(1) || *coef == field - &BigInt::from(1) {
                let (min, max) = if deductions.contains_key(signal){
                    let bounds = deductions.get(signal).unwrap();
                    (bounds.min.clone(), bounds.max.clone())
                } else{
                    (BigInt::from(0), field - BigInt::from(1))
                };
                let (pos_max, pos_min);
                let (valid_bounds, valid_consecutive) = if coef == &BigInt::from(1){
                    let (aux_min, aux_max) = (&upper_limit - max, &lower_limit - min);
                    pos_min = (field - &aux_min) % field;
                    pos_max = (field - &aux_max) % field;
                    (
                        check_same_field_round(&(field - &aux_min), &(field - &aux_max), field),
                        check_consecutive_field_round(&(field - &aux_min), &(field - &aux_max), field)
                    )
                } else{
                    let (aux_min, aux_max) = (&lower_limit + max, &upper_limit + min);
                    pos_min = &aux_min % field;
                    pos_max = &aux_max % field;
                    (
                        check_same_field_round(&aux_min, &aux_max, field),
                        check_consecutive_field_round(&aux_min, &aux_max, field) 
                    )          
                };
        
                if valid_bounds{
                    if update_bounds_signal(deductions, *signal, pos_min, pos_max, field){
                        updated_signals.push(signal.clone());
                    }
                }
                else if false && valid_consecutive{
                    if update_bounds_signal(deductions, *signal, field - pos_min, pos_max, field){
                        updated_signals.push(signal.clone());
                    }
                }
            }
            
        }
        updated_signals
    }

    fn deduction_rule_integrity_domain(&self, deductions: &mut Signal2Bounds, field: &BigInt) -> bool {
        let mut updated_signals = Vec::new();
        let mut completely_studied = false;
        
        let a = self.a();
        let b = self.b();
        let c = self.c();

        if let Option::Some((a_signal, a_value)) = solve_signal_plus_coef(a, field) {
            if let Option::Some((b_signal, b_value)) = solve_signal_plus_coef(b, field) {
                if a_signal == b_signal && c.is_empty() {

                    if a_value > b_value {
                        completely_studied = &a_value - &b_value == BigInt::from(1);
                        if update_bounds_signal(deductions, a_signal, b_value, a_value, field){
                            
                            updated_signals.push(a_signal);
                        }
                    }
                    else {
                        completely_studied = &b_value - &a_value ==  BigInt::from(1);
                        if update_bounds_signal(deductions, a_signal, a_value, b_value, field){
                            
                            updated_signals.push(a_signal);
                        }  
                    }

                }
            }
        }
        completely_studied
    }

}