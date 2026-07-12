mod circuit_implementation;
mod constraint_implementation;
mod encodable_implementation;
mod read_r1cs;

use crate::algebra::ArithmeticExpression;

//This struct contained all the sections

pub struct HeaderData {
    pub field: BigInt,
    pub field_size: usize,
    pub total_wires: usize,
    pub public_outputs: usize,
    pub public_inputs: usize,
    pub private_inputs: usize,
    pub number_of_labels: usize,
    pub number_of_constraints: usize,
}

pub struct R1CSData {
    pub header_data: HeaderData,
    pub constraints: Vec<R1CSConstraint<usize>>,
    pub signals: Vec<usize>,
    custom_gates: bool,
    custom_gates_used_data: Option<Vec<(String, Vec<BigInt>)>>,
    custom_gates_applied_data: Option<Vec<(usize, Vec<usize>)>>,
}

#[derive(Clone, Debug)]
pub struct R1CSConstraint<Signal>
where
    Signal: Hash + Eq,
{
    pub(crate) a: HashMap<Signal, BigInt>,
    pub(crate) b: HashMap<Signal, BigInt>,
    pub(crate) c: HashMap<Signal, BigInt>,
}

fn print_hashmap<C: Display>(hm: HashMap<C, BigInt>) -> String {
    let mut result = String::new();
    for (key, value) in hm.iter() {
        result.push_str(&format!("{}: {},\n", key, value));
    }
    result
}

use std::fmt;

impl<C: Default + Clone + Display + Hash + Eq> fmt::Display for R1CSConstraint<C> {

    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{{\n  a: {},\n  b: {},\n  c: {}\n}}",
            print_hashmap(self.a.clone()),
            print_hashmap(self.b.clone()),
            print_hashmap(self.c.clone())
        )
    }
}

impl<C: Default + Clone + Display + Hash + Eq> R1CSConstraint<C> {
    pub fn new(a: HashMap<C, BigInt>, b: HashMap<C, BigInt>, c: HashMap<C, BigInt>) -> R1CSConstraint<C> {
        Constraint { a, b, c }
    }

    pub fn empty() -> R1CSConstraint<C> {
        Constraint::new(
            HashMap::with_capacity(0),
            HashMap::with_capacity(0),
            HashMap::with_capacity(0),
        )
    }

    pub fn constant_coefficient() -> C {
        ArithmeticExpression::constant_coefficient()
    }
    pub fn apply_correspondence_and_drop<K>(
        constraint: R1CSConstraint<C>,
        symbol_correspondence: &HashMap<C, K>,
    ) -> R1CSConstraint<K>
    where
        K: Default + Clone + Display + Hash + Eq,
    {
        Constraint::apply_correspondence(&constraint, symbol_correspondence)
    }

    pub fn apply_correspondence<K>(
        constraint: &R1CSConstraint<C>,
        symbol_correspondence: &HashMap<C, K>,
    ) -> R1CSConstraint<K>
    where
        K: Default + Clone + Display + Hash + Eq,
    {
        let a = apply_raw_correspondence(&constraint.a, symbol_correspondence);
        let b = apply_raw_correspondence(&constraint.b, symbol_correspondence);
        let c = apply_raw_correspondence(&constraint.c, symbol_correspondence);
        Constraint::new(a, b, c)
    }

    // Constraint simplifications

    pub fn is_linear(constraint: &R1CSConstraint<C>) -> bool {
        constraint.a.is_empty() && constraint.b.is_empty()
    }

    pub fn clear_signal_from_linear(
        constraint: R1CSConstraint<C>,
        signal: &C,
        field: &BigInt,
    ) -> Substitution<C> {
        debug_assert!(Constraint::is_linear(&constraint));
        debug_assert!(constraint.c.contains_key(signal));
        let raw_expression = Constraint::clear_signal(constraint.c, &signal, field);
        Substitution { from: signal.clone(), to: raw_expression }
    }

    pub fn clear_signal_from_linear_not_normalized(
        constraint: R1CSConstraint<C>,
        signal: &C,
        field: &BigInt,
    ) -> (BigInt, Substitution<C>) {
        debug_assert!(Constraint::is_linear(&constraint));
        debug_assert!(constraint.c.contains_key(signal));
        let (coefficient, raw_expression) = Constraint::clear_signal_not_normalized(constraint.c, &signal, field);
        (coefficient, Substitution {from: signal.clone(), to: raw_expression})
    }

    pub fn take_cloned_signals(&self) -> HashSet<C> {
        let mut signals = HashSet::new();
        for signal in self.a().keys() {
            signals.insert(signal.clone());
        }
        for signal in self.b().keys() {
            signals.insert(signal.clone());
        }
        for signal in self.c().keys() {
            signals.insert(signal.clone());
        }
        signals.remove(&Constraint::constant_coefficient());
        signals
    }
    pub fn take_signals(&self) -> HashSet<&C> {
        let cc: C = Constraint::constant_coefficient();
        let mut signals = HashSet::new();
        for signal in self.a().keys() {
            signals.insert(signal);
        }
        for signal in self.b().keys() {
            signals.insert(signal);
        }
        for signal in self.c().keys() {
            signals.insert(signal);
        }
        HashSet::remove(&mut signals, &cc);
        signals
    }

    pub fn take_only_linear_signals(&self) -> HashSet<&C> {
        let cc: C = Constraint::constant_coefficient();
        let mut signals = HashSet::new();
        for signal in self.c().keys() {
            signals.insert(signal);
        }
        for signal in self.a().keys() {
            signals.remove(signal);
        }
        for signal in self.b().keys() {
            signals.remove(signal);
        }
        HashSet::remove(&mut signals, &cc);
        signals
    }

    fn clear_signal(
        mut symbols: HashMap<C, BigInt>,
        key: &C,
        field: &BigInt,
    ) -> HashMap<C, BigInt> {
        let key_value = symbols.remove(&key).unwrap();
        assert!(!key_value.is_zero());
        let value_to_the_right = modular_arithmetic::mul(&key_value, &BigInt::from(-1), field);
        ArithmeticExpression::initialize_hashmap_for_expression(&mut symbols);
        let arithmetic_result = ArithmeticExpression::divide_coefficients_by_constant(
            &value_to_the_right,
            &mut symbols,
            field,
        );
        assert!(arithmetic_result.is_ok());
        remove_zero_value_coefficients(symbols)
    }

    fn clear_signal_not_normalized(
        mut symbols: HashMap<C, BigInt>,
        key: &C,
        field: &BigInt,
    ) -> (BigInt, HashMap<C, BigInt>) {
        let key_value = symbols.remove(&key).unwrap();
        assert!(!key_value.is_zero());
        let value_to_the_right = modular_arithmetic::mul(&key_value, &BigInt::from(-1), field);
        ArithmeticExpression::initialize_hashmap_for_expression(&mut symbols);
        (value_to_the_right, symbols)
    }

    pub fn apply_substitution(
        constraint: &mut R1CSConstraint<C>,
        substitution: &Substitution<C>,
        field: &BigInt,
    ) {
        raw_substitution(&mut constraint.a, substitution, field);
        raw_substitution(&mut constraint.b, substitution, field);
        raw_substitution(&mut constraint.c, substitution, field);
        //Constraint::fix_constraint(constraint, field);
    }

    pub fn remove_zero_value_coefficients(constraint: &mut R1CSConstraint<C>) {
        constraint.a = remove_zero_value_coefficients(std::mem::take(&mut constraint.a));
        constraint.b = remove_zero_value_coefficients(std::mem::take(&mut constraint.b));
        constraint.c = remove_zero_value_coefficients(std::mem::take(&mut constraint.c));
    }

    pub fn fix_constraint(constraint: &mut R1CSConstraint<C>, field: &BigInt) {
        fix_raw_constraint(&mut constraint.a, &mut constraint.b, &mut constraint.c, field);
    }

    pub fn is_empty(&self) -> bool {
        self.a.is_empty() && self.b.is_empty() && self.c.is_empty()
    }

    pub fn has_constant_coefficient(&self) -> bool {
        self.a.contains_key(&Constraint::constant_coefficient())
            || self.b.contains_key(&Constraint::constant_coefficient())
            || self.a.contains_key(&Constraint::constant_coefficient())
    }

    pub fn a(&self) -> &HashMap<C, BigInt> {
        &self.a
    }

    pub fn print_pretty_constraint(&self) {
        println!("--- Printing constraint");
        println!("A: {}", ArithmeticExpression::string_from_coefficients(self.a()));
        println!("B: {}", ArithmeticExpression::string_from_coefficients(self.b()));
        println!("C: {}", ArithmeticExpression::string_from_coefficients(self.c()));
    }

    pub fn constraint_to_smt2(&self, signal_to_smt2_name: &HashMap<C,String>) -> String{
        
        let right_side: String = if self.a.is_empty() || self.b.is_empty(){
            format!("(as ff0 FF0)")
        } else{
            let mul = format!("(ff.mul {} {})",
                ArithmeticExpression::coefficients_to_smt2(self.a(),signal_to_smt2_name),
                ArithmeticExpression::coefficients_to_smt2(self.b(),signal_to_smt2_name)
            );
            mul
        };
        let left_side: String = if self.c.is_empty(){
            format!("(as ff0 FF0)")
        } else{
            ArithmeticExpression::coefficients_to_smt2(self.c(),signal_to_smt2_name)
        };
        format!("(= {} {})", left_side, right_side)
    }

    pub fn constraint_to_smt2_old(&self, signal_to_smt2_name: &HashMap<C,String>) -> String{
        
        let right_side = if self.a.is_empty() || self.b.is_empty(){
            ArithmeticExpression::coefficients_to_smt2_old(self.c(),signal_to_smt2_name)
        } else{
            let mul = format!("(* {} {})",
                ArithmeticExpression::coefficients_to_smt2_old(self.a(),signal_to_smt2_name),
                ArithmeticExpression::coefficients_to_smt2_old(self.b(),signal_to_smt2_name)
            );
            if self.c.is_empty(){
                mul
            } else{
                format!("(+ {} {})",
                    mul,
                    ArithmeticExpression::coefficients_to_smt2_old(self.c(),signal_to_smt2_name)
                )
            }
        };
        format!("(= 0 {})", right_side)
    }


    pub fn b(&self) -> &HashMap<C, BigInt> {
        &self.b
    }

    pub fn c(&self) -> &HashMap<C, BigInt> {
        &self.c
    }

    pub fn is_equality(&self, field: &BigInt) -> bool {
        signal_equals_signal(&self.a, &self.b, &self.c, field)
    }

    pub fn is_constant_equality(&self) -> bool {
        signal_equals_constant(&self.a, &self.b, &self.c)
    }

    pub fn into_arithmetic_expressions(self) -> (ArithmeticExpression<C>, ArithmeticExpression<C>, ArithmeticExpression<C>) {
        (
            ArithmeticExpression::Linear { coefficients: self.a },
            ArithmeticExpression::Linear { coefficients: self.b },
            ArithmeticExpression::Linear { coefficients: self.c }
        )
    }

}