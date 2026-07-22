use std::collections::{HashSet, HashMap};

use utils::read_specification::*;
use std::collections::BTreeMap;
use indexmap::IndexMap;
use utils::structure::*;



pub fn process_correspondence_node_macro(
    structure: &StructureInfo,
    nodeid2pos: &HashMap<usize, usize>,
    macros: &IndexMap<String, MacroDef>,
    node_id: usize,
    macro_name: &String,
    correspondence_node_macro: &mut  HashMap<usize, String>
){

    let pos = nodeid2pos.get(&node_id).unwrap();
    let node_studied = &structure.nodes[*pos];
    let macro_studied: &MacroDef = macros.get(macro_name).unwrap();

    for suc in &node_studied.successors{
        let pos_suc = nodeid2pos.get(suc).unwrap();

        let suc_name = &structure.nodes[*pos_suc].component_name;
        //println!("Suc name: {}", suc_name);
        let macro_suc = macro_studied.components_info.get(suc_name).unwrap();
        correspondence_node_macro.insert(*suc, macro_suc.clone());

        process_correspondence_node_macro(structure, nodeid2pos, macros, *pos_suc, macro_suc, correspondence_node_macro);
    }


}


pub fn get_equivalent_subcomponent_signal_in_macro(signal: usize, studied_macro: &MacroDef, signal_to_name: &BTreeMap<usize, String>)->String{

    let complete_signal_name = signal_to_name.get(&signal).unwrap();
        //println!("Signal name: {}", complete_signal_name);

    // 1. Look for the LAST '[' from the right side of the string
    let (possible_array_access, remaining) = if complete_signal_name.ends_with(']') {
        if let Some(bracket_idx) = complete_signal_name.rfind('[') {
            // Extract the number inside the final brackets
            let number_str = complete_signal_name[bracket_idx + 1..complete_signal_name.len() - 1].to_string();
            let number = number_str.parse::<usize>().unwrap();
            // Cut off the trailing bracket part for the dot analysis
            let left_side = complete_signal_name[..bracket_idx].to_string();
            (Some(number), left_side)

        } else{
            unreachable!()
        }
    } else{
        (None, complete_signal_name.clone())
    };

    // 2. Get the last two dot-separated segments from what remains
    let last_access: Vec<&str> = remaining.rsplit('.').take(2).collect();
    let signal_name: String = format!("{}.{}", last_access[1], last_access[0]);


    let signal_info_macro = studied_macro.vars_info.get(&signal_name).unwrap();
    if signal_info_macro.is_array(){
        assert!(possible_array_access.is_some());
        signal_info_macro.as_array().unwrap()[possible_array_access.unwrap()].to_string()
    } else{
        signal_info_macro.to_string()
    }

}

pub fn get_equivalent_signal_in_macro(signal: usize, studied_macro: &MacroDef, signal_to_name: &BTreeMap<usize, String>)->String{

    let complete_signal_name = signal_to_name.get(&signal).unwrap();

    //println!("The complete signal name is {}", complete_signal_name);
    // 1. Look for the LAST '[' from the right side of the string
    let (possible_array_access, remaining) = if complete_signal_name.ends_with(']') {
        if let Some(bracket_idx) = complete_signal_name.rfind('[') {
            // Extract the number inside the final brackets
            let number_str = complete_signal_name[bracket_idx + 1..complete_signal_name.len() - 1].to_string();
            let number = number_str.parse::<usize>().unwrap();
            // Cut off the trailing bracket part for the dot analysis
            let left_side = complete_signal_name[..bracket_idx].to_string();
            (Some(number), left_side)

        } else{
            unreachable!()
        }
    } else{
        (None, complete_signal_name.clone())
    };

    // 2. Get the last dot-separated segments from what remains
    let last_access: Vec<&str> = remaining.rsplit('.').take(1).collect();
    let signal_name: String = last_access[0].to_string();
    //println!("The accessed signal name is {}", signal_name);
    //println!("The vars of the macro are {:?}", studied_macro.vars_info);

    let signal_info_macro = studied_macro.vars_info.get(&signal_name).unwrap();
    if signal_info_macro.is_array(){
        assert!(possible_array_access.is_some());
        let acc = &signal_info_macro.as_array().unwrap()[possible_array_access.unwrap()];
        acc.as_str().unwrap_or_default().to_string()
    } else{
        signal_info_macro.as_str().unwrap_or_default().to_string()
    }

}

pub fn get_input_signals_macro(number_inputs: usize, studied_macro: &MacroDef) -> Vec<String>{
    let mut inputs = Vec::new();
    let mut input_var_index = 0;
    while inputs.len() < number_inputs{
        let arg_name = format!("%arg{}", input_var_index);
        let signal_info_macro = studied_macro.vars_info.get(&arg_name).unwrap();
        if signal_info_macro.is_array(){
            if let Some(array) = signal_info_macro.as_array() {
                for s in array {
                    let s_str: String = s.as_str().unwrap_or_default().to_string();
                    inputs.push(s_str);
                }
            }
        } else{
            let s_str: String = signal_info_macro.as_str().unwrap_or_default().to_string();
            inputs.push(s_str);
        }

        input_var_index += 1;
    }

    inputs
}

pub fn get_all_signals_macro(studied_macro: &MacroDef)-> Vec<String>{
    let mut signals = Vec::new();
    for v in &studied_macro.params{
        signals.push(v.name.clone());
    }
    signals
}


    pub fn build_call_macro(name: &String, params: &Vec<VarInfo>, mut content: String)-> String{
        //(define-fun @IsZero_0 ((v_0 FFp) (v_7 FFp) (v_1 FFp) (v_2 FFp) (v_3 FFp) (v_4 FFp) (v_5 FFp) (v_6 FFp)) Bool

        
        let mut macro_to_build = format!("(define-fun {} (", name);
        for par in params{
            macro_to_build.push_str(&format!("(macro_{} FF0) ", par.name));
        }
        macro_to_build.push_str(") Bool\n");


       use regex::{Regex, escape};

        for target in params {
            let regex_pattern = format!(r"\b{}\b", escape(&target.name));
            let re = Regex::new(&regex_pattern).unwrap();
    
            let replacement = format!("macro_{}", target.name);
            content = re.replace_all(&content, replacement.as_str()).into_owned();
    
        }
        macro_to_build.push_str(&content);
        macro_to_build.push_str(")\n");
        macro_to_build

    }


pub fn build_macros(macro_defs: &IndexMap<String, MacroDef>, to_include: &HashSet<String>)-> IndexMap<String, String>{
    
    let mut macro_formulas = IndexMap::new();

    for (name_macro, def) in macro_defs{
        if to_include.contains(name_macro){
            let new_macro = build_call_macro(&name_macro, &def.params, def.formula.clone());
            macro_formulas.insert(name_macro.clone(), new_macro);

        } else{
            let empty_formula = "true";
            let new_macro = build_call_macro(&name_macro, &def.params, empty_formula.to_string());
            macro_formulas.insert(name_macro.clone(), new_macro);
        }
    }

    macro_formulas

}
