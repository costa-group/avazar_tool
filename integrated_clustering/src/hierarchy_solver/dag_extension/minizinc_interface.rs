use serde_json::{Map, Value};
use std::fs::File;
use std::io::{BufWriter, BufReader};
use std::path::Path;
use std::io::Write;
use std::error::Error;
use std::process::Command;

use circuit_graphing::directed_acyclic_graph::mixed_graph::MixedGraph;

fn is_2d_matrix(arr: &[Value]) -> Option<(usize, usize)> {
    if arr.is_empty() {
        return Some((0, 0));
    }

    let first_row = arr.get(0)?.as_array()?;
    let cols = first_row.len();

    for row in arr {
        let r = row.as_array()?;
        if r.len() != cols {
            return None; // jagged -> not a matrix
        }
    }

    Some((arr.len(), cols))
}

fn escape_string(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

fn value_to_dzn(v: &Value) -> String {
    match v {
        Value::Null => "undefined".to_string(),
        Value::Bool(b) => b.to_string(),
        Value::Number(n) => n.to_string(),
        Value::String(s) => format!("\"{}\"", escape_string(s)),
        Value::Array(arr) => {
            if let Some((rows, cols)) = is_2d_matrix(arr) {
                let elems: Vec<String> = arr.iter().flat_map(|row| row.as_array().unwrap().iter().map(value_to_dzn) ).collect();
                format!(
                    "array2d(1..{}, 1..{}, [{}])",
                    rows, cols, elems.join(",")
                )
            } else {
                let elems: Vec<String> = arr.iter().map(value_to_dzn).collect();
                format!(
                    "array1d(1..{}, [{}])",
                    elems.len(), elems.join(",")
                )
            }
        }
        Value::Object(_) => {
            // Nested objects are not native in .dzn; usually flattened beforehand
            panic!("Nested objects should be flattened before conversion to .dzn");
        }
    }
}

fn write_json_as_dzn<P: AsRef<Path>>(file: P, data: &Map<String, Value>) -> Result<(), Box<dyn Error>> {

    let file = File::create(file)?;
    let mut writer = BufWriter::new(file);

    for (key, value) in data.into_iter() {
        let dzn_value = value_to_dzn(&value);
        writeln!(writer, "{} = {};", key, dzn_value)?;
    }

    writer.flush()?;
    Ok(())
}

pub fn extend_dag_minizinc(graph: &MixedGraph, viable_arcs: Vec<(usize, usize)>) -> Vec<(usize, usize)> {

    let fixed_arcs: Vec<Value> = graph.dir_adjacencies.iter().enumerate().flat_map(|(idx, adj)| adj.iter().copied().map(move |other| Value::Array(vec![Value::Number((other+1).into()), Value::Number((idx+1).into())]))).collect();

    let mut data = Map::new();
    data.insert("n".to_string(), graph.n.into());
    data.insert("num_fixed_arcs".to_string(), fixed_arcs.len().into());
    data.insert("fixed_arcs".to_string(), Value::Array(fixed_arcs));

    let var_arcs: Vec<Value> = viable_arcs.iter().map(|&(u, v)| Value::Array(vec![Value::Number((u+1).into()), Value::Number((v+1).into())])).collect();
    data.insert("num_var_arcs".to_string(), var_arcs.len().into());
    data.insert("var_arcs".to_string(), Value::Array(var_arcs));

    write_json_as_dzn("data.dzn", &data).expect("Error in writing constraints to dzn");

    // Obviously this isn't great either
    let out = Command::new("minizinc").arg("--solver").arg("gecode").arg("../integrated_clustering/src/hierarchy_solver/dag_extension/hierarchy-dag.mzn").arg("data.dzn").arg("--json-stream").output().expect("error when running minizinc");
    let mut results: Vec<Value> = serde_json::Deserializer::from_slice(&out.stdout).into_iter().filter(|x| x.is_ok()).map(|x| x.unwrap()).collect();
    // ugly as all hell line but its just extracting the solution from the minizinc output format
    let optimal_solution: Vec<bool> = results.swap_remove(results.len() - 2).as_object().unwrap()["output"].as_object().unwrap()["raw"].as_str().unwrap().chars().into_iter().filter_map(|x| match x {'1' => Some(true), '0' => Some(false), _ => None}).collect();
    let chosen_arcs = viable_arcs.into_iter().enumerate().filter(|(x, _)| optimal_solution[*x]).map(|(_, e)| e).collect();
    chosen_arcs

}