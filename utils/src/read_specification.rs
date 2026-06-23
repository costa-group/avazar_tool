use serde::{Serialize,Deserialize};
use std::collections::HashMap;
use std::fs::File;
use std::io::BufReader;
use std::path::Path;
use std::error::Error;
use indexmap::IndexMap;




/// A single variable / parameter entry: `{ "name": "v_0", "type": "ff" }`.
#[derive(Deserialize, Serialize, Debug, Clone)]
pub struct VarInfo {
    pub name: String,
    #[serde(rename = "type")]
    pub var_type: String,
}

/// One entry in the `macros` map.
/// `vars_info` values may be a string, an integer, or an array of strings,
/// so they are kept as raw `serde_json::Value`.
#[derive(Deserialize, Serialize, Debug, Clone)]
pub struct MacroDef {
    pub params: Vec<VarInfo>,
    pub vars_info: HashMap<String, serde_json::Value>,
    pub components_info: HashMap<String, String>,
    pub formula: String,
}



fn value_to_strings(v: Option<&serde_json::Value>) -> Vec<String> {
    match v {
        Some(serde_json::Value::String(s)) => vec![s.clone()],
        Some(serde_json::Value::Array(arr)) => {
            arr.iter().filter_map(|v| v.as_str().map(str::to_string)).collect()
        }
        _ => vec![],
    }
}

/// The top-level `main` section (distinct from the `main` entry inside `macros`).
#[derive(Deserialize, Serialize, Debug, Clone)]
pub struct MainSection {
    pub vars: Vec<VarInfo>,
    pub formula: String,
}

/// Top-level structure of the concrete specification JSON.
#[derive(Deserialize, Serialize, Debug, Clone)]
pub struct SpecificationInfo {
    pub prime: u64,
    pub macros: IndexMap<String, MacroDef>,
    pub main: MainSection,
}

pub fn read_smt_specification<P: AsRef<Path>>(path: P) -> Result<SpecificationInfo, Box<dyn Error>> {
    let file = File::open(path)?;
    let reader = BufReader::new(file);
    let u: SpecificationInfo = serde_json::from_reader(reader)?;
    Ok(u)
}

