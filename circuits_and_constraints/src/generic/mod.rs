mod circuit_implementation;
mod constraint_implementation;

use std::collections::{HashSet};
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct LookupData {
    pub left: Vec<ExpressionData>,
    pub right: Vec<ExpressionData>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct AIRData {
    pub constraints: Vec<ExpressionData>,
    pub signals: Vec<usize>,
    pub inputs: Vec<usize>,
    pub outputs: Vec<usize>,
    pub lookups: Vec<LookupData>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct AIRDataWrapper {
    pub constraints: Vec<ExpressionWrapper>,
    pub signals: Vec<usize>,
    pub inputs: HashSet<usize>,
    pub outputs: HashSet<usize>,
    pub lookups: Vec<LookupData>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct BinaryExpressionData {
    pub operator: String,
    pub left: Box<ExpressionData>,
    pub right: Box<ExpressionData>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct UnaryExpressionData {
    pub operator: String,
    pub value: Box<ExpressionData>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct RangeData {
    pub expression: Box<ExpressionData>,
    pub min: String,
    pub max: String,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub enum ExpressionData {
    BinaryExpression(BinaryExpressionData),
    UnaryExpression(UnaryExpressionData),
    Signal(usize),
    Constant(String),
    Range(RangeData),
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct ExpressionWrapper {
    pub expression: ExpressionData,
    pub signals: Vec<usize>,
}