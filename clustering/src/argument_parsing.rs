use clap::{Parser, ValueEnum};
use strum_macros::{Display};

#[derive(Debug, Display, Copy, Clone, ValueEnum)]
pub enum GraphBackend {
    #[strum(serialize = "graphrs")]
    GraphRS,
    #[strum(serialize = "singleclustering")]
    SingleClustering
}

#[derive(Debug, Display, Copy, Clone, ValueEnum)]
pub enum EquivalenceMode {
    #[strum(serialize = "total")]
    Total,
    #[strum(serialize = "structural")]
    Structural,
    #[strum(serialize = "local")]
    Local,
    #[strum(serialize = "none")]
    None
}

#[derive(Parser)]
#[command(version, about, long_about = None)]
pub struct Args {
    // filepath to input circuit
    pub filepath: String,

    #[arg(short, default_value=".")]
    pub out_directory: String,

    #[arg(short, long, conflicts_with="target_size")]
    // specifies the rsolution used in the modularity-based clustering algorithms
    pub resolution: Option<f64>,

    #[arg(short='x', long, conflicts_with="resolution")]
    // specifies the target_size used in the modularity-based clustering algorithms
    pub target_size: Option<f64>,

    #[arg(short, long, value_enum, default_value_t=GraphBackend::GraphRS)]
    pub graph_backend: GraphBackend,

    #[arg(short, long="equivalence", value_enum, default_value_t=EquivalenceMode::Structural)]
    pub equivalence_mode: EquivalenceMode,

    #[arg(long)]
    pub debug: bool
}