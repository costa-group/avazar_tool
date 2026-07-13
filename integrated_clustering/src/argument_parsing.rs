use clap::{Parser, ArgAction};
use std::path::PathBuf;
use utils::small_utilities::{GraphBackend, FileType, ClusteringPreprocessing, EquivalenceMode};
use solvers_interface::{PossibleSolver};
use crate::hierarchy_solver::{Property, PreprocessingMethods, DAGExtensionMethod, SolverTarget};

#[derive(Parser)]
#[command(version, about, long_about = None)]
pub struct Args {
    // filepath to input circuit
    pub filepath: PathBuf,

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

    #[arg(short, long="preprocessing", value_enum, default_value_t=ClusteringPreprocessing::None)]
    pub preprocessing: ClusteringPreprocessing,

    #[arg(short, long="file_type", value_enum, default_value_t=FileType::R1CS)]
    pub file_type: FileType,

    #[arg(short, long="equivalence", value_enum, default_value_t=EquivalenceMode::None)]
    pub equivalence_mode: EquivalenceMode,

    #[arg(long)]
    pub leiden_max_iterations: Option<usize>,

    #[arg(long)]
    pub extract_raw_partition: Option<PathBuf>,

    #[arg(long)]
    pub clique_cluster_size: Option<usize>,

    #[arg(long)]
    pub existing_partition: Option<PathBuf>,

    #[arg(long, default_value_t=0, help = "Debugger level, 0 = None, 1 = Minimal Checkpoints, 2 = Detailed Checkpoints")]
    pub debug: usize,

    #[arg(long, value_enum, default_value_t=Property::Determinism)]
    pub property: Property,

    #[arg(long, value_enum, value_delimiter = ',', default_values_t=[PreprocessingMethods::DualDistanceOrdering, PreprocessingMethods::MergeDistanceClasses])]
    pub hierarchy_preprocessing: Vec<PreprocessingMethods>,

    #[arg(long, value_enum, default_value_t=SolverTarget::AllOutput)]
    pub solver_target: SolverTarget,

    #[arg(long, value_enum, default_value_t=PossibleSolver::CIVER)]
    pub solver_option: PossibleSolver,

    #[arg(long, value_enum, default_value_t=DAGExtensionMethod::CyclesCover)]
    pub dag_extension_method: DAGExtensionMethod,

    #[arg(long, default_value_t=8)]
    pub hierarchy_num_cores: usize,

    #[arg(long, default_value_t=250)]
    pub hierarchy_timeout: usize,

    #[arg(long)]
    pub original_structure: Option<PathBuf>,

    #[arg(long)]
    pub extract_integrated_hierarchy: Option<PathBuf>,

    #[arg(long = "deactivate-deduction-assigned", action = ArgAction::SetFalse)]
    pub apply_deduction_assigned: bool,

    #[arg(long, conflicts_with="apply_bidirectional")]
    pub apply_predecessors: bool,

    #[arg(long, conflicts_with="apply_predecessors")]
    pub apply_bidirectional: bool,

    #[arg(long)]
    pub include_niaz3_in_all: bool,

    #[arg(long, default_value_t=0)]
    pub clustering_size: usize,

    #[arg(long, default_value_t=0)]
    pub extra_rounds: usize,

    #[arg(long, default_value_t=500000)]
    pub limit_size: usize,

    #[arg(long, default_value_t=5000)]
    pub determinism_timeout: u64
}