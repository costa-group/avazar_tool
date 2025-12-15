use clap::{Parser};

#[derive(Parser)]
#[command(version, about, long_about = None)]
pub struct Args {
    // filepath to input circuit
    pub file1path: String,

    #[arg(required_unless_present = "test", conflicts_with = "test")]
    pub file2path: Option<String>,

    #[arg(long)]
    pub test: bool,

    #[arg(long)]
    pub debug: bool,

    #[arg(long)]
    pub dont_shuffle_internals: bool
}