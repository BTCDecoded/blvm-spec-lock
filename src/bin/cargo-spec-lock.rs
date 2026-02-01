//! Cargo subcommand for BLVM Spec Lock verification
//!
//! Usage: cargo spec-lock verify [options]

use clap::{Parser, Subcommand};
use std::path::PathBuf;

// Include library modules (using path to access them from binary)
#[path = "../parser/mod.rs"]
mod parser;
#[path = "../translator/mod.rs"]
mod translator;

// Include CLI modules (they're in src/bin/cli/)
mod cli;

#[derive(Parser)]
#[command(name = "cargo-spec-lock")]
#[command(about = "BLVM Spec Lock verification tool", long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Verify functions with #[spec_locked] attributes
    Verify {
        /// Files to verify (default: all files in workspace)
        files: Vec<String>,
        
        /// Filter by subsystem
        #[arg(long)]
        subsystem: Option<String>,
        
        /// Filter by function name (supports patterns)
        #[arg(long)]
        name: Option<String>,
        
        /// Filter by Orange Paper section
        #[arg(long, action = clap::ArgAction::Append)]
        section: Vec<String>,
        
        /// Output format
        #[arg(long, default_value = "human")]
        format: OutputFormat,
        
        /// Number of parallel jobs
        #[arg(short, long, default_value = "1")]
        jobs: usize,
        
        /// Timeout per function (seconds)
        #[arg(long, default_value = "5")]
        timeout: u64,
        
        /// Verbose output
        #[arg(short, long)]
        verbose: bool,
    },
    
    /// Show coverage report
    Coverage {
        /// Output format
        #[arg(long, default_value = "human")]
        format: OutputFormat,
    },
    
    /// List all verified functions
    List {
        /// Filter by subsystem
        #[arg(long)]
        subsystem: Option<String>,
        
        /// Filter by section
        #[arg(long)]
        section: Option<String>,
    },
    
    /// Check for spec drift (Orange Paper vs implementation)
    CheckDrift {
        /// Path to Orange Paper (default: ../blvm-spec/THE_ORANGE_PAPER.md)
        #[arg(long)]
        spec_path: Option<PathBuf>,
        
        /// Output format
        #[arg(long, default_value = "human")]
        format: OutputFormat,
    },
}

#[derive(Clone, Debug)]
enum OutputFormat {
    Human,
    Json,
    Junit,
    Markdown,
}

impl std::str::FromStr for OutputFormat {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "human" => Ok(OutputFormat::Human),
            "json" => Ok(OutputFormat::Json),
            "junit" => Ok(OutputFormat::Junit),
            "markdown" => Ok(OutputFormat::Markdown),
            _ => Err(format!("Unknown format: {}. Expected: human, json, junit, markdown", s)),
        }
    }
}

fn main() {
    let cli = Cli::parse();

    let exit_code = match cli.command {
        Commands::Verify { 
            files, 
            subsystem, 
            name, 
            section, 
            format, 
            jobs: _,
            timeout: _,
            verbose: _,
        } => {
            handle_verify(files, subsystem, name, section, format)
        }
        Commands::Coverage { format } => {
            handle_coverage(format)
        }
        Commands::List { subsystem, section } => {
            eprintln!("List command not yet implemented");
            eprintln!("Subsystem: {:?}, Section: {:?}", subsystem, section);
            1
        }
        Commands::CheckDrift { spec_path, format } => {
            handle_check_drift(spec_path.as_ref(), format)
        }
    };

    std::process::exit(exit_code);
}

fn handle_check_drift(spec_path: Option<&PathBuf>, format: OutputFormat) -> i32 {
    let workspace_root = std::env::current_dir()
        .unwrap_or_else(|_| PathBuf::from("."));

    let result = match cli::drift::detect_drift(&workspace_root, spec_path) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("Error detecting drift: {}", e);
            return 1;
        }
    };

    let output = match format {
        OutputFormat::Human => cli::drift::format_drift_human(&result),
        OutputFormat::Json => cli::drift::format_drift_json(&result),
        OutputFormat::Markdown => {
            eprintln!("Markdown format not yet implemented for drift detection");
            return 1;
        }
        OutputFormat::Junit => {
            eprintln!("JUnit format not yet implemented for drift detection");
            return 1;
        }
    };

    print!("{}", output);
    
    // Return non-zero exit code if drift detected
    if !result.mismatched_contracts.is_empty() || 
       !result.missing_from_spec.is_empty() ||
       !result.missing_implementations.is_empty() {
        1
    } else {
        0
    }
}

fn handle_coverage(format: OutputFormat) -> i32 {
    let workspace_root = std::env::current_dir()
        .unwrap_or_else(|_| PathBuf::from("."));

    let stats = match cli::coverage::generate_coverage(&workspace_root) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Error generating coverage: {}", e);
            return 1;
        }
    };

    let output = match format {
        OutputFormat::Human => cli::coverage::format_coverage_human(&stats),
        OutputFormat::Json => cli::coverage::format_coverage_json(&stats),
        OutputFormat::Markdown => cli::coverage::format_coverage_markdown(&stats),
        OutputFormat::Junit => {
            eprintln!("JUnit format not yet implemented for coverage");
            return 1;
        }
    };

    print!("{}", output);
    0
}

fn handle_verify(
    files: Vec<String>,
    subsystem: Option<String>,
    name: Option<String>,
    sections: Vec<String>,
    format: OutputFormat,
) -> i32 {
    // Find workspace root (simplified - would use cargo-metadata in full implementation)
    let workspace_root = std::env::current_dir()
        .unwrap_or_else(|_| PathBuf::from("."));

    // Discover functions
    let all_functions = match cli::verify::discover_functions(&workspace_root) {
        Ok(funcs) => funcs,
        Err(e) => {
            eprintln!("Error discovering functions: {}", e);
            return 1;
        }
    };

    // Apply filters
    let filtered = cli::filters::filter_functions(
        all_functions,
        subsystem.as_deref(),
        name.as_deref(),
        &sections,
    );

    if filtered.is_empty() {
        eprintln!("No functions found matching criteria");
        return 1;
    }

    // Verify functions
    let mut results = Vec::new();
    for func in &filtered {
        let result = cli::verify::verify_function(func);
        results.push((func.clone(), result));
    }

    // Format and output results
    let format_str = match format {
        OutputFormat::Human => "human",
        OutputFormat::Json => "json",
        OutputFormat::Junit => "junit",
        OutputFormat::Markdown => "markdown",
    };
    
    let output = cli::output::format_results(&results, format_str);
    print!("{}", output);

    // Return exit code: 0 if all passed, 1 if any failed
    let has_failures = results.iter().any(|(_, r)| {
        matches!(r, cli::verify::VerificationResult::Failed { .. })
    });
    
    if has_failures {
        1
    } else {
        0
    }
}

