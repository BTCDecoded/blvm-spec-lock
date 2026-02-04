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
    
    /// Extract constants from Orange Paper and generate Rust module
    ExtractConstants {
        /// Path to Orange Paper (default: ../blvm-spec/THE_ORANGE_PAPER.md)
        #[arg(long)]
        spec_path: Option<PathBuf>,
        
        /// Output file path (default: blvm-consensus/src/orange_paper_constants.rs)
        #[arg(short, long)]
        output: Option<PathBuf>,
    },
    
    /// Extract formulas from Orange Paper and generate property test helpers
    ExtractFormulas {
        /// Path to Orange Paper (default: ../blvm-spec/THE_ORANGE_PAPER.md)
        #[arg(long)]
        spec_path: Option<PathBuf>,
        
        /// Output file path (default: blvm-consensus/src/orange_paper_property_helpers.rs)
        #[arg(short, long)]
        output: Option<PathBuf>,
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
        Commands::ExtractConstants { spec_path, output } => {
            handle_extract_constants(spec_path.as_ref(), output.as_ref())
        }
        Commands::ExtractFormulas { spec_path, output } => {
            handle_extract_formulas(spec_path.as_ref(), output.as_ref())
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

fn handle_extract_constants(spec_path: Option<&PathBuf>, output_path: Option<&PathBuf>) -> i32 {
    let workspace_root = std::env::current_dir()
        .unwrap_or_else(|_| PathBuf::from("."));
    
    // Default spec path
    let spec_path = spec_path
        .cloned()
        .unwrap_or_else(|| workspace_root.join("../blvm-spec/THE_ORANGE_PAPER.md"));
    
    // Default output path
    let output_path = output_path
        .cloned()
        .unwrap_or_else(|| workspace_root.join("../blvm-consensus/src/orange_paper_constants.rs"));
    
    // Read Orange Paper
    let content = match std::fs::read_to_string(&spec_path) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Error reading Orange Paper from {}: {}", spec_path.display(), e);
            return 1;
        }
    };
    
    // Parse Orange Paper
    let mut parser = parser::orange_paper::SpecParser::new(content);
    if let Err(e) = parser.parse() {
        eprintln!("Error parsing Orange Paper: {}", e);
        return 1;
    }
    
    // Extract constants
    let constants = parser.extract_constants();
    
    if constants.is_empty() {
        eprintln!("No constants found in Orange Paper Section 4");
        return 1;
    }
    
    // Generate Rust module
    let rust_code = generate_constants_module(&constants);
    
    // Write to file
    if let Err(e) = std::fs::write(&output_path, rust_code) {
        eprintln!("Error writing constants module to {}: {}", output_path.display(), e);
        return 1;
    }
    
    eprintln!("✅ Generated {} constants in {}", constants.len(), output_path.display());
    0
}

fn generate_constants_module(constants: &[&parser::orange_paper::ExtractedConstant]) -> String {
    let mut code = String::from("//! Constants extracted from Orange Paper Section 4 (Consensus Constants)\n");
    code.push_str("//!\n");
    code.push_str("//! This file is AUTO-GENERATED from blvm-spec/THE_ORANGE_PAPER.md\n");
    code.push_str("//! DO NOT EDIT MANUALLY - changes should be made to Orange Paper\n");
    code.push_str("//!\n");
    code.push_str("//! To regenerate: cargo spec-lock extract-constants\n");
    code.push_str("//!\n");
    code.push_str("//! These constants are always available for use in property tests and code.\n");
    code.push_str("//! Each constant is linked to its Orange Paper section via documentation comments.\n\n");
    
    for constant in constants {
        code.push_str(&format!("/// {}\n", constant.description));
        code.push_str(&format!("/// \n"));
        code.push_str(&format!("/// Source: Orange Paper Section {}\n", constant.section));
        code.push_str(&format!("/// Formula: ${} = {}$\n", constant.name, constant.value));
        
        // Note: #[spec_locked] is for functions, not constants
        // Constants are linked to Orange Paper via documentation comments above
        
        // Handle special case: M_MAX uses C constant, need to cast
        let rust_expr = if constant.rust_expr.contains("* C") && constant.rust_type == "i64" {
            format!("({}) as i64", constant.rust_expr)
        } else {
            constant.rust_expr.clone()
        };
        
        // Constant is always available (no feature flag)
        code.push_str(&format!("pub const {}: {} = {};\n\n", constant.name, constant.rust_type, rust_expr));
    }
    
    code
}

fn handle_extract_formulas(spec_path: Option<&PathBuf>, output_path: Option<&PathBuf>) -> i32 {
    let workspace_root = std::env::current_dir()
        .unwrap_or_else(|_| PathBuf::from("."));
    
    // Default spec path
    let spec_path = spec_path
        .cloned()
        .unwrap_or_else(|| workspace_root.join("../blvm-spec/THE_ORANGE_PAPER.md"));
    
    // Default output path
    let output_path = output_path
        .cloned()
        .unwrap_or_else(|| workspace_root.join("../blvm-consensus/src/orange_paper_property_helpers.rs"));
    
    // Read Orange Paper
    let content = match std::fs::read_to_string(&spec_path) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Error reading Orange Paper from {}: {}", spec_path.display(), e);
            return 1;
        }
    };
    
    // Parse Orange Paper
    let mut parser = parser::orange_paper::SpecParser::new(content);
    if let Err(e) = parser.parse() {
        eprintln!("Error parsing Orange Paper: {}", e);
        return 1;
    }
    
    // Extract functions with formulas
    let functions = parser.extract_functions_with_formulas();
    
    if functions.is_empty() {
        eprintln!("No functions with formulas found in Orange Paper");
        return 1;
    }
    
    // Generate Rust property test helpers
    let rust_code = generate_property_helpers(&functions);
    
    // Write to file
    if let Err(e) = std::fs::write(&output_path, rust_code) {
        eprintln!("Error writing property helpers to {}: {}", output_path.display(), e);
        return 1;
    }
    
    eprintln!("✅ Generated property test helpers for {} functions in {}", functions.len(), output_path.display());
    0
}

fn generate_property_helpers(functions: &[&parser::orange_paper::FunctionSpec]) -> String {
    let mut code = String::from("//! Property test helpers generated from Orange Paper formulas\n");
    code.push_str("//!\n");
    code.push_str("//! This file is AUTO-GENERATED from blvm-spec/THE_ORANGE_PAPER.md\n");
    code.push_str("//! DO NOT EDIT MANUALLY - changes should be made to Orange Paper\n");
    code.push_str("//!\n");
    code.push_str("//! To regenerate: cargo spec-lock extract-formulas\n");
    code.push_str("//!\n");
    code.push_str("//! These helpers allow property tests to compare implementation results\n");
    code.push_str("//! against the mathematical formulas defined in the Orange Paper.\n\n");
    
    code.push_str("use blvm_consensus::orange_paper_constants::*;\n");
    code.push_str("#[cfg(test)]\n");
    code.push_str("use proptest::prelude::*;\n\n");
    
    // Only generate helpers for functions we can actually implement
    // Focus on economic functions first (most important for property tests)
    let implementable_functions: Vec<&str> = vec![
        "GetBlockSubsidy", "get_block_subsidy", "BlockSubsidy",
        "TotalSupply", "total_supply", "Supply",
    ];
    
    for func in functions {
        if let Some(formula) = &func.formula {
            // Check if this function is implementable
            let func_lower = func.name.to_lowercase();
            let formula_lower = formula.to_lowercase();
            let is_implementable = implementable_functions.iter().any(|&name| {
                func_lower.contains(&name.to_lowercase()) || 
                formula_lower.contains(&name.to_lowercase())
            });
            
            if !is_implementable {
                continue;  // Skip functions we can't implement yet
            }
            
            // Generate helper function for this formula
            let helper_name = format!("expected_{}_from_orange_paper", func.name.to_lowercase().replace(" ", "_"));
            let rust_formula = translate_formula_to_rust(formula, &func.name);
            
            code.push_str(&format!("/// Expected result from Orange Paper formula\n"));
            code.push_str(&format!("/// \n"));
            code.push_str(&format!("/// Source: Orange Paper Section {}\n", func.section));
            // Clean formula for documentation (remove $$, limit length)
            // For doc comments, we'll use a simplified description instead of raw LaTeX
            let formula_cleaned = formula.replace("$$", "");
            let formula_trimmed = formula_cleaned.trim();
            // Extract just the function name and basic structure, avoid LaTeX
            let formula_doc = if formula_trimmed.len() > 100 {
                // Just show function name and section reference
                format!("See Orange Paper Section {} for full formula", func.section)
            } else {
                // Try to extract readable parts, avoiding LaTeX commands
                formula_trimmed
                    .replace("\\text{", "")
                    .replace("\\begin{cases}", "")
                    .replace("\\end{cases}", "")
                    .replace("\\times", "×")
                    .replace("\\geq", "≥")
                    .replace("\\leq", "≤")
                    .chars()
                    .take(100)
                    .collect::<String>()
            };
            code.push_str(&format!("/// Formula: {}\n", formula_doc));
            code.push_str(&format!("/// \n"));
            if let Some(desc) = &func.description {
                let desc_clean = desc.chars().take(200).collect::<String>();
                code.push_str(&format!("/// {}\n", desc_clean));
            }
            code.push_str(&format!("pub fn {}(", helper_name));
            
            // Extract parameters from formula
            let params = extract_formula_parameters(formula, &func.name);
            if params.is_empty() {
                // Default parameter based on function name
                if func.name.contains("Subsidy") || func.name.contains("Supply") {
                    code.push_str("height: u64");
                } else {
                    code.push_str("_params: u64");  // Placeholder
                }
            } else {
                code.push_str(&params.join(", "));
            }
            
            // Determine return type based on function
            let return_type = if func.name.contains("valid") || func.name.contains("Check") || func.name.contains("Validate") {
                "bool"
            } else if func.name.contains("Supply") || func.name.contains("Subsidy") || func.name.contains("Fee") {
                "i64"
            } else {
                "i64"  // Default
            };
            
            code.push_str(&format!(") -> {} {{\n", return_type));
            code.push_str(&format!("    {}\n", rust_formula));
            code.push_str("}\n\n");
        }
    }
    
    code
}

fn translate_formula_to_rust(formula: &str, func_name: &str) -> String {
    // Handle specific formulas with known patterns
    let func_lower = func_name.to_lowercase();
    let formula_lower = formula.to_lowercase();
    
    if func_lower.contains("getblocksubsidy") || func_lower.contains("block_subsidy") || 
       formula_lower.contains("getblocksubsidy") || formula_lower.contains("block_subsidy") {
        generate_get_block_subsidy_helper()
    } else if func_lower.contains("totalsupply") || func_lower.contains("total_supply") ||
              formula_lower.contains("totalsupply") || formula_lower.contains("total_supply") ||
              formula_lower.contains("sum") && formula_lower.contains("getblocksubsidy") {
        generate_total_supply_helper()
    } else if func_lower.contains("calculatefee") || func_lower.contains("calculate_fee") ||
              formula_lower.contains("calculatefee") || formula_lower.contains("calculate_fee") {
        generate_calculate_fee_helper()
    } else {
        // Generic placeholder - will need manual implementation
        // Only generate helpers for functions we can actually implement
        let formula_clean = formula.replace("$$", "").trim().chars().take(80).collect::<String>();
        format!("    // TODO: Implement formula translation for {}\n    // Formula: {}...\n    // This formula requires manual implementation\n    unimplemented!(\"Formula translation not yet implemented for {}\")", 
            func_name, formula_clean, func_name)
    }
}

fn generate_get_block_subsidy_helper() -> String {
    String::from("    let halving_period = height / H;
    let initial_subsidy = 50 * C;  // 50 BTC = 50 × C
    if halving_period >= 64 {
        0
    } else {
        initial_subsidy >> halving_period  // Uses Orange Paper formula: 50 × C × 2^(-⌊h/H⌋)
    }")
}

fn generate_total_supply_helper() -> String {
    String::from("    // TotalSupply(h) = sum of all block subsidies from 0 to h
    // Formula: TotalSupply(h) = sum_{i=0}^{h} GetBlockSubsidy(i)
    // This is computed by summing GetBlockSubsidy for each height
    let mut total = 0i64;
    for h in 0..=height {
        let halving_period = h / H;
        let initial_subsidy = 50 * C;
        if halving_period < 64 {
            total += (initial_subsidy >> halving_period) as i64;
        }
    }
    total")
}

fn generate_calculate_fee_helper() -> String {
    String::from("    // CalculateFee(inputs, outputs) = sum(inputs.value) - sum(outputs.value)
    // Note: This is a placeholder - actual implementation needs input/output values
    // TODO: Implement with actual transaction inputs and outputs
    0")
}

fn extract_formula_parameters(formula: &str, func_name: &str) -> Vec<String> {
    // Extract parameters from formula
    let mut params = Vec::new();
    
    // Look for common parameter patterns
    if formula.contains("(h)") || formula.contains("(h,") {
        params.push("height: u64".to_string());
    }
    if formula.contains("(tx)") || formula.contains("(tx,") {
        params.push("tx: &Transaction".to_string());
    }
    if formula.contains("(b)") || formula.contains("(b,") {
        params.push("block: &Block".to_string());
    }
    if formula.contains("(us)") || formula.contains("(us,") {
        params.push("utxo_set: &UtxoSet".to_string());
    }
    
    // If no parameters found, use function name to infer
    if params.is_empty() {
        if func_name.contains("Subsidy") || func_name.contains("Supply") {
            params.push("height: u64".to_string());
        }
    }
    
    params
}

