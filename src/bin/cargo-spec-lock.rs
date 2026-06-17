//! Cargo subcommand for BLVM Spec Lock verification
//!
//! Usage: cargo spec-lock verify [options]

// Parser/translator and CLI have code paths used conditionally (z3, drift, etc.)
#![allow(dead_code, unused_imports)]

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
#[command(
    name = "cargo-spec-lock",
    version,
    about = "BLVM Spec Lock verification tool",
    long_about = None
)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

/// Resolve crate path: --crate-path, or SPEC_LOCK_CRATE_PATH env, or current dir
fn resolve_crate_path(crate_path: Option<PathBuf>) -> PathBuf {
    crate_path
        .or_else(|| {
            std::env::var("SPEC_LOCK_CRATE_PATH")
                .ok()
                .map(PathBuf::from)
        })
        .unwrap_or_else(|| std::env::current_dir().unwrap_or_else(|_| PathBuf::from(".")))
}

/// Resolve spec paths: --spec-path (can be repeated), or SPEC_LOCK_SPEC_PATH env (comma/colon-separated).
/// Returns empty Vec if neither set.
///
/// Also validates that none of the resolved paths is a directory — directories cannot be
/// spec Markdown files and are almost always a user error where `--crate-path` was intended
/// (e.g. `--spec-path PROTOCOL.md VERIFIED.md src/` accidentally passes `src/` here).
fn resolve_spec_paths(spec_paths: Vec<PathBuf>) -> Vec<PathBuf> {
    let paths = if !spec_paths.is_empty() {
        spec_paths
    } else if let Ok(env_val) = std::env::var("SPEC_LOCK_SPEC_PATH") {
        env_val
            .split([',', ':'])
            .map(|s| PathBuf::from(s.trim()))
            .filter(|p| !p.as_os_str().is_empty())
            .collect()
    } else {
        return Vec::new();
    };

    for p in &paths {
        if p.is_dir() {
            eprintln!(
                "error: --spec-path argument `{}` is a directory, not a Markdown spec file.\n\
                 Hint: pass the crate/workspace root via --crate-path instead:\n\
                 \n  cargo spec-lock verify --spec-path PROTOCOL.md --crate-path {}\n",
                p.display(),
                p.display(),
            );
            std::process::exit(2);
        }
    }
    paths
}

/// When **`Depends on`** cites missing **`F_*`** / **`C_*`**, or **defined **`F_*`→`F_*`** edges form a cycle** (informational).
fn warn_formula_dep_diagnostics(parser: &parser::orange_paper::SpecParser, context_label: &str) {
    let uf = parser.unresolved_formula_dependencies();
    let uc = parser.unresolved_constant_dependencies();
    if !uf.is_empty() {
        eprintln!(
            "{context_label}: warning: {} **`F_*`** **Depends on** reference(s) missing from merged formula registry:",
            uf.len(),
        );
        for (formula_id, dep) in &uf {
            eprintln!("    {formula_id} -> {dep}");
        }
    }
    if !uc.is_empty() {
        eprintln!(
            "{context_label}: warning: {} **`C_*`** **Depends on** reference(s) missing from merged consensus-constant set (§**4** excerpts in `--spec-path` merge):",
            uc.len(),
        );
        for (formula_id, dep) in &uc {
            eprintln!("    {formula_id} -> {dep}");
        }
    }

    let cycles = cli::formula_dep_graph::find_formula_id_cycles(parser.formulas());
    if !cycles.is_empty() {
        eprintln!(
            "{context_label}: warning: cyclic **`F_*`→`F_*`** **Depends on** among defined formulas (informational):",
        );
        for c in &cycles {
            eprintln!("    {}", c.join(" -> "));
        }
    }
}

#[derive(Subcommand)]
enum Commands {
    /// Verify functions with #[spec_locked] attributes
    Verify {
        /// Path to crate to scan (default: current dir, or SPEC_LOCK_CRATE_PATH)
        #[arg(long)]
        crate_path: Option<PathBuf>,

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

        /// Timeout per function (seconds); increase if Z3 returns Unknown (e.g. complex formulas)
        #[arg(long, default_value = "10")]
        timeout: u64,

        /// Verbose output
        #[arg(short, long)]
        verbose: bool,

        /// Fail on partial verification (e.g. contracts needing Z3 when Z3 not built)
        #[arg(long)]
        strict: bool,

        /// Path to Orange Paper (can pass multiple: --spec-path A B or --spec-path A,B)
        #[arg(long, num_args = 1.., value_delimiter = ',')]
        spec_path: Vec<PathBuf>,

        /// Write verify JSON report (same as `--format json`, `report_format` 1) to PATH in addition to stdout (any `--format`, e.g. human + sidecar JSON for CI).
        #[arg(long, value_name = "PATH")]
        json_out: Option<PathBuf>,

        // Positional args must be last so `--spec-path` and other flags parse correctly.
        /// Files to verify (default: all files in crate)
        files: Vec<String>,
    },

    /// Show coverage report
    Coverage {
        /// Path to crate to scan (default: current dir, or SPEC_LOCK_CRATE_PATH)
        #[arg(long)]
        crate_path: Option<PathBuf>,

        /// Path to Orange Paper (can pass multiple: --spec-path A B or --spec-path A,B)
        #[arg(long, num_args = 1.., value_delimiter = ',')]
        spec_path: Vec<PathBuf>,

        /// Optional **`cargo spec-lock verify`** **`report_format` 1** JSON path — adds **`formulas_verify_rollup`** /
        /// **`constants_verify_rollup`** (rows with **`formula_anchor`** / **`constant_anchor`**).
        #[arg(long, value_name = "PATH")]
        rollup_from_verify_json: Option<PathBuf>,

        /// Output format
        #[arg(long, default_value = "human")]
        format: OutputFormat,
    },

    /// **`F_*`** formula registry: static LaTeX→Rust enrich/verify gate; optional Z3 SAT smoke per formula (**no Rust** witness).
    /// Use **`verify-formulas --format json --json-out …`** when CI needs machine-readable output (`command` == `verify-formulas`; **not** `verify`).
    #[command(name = "verify-formulas")]
    VerifyFormulas {
        /// Path to Orange Paper (can pass multiple: --spec-path A B or --spec-path A,B)
        #[arg(long, num_args = 1.., value_delimiter = ',')]
        spec_path: Vec<PathBuf>,
        /// Per-formula Z3 timeout (seconds) when SAT smoke runs (requires `--features z3` and no `--skip-z3`).
        #[arg(long, default_value = "10")]
        timeout: u64,
        /// Static gate **only** (skip Z3 SAT smoke even when **`z3`** is enabled).
        #[arg(long)]
        skip_z3: bool,

        #[arg(long, default_value = "human")]
        format: OutputFormat,

        /// Write **`verify-formulas`** JSON (**`report_format` 1**) in addition to **`--format`** stdout.
        #[arg(long, value_name = "PATH")]
        json_out: Option<PathBuf>,
    },

    /// [experimental] Check every **`Formula` (`F_*`)** body parses for enrich/verify (no Rust/Z3 — static gate beyond drift).
    /// With **`--z3-sat`**, after static success, run a lightweight Z3 **satisfiability** smoke test (LaTeX → Z3, no implementation).
    CheckFormulas {
        /// Path to Orange Paper (can pass multiple: --spec-path A B or --spec-path A,B)
        #[arg(long, num_args = 1.., value_delimiter = ',')]
        spec_path: Vec<PathBuf>,
        /// Z3: check translated formula is satisfiable (contradictions like `x < x` fail).
        #[arg(long)]
        z3_sat: bool,
        /// Per-formula Z3 timeout (seconds) when **`--z3-sat`** is set.
        #[arg(long, default_value = "5")]
        timeout: u64,
    },

    /// List all spec-locked functions
    List {
        /// Path to crate to scan (default: current dir, or SPEC_LOCK_CRATE_PATH)
        #[arg(long)]
        crate_path: Option<PathBuf>,

        /// Filter by subsystem
        #[arg(long)]
        subsystem: Option<String>,

        /// Filter by section
        #[arg(long)]
        section: Option<String>,
    },

    /// Show lock status summary (functions, sections, contract coverage)
    Summary {
        /// Path to crate to scan (default: current dir, or SPEC_LOCK_CRATE_PATH)
        #[arg(long)]
        crate_path: Option<PathBuf>,

        /// Path to Orange Paper (can pass multiple: --spec-path A B or --spec-path A,B)
        #[arg(long, num_args = 1.., value_delimiter = ',')]
        spec_path: Vec<PathBuf>,

        /// Output format: human (default) or badge (markdown badge for README)
        #[arg(long, default_value = "human")]
        format: String,
    },

    /// [experimental] List named **`F_*`** formulas (**v1** `**Formula**` blocks in merged **`--spec-path`**).
    ///
    /// Emits tab-separated stdout; prints **warnings to stderr** for missing **`Depends on`** refs and **cyclic **`F_*`→`F_*`** edges** among defined formulas (informational — same as other **`--spec-path`** commands; exit **0** unless parse fails).
    ListFormulas {
        /// Path to Orange Paper (can pass multiple: --spec-path A B or --spec-path A,B)
        #[arg(long, num_args = 1.., value_delimiter = ',')]
        spec_path: Vec<PathBuf>,
    },

    /// Check for spec drift (Orange Paper vs implementation)
    CheckDrift {
        /// Path to Orange Paper (can pass multiple: --spec-path A B or --spec-path A,B)
        #[arg(long, num_args = 1.., value_delimiter = ',')]
        spec_path: Vec<PathBuf>,

        /// Path to crate to scan (default: current dir, or SPEC_LOCK_CRATE_PATH)
        #[arg(long)]
        crate_path: Option<PathBuf>,

        /// Only treat unparseable spec properties as drift when their section is referenced by a
        /// `#[spec_locked]` attribute in the scanned crate (prefix match, e.g. lock `5.1` includes `5.1.2`).
        #[arg(long)]
        scoped_unparseables: bool,

        /// Same prefix rule as **`--scoped-unparseables`**, but for **`Formula` (`F_*`)** **`$$`** bodies that fail the **verify**/enrich parse gate (**`extract_parseable_condition`** + **`syn::Expr`**).
        #[arg(long)]
        scoped_formulas: bool,

        /// Output format
        #[arg(long, default_value = "human")]
        format: OutputFormat,
    },

    /// Extract constants from Orange Paper and generate Rust module
    ExtractConstants {
        /// Path to Orange Paper (can pass multiple: --spec-path A B or --spec-path A,B)
        #[arg(long, num_args = 1.., value_delimiter = ',')]
        spec_path: Vec<PathBuf>,

        /// Output file path (required, or SPEC_LOCK_OUTPUT env for constants)
        #[arg(short, long)]
        output: Option<PathBuf>,
    },

    /// [experimental] Extract formulas from Orange Paper and generate property test helpers.
    /// Heuristic codegen only — not **`verify`** and not a release assurance path until covered by tests.
    ExtractFormulas {
        /// Path to Orange Paper (can pass multiple: --spec-path A B or --spec-path A,B)
        #[arg(long, num_args = 1.., value_delimiter = ',')]
        spec_path: Vec<PathBuf>,

        /// Output file path (required unless SPEC_LOCK_OUTPUT env set for formulas)
        #[arg(short, long)]
        output: Option<PathBuf>,
    },

    /// [experimental] Extract property tests from Orange Paper round-trip properties.
    /// Heuristic codegen only — not **`verify`** and not a release assurance path until covered by tests.
    ExtractPropertyTests {
        /// Path to Orange Paper (can pass multiple: --spec-path A B or --spec-path A,B)
        #[arg(long, num_args = 1.., value_delimiter = ',')]
        spec_path: Vec<PathBuf>,
        /// Path to PROPERTY_BINDINGS.toml (default: same dir as spec, or --bindings)
        #[arg(long)]
        bindings_path: Option<PathBuf>,
        /// Output file path (required)
        #[arg(short, long)]
        output: Option<PathBuf>,
        /// Path to target crate for module paths (for binding resolution)
        #[arg(long)]
        crate_path: Option<PathBuf>,
    },
}

#[derive(Clone, Debug)]
enum OutputFormat {
    Human,
    Json,
    Junit,
    Markdown,
}

/// Arguments for `verify` subcommand (keeps `handle_verify` arity small for clippy).
struct VerifyArgs {
    crate_path: PathBuf,
    files: Vec<String>,
    subsystem: Option<String>,
    name: Option<String>,
    sections: Vec<String>,
    format: OutputFormat,
    strict: bool,
    spec_paths: Vec<PathBuf>,
    timeout_secs: u64,
    json_out: Option<PathBuf>,
}

impl std::str::FromStr for OutputFormat {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "human" => Ok(OutputFormat::Human),
            "json" => Ok(OutputFormat::Json),
            "junit" => Ok(OutputFormat::Junit),
            "markdown" => Ok(OutputFormat::Markdown),
            _ => Err(format!(
                "Unknown format: {s}. Expected: human, json, junit, markdown"
            )),
        }
    }
}

fn main() {
    let cli = Cli::parse();

    let exit_code = match cli.command {
        Commands::Verify {
            crate_path,
            subsystem,
            name,
            section,
            format,
            jobs: _,
            timeout,
            verbose: _,
            strict,
            spec_path,
            files,
            json_out,
        } => handle_verify(VerifyArgs {
            crate_path: resolve_crate_path(crate_path),
            files,
            subsystem,
            name,
            sections: section,
            format,
            strict,
            spec_paths: resolve_spec_paths(spec_path),
            timeout_secs: timeout,
            json_out,
        }),
        Commands::Coverage {
            crate_path,
            spec_path,
            rollup_from_verify_json,
            format,
        } => handle_coverage(
            resolve_crate_path(crate_path),
            resolve_spec_paths(spec_path),
            rollup_from_verify_json,
            format,
        ),
        Commands::List {
            crate_path,
            subsystem,
            section,
        } => handle_list(resolve_crate_path(crate_path), subsystem, section),
        Commands::Summary {
            crate_path,
            spec_path,
            format,
        } => handle_summary(
            resolve_crate_path(crate_path),
            resolve_spec_paths(spec_path),
            format,
        ),
        Commands::ListFormulas { spec_path } => handle_list_formulas(resolve_spec_paths(spec_path)),
        Commands::CheckDrift {
            spec_path,
            crate_path,
            scoped_unparseables,
            scoped_formulas,
            format,
        } => handle_check_drift(
            resolve_spec_paths(spec_path),
            resolve_crate_path(crate_path),
            scoped_unparseables,
            scoped_formulas,
            format,
        ),
        Commands::VerifyFormulas {
            spec_path,
            timeout,
            skip_z3,
            format,
            json_out,
        } => handle_verify_formulas(
            resolve_spec_paths(spec_path),
            timeout,
            skip_z3,
            format,
            json_out,
        ),
        Commands::CheckFormulas {
            spec_path,
            z3_sat,
            timeout,
        } => handle_check_formulas(resolve_spec_paths(spec_path), z3_sat, timeout),
        Commands::ExtractConstants { spec_path, output } => {
            handle_extract_constants(resolve_spec_paths(spec_path), output)
        }
        Commands::ExtractFormulas { spec_path, output } => {
            handle_extract_formulas(resolve_spec_paths(spec_path), output)
        }
        Commands::ExtractPropertyTests {
            spec_path,
            bindings_path,
            output,
            crate_path: _,
        } => handle_extract_property_tests(resolve_spec_paths(spec_path), bindings_path, output),
    };

    std::process::exit(exit_code);
}

fn handle_list_formulas(spec_paths: Vec<PathBuf>) -> i32 {
    if spec_paths.is_empty() {
        eprintln!("Error: --spec-path or SPEC_LOCK_SPEC_PATH required for list-formulas");
        return 1;
    }
    match parser::orange_paper::SpecParser::from_paths(&spec_paths) {
        Ok(parser) => {
            warn_formula_dep_diagnostics(&parser, "list-formulas");

            if parser.formulas().is_empty() {
                println!("(no F_* Formula blocks in merged spec)");
            } else {
                let ids: std::collections::HashSet<&str> =
                    parser.formulas().keys().map(|s| s.as_str()).collect();
                let c_stable = parser.merged_consensus_constant_ids();
                let mut formulas: Vec<_> = parser.formulas().values().collect();
                formulas.sort_by(|a, b| a.id.cmp(&b.id));
                for f in formulas {
                    let condensed: String = f
                        .latex_body
                        .split_whitespace()
                        .collect::<Vec<_>>()
                        .join(" ");
                    let deps = f.depends_on.join(",");
                    let gate =
                        if crate::cli::drift::formula_latex_parseable_for_verify(&f.latex_body) {
                            "ok"
                        } else {
                            "fail"
                        };
                    let missing_f_refs: String = f
                        .depends_on
                        .iter()
                        .filter(|d| d.starts_with("F_") && !ids.contains(d.as_str()))
                        .cloned()
                        .collect::<Vec<_>>()
                        .join(",");
                    let missing_c_refs: String = f
                        .depends_on
                        .iter()
                        .filter(|d| d.starts_with("C_") && !c_stable.contains(d.as_str()))
                        .cloned()
                        .collect::<Vec<_>>()
                        .join(",");
                    println!(
                        "{}\t{}\t{gate}\t{deps}\t{missing_f_refs}\t{missing_c_refs}\t{condensed}",
                        f.id, f.section,
                    );
                }
            }
            0
        }
        Err(e) => {
            eprintln!("{e}");
            1
        }
    }
}

fn handle_check_drift(
    spec_paths: Vec<PathBuf>,
    crate_path: PathBuf,
    scoped_unparseables: bool,
    scoped_formulas: bool,
    format: OutputFormat,
) -> i32 {
    if spec_paths.is_empty() {
        eprintln!("Error: --spec-path or SPEC_LOCK_SPEC_PATH required for check-drift");
        return 1;
    }

    if let Ok(sp) = parser::orange_paper::SpecParser::from_paths(&spec_paths) {
        warn_formula_dep_diagnostics(&sp, "check-drift");
    }

    let result = match cli::drift::detect_drift(
        &crate_path,
        Some(&spec_paths),
        scoped_unparseables,
        scoped_formulas,
    ) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("Error detecting drift: {e}");
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

    print!("{output}");

    // Unparseable contracts are informational: they indicate spec math that the condition parser
    // cannot yet translate to Z3, not an implementation mismatch.  Exit non-zero only for real
    // drift: mismatches, missing spec entries, or missing implementations.
    if !result.mismatched_contracts.is_empty()
        || !result.missing_from_spec.is_empty()
        || !result.missing_implementations.is_empty()
    {
        1
    } else {
        0
    }
}

fn handle_coverage(
    crate_path: PathBuf,
    spec_paths: Vec<PathBuf>,
    rollup_from_verify_json: Option<PathBuf>,
    format: OutputFormat,
) -> i32 {
    let stats = match cli::coverage::generate_coverage(
        &crate_path,
        if spec_paths.is_empty() {
            None
        } else {
            Some(spec_paths.as_slice())
        },
        rollup_from_verify_json.as_deref(),
    ) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Error generating coverage: {e}");
            return 1;
        }
    };

    if !spec_paths.is_empty() {
        if let Ok(sp) = parser::orange_paper::SpecParser::from_paths(&spec_paths) {
            warn_formula_dep_diagnostics(&sp, "coverage");
        }
    }

    let output = if !spec_paths.is_empty() {
        match cli::coverage::generate_spec_coverage_report(&crate_path, &spec_paths, &stats) {
            Ok(report) => match format {
                OutputFormat::Human => cli::coverage::format_spec_coverage_human(&report),
                OutputFormat::Json => cli::coverage::format_spec_coverage_json(&report),
                OutputFormat::Markdown => cli::coverage::format_spec_coverage_markdown(&report),
                OutputFormat::Junit => {
                    eprintln!("JUnit format not yet implemented for spec coverage");
                    return 1;
                }
            },
            Err(e) => {
                eprintln!("Error generating spec coverage: {e}");
                return 1;
            }
        }
    } else {
        match format {
            OutputFormat::Human => cli::coverage::format_coverage_human(&stats),
            OutputFormat::Json => cli::coverage::format_coverage_json(&stats),
            OutputFormat::Markdown => cli::coverage::format_coverage_markdown(&stats),
            OutputFormat::Junit => {
                eprintln!("JUnit format not yet implemented for coverage");
                return 1;
            }
        }
    };

    print!("{output}");
    0
}

fn handle_list(crate_path: PathBuf, subsystem: Option<String>, section: Option<String>) -> i32 {
    let all_functions = match cli::verify::discover_functions(&crate_path) {
        Ok(funcs) => funcs,
        Err(e) => {
            eprintln!("Error discovering functions: {e}");
            return 1;
        }
    };

    let sections: Vec<String> = section.into_iter().collect();
    let filtered =
        cli::filters::filter_functions(all_functions, subsystem.as_deref(), None, &sections);

    if filtered.is_empty() {
        eprintln!("No spec-locked functions found");
        return 0;
    }

    // Sort by file, then function name
    let mut sorted: Vec<_> = filtered.into_iter().collect();
    sorted.sort_by(|a, b| {
        a.file_path
            .cmp(&b.file_path)
            .then_with(|| a.function_name.cmp(&b.function_name))
    });

    for f in &sorted {
        let section_str = f.section.as_deref().unwrap_or("(no section)");
        println!(
            "{}\t{}\t{}",
            f.function_name,
            f.file_path.display(),
            section_str
        );
    }
    eprintln!("{} spec-locked function(s)", sorted.len());
    0
}

fn handle_summary(crate_path: PathBuf, spec_paths: Vec<PathBuf>, format: String) -> i32 {
    let all_functions = match cli::verify::discover_functions(&crate_path) {
        Ok(funcs) => funcs,
        Err(e) => {
            eprintln!("Error discovering functions: {e}");
            return 1;
        }
    };

    if all_functions.is_empty() {
        if format == "badge" {
            println!(
                "[![spec-lock](https://img.shields.io/badge/spec--lock-0%20locked-lightgrey)](#)"
            );
        } else {
            eprintln!("No spec-locked functions found in {}", crate_path.display());
        }
        return 0;
    }

    let mut functions = all_functions.clone();
    let mut enriched_count = 0;
    if !spec_paths.is_empty() {
        match cli::spec_enrich::enrich_functions_with_spec(&mut functions, &spec_paths) {
            Ok(n) => enriched_count = n,
            Err(e) => eprintln!("Warning: Could not parse spec: {e}"),
        }
    }

    if !spec_paths.is_empty() {
        if let Ok(sp) = parser::orange_paper::SpecParser::from_paths(&spec_paths) {
            warn_formula_dep_diagnostics(&sp, "summary");
        }
    }

    if format == "badge" {
        let n = functions.len();
        let color = if n > 0 { "brightgreen" } else { "lightgrey" };
        println!("[![spec-lock](https://img.shields.io/badge/spec--lock-{n}%20locked-{color})](#)");
        return 0;
    }

    // Aggregate by section
    let mut by_section: std::collections::HashMap<String, Vec<String>> =
        std::collections::HashMap::new();
    for f in &functions {
        let section = f.section.as_deref().unwrap_or("(no section)");
        by_section
            .entry(section.to_string())
            .or_default()
            .push(f.function_name.clone());
    }

    let mut sections: Vec<_> = by_section.keys().collect();
    sections.sort();

    println!("Lock status: {}", crate_path.display());
    println!("  Functions: {}", functions.len());
    println!("  Sections: {}", sections.len());
    if !spec_paths.is_empty() {
        println!("  Enriched with spec: {enriched_count} (contracts from Orange Paper)");
    } else {
        println!("  Enriched: (use --spec-path for spec-derived contracts)");
    }
    println!();
    println!("Sections:");
    for section in sections {
        let funcs = by_section.get(section).unwrap();
        println!("  {}  {} function(s)", section, funcs.len());
    }
    0
}

fn handle_verify(args: VerifyArgs) -> i32 {
    let VerifyArgs {
        crate_path,
        files: _files,
        subsystem,
        name,
        sections,
        format,
        strict: strict_cli,
        spec_paths,
        timeout_secs,
        json_out,
    } = args;
    // CI / scripts can force strict mode when using older cargo-spec-lock without `--strict` on the CLI.
    let strict = strict_cli
        || matches!(
            std::env::var("SPEC_LOCK_STRICT").as_deref(),
            Ok("1") | Ok("true") | Ok("yes")
        );

    // Richer / heavier Z3 obligations: raise timeout without changing CI invocations.
    // Overrides `--timeout` when set to a positive integer (seconds per function).
    let timeout_secs = std::env::var("SPEC_LOCK_Z3_TIMEOUT_SECS")
        .ok()
        .and_then(|s| s.parse::<u64>().ok())
        .filter(|&t| t > 0)
        .unwrap_or(timeout_secs);

    // Discover functions from explicit crate path
    let mut all_functions = match cli::verify::discover_functions(&crate_path) {
        Ok(funcs) => funcs,
        Err(e) => {
            eprintln!("Error discovering functions: {e}");
            return 1;
        }
    };

    // Snapshot inline `#[ensures]` and `#[axiom]` contracts BEFORE spec enrichment replaces
    // them with spec-derived contracts.  Spec enrichment substitutes inline ensures with
    // spec-derived ones (e.g. `Defined: true`), so the tighter postconditions like
    // `result >= 0` or `result <= INITIAL_SUBSIDY` would otherwise be lost from the
    // post-enrichment contract set.
    //
    // By capturing them here we can propagate callee-proven postconditions to callers
    // (wrapper functions that delegate to these implementations) even after enrichment.
    // This is the data-driven replacement for the old hardcoded `nonneg_callees` list.
    let callee_postconds: Vec<cli::verify::CalleePostcond> = {
        use cli::verify::ContractType;
        all_functions
            .iter()
            .flat_map(|f| {
                f.contracts.iter().filter_map(move |c| {
                    if (c.contract_type == ContractType::Ensures
                        || c.contract_type == ContractType::Axiom)
                        && !c.is_spec_derived
                        && c.expr.is_some()
                        && !c.condition.is_empty()
                    {
                        Some(cli::verify::CalleePostcond {
                            function_name: f.function_name.clone(),
                            condition: c.condition.clone(),
                        })
                    } else {
                        None
                    }
                })
            })
            .collect()
    };

    // Spec is single source of truth: --spec-path required for contract derivation
    if !spec_paths.is_empty() {
        match cli::spec_enrich::enrich_functions_with_spec(&mut all_functions, &spec_paths) {
            Ok(enriched) => {
                if enriched > 0 {
                    eprintln!("📋 Enriched {enriched} functions with spec-derived contracts");
                }
            }
            Err(e) => {
                eprintln!("error: Could not parse spec for contract extraction: {e}");
                eprintln!("  Fix the spec files passed via --spec-path and retry.");
                eprintln!("  Common causes: duplicate section IDs across merged spec files.");
                return 1;
            }
        }
    } else {
        eprintln!(
            "Note: --spec-path not set. Use --spec-path <ORANGE_PAPER.md> for spec-derived contracts."
        );
        eprintln!("  Without it, only manual #[requires]/#[ensures] are used.");
    }

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

    // Deterministic order: sort by file path, then function name
    let mut sorted: Vec<_> = filtered.into_iter().collect();
    sorted.sort_by(|a, b| {
        a.file_path
            .cmp(&b.file_path)
            .then_with(|| a.function_name.cmp(&b.function_name))
    });

    // Merged **`F_*`** registry gate (same as **`check-formulas`** + **`verify-formulas`** SAT smoke): runs
    // before Rust function verification and fails fast on blocking static/Z3 outcomes.
    use crate::cli::formula_checks::{
        FormulaAnalyzeConfig, FormulaRegistryAnalysis, analyze_formula_registry,
        registry_has_blocking_static_failure, registry_has_blocking_z3_outcome,
    };
    use crate::cli::output::{
        FormulaVerifyJsonFlags, format_formula_verify_human, format_verify_json_report,
    };

    let mut formula_registry_for_json: Option<(FormulaRegistryAnalysis, FormulaVerifyJsonFlags)> =
        None;

    if !spec_paths.is_empty() {
        if let Ok(parser) = parser::orange_paper::SpecParser::from_paths(&spec_paths) {
            warn_formula_dep_diagnostics(&parser, "verify");

            let skip_z3 = matches!(
                std::env::var("SPEC_LOCK_VERIFY_FORMULAS_SKIP_Z3").as_deref(),
                Ok("1") | Ok("true") | Ok("yes")
            );
            let z3_requested = !skip_z3;
            let want_z3 = z3_requested && cfg!(feature = "z3");
            let analysis = analyze_formula_registry(
                &parser,
                FormulaAnalyzeConfig {
                    request_z3_sat: want_z3,
                    timeout_ms: timeout_secs.saturating_mul(1000).max(1),
                },
            );
            let formulas_len = parser.formulas().len();
            let flags = FormulaVerifyJsonFlags {
                z3_sat_requested: z3_requested,
                cargo_built_with_z3: cfg!(feature = "z3"),
            };

            let fail_static = registry_has_blocking_static_failure(&analysis);
            let fail_z3 = want_z3 && registry_has_blocking_z3_outcome(&analysis);
            let cannot_run_requested_z3 =
                z3_requested && !cfg!(feature = "z3") && formulas_len > 0 && !fail_static;

            if cannot_run_requested_z3 {
                eprintln!(
                    "verify: Z3 SAT smoke for the merged **`F_*`** registry was requested — rebuild **`cargo-spec-lock`** with **`--features z3`** (or set **`SPEC_LOCK_VERIFY_FORMULAS_SKIP_Z3=1`** for static-only)."
                );
            }

            let formula_blocking = fail_static || fail_z3 || cannot_run_requested_z3;

            if formula_blocking {
                match format {
                    OutputFormat::Human | OutputFormat::Junit | OutputFormat::Markdown => {
                        println!("{}", format_formula_verify_human(&analysis, z3_requested));
                    }
                    OutputFormat::Json => {
                        println!(
                            "{}",
                            format_verify_json_report(&[], Some((&analysis, flags)))
                        );
                    }
                }
                if let Some(ref path) = json_out {
                    let json = format_verify_json_report(&[], Some((&analysis, flags)));
                    if let Some(parent) = path.parent() {
                        if !parent.as_os_str().is_empty() {
                            if let Err(e) = std::fs::create_dir_all(parent) {
                                eprintln!(
                                    "Error creating parent directories for --json-out {}: {}",
                                    path.display(),
                                    e
                                );
                                return 1;
                            }
                        }
                    }
                    if let Err(e) = std::fs::write(path, json.as_bytes()) {
                        eprintln!("Error writing --json-out {}: {}", path.display(), e);
                        return 1;
                    }
                }
                return 1;
            }

            formula_registry_for_json = Some((analysis, flags));
        } else {
            eprintln!(
                "error: could not parse merged spec for **`F_*`** registry (file not found or parse error)"
            );
            return 1;
        }
    }

    // Verify functions (deterministic iteration order)
    let mut results = Vec::new();
    for func in &sorted {
        let result = cli::verify::verify_function(func, timeout_secs, &callee_postconds);
        results.push((func.clone(), result));
    }

    // Format and output results
    let format_str = match format {
        OutputFormat::Human => "human",
        OutputFormat::Json => "json",
        OutputFormat::Junit => "junit",
        OutputFormat::Markdown => "markdown",
    };

    let printed = match format {
        OutputFormat::Json => cli::output::format_verify_json_report(
            &results,
            formula_registry_for_json.as_ref().map(|(a, f)| (a, *f)),
        ),
        _ => cli::output::format_results(&results, format_str),
    };
    print!("{printed}");

    if let Some(ref path) = json_out {
        let json = cli::output::format_verify_json_report(
            &results,
            formula_registry_for_json.as_ref().map(|(a, f)| (a, *f)),
        );
        if let Some(parent) = path.parent() {
            if !parent.as_os_str().is_empty() {
                if let Err(e) = std::fs::create_dir_all(parent) {
                    eprintln!(
                        "Error creating parent directories for --json-out {}: {}",
                        path.display(),
                        e
                    );
                    return 1;
                }
            }
        }
        if let Err(e) = std::fs::write(path, json.as_bytes()) {
            eprintln!("Error writing --json-out {}: {}", path.display(), e);
            return 1;
        }
    }

    // Return exit code: 0 if all passed or partial; 1 only for hard failures or no-contracts.
    // Partial results come from spec-derived (auto-enriched) contracts that Z3 cannot prove — these
    // are best-effort and do NOT block CI even under SPEC_LOCK_STRICT=1.
    let _ = strict; // strict no longer affects partial outcomes
    let has_failures = results
        .iter()
        .any(|(_, r)| matches!(r, cli::verify::VerificationResult::Failed { .. }));
    let has_no_contracts = results
        .iter()
        .any(|(_, r)| matches!(r, cli::verify::VerificationResult::NoContracts { .. }));

    if has_failures || has_no_contracts {
        1
    } else {
        0
    }
}

fn handle_verify_formulas(
    spec_paths: Vec<PathBuf>,
    timeout_secs: u64,
    skip_z3: bool,
    format: OutputFormat,
    json_out: Option<PathBuf>,
) -> i32 {
    use crate::cli::formula_checks::{
        FormulaAnalyzeConfig, analyze_formula_registry, registry_has_blocking_static_failure,
        registry_has_blocking_z3_outcome,
    };
    use crate::cli::output::{
        FormulaVerifyJsonFlags, format_formula_verify_human, format_formula_verify_json_report,
    };
    use crate::parser::orange_paper::SpecParser;

    if spec_paths.is_empty() {
        eprintln!("Error: --spec-path or SPEC_LOCK_SPEC_PATH required for verify-formulas");
        return 1;
    }

    let parser = match SpecParser::from_paths(&spec_paths) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("Error parsing merged spec: {e}");
            return 1;
        }
    };

    warn_formula_dep_diagnostics(&parser, "verify-formulas");

    let formulas_len = parser.formulas().len();
    let z3_requested = !skip_z3;
    let want_z3 = z3_requested && cfg!(feature = "z3");
    let analysis = analyze_formula_registry(
        &parser,
        FormulaAnalyzeConfig {
            request_z3_sat: want_z3,
            timeout_ms: timeout_secs.saturating_mul(1000).max(1),
        },
    );

    let flags = FormulaVerifyJsonFlags {
        z3_sat_requested: z3_requested,
        cargo_built_with_z3: cfg!(feature = "z3"),
    };
    let json_doc = format_formula_verify_json_report(&analysis, flags);

    let format_str = match format {
        OutputFormat::Human => "human",
        OutputFormat::Json => "json",
        OutputFormat::Junit | OutputFormat::Markdown => {
            eprintln!(
                "verify-formulas: `{}` unsupported for this subcommand — using human stdout",
                match format {
                    OutputFormat::Junit => "junit",
                    OutputFormat::Markdown => "markdown",
                    _ => unreachable!(),
                }
            );
            "human"
        }
    };

    match format_str {
        "json" => println!("{json_doc}"),
        _ => print!("{}", format_formula_verify_human(&analysis, z3_requested)),
    }

    if let Some(ref path) = json_out {
        if let Some(parent) = path.parent() {
            if !parent.as_os_str().is_empty() {
                if let Err(e) = std::fs::create_dir_all(parent) {
                    eprintln!(
                        "Error creating parent directories for verify-formulas --json-out {}: {}",
                        path.display(),
                        e
                    );
                    return 1;
                }
            }
        }
        if let Err(e) = std::fs::write(path, json_doc.as_bytes()) {
            eprintln!(
                "Error writing verify-formulas --json-out {}: {}",
                path.display(),
                e
            );
            return 1;
        }
    }

    let fail_static = registry_has_blocking_static_failure(&analysis);
    let fail_z3 = want_z3 && registry_has_blocking_z3_outcome(&analysis);
    let cannot_run_requested_z3 =
        z3_requested && !cfg!(feature = "z3") && formulas_len > 0 && !fail_static;
    if cannot_run_requested_z3 {
        eprintln!(
            "verify-formulas: Z3 SAT smoke was requested — rebuild **`cargo-spec-lock`** with **`--features z3`** (or pass **`--skip-z3`** for static-only)."
        );
    }
    if fail_static || fail_z3 || cannot_run_requested_z3 {
        1
    } else {
        0
    }
}

fn handle_check_formulas(spec_paths: Vec<PathBuf>, z3_sat: bool, timeout_secs: u64) -> i32 {
    use crate::cli::formula_checks::{
        FormulaAnalyzeConfig, FormulaStaticOutcome, Z3FormulaPhase, analyze_formula_registry,
        registry_has_blocking_static_failure, registry_has_blocking_z3_outcome,
    };
    use crate::parser::orange_paper::SpecParser;

    if spec_paths.is_empty() {
        eprintln!("Error: --spec-path or SPEC_LOCK_SPEC_PATH required for check-formulas");
        return 1;
    }

    let parser = match SpecParser::from_paths(&spec_paths) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("Error parsing merged spec: {e}");
            return 1;
        }
    };

    warn_formula_dep_diagnostics(&parser, "check-formulas");

    let analysis = analyze_formula_registry(
        &parser,
        FormulaAnalyzeConfig {
            request_z3_sat: z3_sat && cfg!(feature = "z3"),
            timeout_ms: timeout_secs.saturating_mul(1000).max(1),
        },
    );

    let formulas_len = parser.formulas().len();

    if registry_has_blocking_static_failure(&analysis) {
        let bad: Vec<String> = analysis
            .rows
            .iter()
            .filter_map(|r| match &r.static_gate {
                FormulaStaticOutcome::Failed { message } => {
                    Some(format!("{}: {message}", r.formula_id))
                }
                _ => None,
            })
            .collect();
        eprintln!(
            "check-formulas: {} failure(s) (static gate) among {} **`F_*`** formula(s):\n{}",
            bad.len(),
            formulas_len,
            bad.join("\n")
        );
        return 1;
    }

    if !z3_sat {
        println!(
            "check-formulas: {formulas_len} **`F_*`** body(ies) OK (static enrich/verify gate)."
        );
        return 0;
    }

    #[cfg(not(feature = "z3"))]
    {
        eprintln!(
            "check-formulas: **`--z3-sat`** requires building **`cargo-spec-lock`** with **`--features z3`**."
        );
        return 1;
    }

    #[cfg(feature = "z3")]
    {
        if registry_has_blocking_z3_outcome(&analysis) {
            let mut z3_bad = Vec::new();
            for r in &analysis.rows {
                match &r.z3_phase {
                    Z3FormulaPhase::SatSmokeOk => {}
                    Z3FormulaPhase::NotRequested | Z3FormulaPhase::SkippedDueToStatic => {}
                    Z3FormulaPhase::SkippedNoZ3Feature => z3_bad.push(format!(
                        "{}: Z3 SAT smoke requested — rebuild **`cargo-spec-lock`** with **`--features z3`**",
                        r.formula_id
                    )),
                    Z3FormulaPhase::UnsatContradiction => z3_bad.push(format!(
                        "{}: Z3 reports UNSAT (formula is a contradiction under current translation)",
                        r.formula_id
                    )),
                    Z3FormulaPhase::Unknown { reason } => {
                        z3_bad.push(format!("{}: Z3 unknown — {reason}", r.formula_id));
                    }
                    Z3FormulaPhase::Error { message } => {
                        z3_bad.push(format!("{}: {message}", r.formula_id));
                    }
                }
            }
            eprintln!(
                "check-formulas: {} Z3 satisfiability issue(s) among {} formula(s) (static gate passed):\n{}",
                z3_bad.len(),
                formulas_len,
                z3_bad.join("\n")
            );
            return 1;
        }

        println!(
            "check-formulas: {formulas_len} **`F_*`** static OK; **`--z3-sat`**: all {formulas_len} satisfiability smoke checks passed."
        );
        0
    }
}

fn handle_extract_constants(spec_paths: Vec<PathBuf>, output_path: Option<PathBuf>) -> i32 {
    if spec_paths.is_empty() {
        eprintln!("Error: --spec-path or SPEC_LOCK_SPEC_PATH required for extract-constants");
        return 1;
    }

    let output_path =
        output_path.or_else(|| std::env::var("SPEC_LOCK_OUTPUT").ok().map(PathBuf::from));
    let output_path = match output_path {
        Some(p) => p,
        None => {
            eprintln!("Error: --output or SPEC_LOCK_OUTPUT required for extract-constants");
            return 1;
        }
    };

    // Parse Orange Paper(s)
    let parser = match parser::orange_paper::SpecParser::from_paths(&spec_paths) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("Error parsing Orange Paper: {e}");
            return 1;
        }
    };
    warn_formula_dep_diagnostics(&parser, "extract-constants");

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
        eprintln!(
            "Error writing constants module to {}: {}",
            output_path.display(),
            e
        );
        return 1;
    }

    eprintln!(
        "✅ Generated {} constants in {}",
        constants.len(),
        output_path.display()
    );
    0
}

fn generate_constants_module(constants: &[&parser::orange_paper::ExtractedConstant]) -> String {
    let mut code =
        String::from("//! Constants extracted from Orange Paper Section 4 (Consensus Constants)\n");
    code.push_str("//!\n");
    code.push_str("//! This file is AUTO-GENERATED from blvm-spec/THE_ORANGE_PAPER.md\n");
    code.push_str("//! DO NOT EDIT MANUALLY - changes should be made to Orange Paper\n");
    code.push_str("//!\n");
    code.push_str("//! To regenerate: cargo spec-lock extract-constants\n");
    code.push_str("//!\n");
    code.push_str("//! These constants are always available for use in property tests and code.\n");
    code.push_str(
        "//! Each constant is linked to its Orange Paper section via documentation comments.\n\n",
    );

    for constant in constants {
        code.push_str(&format!("/// {}\n", constant.description));
        code.push_str("/// \n");
        code.push_str(&format!(
            "/// Source: Orange Paper Section {}\n",
            constant.section
        ));
        code.push_str(&format!(
            "/// Formula: ${} = {}$\n",
            constant.name, constant.value
        ));

        // Note: #[spec_locked] is for functions, not constants
        // Constants are linked to Orange Paper via documentation comments above

        // Handle special case: M_MAX uses C constant, need to cast
        let rust_expr = if constant.rust_expr.contains("* C") && constant.rust_type == "i64" {
            format!("({}) as i64", constant.rust_expr)
        } else {
            constant.rust_expr.clone()
        };

        // Constant is always available (no feature flag)
        code.push_str(&format!(
            "pub const {}: {} = {};\n\n",
            constant.name, constant.rust_type, rust_expr
        ));
    }

    code
}

fn handle_extract_formulas(spec_paths: Vec<PathBuf>, output_path: Option<PathBuf>) -> i32 {
    if spec_paths.is_empty() {
        eprintln!("Error: --spec-path or SPEC_LOCK_SPEC_PATH required for extract-formulas");
        return 1;
    }

    let output_path =
        output_path.or_else(|| std::env::var("SPEC_LOCK_OUTPUT").ok().map(PathBuf::from));
    let output_path = match output_path {
        Some(p) => p,
        None => {
            eprintln!("Error: --output or SPEC_LOCK_OUTPUT required for extract-formulas");
            return 1;
        }
    };

    // Parse Orange Paper(s)
    let parser = match parser::orange_paper::SpecParser::from_paths(&spec_paths) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("Error parsing Orange Paper: {e}");
            return 1;
        }
    };
    warn_formula_dep_diagnostics(&parser, "extract-formulas");

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
        eprintln!(
            "Error writing property helpers to {}: {}",
            output_path.display(),
            e
        );
        return 1;
    }

    eprintln!(
        "✅ Generated property test helpers for {} functions in {}",
        functions.len(),
        output_path.display()
    );
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
        "GetBlockSubsidy",
        "get_block_subsidy",
        "BlockSubsidy",
        "TotalSupply",
        "total_supply",
        "Supply",
    ];

    for func in functions {
        if let Some(formula) = &func.formula {
            // Check if this function is implementable
            let func_lower = func.name.to_lowercase();
            let formula_lower = formula.to_lowercase();
            let is_implementable = implementable_functions.iter().any(|&name| {
                func_lower.contains(&name.to_lowercase())
                    || formula_lower.contains(&name.to_lowercase())
            });

            if !is_implementable {
                continue; // Skip functions we can't implement yet
            }

            // Generate helper function for this formula
            let helper_name = format!(
                "expected_{}_from_orange_paper",
                func.name.to_lowercase().replace(" ", "_")
            );
            let rust_formula = translate_formula_to_rust(formula, &func.name);

            code.push_str("/// Expected result from Orange Paper formula\n");
            code.push_str("/// \n");
            code.push_str(&format!(
                "/// Source: Orange Paper Section {}\n",
                func.section
            ));
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
            code.push_str(&format!("/// Formula: {formula_doc}\n"));
            code.push_str("/// \n");
            if let Some(desc) = &func.description {
                let desc_clean = desc.chars().take(200).collect::<String>();
                code.push_str(&format!("/// {desc_clean}\n"));
            }
            code.push_str(&format!("pub fn {helper_name}("));

            // Extract parameters from formula
            let params = extract_formula_parameters(formula, &func.name);
            if params.is_empty() {
                // Default parameter based on function name
                if func.name.contains("Subsidy") || func.name.contains("Supply") {
                    code.push_str("height: u64");
                } else {
                    code.push_str("_params: u64"); // Placeholder
                }
            } else {
                code.push_str(&params.join(", "));
            }

            // Determine return type based on function
            let return_type = if func.name.contains("valid")
                || func.name.contains("Check")
                || func.name.contains("Validate")
            {
                "bool"
            } else {
                "i64"
            };

            code.push_str(&format!(") -> {return_type} {{\n"));
            code.push_str(&format!("    {rust_formula}\n"));
            code.push_str("}\n\n");
        }
    }

    code
}

/// **Experimental / heuristic:** emits Rust snippets for **`extract-property-tests`** helpers only.
/// Not invoked by **`verify`** / **`spec_enrich`**; does **not** establish solver-backed assurance.
fn translate_formula_to_rust(formula: &str, func_name: &str) -> String {
    // Handle specific formulas with known patterns
    let func_lower = func_name.to_lowercase();
    let formula_lower = formula.to_lowercase();

    if func_lower.contains("getblocksubsidy")
        || func_lower.contains("block_subsidy")
        || formula_lower.contains("getblocksubsidy")
        || formula_lower.contains("block_subsidy")
    {
        generate_get_block_subsidy_helper()
    } else if func_lower.contains("totalsupply")
        || func_lower.contains("total_supply")
        || formula_lower.contains("totalsupply")
        || formula_lower.contains("total_supply")
        || formula_lower.contains("sum") && formula_lower.contains("getblocksubsidy")
    {
        generate_total_supply_helper()
    } else if func_lower.contains("calculatefee")
        || func_lower.contains("calculate_fee")
        || formula_lower.contains("calculatefee")
        || formula_lower.contains("calculate_fee")
    {
        generate_calculate_fee_helper()
    } else {
        // Generic placeholder - will need manual implementation
        // Only generate helpers for functions we can actually implement
        let formula_clean = formula
            .replace("$$", "")
            .trim()
            .chars()
            .take(80)
            .collect::<String>();
        format!(
            "    // TODO: Implement formula translation for {func_name}\n    // Formula: {formula_clean}...\n    // This formula requires manual implementation\n    unimplemented!(\"Formula translation not yet implemented for {func_name}\")"
        )
    }
}

fn generate_get_block_subsidy_helper() -> String {
    String::from(
        "    let halving_period = height / H;
    let initial_subsidy = 50 * C;  // 50 BTC = 50 × C
    if halving_period >= 64 {
        0
    } else {
        initial_subsidy >> halving_period  // Uses Orange Paper formula: 50 × C × 2^(-⌊h/H⌋)
    }",
    )
}

fn generate_total_supply_helper() -> String {
    String::from(
        "    // TotalSupply(h) = sum of all block subsidies from 0 to h
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
    total",
    )
}

fn generate_calculate_fee_helper() -> String {
    String::from(
        "    // CalculateFee(inputs, outputs) = sum(inputs.value) - sum(outputs.value)
    // Note: This is a placeholder - actual implementation needs input/output values
    // TODO: Implement with actual transaction inputs and outputs
    0",
    )
}

fn handle_extract_property_tests(
    spec_paths: Vec<PathBuf>,
    bindings_path: Option<PathBuf>,
    output_path: Option<PathBuf>,
) -> i32 {
    if spec_paths.is_empty() {
        eprintln!("Error: --spec-path or SPEC_LOCK_SPEC_PATH required for extract-property-tests");
        return 1;
    }

    let output_path =
        output_path.or_else(|| std::env::var("SPEC_LOCK_OUTPUT").ok().map(PathBuf::from));
    let output_path = match output_path {
        Some(p) => p,
        None => {
            eprintln!("Error: --output or SPEC_LOCK_OUTPUT required for extract-property-tests");
            return 1;
        }
    };

    let bindings_path = bindings_path.unwrap_or_else(|| {
        spec_paths
            .first()
            .and_then(|p| p.parent())
            .map(|p| p.join("PROPERTY_BINDINGS.toml"))
            .unwrap_or_else(|| PathBuf::from("PROPERTY_BINDINGS.toml"))
    });

    let parser = match parser::orange_paper::SpecParser::from_paths(&spec_paths) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("Error parsing Orange Paper: {e}");
            return 1;
        }
    };
    warn_formula_dep_diagnostics(&parser, "extract-property-tests");

    let props = parser.get_all_standalone_properties();
    let round_trips: Vec<_> = props
        .iter()
        .filter(|p| p.property_type == parser::orange_paper::StandalonePropertyType::RoundTrip)
        .filter(|p| p.inner_func.is_some() && p.outer_func.is_some())
        .copied()
        .collect();

    // Load bindings
    let bindings_content = match std::fs::read_to_string(&bindings_path) {
        Ok(c) => c,
        Err(e) => {
            eprintln!(
                "Error reading bindings from {}: {}",
                bindings_path.display(),
                e
            );
            return 1;
        }
    };

    let bindings: toml::Value = match toml::from_str(&bindings_content) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("Error parsing bindings TOML: {e}");
            return 1;
        }
    };

    let rust_code = generate_property_tests(&round_trips, &bindings);

    if let Err(e) = std::fs::write(&output_path, rust_code) {
        eprintln!(
            "Error writing property tests to {}: {}",
            output_path.display(),
            e
        );
        return 1;
    }

    eprintln!(
        "✅ Generated {} round-trip property test(s) in {}",
        round_trips.len(),
        output_path.display()
    );
    0
}

fn get_binding(bindings: &toml::Value, func_name: &str) -> Option<String> {
    let tbl = bindings.get("blvm_consensus")?.get("serialization")?;
    tbl.get(func_name)?.as_str().map(String::from)
}

fn generate_property_tests(
    round_trips: &[&parser::orange_paper::StandaloneProperty],
    bindings: &toml::Value,
) -> String {
    let mut code = String::from("//! AUTO-GENERATED from Orange Paper - DO NOT EDIT\n");
    code.push_str(
        "//! Run: cargo spec-lock extract-property-tests --spec-path ... --output ...\n\n",
    );
    code.push_str("#![cfg(test)]\n");
    code.push_str("#![cfg(feature = \"property-tests\")]\n");
    code.push_str("use proptest::prelude::*;\n\n");

    for prop in round_trips {
        let inner = prop.inner_func.as_deref().unwrap_or("");
        let outer = prop.outer_func.as_deref().unwrap_or("");
        let inner_path = get_binding(bindings, inner)
            .or_else(|| get_binding(bindings, &inner.replace("Header", "BlockHeader")));
        let outer_path = get_binding(bindings, outer)
            .or_else(|| get_binding(bindings, &outer.replace("Header", "BlockHeader")));

        if inner_path.is_none() || outer_path.is_none() {
            code.push_str(&format!(
                "// Skipped {}: missing binding for {} or {}\n",
                prop.name, inner, outer
            ));
            continue;
        }

        let (inner_path, outer_path) = (inner_path.unwrap(), outer_path.unwrap());
        let test_name = format!(
            "prop_{}",
            prop.name
                .to_lowercase()
                .replace(" ", "_")
                .replace("-", "_")
                .replace("(", "")
                .replace(")", "")
        );

        // Determine strategy and assertion based on property
        if prop.constraint.is_some() && prop.name.contains("SegWit") {
            // (tx, w) with |w| = |tx.inputs|
            code.push_str(&format!(
                "/// Property ({}) - Orange Paper {}\n",
                prop.name, prop.section_id
            ));
            code.push_str(&format!("#[test]\nfn {test_name}() {{\n"));
            code.push_str("    proptest!(|((tx, w) in blvm_consensus::test_utils::transaction_with_witness_strategy())| {\n");
            code.push_str(&format!("        let bytes = {inner_path}(&tx, &w);\n"));
            code.push_str(&format!(
                "        let (tx2, w2, _) = {outer_path}(&bytes).unwrap();\n"
            ));
            code.push_str("        prop_assert_eq!(tx, tx2);\n");
            code.push_str("        prop_assert_eq!(w, w2);\n");
            code.push_str("    });\n}\n\n");
        } else if prop.name.contains("Transaction") && !prop.name.contains("SegWit") {
            // tx only
            code.push_str(&format!(
                "/// Property ({}) - Orange Paper {}\n",
                prop.name, prop.section_id
            ));
            code.push_str(&format!("#[test]\nfn {test_name}() {{\n"));
            code.push_str(
                "    proptest!(|(tx in blvm_consensus::test_utils::transaction_strategy())| {\n",
            );
            code.push_str(
                "        let bytes = blvm_consensus::serialization::serialize_transaction(&tx);\n",
            );
            code.push_str("        let tx2 = blvm_consensus::serialization::deserialize_transaction(&bytes).unwrap();\n");
            code.push_str("        prop_assert_eq!(tx, tx2);\n");
            code.push_str("    });\n}\n\n");
        } else if prop.name.contains("Block Header") || prop.name.contains("Header") {
            // BlockHeader - use proptest array strategy (version: i64, timestamp/bits/nonce: u64)
            code.push_str(&format!(
                "/// Property ({}) - Orange Paper {}\n",
                prop.name, prop.section_id
            ));
            code.push_str(&format!("#[test]\nfn {test_name}() {{\n"));
            code.push_str("    use blvm_consensus::types::BlockHeader;\n");
            code.push_str("    proptest!(|(v in any::<i64>(), prev in prop::array::uniform32(any::<u8>()), mr in prop::array::uniform32(any::<u8>()), ts in 0u64..u64::MAX, bits in any::<u64>(), nonce in any::<u64>())| {\n");
            code.push_str("        let header = BlockHeader { version: v, prev_block_hash: prev, merkle_root: mr, timestamp: ts, bits, nonce };\n");
            code.push_str("        let bytes = blvm_consensus::serialization::serialize_block_header(&header);\n");
            code.push_str("        let header2 = blvm_consensus::serialization::deserialize_block_header(&bytes).unwrap();\n");
            code.push_str("        prop_assert_eq!(header.version, header2.version);\n");
            code.push_str(
                "        prop_assert_eq!(header.prev_block_hash, header2.prev_block_hash);\n",
            );
            code.push_str("        prop_assert_eq!(header.merkle_root, header2.merkle_root);\n");
            code.push_str("        prop_assert_eq!(header.timestamp, header2.timestamp);\n");
            code.push_str("        prop_assert_eq!(header.bits, header2.bits);\n");
            code.push_str("        prop_assert_eq!(header.nonce, header2.nonce);\n");
            code.push_str("    });\n}\n\n");
        } else {
            code.push_str(&format!("// TODO: {} - add strategy\n", prop.name));
        }
    }

    code
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
    if params.is_empty() && (func_name.contains("Subsidy") || func_name.contains("Supply")) {
        params.push("height: u64".to_string());
    }

    params
}
