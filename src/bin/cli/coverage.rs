//! Coverage reporting for spec-locked functions
//!
//! Reports which functions are spec-locked, coverage by section, missing functions, etc.
//! With --spec-path: theorems/properties → contracts → parseable vs unparseable.

use crate::cli::verify::{FunctionToVerify, discover_functions};
use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};

/// Counts **`verify`** rows keyed by **`formula_anchor`** vs **`constant_anchor`** in **`report_format` 1** JSON.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct WitnessVerifyRollup {
    pub passed: usize,
    pub failed: usize,
    pub partial: usize,
    pub not_implemented: usize,
    pub total: usize,
}

pub fn parse_verify_json_witness_rollups(
    json_text: &str,
) -> Result<(Option<WitnessVerifyRollup>, Option<WitnessVerifyRollup>), String> {
    let root: serde_json::Value =
        serde_json::from_str(json_text).map_err(|e| format!("verify rollup JSON: {e}"))?;
    let results = root
        .get("results")
        .and_then(|r| r.as_array())
        .ok_or_else(|| "verify rollup JSON: missing `.results` array".to_string())?;

    fn bump(r: &mut WitnessVerifyRollup, status: Option<&str>) {
        r.total += 1;
        match status.unwrap_or("") {
            "passed" => r.passed += 1,
            "failed" => r.failed += 1,
            "partial" => r.partial += 1,
            "not_implemented" => r.not_implemented += 1,
            _ => r.failed += 1,
        }
    }

    let mut formulas = WitnessVerifyRollup::default();
    let mut formulas_any = false;
    let mut constants = WitnessVerifyRollup::default();
    let mut constants_any = false;

    for row in results {
        let st = row.get("status").and_then(|s| s.as_str());
        if row
            .get("formula_anchor")
            .and_then(|v| v.as_str())
            .filter(|s| !s.is_empty())
            .is_some()
        {
            formulas_any = true;
            bump(&mut formulas, st);
        }
        if row
            .get("constant_anchor")
            .and_then(|v| v.as_str())
            .filter(|s| !s.is_empty())
            .is_some()
        {
            constants_any = true;
            bump(&mut constants, st);
        }
    }

    Ok((
        if formulas_any { Some(formulas) } else { None },
        if constants_any { Some(constants) } else { None },
    ))
}

fn witness_rollup_to_json(o: Option<&WitnessVerifyRollup>) -> serde_json::Value {
    match o {
        None => serde_json::Value::Null,
        Some(r) => serde_json::json!({
            "passed": r.passed,
            "failed": r.failed,
            "partial": r.partial,
            "not_implemented": r.not_implemented,
            "total": r.total,
        }),
    }
}

fn witness_rollup_human_blurb(which: &str, o: Option<&WitnessVerifyRollup>) -> String {
    match o {
        None => String::new(),
        Some(r) => format!(
            "{which} (**`cargo spec-lock verify`** JSON rollup): {} passed / {} total (partial {}, failed {}, not_implemented {})\n",
            r.passed, r.total, r.partial, r.failed, r.not_implemented,
        ),
    }
}

fn witness_rollup_markdown(which: &str, o: Option<&WitnessVerifyRollup>) -> String {
    match o {
        None => String::new(),
        Some(r) => format!(
            "- **{} verify rollup** (`--rollup-from-verify-json`): {} passed / {} total — partial {}; failed {}; not_implemented {}\n",
            which, r.passed, r.total, r.partial, r.failed, r.not_implemented,
        ),
    }
}

/// Coverage statistics
#[derive(Debug, Clone)]
pub struct CoverageStats {
    /// Total number of spec-locked functions
    pub total_spec_locked: usize,
    /// Functions grouped by section
    pub by_section: HashMap<String, Vec<FunctionToVerify>>,
    /// Functions without section (auto-inferred)
    pub without_section: Vec<FunctionToVerify>,
    /// Functions with contracts
    pub with_contracts: usize,
    /// Functions without contracts
    pub without_contracts: usize,
    /// **`Formula` (`F_*`)** ids in merged **`--spec-path`** (**`0`** when no paths / parse fails)
    pub formulas_defined: usize,
    /// **Rust** **`#[spec_locked]`** anchors naming **`formula_anchor`** (`F_*`), after enrichment / discovery
    pub formulas_bound_to_rust: usize,
    /// **`F_*`** entries whose **`latex_body`** passes the **`verify`/enrich** static parse gate (same rule as **`check-drift`** formula rows)
    pub formulas_parseable_body: usize,
    /// Rust **`formula_anchor`** rows where the **`id`** resolves in **`SpecParser`** and the body passes the parse gate
    pub formula_anchor_parse_gate_ok: usize,
    /// **`formula_anchor`** present but **`id`** missing from merged **`SpecParser::formulas()`**
    pub formula_anchor_spec_missing_id: usize,
    /// **`formula_anchor`** resolves but **`latex_body`** fails the parse gate
    pub formula_anchor_unparseable_body: usize,
    /// **`constants_stable_id_map`** entries (Orange Paper §4 **`$NAME = …$`**).
    pub constants_defined: usize,
    /// **`#[spec_locked]`** with **`constant_anchor`** (**`C_*`**).
    pub constants_bound_to_rust: usize,
    /// Rows with **`formula_anchor`** (**`cargo spec-lock verify`** JSON via **`--rollup-from-verify-json`**).
    pub formulas_verify_rollup: Option<WitnessVerifyRollup>,
    /// Rows with **`constant_anchor`** (same JSON).
    pub constants_verify_rollup: Option<WitnessVerifyRollup>,
}

/// Generate coverage report. When spec_paths is provided, enriches functions with spec-derived contracts first.
pub fn generate_coverage(
    workspace_root: &Path,
    spec_paths: Option<&[PathBuf]>,
    rollup_from_verify_json: Option<&Path>,
) -> Result<CoverageStats, String> {
    let mut functions = discover_functions(workspace_root)?;

    if let Some(paths) = spec_paths {
        super::spec_enrich::enrich_functions_with_spec(&mut functions, paths)?;
    }

    let formulas_bound_to_rust = functions
        .iter()
        .filter(|f| f.formula_anchor.is_some())
        .count();
    let constants_bound_to_rust = functions
        .iter()
        .filter(|f| f.constant_anchor.is_some())
        .count();

    let (
        formulas_defined,
        formulas_parseable_body,
        formula_anchor_parse_gate_ok,
        formula_anchor_spec_missing_id,
        formula_anchor_unparseable_body,
        constants_defined,
    ) = formula_and_constant_registry_metrics(spec_paths, &functions);

    let (formulas_vf, constants_vf) = if let Some(p) = rollup_from_verify_json {
        let txt = fs::read_to_string(p).map_err(|e| {
            format!(
                "coverage rollup cannot read verify JSON `{}`: {e}",
                p.display()
            )
        })?;
        parse_verify_json_witness_rollups(&txt)?
    } else {
        (None, None)
    };

    let mut by_section: HashMap<String, Vec<FunctionToVerify>> = HashMap::new();
    let mut without_section = Vec::new();
    let mut with_contracts = 0;
    let mut without_contracts = 0;

    for func in functions {
        if func.contracts.is_empty() {
            without_contracts += 1;
        } else {
            with_contracts += 1;
        }

        if let Some(section) = &func.section {
            by_section.entry(section.clone()).or_default().push(func);
        } else {
            without_section.push(func);
        }
    }

    Ok(CoverageStats {
        total_spec_locked: with_contracts + without_contracts,
        by_section,
        without_section,
        with_contracts,
        without_contracts,
        formulas_defined,
        formulas_bound_to_rust,
        formulas_parseable_body,
        formula_anchor_parse_gate_ok,
        formula_anchor_spec_missing_id,
        formula_anchor_unparseable_body,
        constants_defined,
        constants_bound_to_rust,
        formulas_verify_rollup: formulas_vf,
        constants_verify_rollup: constants_vf,
    })
}

/// One **`SpecParser::from_paths`** load for **`F_*`** / **`C_*`** registry coverage.
fn formula_and_constant_registry_metrics(
    spec_paths: Option<&[PathBuf]>,
    functions: &[FunctionToVerify],
) -> (usize, usize, usize, usize, usize, usize) {
    use crate::cli::drift::formula_latex_parseable_for_verify;
    use crate::parser::orange_paper::SpecParser;

    let paths = match spec_paths {
        Some(p) if !p.is_empty() => p,
        _ => {
            return (0, 0, 0, 0, 0, 0);
        }
    };

    let Ok(parser) = SpecParser::from_paths(paths) else {
        return (0, 0, 0, 0, 0, 0);
    };

    let constants_defined = match parser.constants_stable_id_map() {
        Ok(c) => c.len(),
        Err(_) => 0,
    };

    let formulas_defined = parser.formulas().len();
    let formulas_parseable_body = parser
        .formulas()
        .values()
        .filter(|fs| formula_latex_parseable_for_verify(&fs.latex_body))
        .count();

    let mut ok = 0usize;
    let mut missing_id = 0usize;
    let mut unparseable_body = 0usize;
    for f in functions {
        let Some(fid) = f.formula_anchor.as_deref() else {
            continue;
        };
        match parser.formulas().get(fid) {
            None => missing_id += 1,
            Some(fspec) => {
                if formula_latex_parseable_for_verify(&fspec.latex_body) {
                    ok += 1;
                } else {
                    unparseable_body += 1;
                }
            }
        }
    }

    (
        formulas_defined,
        formulas_parseable_body,
        ok,
        missing_id,
        unparseable_body,
        constants_defined,
    )
}

/// Format coverage report as human-readable text
pub fn format_coverage_human(stats: &CoverageStats) -> String {
    let mut output = String::new();

    output.push_str("=== Spec Lock Coverage Report ===\n\n");

    // Overall statistics
    output.push_str(&format!(
        "Total spec-locked functions: {}\n",
        stats.total_spec_locked
    ));
    output.push_str(&format!("  - With contracts: {}\n", stats.with_contracts));
    output.push_str(&format!(
        "  - Without contracts: {}\n",
        stats.without_contracts
    ));
    output.push_str(&format!(
        "**Formula** registry (`--spec-path`): {}\n",
        stats.formulas_defined
    ));
    output.push_str(&format!(
        "**`F_*`** bodies parseable (enrich/verify gate), spec-wide: {} / {}\n",
        stats.formulas_parseable_body, stats.formulas_defined
    ));
    output.push_str(&format!(
        "Rust **`F_*`** anchors (`formula_anchor`): {}\n",
        stats.formulas_bound_to_rust
    ));
    output.push_str(&format!(
        "  → resolve + parseable body: {}; missing formula id: {}; unparseable formula body: {}\n",
        stats.formula_anchor_parse_gate_ok,
        stats.formula_anchor_spec_missing_id,
        stats.formula_anchor_unparseable_body
    ));
    output.push_str(&format!(
        "**Constants** registry (`constants_stable_id_map`): {}\n",
        stats.constants_defined
    ));
    output.push_str(&format!(
        "Rust **`C_*`** anchors (`constant_anchor`): {}\n",
        stats.constants_bound_to_rust
    ));
    output.push_str(&witness_rollup_human_blurb(
        "Formula witnesses (`formula_anchor`)",
        stats.formulas_verify_rollup.as_ref(),
    ));
    output.push_str(&witness_rollup_human_blurb(
        "Constant witnesses (`constant_anchor`)",
        stats.constants_verify_rollup.as_ref(),
    ));

    if stats.total_spec_locked > 0 {
        let contract_coverage =
            (stats.with_contracts as f64 / stats.total_spec_locked as f64) * 100.0;
        output.push_str(&format!("Contract coverage: {contract_coverage:.1}%\n"));
    }

    output.push('\n');

    // By section
    if !stats.by_section.is_empty() {
        output.push_str("Coverage by Orange Paper Section:\n");
        output.push_str("--------------------------------\n");

        let mut sections: Vec<(&String, &Vec<FunctionToVerify>)> =
            stats.by_section.iter().collect();
        sections.sort_by_key(|(section, _)| {
            // Sort by section number (e.g., "5.1" < "5.2" < "6.1")
            let parts: Vec<&str> = section.split('.').collect();
            let major: u32 = parts.first().and_then(|s| s.parse().ok()).unwrap_or(0);
            let minor: u32 = parts.get(1).and_then(|s| s.parse().ok()).unwrap_or(0);
            let sub: u32 = parts.get(2).and_then(|s| s.parse().ok()).unwrap_or(0);
            (major, minor, sub)
        });

        for (section, funcs) in sections {
            output.push_str(&format!(
                "  Section {}: {} functions\n",
                section,
                funcs.len()
            ));
            for func in funcs {
                let contract_status = if func.contracts.is_empty() {
                    "⚠️  no contracts"
                } else {
                    "✅"
                };
                output.push_str(&format!(
                    "    - {} {} ({})\n",
                    contract_status,
                    func.function_name,
                    func.file_path.display()
                ));
            }
        }
        output.push('\n');
    }

    // Functions without section (auto-inferred)
    if !stats.without_section.is_empty() {
        output.push_str("Functions with auto-inferred sections:\n");
        output.push_str("--------------------------------------\n");
        for func in &stats.without_section {
            let contract_status = if func.contracts.is_empty() {
                "⚠️  no contracts"
            } else {
                "✅"
            };
            output.push_str(&format!(
                "  {} {} ({})\n",
                contract_status,
                func.function_name,
                func.file_path.display()
            ));
        }
        output.push('\n');
    }

    // Summary
    output.push_str("Summary:\n");
    output.push_str("--------\n");
    output.push_str(&format!(
        "  Total sections covered: {}\n",
        stats.by_section.len()
    ));
    output.push_str(&format!(
        "  Functions with contracts: {}\n",
        stats.with_contracts
    ));
    output.push_str(&format!(
        "  Functions without contracts: {}\n",
        stats.without_contracts
    ));
    output.push_str(&format!(
        "  Formulas defined (merged spec): {}\n",
        stats.formulas_defined
    ));
    output.push_str(&format!(
        "  Formulas with parseable **`$$`** bodies: {}\n",
        stats.formulas_parseable_body
    ));
    output.push_str(&format!(
        "  Rust **`F_*`** anchors on functions: {}\n",
        stats.formulas_bound_to_rust
    ));
    output.push_str(&format!(
        "  Anchors (resolve + parseable): {}\n",
        stats.formula_anchor_parse_gate_ok
    ));
    output.push_str(&format!(
        "  Anchors (missing formula id): {}\n",
        stats.formula_anchor_spec_missing_id
    ));
    output.push_str(&format!(
        "  Anchors (unparseable formula body): {}\n",
        stats.formula_anchor_unparseable_body
    ));
    output.push_str(&format!(
        "  Constants indexed (`constants_stable_id_map`): {}\n",
        stats.constants_defined
    ));
    output.push_str(&format!(
        "  Rust **`C_*`** anchors (`constant_anchor`): {}\n",
        stats.constants_bound_to_rust
    ));
    output.push_str(&witness_rollup_human_blurb(
        "  Formula verify rollup (`formula_anchor` rows)",
        stats.formulas_verify_rollup.as_ref(),
    ));
    output.push_str(&witness_rollup_human_blurb(
        "  Constant verify rollup (`constant_anchor` rows)",
        stats.constants_verify_rollup.as_ref(),
    ));

    if stats.total_spec_locked > 0 {
        let contract_coverage =
            (stats.with_contracts as f64 / stats.total_spec_locked as f64) * 100.0;
        output.push_str(&format!("  Contract coverage: {contract_coverage:.1}%\n"));
    }

    output
}

/// Format coverage report as JSON
pub fn format_coverage_json(stats: &CoverageStats) -> String {
    let mut json = serde_json::json!({
        "total_spec_locked": stats.total_spec_locked,
        "with_contracts": stats.with_contracts,
        "without_contracts": stats.without_contracts,
        "formulas_defined": stats.formulas_defined,
        "formulas_bound_to_rust": stats.formulas_bound_to_rust,
        "formulas_parseable_body": stats.formulas_parseable_body,
        "formula_anchor_parse_gate_ok": stats.formula_anchor_parse_gate_ok,
        "formula_anchor_spec_missing_id": stats.formula_anchor_spec_missing_id,
        "formula_anchor_unparseable_body": stats.formula_anchor_unparseable_body,
        "constants_defined": stats.constants_defined,
        "constants_bound_to_rust": stats.constants_bound_to_rust,
        "formulas_verify_rollup": witness_rollup_to_json(stats.formulas_verify_rollup.as_ref()),
        "constants_verify_rollup": witness_rollup_to_json(stats.constants_verify_rollup.as_ref()),
        "contract_coverage_percent": if stats.total_spec_locked > 0 {
            (stats.with_contracts as f64 / stats.total_spec_locked as f64) * 100.0
        } else {
            0.0
        },
        "by_section": {},
        "without_section": []
    });

    // Add by_section
    let by_section_obj = json["by_section"].as_object_mut().unwrap();
    for (section, funcs) in &stats.by_section {
        by_section_obj.insert(
            section.clone(),
            serde_json::json!({
                "count": funcs.len(),
                "functions": funcs.iter().map(|f| serde_json::json!({
                    "name": f.function_name,
                    "file": f.file_path.display().to_string(),
                    "has_contracts": !f.contracts.is_empty(),
                    "contract_count": f.contracts.len()
                })).collect::<Vec<_>>()
            }),
        );
    }

    // Add without_section
    let without_section_arr = json["without_section"].as_array_mut().unwrap();
    for func in &stats.without_section {
        without_section_arr.push(serde_json::json!({
            "name": func.function_name,
            "file": func.file_path.display().to_string(),
            "has_contracts": !func.contracts.is_empty(),
            "contract_count": func.contracts.len()
        }));
    }

    serde_json::to_string_pretty(&json).unwrap_or_else(|_| "{}".to_string())
}

/// Format coverage report as Markdown
pub fn format_coverage_markdown(stats: &CoverageStats) -> String {
    let mut output = String::new();

    output.push_str("# Spec Lock Coverage Report\n\n");

    // Overall statistics
    output.push_str("## Overall Statistics\n\n");
    output.push_str(&format!(
        "- **Total spec-locked functions**: {}\n",
        stats.total_spec_locked
    ));
    output.push_str(&format!("- **With contracts**: {}\n", stats.with_contracts));
    output.push_str(&format!(
        "- **Without contracts**: {}\n",
        stats.without_contracts
    ));
    output.push_str(&format!(
        "- **Formulas defined** (`--spec-path` registry): {}\n",
        stats.formulas_defined
    ));
    output.push_str(&format!(
        "- **Rust `F_*` anchors**: {}\n",
        stats.formulas_bound_to_rust
    ));
    if stats.formulas_defined == 0 {
        output.push_str(
            "- **Formulas with parseable body** (`enrich`/verify gate): *(no formulas in merged spec)*\n",
        );
    } else {
        output.push_str(&format!(
            "- **Formulas with parseable body** (`enrich`/verify gate): {} / {}\n",
            stats.formulas_parseable_body, stats.formulas_defined
        ));
    }
    if stats.formulas_defined == 0 {
        output.push_str("- **Anchors resolving + parseable** / **missing id** / **unparseable body**: (no merged spec formulas)\n");
    } else {
        output.push_str(&format!(
            "- **Anchors resolving + parseable**: {}\n",
            stats.formula_anchor_parse_gate_ok
        ));
        output.push_str(&format!(
            "- **Anchors missing formula id**: {}\n",
            stats.formula_anchor_spec_missing_id
        ));
        output.push_str(&format!(
            "- **Anchors → unparseable formula body**: {}\n",
            stats.formula_anchor_unparseable_body
        ));
    }

    output.push_str(&format!(
        "- **`constants_stable_id_map` size**: {}\n",
        stats.constants_defined
    ));
    output.push_str(&format!(
        "- **Rust `C_*` anchors (`constant_anchor`)**: {}\n",
        stats.constants_bound_to_rust
    ));
    output.push_str(&witness_rollup_markdown(
        "`formula_anchor` rows",
        stats.formulas_verify_rollup.as_ref(),
    ));
    output.push_str(&witness_rollup_markdown(
        "`constant_anchor` rows",
        stats.constants_verify_rollup.as_ref(),
    ));

    if stats.total_spec_locked > 0 {
        let contract_coverage =
            (stats.with_contracts as f64 / stats.total_spec_locked as f64) * 100.0;
        output.push_str(&format!(
            "- **Contract coverage**: {contract_coverage:.1}%\n"
        ));
    }

    output.push('\n');

    // By section
    if !stats.by_section.is_empty() {
        output.push_str("## Coverage by Orange Paper Section\n\n");
        output.push_str("| Section | Functions | Status |\n");
        output.push_str("|---------|-----------|--------|\n");

        let mut sections: Vec<(&String, &Vec<FunctionToVerify>)> =
            stats.by_section.iter().collect();
        sections.sort_by_key(|(section, _)| {
            let parts: Vec<&str> = section.split('.').collect();
            let major: u32 = parts.first().and_then(|s| s.parse().ok()).unwrap_or(0);
            let minor: u32 = parts.get(1).and_then(|s| s.parse().ok()).unwrap_or(0);
            let sub: u32 = parts.get(2).and_then(|s| s.parse().ok()).unwrap_or(0);
            (major, minor, sub)
        });

        for (section, funcs) in sections {
            let with_contracts = funcs.iter().filter(|f| !f.contracts.is_empty()).count();
            let status = if with_contracts == funcs.len() {
                "✅ Complete"
            } else if with_contracts > 0 {
                "⚠️  Partial"
            } else {
                "❌ No contracts"
            };
            output.push_str(&format!("| {} | {} | {} |\n", section, funcs.len(), status));
        }
        output.push('\n');
    }

    output
}

/// Spec coverage: theorems/properties → contracts → parseable
#[derive(Debug, Clone)]
pub struct SpecCoverageReport {
    pub total_spec_functions: usize,
    pub total_contracts: usize,
    pub parseable_contracts: usize,
    pub unparseable_contracts: usize,
    pub impl_functions_with_contracts: usize,
    pub impl_functions_without_contracts: usize,
    /// Same fields as [`CoverageStats`] — from one merged **`SpecParser`** pass (parse gate = **`check-drift`** formulas).
    pub formulas_defined: usize,
    pub formulas_parseable_body: usize,
    pub formulas_bound_to_rust: usize,
    pub formula_anchor_parse_gate_ok: usize,
    pub formula_anchor_spec_missing_id: usize,
    pub formula_anchor_unparseable_body: usize,
    pub constants_defined: usize,
    pub constants_bound_to_rust: usize,
    pub formulas_verify_rollup: Option<WitnessVerifyRollup>,
    pub constants_verify_rollup: Option<WitnessVerifyRollup>,
    pub by_section: Vec<SpecSectionCoverage>,
}

#[derive(Debug, Clone)]
pub struct SpecSectionCoverage {
    pub section_id: String,
    pub spec_functions: usize,
    pub contracts_total: usize,
    pub contracts_parseable: usize,
    pub impl_functions: usize,
    pub unparseable_examples: Vec<String>,
}

/// Generate spec coverage report (theorems → contracts → parseable)
pub fn generate_spec_coverage_report(
    _crate_path: &Path,
    spec_paths: &[PathBuf],
    stats: &CoverageStats,
) -> Result<SpecCoverageReport, String> {
    use crate::parser::condition;
    use crate::parser::orange_paper::SpecParser;

    let parser = SpecParser::from_paths(spec_paths)?;

    let mut total_contracts = 0usize;
    let mut parseable_contracts = 0usize;
    let mut by_section = Vec::new();

    for (section_id, section) in parser.iter_sections() {
        let mut contracts_total = 0usize;
        let mut contracts_parseable = 0usize;
        let mut unparseable_examples = Vec::new();

        for func in &section.functions {
            for contract in &func.contracts {
                contracts_total += 1;
                total_contracts += 1;
                let cond = &contract.condition;
                if condition::extract_parseable_condition(cond).is_some() {
                    contracts_parseable += 1;
                    parseable_contracts += 1;
                } else if unparseable_examples.len() < 3 {
                    let short = if cond.len() > 60 {
                        format!("{}...", &cond[..57])
                    } else {
                        cond.clone()
                    };
                    unparseable_examples.push(short);
                }
            }
        }

        let impl_functions = stats
            .by_section
            .get(section_id)
            .map(|v| v.len())
            .unwrap_or(0);

        by_section.push(SpecSectionCoverage {
            section_id: section_id.clone(),
            spec_functions: section.functions.len(),
            contracts_total,
            contracts_parseable,
            impl_functions,
            unparseable_examples,
        });
    }

    by_section.sort_by_key(|s| {
        let parts: Vec<&str> = s.section_id.split('.').collect();
        let major: u32 = parts.first().and_then(|p| p.parse().ok()).unwrap_or(0);
        let minor: u32 = parts.get(1).and_then(|p| p.parse().ok()).unwrap_or(0);
        let sub: u32 = parts.get(2).and_then(|p| p.parse().ok()).unwrap_or(0);
        (major, minor, sub)
    });

    let total_spec_functions = by_section.iter().map(|s| s.spec_functions).sum();
    let unparseable_contracts = total_contracts - parseable_contracts;

    Ok(SpecCoverageReport {
        total_spec_functions,
        total_contracts,
        parseable_contracts,
        unparseable_contracts,
        impl_functions_with_contracts: stats.with_contracts,
        impl_functions_without_contracts: stats.without_contracts,
        formulas_defined: stats.formulas_defined,
        formulas_parseable_body: stats.formulas_parseable_body,
        formulas_bound_to_rust: stats.formulas_bound_to_rust,
        formula_anchor_parse_gate_ok: stats.formula_anchor_parse_gate_ok,
        formula_anchor_spec_missing_id: stats.formula_anchor_spec_missing_id,
        formula_anchor_unparseable_body: stats.formula_anchor_unparseable_body,
        constants_defined: stats.constants_defined,
        constants_bound_to_rust: stats.constants_bound_to_rust,
        formulas_verify_rollup: stats.formulas_verify_rollup.clone(),
        constants_verify_rollup: stats.constants_verify_rollup.clone(),
        by_section,
    })
}

pub fn format_spec_coverage_human(report: &SpecCoverageReport) -> String {
    let mut output = String::new();
    output.push_str("=== Spec Coverage Report (Theorems → Contracts → Parseable) ===\n\n");
    output.push_str(&format!(
        "Spec functions: {}\n",
        report.total_spec_functions
    ));
    output.push_str(&format!("Total contracts: {}\n", report.total_contracts));
    let pct = if report.total_contracts > 0 {
        100.0 * report.parseable_contracts as f64 / report.total_contracts as f64
    } else {
        0.0
    };
    output.push_str(&format!(
        "  Parseable: {} ({:.1}%)\n",
        report.parseable_contracts, pct
    ));
    output.push_str(&format!(
        "  Unparseable: {}\n",
        report.unparseable_contracts
    ));
    output.push_str(&format!(
        "\nImpl functions with contracts: {}\n",
        report.impl_functions_with_contracts
    ));
    output.push_str(&format!(
        "Impl functions without contracts: {}\n\n",
        report.impl_functions_without_contracts
    ));
    output.push_str("Named formulas (F_*), merged spec + Rust anchors:\n");
    output.push_str(&format!("  Registry size: {}\n", report.formulas_defined));
    output.push_str(&format!(
        "  Bodies parseable (verify/enrich gate): {} / {}\n",
        report.formulas_parseable_body, report.formulas_defined
    ));
    output.push_str(&format!(
        "  Rust formula_anchor count: {}\n",
        report.formulas_bound_to_rust
    ));
    output.push_str(&format!(
        "  Anchors resolve + parseable: {}; missing id: {}; unparseable body: {}\n",
        report.formula_anchor_parse_gate_ok,
        report.formula_anchor_spec_missing_id,
        report.formula_anchor_unparseable_body
    ));
    output.push_str("Consensus constants (`C_*`) registry + anchors:\n");
    output.push_str(&format!(
        "  Indexed (`constants_stable_id_map`): {}\n",
        report.constants_defined
    ));
    output.push_str(&format!(
        "  Rust constant_anchor count: {}\n",
        report.constants_bound_to_rust
    ));
    output.push_str(&witness_rollup_human_blurb(
        "  Formula witnesses (`formula_anchor`)",
        report.formulas_verify_rollup.as_ref(),
    ));
    output.push_str(&witness_rollup_human_blurb(
        "  Constant witnesses (`constant_anchor`)",
        report.constants_verify_rollup.as_ref(),
    ));
    output.push_str("\nBy section:\n");
    output.push_str("Section | Spec Funcs | Contracts | Parseable | Impl\n");
    output.push_str("--------|------------|-----------|-----------|-----\n");
    for s in &report.by_section {
        let spct = if s.contracts_total > 0 {
            100.0 * s.contracts_parseable as f64 / s.contracts_total as f64
        } else {
            0.0
        };
        output.push_str(&format!(
            "{} | {} | {} | {} ({:.0}%) | {}\n",
            s.section_id,
            s.spec_functions,
            s.contracts_total,
            s.contracts_parseable,
            spct,
            s.impl_functions
        ));
        if !s.unparseable_examples.is_empty() {
            for ex in &s.unparseable_examples {
                output.push_str(&format!("  Unparseable: {ex}\n"));
            }
        }
    }
    output
}

pub fn format_spec_coverage_json(report: &SpecCoverageReport) -> String {
    serde_json::json!({
        "total_spec_functions": report.total_spec_functions,
        "total_contracts": report.total_contracts,
        "parseable_contracts": report.parseable_contracts,
        "unparseable_contracts": report.unparseable_contracts,
        "parseable_percent": if report.total_contracts > 0 { 100.0 * report.parseable_contracts as f64 / report.total_contracts as f64 } else { 0.0 },
        "impl_with_contracts": report.impl_functions_with_contracts,
        "impl_without_contracts": report.impl_functions_without_contracts,
        "formulas_defined": report.formulas_defined,
        "formulas_parseable_body": report.formulas_parseable_body,
        "formulas_bound_to_rust": report.formulas_bound_to_rust,
        "formula_anchor_parse_gate_ok": report.formula_anchor_parse_gate_ok,
        "formula_anchor_spec_missing_id": report.formula_anchor_spec_missing_id,
        "formula_anchor_unparseable_body": report.formula_anchor_unparseable_body,
        "constants_defined": report.constants_defined,
        "constants_bound_to_rust": report.constants_bound_to_rust,
        "formulas_verify_rollup": witness_rollup_to_json(report.formulas_verify_rollup.as_ref()),
        "constants_verify_rollup": witness_rollup_to_json(report.constants_verify_rollup.as_ref()),
        "by_section": report.by_section.iter().map(|s| serde_json::json!({
            "section": s.section_id,
            "spec_functions": s.spec_functions,
            "contracts_total": s.contracts_total,
            "contracts_parseable": s.contracts_parseable,
            "impl_functions": s.impl_functions,
            "unparseable_examples": s.unparseable_examples,
        })).collect::<Vec<_>>(),
    })
    .to_string()
}

pub fn format_spec_coverage_markdown(report: &SpecCoverageReport) -> String {
    let mut output = String::new();
    output.push_str("# Spec Coverage Report\n\n");
    output.push_str("| Metric | Count |\n|--------|-------|\n");
    output.push_str(&format!(
        "| Spec functions | {} |\n",
        report.total_spec_functions
    ));
    output.push_str(&format!(
        "| Total contracts | {} |\n",
        report.total_contracts
    ));
    output.push_str(&format!("| Parseable | {} |\n", report.parseable_contracts));
    output.push_str(&format!(
        "| Unparseable | {} |\n",
        report.unparseable_contracts
    ));
    let pct = if report.total_contracts > 0 {
        100.0 * report.parseable_contracts as f64 / report.total_contracts as f64
    } else {
        0.0
    };
    output.push_str(&format!("| Parseable % | {pct:.1} |\n"));
    output.push_str(&format!(
        "| **`F_*` defined (registry)** | {} |\n",
        report.formulas_defined
    ));
    if report.formulas_defined == 0 {
        output.push_str("| **`F_*` bodies parseable** | *(none)* |\n");
    } else {
        output.push_str(&format!(
            "| **`F_*` bodies parseable** | {} / {} |\n",
            report.formulas_parseable_body, report.formulas_defined
        ));
    }
    output.push_str(&format!(
        "| Rust **`formula_anchor`** | {} |\n",
        report.formulas_bound_to_rust
    ));
    output.push_str(&format!(
        "| Anchors OK / missing id / bad body | {} / {} / {} |\n",
        report.formula_anchor_parse_gate_ok,
        report.formula_anchor_spec_missing_id,
        report.formula_anchor_unparseable_body
    ));
    output.push_str(&format!(
        "| **`constants_stable_id_map` size** | {} |\n",
        report.constants_defined
    ));
    output.push_str(&format!(
        "| Rust **`constant_anchor`** | {} |\n",
        report.constants_bound_to_rust
    ));
    output.push_str(&witness_rollup_markdown(
        "`formula_anchor` verify rows",
        report.formulas_verify_rollup.as_ref(),
    ));
    output.push_str(&witness_rollup_markdown(
        "`constant_anchor` verify rows",
        report.constants_verify_rollup.as_ref(),
    ));
    output.push_str("\n## By Section\n\n| Section | Spec | Contracts | Parseable | Impl |\n|---------|------|-----------|-----------|------|\n");
    for s in &report.by_section {
        let spct = if s.contracts_total > 0 {
            100.0 * s.contracts_parseable as f64 / s.contracts_total as f64
        } else {
            0.0
        };
        output.push_str(&format!(
            "| {} | {} | {} | {} ({:.0}%) | {} |\n",
            s.section_id,
            s.spec_functions,
            s.contracts_total,
            s.contracts_parseable,
            spct,
            s.impl_functions
        ));
    }
    output
}

#[cfg(test)]
mod witness_verify_rollup_tests {
    use super::parse_verify_json_witness_rollups;

    #[test]
    fn rollup_partitions_formula_constant_and_unknown_status_buckets_failed() {
        let json = r#"{
            "report_format": 1,
            "results": [
                {"status": "passed", "formula_anchor": "F_A"},
                {"status": "failed", "formula_anchor": "F_B"},
                {"status": "not_implemented", "constant_anchor": "C_Q"},
                {"status": "weird", "formula_anchor": "F_C"}
            ]
        }"#;
        let (f, c) = parse_verify_json_witness_rollups(json).unwrap();
        let fr = f.expect("formula rollup present");
        assert_eq!(fr.total, 3);
        assert_eq!(fr.passed, 1);
        assert_eq!(fr.failed, 2);
        assert_eq!(fr.partial, 0);
        assert_eq!(fr.not_implemented, 0);
        let cr = c.expect("constant rollup present");
        assert_eq!(cr.total, 1);
        assert_eq!(cr.not_implemented, 1);
    }

    #[test]
    fn rollup_none_when_no_anchors_even_if_other_results() {
        let json = r#"{"results": [{"status": "passed", "section": "1.1"}]}"#;
        let (f, c) = parse_verify_json_witness_rollups(json).unwrap();
        assert!(f.is_none());
        assert!(c.is_none());
    }
}
