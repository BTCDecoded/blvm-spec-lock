//! Output formatting for verification results
//!
//! Formats results as human-readable, JSON, JUnit XML, or Markdown

use crate::cli::formula_checks::{
    FormulaAnalysisRow, FormulaRegistryAnalysis, FormulaStaticOutcome, Z3FormulaPhase,
};
use crate::cli::verify::{FailureKind, FunctionToVerify, VerificationResult};

/// Format verification results
pub fn format_results(results: &[(FunctionToVerify, VerificationResult)], format: &str) -> String {
    match format {
        "human" => format_human(results),
        "json" => format_json(results),
        "junit" => format_junit(results),
        "markdown" => format_markdown(results),
        _ => format_human(results),
    }
}

/// Format as human-readable text
fn format_human(results: &[(FunctionToVerify, VerificationResult)]) -> String {
    let mut output = String::new();
    output.push_str("Running BLVM Spec Lock verification...\n\n");

    for (func, result) in results {
        output.push_str(&format!(
            "{}::{}\n",
            func.file_path.display(),
            func.function_name
        ));

        match result {
            VerificationResult::Passed { body_translated } => {
                output.push_str("  ✅ Status: PASSED\n");
                output.push_str(&format!(
                    "  body_translated: {}\n",
                    if *body_translated {
                        "yes"
                    } else {
                        "no (type-level only)"
                    }
                ));
            }
            VerificationResult::Failed {
                contract,
                reason,
                kind,
                partial_reason,
            } => {
                output.push_str("  ❌ Status: FAILED\n");
                output.push_str(&format!("    Contract: {contract}\n"));
                output.push_str(&format!("    Reason: {reason}\n"));
                output.push_str(&format!("    Kind: {}\n", kind.as_str()));
                if let Some(pr) = partial_reason {
                    output.push_str(&format!("    Solver note: {}\n", pr.as_str()));
                }
            }
            VerificationResult::Partial {
                verified,
                total,
                reason,
                partial_reason,
            } => {
                output.push_str(&format!(
                    "  ⚠️  Status: PARTIAL ({verified} of {total} verified)\n"
                ));
                if let Some(pr) = partial_reason {
                    output.push_str(&format!("    Partial reason: {}\n", pr.as_str()));
                }
                if let Some(r) = reason {
                    output.push_str(&format!("    Reason: {r}\n"));
                }
            }
            VerificationResult::NoContracts { section } => {
                output.push_str(&format!(
                    "  ❌ Status: FAILED (no contracts - section {section}; add to Orange Paper or #[requires]/#[ensures])\n"
                ));
            }
            VerificationResult::NotImplemented => {
                output.push_str("  ⏳ Status: NOT IMPLEMENTED\n");
            }
        }
        output.push('\n');
    }

    // Summary
    let passed = results
        .iter()
        .filter(|(_, r)| matches!(r, VerificationResult::Passed { .. }))
        .count();
    let failed = results
        .iter()
        .filter(|(_, r)| matches!(r, VerificationResult::Failed { .. }))
        .count();
    let no_contracts = results
        .iter()
        .filter(|(_, r)| matches!(r, VerificationResult::NoContracts { .. }))
        .count();
    let partial = results
        .iter()
        .filter(|(_, r)| matches!(r, VerificationResult::Partial { .. }))
        .count();

    output.push_str(&format!(
        "test result: {}. {} passed; {} failed; {} partial; 0 skipped\n",
        if failed > 0 || no_contracts > 0 {
            "FAILED"
        } else if partial > 0 {
            "PARTIAL"
        } else {
            "ok"
        },
        passed,
        failed + no_contracts,
        partial
    ));

    // Add duration and summary stats
    output.push_str(&format!("  Functions verified: {}\n", results.len()));

    output
}

/// Machine-readable verify report for CI (`report_format` **1**).
///
/// When `formula_registry` is set, the same **`verify-formulas`**-shaped document is embedded under **`formula_registry`** (full **`report_format` 1** object with **`command`:** **`verify-formulas`** inside the gate).
///
/// Same payload printed when `--format json`; also written when using `--json-out` with any `--format`.
pub fn format_verify_json_report(
    results: &[(FunctionToVerify, VerificationResult)],
    formula_registry: Option<(&FormulaRegistryAnalysis, FormulaVerifyJsonFlags)>,
) -> String {
    use serde_json::json;

    let passed = results
        .iter()
        .filter(|(_, r)| matches!(r, VerificationResult::Passed { .. }))
        .count();
    let failed = results
        .iter()
        .filter(|(_, r)| matches!(r, VerificationResult::Failed { .. }))
        .count();
    let partial = results
        .iter()
        .filter(|(_, r)| matches!(r, VerificationResult::Partial { .. }))
        .count();

    let mut json_results = Vec::new();
    for (func, result) in results {
        let mut result_obj = json!({
            "file": func.file_path.to_string_lossy(),
            "function": func.function_name,
        });

        if let Some(ref section) = func.section {
            result_obj["section"] = json!(section);
        }
        result_obj["anchor_kind"] = json!(verify_row_anchor_kind(func));
        if let Some(ref fid) = func.formula_anchor {
            result_obj["formula_anchor"] = json!(fid);
        }
        if let Some(ref cid) = func.constant_anchor {
            result_obj["constant_anchor"] = json!(cid);
        }

        match result {
            VerificationResult::Passed { body_translated } => {
                result_obj["status"] = json!("passed");
                result_obj["body_translated"] = json!(body_translated);
            }
            VerificationResult::Failed {
                contract,
                reason,
                kind,
                partial_reason,
            } => {
                result_obj["status"] = json!("failed");
                result_obj["contract"] = json!(contract);
                result_obj["reason"] = json!(reason);
                let mut detail = serde_json::Map::new();
                detail.insert("failure_kind".into(), json!(kind.as_str()));
                if let Some(pr) = partial_reason {
                    detail.insert("partial_reason".into(), json!(pr.as_str()));
                }
                result_obj["detail"] = json!(detail);
            }
            VerificationResult::Partial {
                verified,
                total,
                reason,
                partial_reason,
            } => {
                result_obj["status"] = json!("partial");
                result_obj["verified"] = json!(*verified);
                result_obj["total"] = json!(*total);
                if let Some(r) = reason {
                    result_obj["reason"] = json!(r);
                }
                if let Some(pr) = partial_reason {
                    result_obj["detail"] = json!({
                        "partial_reason": pr.as_str(),
                    });
                }
            }
            VerificationResult::NoContracts { section } => {
                result_obj["status"] = json!("failed");
                result_obj["reason"] = json!(format!("no contracts (section {})", section));
            }
            VerificationResult::NotImplemented => {
                result_obj["status"] = json!("not_implemented");
            }
        }

        json_results.push(result_obj);
    }

    let no_contracts = results
        .iter()
        .filter(|(_, r)| matches!(r, VerificationResult::NoContracts { .. }))
        .count();

    let mut output_val = json!({
        "report_format": 1u32,
        "command": "verify",
        "tool": {
            "name": "blvm-spec-lock",
            "version": env!("CARGO_PKG_VERSION"),
        },
        "summary": {
            "total": results.len(),
            "passed": passed,
            "failed": failed,
            "partial": partial,
            "no_contracts": no_contracts,
        },
        "results": json_results,
    });

    if let Some((analysis, flags)) = formula_registry {
        if let Ok(nested) = serde_json::from_str::<serde_json::Value>(
            &format_formula_verify_json_report(analysis, flags),
        ) {
            output_val["formula_registry"] = nested;
        }
    }

    serde_json::to_string_pretty(&output_val).unwrap_or_else(|_| "{}".to_string())
}

/// Metadata for **`verify-formulas`** JSON summary (solver/stub flags mirror CLI).
#[derive(Clone, Copy, Debug)]
pub struct FormulaVerifyJsonFlags {
    pub z3_sat_requested: bool,
    pub cargo_built_with_z3: bool,
}

/// Machine-readable **`verify-formulas`** report (**`report_format` 1**).
///
/// **`command`** is **`verify-formulas`** — not **`verify`** (no **`Rust`** **`#[spec_locked]`** rows).
pub fn format_formula_verify_json_report(
    analysis: &FormulaRegistryAnalysis,
    flags: FormulaVerifyJsonFlags,
) -> String {
    use serde_json::json;

    let json_results: Vec<serde_json::Value> = analysis
        .rows
        .iter()
        .map(formula_analysis_row_json)
        .collect();

    let static_pass = analysis
        .rows
        .iter()
        .filter(|r| matches!(r.static_gate, FormulaStaticOutcome::Passed))
        .count();
    let static_fail = analysis.rows.len() - static_pass;

    let z3_requested = flags.z3_sat_requested;
    let z3_build = flags.cargo_built_with_z3;
    let z3_effective = z3_requested && z3_build;

    let z3_ok = analysis
        .rows
        .iter()
        .filter(|r| matches!(r.z3_phase, Z3FormulaPhase::SatSmokeOk))
        .count();
    let mut z3_unsat = 0usize;
    let mut z3_unknown = 0usize;
    let mut z3_error = 0usize;
    let mut z3_skipped_static = 0usize;
    let mut z3_skipped_no_build = 0usize;
    for r in &analysis.rows {
        match &r.z3_phase {
            Z3FormulaPhase::UnsatContradiction => z3_unsat += 1,
            Z3FormulaPhase::Unknown { .. } => z3_unknown += 1,
            Z3FormulaPhase::Error { .. } => z3_error += 1,
            Z3FormulaPhase::SkippedDueToStatic => z3_skipped_static += 1,
            Z3FormulaPhase::SkippedNoZ3Feature => z3_skipped_no_build += 1,
            _ => {}
        }
    }

    let output = json!({
        "report_format": 1u32,
        "command": "verify-formulas",
        "tool": {
            "name": "blvm-spec-lock",
            "version": env!("CARGO_PKG_VERSION"),
        },
        "summary": {
            "total": analysis.rows.len(),
            "static_pass": static_pass,
            "static_fail": static_fail,
            "z3_sat_requested": z3_requested,
            "z3_sat_build_available": z3_build,
            "z3_sat_effective": z3_effective,
            "z3_sat_pass": z3_ok,
            "z3_sat_unsat": z3_unsat,
            "z3_sat_unknown": z3_unknown,
            "z3_sat_error": z3_error,
            "z3_skipped_due_to_static": z3_skipped_static,
            "z3_skipped_no_z3_build": z3_skipped_no_build,
        },
        "results": json_results,
    });

    serde_json::to_string_pretty(&output).unwrap_or_else(|_| "{}".to_string())
}

fn formula_analysis_row_json(r: &FormulaAnalysisRow) -> serde_json::Value {
    use serde_json::json;

    let (static_status, static_detail): (&str, serde_json::Value) = match &r.static_gate {
        FormulaStaticOutcome::Passed => ("passed", json!(null)),
        FormulaStaticOutcome::Failed { message } => ("failed", json!(message)),
    };

    json!({
        "formula_id": &r.formula_id,
        "section": &r.section,
        "static": {
            "status": static_status,
            "detail": static_detail,
        },
        "z3_sat": formula_z3_phase_json(r),
    })
}

fn formula_z3_phase_json(r: &FormulaAnalysisRow) -> serde_json::Value {
    use serde_json::json;
    match &r.z3_phase {
        Z3FormulaPhase::NotRequested => json!(null),
        Z3FormulaPhase::SkippedDueToStatic => json!({"status": "skipped_static_gate_failed"}),
        Z3FormulaPhase::SkippedNoZ3Feature => {
            json!({"status": "skipped_no_z3_build", "detail": "cargo-spec-lock binary built without `--features z3`"})
        }
        Z3FormulaPhase::SatSmokeOk => json!({"status": "sat"}),
        Z3FormulaPhase::UnsatContradiction => {
            json!({"status": "unsat", "detail": "formula unsatisfiable under LaTeX→Rust→Z3 translation (e.g. contradiction)"})
        }
        Z3FormulaPhase::Unknown { reason } => {
            json!({"status": "unknown", "detail": reason.as_str()})
        }
        Z3FormulaPhase::Error { message } => {
            json!({"status": "error", "detail": message.as_str()})
        }
    }
}

pub fn format_formula_verify_human(
    analysis: &FormulaRegistryAnalysis,
    z3_requested: bool,
) -> String {
    use std::fmt::Write;
    let mut s = String::new();
    let _ = writeln!(
        &mut s,
        "verify-formulas: merged **`Formula` (`F_*`)** registry (static LaTeX → Rust enrich/verify gate{})",
        if z3_requested {
            "; Z3 **SAT smoke** when built with **`z3`**"
        } else {
            ""
        },
    );
    let _ = writeln!(&mut s);

    if analysis.rows.is_empty() {
        let _ = writeln!(
            &mut s,
            "  (no **`F_*`** formulas in merged spec — ingest enabled via **`SPEC_LOCK_FORMULAS`**)"
        );
        let _ = writeln!(&mut s);
        let _ = writeln!(&mut s, "summary: 0 **`F_*`** rows");
        return s;
    }

    for r in &analysis.rows {
        let line = formula_row_human_summary(r);
        let _ = writeln!(&mut s, "  {line}");
    }
    let _ = writeln!(&mut s);

    let sp = analysis
        .rows
        .iter()
        .filter(|r| matches!(r.static_gate, FormulaStaticOutcome::Passed))
        .count();
    let sf = analysis.rows.len() - sp;
    let _ = writeln!(
        &mut s,
        "summary: {} **`F_*`** · static_pass={sp} · static_fail={sf}",
        analysis.rows.len(),
    );

    s
}

fn formula_row_human_summary(r: &FormulaAnalysisRow) -> String {
    let static_s = match &r.static_gate {
        FormulaStaticOutcome::Passed => "static PASS".into(),
        FormulaStaticOutcome::Failed { message } => format!("static FAIL ({message})"),
    };
    let z3_s = match &r.z3_phase {
        Z3FormulaPhase::NotRequested => "Z3 (not requested)".into(),
        Z3FormulaPhase::SkippedDueToStatic => "Z3 skipped (static FAIL)".into(),
        Z3FormulaPhase::SkippedNoZ3Feature => "Z3 skipped (no **`z3`** build)".into(),
        Z3FormulaPhase::SatSmokeOk => "Z3 SAT smoke OK".into(),
        Z3FormulaPhase::UnsatContradiction => "Z3 UNSAT (contradiction)".into(),
        Z3FormulaPhase::Unknown { reason } => format!("Z3 unknown ({reason})"),
        Z3FormulaPhase::Error { message } => format!("Z3 error ({message})"),
    };
    format!("{} §{} · {static_s} · {z3_s}", r.formula_id, r.section)
}

/// Stable classifier for **`results[]`** rows: which **`#[spec_locked]`** anchor kind drove enrichment.
///
/// **`formula_anchor`** wins if both are set (resolver treats **`F_*`** first); otherwise **`constant`**, else traditional **function**/section lock.
fn verify_row_anchor_kind(func: &FunctionToVerify) -> &'static str {
    if func.formula_anchor.is_some() {
        "formula"
    } else if func.constant_anchor.is_some() {
        "constant"
    } else {
        "function"
    }
}

/// Format as JSON (stdout when `--format json`)
fn format_json(results: &[(FunctionToVerify, VerificationResult)]) -> String {
    format_verify_json_report(results, None)
}

/// Format as JUnit XML
fn format_junit(results: &[(FunctionToVerify, VerificationResult)]) -> String {
    use std::fmt::Write;

    let _passed = results
        .iter()
        .filter(|(_, r)| matches!(r, VerificationResult::Passed { .. }))
        .count();
    let failed = results
        .iter()
        .filter(|(_, r)| {
            matches!(
                r,
                VerificationResult::Failed { .. } | VerificationResult::NoContracts { .. }
            )
        })
        .count();
    let total = results.len();

    let mut xml = String::new();
    xml.push_str("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n");
    writeln!(
        &mut xml,
        "<testsuites name=\"blvm-spec-lock\" tests=\"{total}\" failures=\"{failed}\" time=\"0.0\">"
    )
    .unwrap();
    writeln!(
        &mut xml,
        "  <testsuite name=\"verification\" tests=\"{total}\" failures=\"{failed}\" time=\"0.0\">"
    )
    .unwrap();

    for (func, result) in results {
        let classname = func
            .file_path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("unknown");

        let status_attr = match result {
            VerificationResult::Passed { .. } => "",
            VerificationResult::Failed { .. } => " status=\"failed\"",
            VerificationResult::Partial { .. } => " status=\"partial\"",
            VerificationResult::NoContracts { .. } => " status=\"failed\"",
            VerificationResult::NotImplemented => " status=\"not_implemented\"",
        };

        writeln!(
            &mut xml,
            "    <testcase name=\"{}\" classname=\"{}\"{}>",
            func.function_name, classname, status_attr
        )
        .unwrap();

        if let Some(ref section) = func.section {
            write!(
                &mut xml,
                "      <properties>\n        <property name=\"section\" value=\"{section}\"/>\n      </properties>\n"
            ).unwrap();
        }

        if let VerificationResult::Failed {
            contract,
            reason,
            kind,
            partial_reason,
        } = result
        {
            let mut suffix = format!("contract: {}; kind: {}", contract, kind.as_str(),);
            if let Some(pr) = partial_reason {
                suffix.push_str(&format!("; partial_reason={}", pr.as_str()));
            }
            writeln!(
                &mut xml,
                "      <failure message=\"{}\">{}</failure>",
                reason.replace('"', "&quot;"),
                suffix.replace('"', "&quot;"),
            )
            .unwrap();
        }

        if let VerificationResult::Partial {
            verified,
            total,
            reason,
            partial_reason,
        } = result
        {
            let mut body = format!("partial {verified}/{total}");
            if let Some(pr) = partial_reason {
                body.push_str(&format!("; partial_reason={}", pr.as_str()));
            }
            if let Some(r) = reason {
                body.push_str(&format!("; {r}"));
            }
            writeln!(
                &mut xml,
                "      <system-out>{}</system-out>",
                body.replace('"', "&quot;")
            )
            .unwrap();
        }

        xml.push_str("    </testcase>\n");
    }

    xml.push_str("  </testsuite>\n");
    xml.push_str("</testsuites>\n");

    xml
}

/// Format as Markdown
fn format_markdown(results: &[(FunctionToVerify, VerificationResult)]) -> String {
    let mut md = String::new();

    md.push_str("# BLVM Spec Lock Verification Report\n\n");
    // Simple timestamp (would use chrono if available)
    md.push_str("**Generated:** Verification Report\n\n");

    // Summary
    let passed = results
        .iter()
        .filter(|(_, r)| matches!(r, VerificationResult::Passed { .. }))
        .count();
    let failed = results
        .iter()
        .filter(|(_, r)| matches!(r, VerificationResult::Failed { .. }))
        .count();
    let partial = results
        .iter()
        .filter(|(_, r)| matches!(r, VerificationResult::Partial { .. }))
        .count();
    let no_contracts = results
        .iter()
        .filter(|(_, r)| matches!(r, VerificationResult::NoContracts { .. }))
        .count();

    md.push_str("## Summary\n\n");
    md.push_str(&format!("- **Total Functions:** {}\n", results.len()));
    md.push_str(&format!("- **Passed:** {passed} ✅\n"));
    md.push_str(&format!("- **Failed:** {} ❌\n", failed + no_contracts));
    md.push_str(&format!("- **Partial:** {partial} ⚠️\n\n"));

    // Results table
    md.push_str("## Results\n\n");
    md.push_str("| File | Function | Section | Status |\n");
    md.push_str("|------|----------|---------|--------|\n");

    for (func, result) in results {
        let file_name = func
            .file_path
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or("unknown");

        let section = func.section.as_deref().unwrap_or("-");

        let status = match result {
            VerificationResult::Passed { body_translated } => {
                if *body_translated {
                    "✅ Passed (semantic)".to_string()
                } else {
                    "✅ Passed (type-level)".to_string()
                }
            }
            VerificationResult::Failed {
                kind,
                partial_reason,
                ..
            } => {
                let mut s = format!("❌ Failed [{}]", kind.as_str());
                if *kind == FailureKind::SolverUnknown {
                    if let Some(pr) = partial_reason {
                        s.push_str(&format!(" ({})", pr.as_str()));
                    }
                }
                s
            }
            VerificationResult::Partial {
                verified,
                total,
                reason,
                partial_reason,
            } => {
                let mut s = format!("⚠️ Partial ({verified}/{total})");
                if let Some(pr) = partial_reason {
                    s.push_str(&format!(" [{}]", pr.as_str()));
                }
                if let Some(r) = reason {
                    s.push_str(&format!(": {r}"));
                }
                s
            }
            VerificationResult::NoContracts { section } => {
                format!("❌ Failed (no contracts §{section})")
            }
            VerificationResult::NotImplemented => "⏳ Not Implemented".to_string(),
        };

        md.push_str(&format!(
            "| `{}` | `{}` | {} | {} |\n",
            file_name, func.function_name, section, status
        ));
    }

    // Failed details
    let failed_results: Vec<_> = results
        .iter()
        .filter(|(_, r)| {
            matches!(
                r,
                VerificationResult::Failed { .. } | VerificationResult::NoContracts { .. }
            )
        })
        .collect();

    if !failed_results.is_empty() {
        md.push_str("\n## Failed Verifications\n\n");
        for (func, result) in failed_results {
            md.push_str(&format!(
                "### `{}::{}`\n\n",
                func.file_path.display(),
                func.function_name
            ));
            match result {
                VerificationResult::Failed {
                    contract,
                    reason,
                    kind,
                    partial_reason,
                } => {
                    md.push_str(&format!("- **Contract:** {contract}\n"));
                    md.push_str(&format!("- **Reason:** {reason}\n"));
                    md.push_str(&format!("- **Failure kind:** {}\n", kind.as_str()));
                    if let Some(pr) = partial_reason {
                        md.push_str(&format!("- **Solver note:** {}\n", pr.as_str()));
                    }
                    md.push('\n');
                }
                VerificationResult::NoContracts { section } => {
                    md.push_str(&format!(
                        "- **Reason:** no contracts (section {section})\n\n"
                    ));
                }
                _ => {}
            }
        }
    }

    md
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cli::verify::{
        FailureKind, FunctionToVerify, PartialReason, VerificationResult, failed_verification,
    };
    use std::path::PathBuf;

    #[test]
    fn verify_json_report_includes_report_format_and_tool() {
        let results: Vec<(FunctionToVerify, VerificationResult)> = vec![];
        let s = format_verify_json_report(&results, None);
        assert!(s.contains("\"report_format\": 1"));
        assert!(s.contains("\"command\": \"verify\""));
        assert!(s.contains("\"name\": \"blvm-spec-lock\""));
        assert!(s.contains("\"summary\""));
        assert!(s.contains("\"passed\": 0"));
    }

    #[test]
    fn verify_json_rows_include_anchor_kind() {
        let base = |fa: Option<String>, ca: Option<String>, expect: &str| {
            let f = FunctionToVerify {
                file_path: PathBuf::from("src/x.rs"),
                function_name: "witness".to_string(),
                contracts: vec![],
                section: Some("1.0".to_string()),
                spec_name_override: None,
                formula_anchor: fa,
                constant_anchor: ca,
                function_sig: None,
            };
            let s = format_verify_json_report(
                &[(
                    f,
                    VerificationResult::Passed {
                        body_translated: false,
                    },
                )],
                None,
            );
            assert!(
                s.contains(&format!("\"anchor_kind\": \"{expect}\"")),
                "expected anchor_kind {expect} in:\n{s}"
            );
        };
        base(None, None, "function");
        base(Some("F_X".to_string()), None, "formula");
        base(None, Some("C_Y".to_string()), "constant");
        base(Some("F_Z".to_string()), Some("C_Z".to_string()), "formula");
    }

    #[test]
    fn formula_verify_json_uses_verify_formulas_command_and_static_shape() {
        use crate::cli::formula_checks::{
            FormulaAnalysisRow, FormulaRegistryAnalysis, FormulaStaticOutcome, Z3FormulaPhase,
        };
        let analysis = FormulaRegistryAnalysis {
            rows: vec![
                FormulaAnalysisRow {
                    formula_id: "F_Test".into(),
                    section: "9.9".into(),
                    static_gate: FormulaStaticOutcome::Passed,
                    z3_phase: Z3FormulaPhase::NotRequested,
                },
                FormulaAnalysisRow {
                    formula_id: "F_Bad".into(),
                    section: "1".into(),
                    static_gate: FormulaStaticOutcome::Failed {
                        message: "oops".into(),
                    },
                    z3_phase: Z3FormulaPhase::SkippedDueToStatic,
                },
            ],
        };
        let s = format_formula_verify_json_report(
            &analysis,
            FormulaVerifyJsonFlags {
                z3_sat_requested: false,
                cargo_built_with_z3: false,
            },
        );
        assert!(s.contains("\"command\": \"verify-formulas\""), "{s}");
        assert!(s.contains("\"formula_id\": \"F_Test\""), "{s}");
        assert!(s.contains("\"static_pass\": 1"), "{s}");
        assert!(s.contains("\"static_fail\": 1"), "{s}");
    }

    #[test]
    fn verify_json_report_counts_passed() {
        let f = FunctionToVerify {
            file_path: PathBuf::from("src/x.rs"),
            function_name: "foo".to_string(),
            contracts: vec![],
            section: Some("6.1".to_string()),
            spec_name_override: None,
            formula_anchor: None,
            constant_anchor: None,
            function_sig: None,
        };
        let results = vec![(
            f,
            VerificationResult::Passed {
                body_translated: true,
            },
        )];
        let s = format_verify_json_report(&results, None);
        assert!(s.contains("\"passed\": 1"));
        assert!(s.contains("\"total\": 1"));
    }

    #[test]
    fn verify_json_report_includes_failure_detail() {
        let f = FunctionToVerify {
            file_path: PathBuf::from("src/x.rs"),
            function_name: "foo".to_string(),
            contracts: vec![],
            section: Some("6.1".to_string()),
            spec_name_override: None,
            formula_anchor: None,
            constant_anchor: None,
            function_sig: None,
        };
        let results = vec![(
            f,
            VerificationResult::Failed {
                contract: "Requires".to_string(),
                reason: "parse error".to_string(),
                kind: FailureKind::ParseError,
                partial_reason: None,
            },
        )];
        let s = format_verify_json_report(&results, None);
        assert!(s.contains("\"failure_kind\": \"parse_error\""));
    }

    #[test]
    fn verify_json_report_includes_partial_detail() {
        let f = FunctionToVerify {
            file_path: PathBuf::from("src/x.rs"),
            function_name: "foo".to_string(),
            contracts: vec![],
            section: Some("6.1".to_string()),
            spec_name_override: None,
            formula_anchor: None,
            constant_anchor: None,
            function_sig: None,
        };
        let results = vec![(
            f,
            VerificationResult::Partial {
                verified: 1,
                total: 2,
                reason: Some("r".to_string()),
                partial_reason: Some(PartialReason::MissingZ3Build),
            },
        )];
        let s = format_verify_json_report(&results, None);
        assert!(s.contains("\"partial_reason\": \"missing_z3_build\""));
    }

    #[test]
    fn verify_json_partial_reason_variants_emit_stable_strings() {
        for (partial_reason, needle) in [
            (
                PartialReason::Z3Unknown,
                "\"partial_reason\": \"z3_unknown\"",
            ),
            (
                PartialReason::Z3Timeout,
                "\"partial_reason\": \"z3_timeout\"",
            ),
            (
                PartialReason::UnsupportedTranslation,
                "\"partial_reason\": \"unsupported_translation\"",
            ),
            (
                PartialReason::MissingZ3Build,
                "\"partial_reason\": \"missing_z3_build\"",
            ),
            (
                PartialReason::IncompleteCoverage,
                "\"partial_reason\": \"incomplete_coverage\"",
            ),
            (PartialReason::Other, "\"partial_reason\": \"other\""),
        ] {
            let f = FunctionToVerify {
                file_path: PathBuf::from("src/x.rs"),
                function_name: "foo".to_string(),
                contracts: vec![],
                section: Some("6.1".to_string()),
                spec_name_override: None,
                formula_anchor: None,
                constant_anchor: None,
                function_sig: None,
            };
            let results = vec![(
                f,
                VerificationResult::Partial {
                    verified: 0,
                    total: 1,
                    reason: None,
                    partial_reason: Some(partial_reason),
                },
            )];
            let s = format_verify_json_report(&results, None);
            assert!(s.contains(needle), "expected {needle} in:\n{s}");
        }
    }

    #[test]
    fn verify_json_failure_kind_variants_emit_stable_strings() {
        for (kind, needle) in [
            (
                FailureKind::Counterexample,
                "\"failure_kind\": \"counterexample\"",
            ),
            (FailureKind::ParseError, "\"failure_kind\": \"parse_error\""),
            (
                FailureKind::SolverUnknown,
                "\"failure_kind\": \"solver_unknown\"",
            ),
            (
                FailureKind::SolverError,
                "\"failure_kind\": \"solver_error\"",
            ),
            (FailureKind::Tooling, "\"failure_kind\": \"tooling\""),
            (FailureKind::Other, "\"failure_kind\": \"other\""),
        ] {
            let f = FunctionToVerify {
                file_path: PathBuf::from("src/x.rs"),
                function_name: "foo".to_string(),
                contracts: vec![],
                section: Some("6.1".to_string()),
                spec_name_override: None,
                formula_anchor: None,
                constant_anchor: None,
                function_sig: None,
            };
            let results = vec![(
                f,
                VerificationResult::Failed {
                    contract: "Requires".to_string(),
                    reason: "r".to_string(),
                    kind,
                    partial_reason: None,
                },
            )];
            let s = format_verify_json_report(&results, None);
            assert!(s.contains(needle), "expected {needle} in:\n{s}");
        }
    }

    #[test]
    fn verify_json_solver_unknown_failed_includes_partial_reason_timeout_heuristic() {
        let f = FunctionToVerify {
            file_path: PathBuf::from("src/x.rs"),
            function_name: "foo".to_string(),
            contracts: vec![],
            section: Some("6.1".to_string()),
            spec_name_override: None,
            formula_anchor: None,
            constant_anchor: None,
            function_sig: None,
        };

        let timeout_row = failed_verification(
            "Ensures",
            "Z3: Z3 verification unknown: timeout or complexity.",
            1,
        );
        let st = format_verify_json_report(&[(f.clone(), timeout_row)], None);
        assert!(st.contains("\"failure_kind\": \"solver_unknown\""), "{st}");
        assert!(st.contains("\"partial_reason\": \"z3_timeout\""), "{st}");

        let other_row = failed_verification(
            "Ensures",
            "Z3: Z3 verification unknown: nondeterministic cause.",
            1,
        );
        let s2 = format_verify_json_report(&[(f, other_row)], None);
        assert!(s2.contains("\"failure_kind\": \"solver_unknown\""), "{s2}");
        assert!(s2.contains("\"partial_reason\": \"z3_unknown\""), "{s2}");
    }
}
