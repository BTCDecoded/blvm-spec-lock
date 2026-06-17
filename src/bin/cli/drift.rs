//! Spec drift detection
//!
//! Detects when Orange Paper and implementation diverge

use super::verify::{FunctionToVerify, discover_functions};
use std::path::{Path, PathBuf};
// Note: SpecParser is not accessible from binary (proc-macro crate limitation)
// Using simplified drift detection for now

/// Drift detection result
#[derive(Debug, Clone)]
pub struct DriftResult {
    /// Functions with contracts that don't match Orange Paper
    pub mismatched_contracts: Vec<MismatchedContract>,
    /// Functions missing from Orange Paper
    pub missing_from_spec: Vec<FunctionToVerify>,
    /// Orange Paper theorems without implementations
    pub missing_implementations: Vec<String>,
    /// Functions with auto-inferred sections (may need verification)
    pub auto_inferred: Vec<FunctionToVerify>,
    /// Spec contracts that are unparseable (spec has them but we can't verify)
    pub unparseable_spec_contracts: Vec<UnparseableContract>,
    /// **`F_*`** formula bodies (**`latex_body`**) failing the verifier parse gate
    pub unparseable_formulas: Vec<UnparseableFormula>,
    /// With `--scoped-unparseables`: unparseables in sections not referenced by `#[spec_locked]` (informational)
    pub unparseable_omitted_outside_scope: usize,
    /// With `--scoped-formulas`: formula drift rows omitted outside locked § prefixes (informational)
    pub unparseable_formulas_omitted_outside_scope: usize,
    /// Parseable but unconditional `result == true/false` claims with no antecedent.
    /// These are almost always false universal claims (the function does not always return the same value).
    pub suspect_universal_claims: Vec<SuspectUniversalClaim>,
}

/// A spec property that parses to an unconditional `result == true/false` with no antecedent.
/// Likely indicates a missing conditional that was accidentally dropped from the spec.
#[derive(Debug, Clone)]
pub struct SuspectUniversalClaim {
    pub section: String,
    pub function: String,
    pub condition: String,
}

/// A spec contract that couldn't be parsed for verification
#[derive(Debug, Clone)]
pub struct UnparseableContract {
    pub section: String,
    pub function: String,
    pub condition: String,
}

/// A **`Formula` (`F_*`)** **`$$`** body that does not satisfy the same **`extract_parseable_condition` +
/// `syn`** gate used by **`spec_enrich`** / **`verify`**.
#[derive(Debug, Clone)]
pub struct UnparseableFormula {
    pub id: String,
    pub section: String,
    pub body_preview: String,
}

/// A contract mismatch
#[derive(Debug, Clone)]
pub struct MismatchedContract {
    pub function: FunctionToVerify,
    pub orange_paper_contract: String,
    pub implementation_contract: String,
    pub section: String,
}

/// Detect spec drift
///
/// When **`scoped_unparseables`** is true, only unparseable spec properties in sections that match a
/// **`#[spec_locked("…")]`** prefix in the crate contribute to drift / failure for **Function** contracts.
///
/// **`scoped_formulas`**: same prefix rule applies to **`F_*`** **Formula** **`latex_body`** rows.
pub fn detect_drift(
    workspace_root: &Path,
    orange_paper_paths: Option<&[PathBuf]>,
    scoped_unparseables: bool,
    scoped_formulas: bool,
) -> Result<DriftResult, String> {
    use crate::parser::condition;
    use crate::parser::orange_paper::SpecParser;

    let mut functions = discover_functions(workspace_root)?;

    let spec_paths: Vec<PathBuf> = orange_paper_paths.map(|p| p.to_vec()).unwrap_or_else(|| {
        // Default to the split spec files used by CI (PROTOCOL.md + ARCHITECTURE.md).
        // Fall back to THE_ORANGE_PAPER.md if neither split file exists, and warn.
        let protocol = workspace_root.join("../blvm-spec/PROTOCOL.md");
        let architecture = workspace_root.join("../blvm-spec/ARCHITECTURE.md");
        if protocol.exists() || architecture.exists() {
            vec![protocol, architecture]
        } else {
            let fallback = workspace_root.join("../blvm-spec/THE_ORANGE_PAPER.md");
            if !fallback.exists() {
                eprintln!(
                    "warning: no spec files found at default paths \
                         (PROTOCOL.md, ARCHITECTURE.md, THE_ORANGE_PAPER.md). \
                         Pass --spec-path explicitly."
                );
            } else {
                eprintln!(
                    "warning: using THE_ORANGE_PAPER.md fallback; \
                         prefer split PROTOCOL.md + ARCHITECTURE.md to match CI."
                );
            }
            vec![fallback]
        }
    });

    // Enrich functions with spec-derived contracts before drift check.
    // Without this, #[spec_locked] functions have empty contracts (macro output not in parsed source).
    if spec_paths.iter().all(|p| p.exists()) && !spec_paths.is_empty() {
        let _ = super::spec_enrich::enrich_functions_with_spec(&mut functions, &spec_paths);
    }

    let mut mismatched_contracts = Vec::new();
    let mut missing_from_spec = Vec::new();
    let mut auto_inferred = Vec::new();
    let mut unparseable_spec_contracts = Vec::new();
    let missing_implementations = Vec::new();

    for func in &functions {
        if func.section.is_none() {
            auto_inferred.push(func.clone());
            continue;
        }
        if func.contracts.is_empty() {
            missing_from_spec.push(func.clone());
            continue;
        }

        // Compare manually-written contracts against spec-derived contracts.
        // If a manual contract has no similar spec counterpart of the same type,
        // it represents drift from the Orange Paper.
        let manual: Vec<_> = func
            .contracts
            .iter()
            .filter(|c| !c.is_spec_derived)
            .collect();
        let spec: Vec<_> = func
            .contracts
            .iter()
            .filter(|c| c.is_spec_derived)
            .collect();

        if !manual.is_empty() && !spec.is_empty() {
            for m in &manual {
                let has_match = spec.iter().any(|s| {
                    s.contract_type == m.contract_type
                        && contracts_similar(&s.condition, &m.condition)
                });
                if !has_match {
                    // Find the first spec contract of the same type for the mismatch report.
                    if let Some(s) = spec.iter().find(|s| s.contract_type == m.contract_type) {
                        mismatched_contracts.push(MismatchedContract {
                            function: func.clone(),
                            orange_paper_contract: s.condition.clone(),
                            implementation_contract: m.condition.clone(),
                            section: func.section.clone().unwrap_or_default(),
                        });
                    }
                }
            }
        }
    }

    let locked_sections: std::collections::HashSet<String> =
        functions.iter().filter_map(|f| f.section.clone()).collect();

    let mut unparseable_formulas = Vec::new();
    let mut suspect_universal_claims = Vec::new();

    if spec_paths.iter().all(|p| p.exists()) && !spec_paths.is_empty() {
        let parser =
            SpecParser::from_paths(&spec_paths).map_err(|e| format!("Failed to load spec: {e}"))?;

        for (section_id, section) in parser.iter_sections() {
            for func in &section.functions {
                for contract in &func.contracts {
                    let raw = &contract.condition;
                    if condition::extract_parseable_condition(raw).is_none() {
                        let short = if raw.len() > 80 {
                            format!("{}...", &raw[..77])
                        } else {
                            raw.clone()
                        };
                        unparseable_spec_contracts.push(UnparseableContract {
                            section: section_id.clone(),
                            function: func.name.clone(),
                            condition: short,
                        });
                    }
                }

                // Lint: check the *original* property statement (before implication-stripping
                // translation) for unconditional `result = \text{true/false}` with no antecedent.
                // `contract.condition` is already translated and stripped, so we look at the raw
                // `property.statement` from the spec parser instead.
                for property in &func.properties {
                    let stmt = &property.statement;
                    // Quick pre-filter: must contain "result" and "true" or "false"
                    if !(stmt.contains("result")
                        && (stmt.contains("true") || stmt.contains("false")))
                    {
                        continue;
                    }
                    if let Some(ref parsed) = condition::extract_parseable_condition(stmt) {
                        if is_suspect_universal(stmt, parsed) {
                            suspect_universal_claims.push(SuspectUniversalClaim {
                                section: section_id.clone(),
                                function: func.name.clone(),
                                condition: stmt.trim().to_string(),
                            });
                        }
                    }
                }
            }
        }

        for fspec in parser.formulas().values() {
            if !formula_latex_parseable_for_verify(&fspec.latex_body) {
                let preview = trim_preview(&fspec.latex_body, 120);
                unparseable_formulas.push(UnparseableFormula {
                    id: fspec.id.clone(),
                    section: fspec.section.clone(),
                    body_preview: preview,
                });
            }
        }
    }

    let (unparseable_spec_contracts, unparseable_omitted_outside_scope) = if scoped_unparseables {
        let full = unparseable_spec_contracts;
        let mut kept = Vec::new();
        let mut omitted = 0usize;
        for u in full {
            if unparseable_in_scope(&u.section, &locked_sections) {
                kept.push(u);
            } else {
                omitted += 1;
            }
        }
        (kept, omitted)
    } else {
        (unparseable_spec_contracts, 0)
    };

    let (unparseable_formulas, unparseable_formulas_omitted_outside_scope) = if scoped_formulas {
        let full = unparseable_formulas;
        let mut kept = Vec::new();
        let mut omitted = 0usize;
        for u in full {
            if unparseable_in_scope(&u.section, &locked_sections) {
                kept.push(u);
            } else {
                omitted += 1;
            }
        }
        (kept, omitted)
    } else {
        (unparseable_formulas, 0)
    };

    Ok(DriftResult {
        mismatched_contracts,
        missing_from_spec,
        missing_implementations,
        auto_inferred,
        unparseable_spec_contracts,
        unparseable_formulas,
        unparseable_omitted_outside_scope,
        unparseable_formulas_omitted_outside_scope,
        suspect_universal_claims,
    })
}

/// Returns true when a spec condition is an unconditional `result == true/false` claim with no
/// antecedent.  These are almost always spec errors: the writer forgot the `\implies` and
/// antecedent, accidentally asserting that a function *always* returns the same value.
///
/// Heuristic: the raw spec text has no implication markers AND the parsed form is exactly
/// `result == true` or `result == false` (allowing whitespace normalisation).
fn is_suspect_universal(raw: &str, parsed: &str) -> bool {
    // Unconditional booleans only — `result == 0` / `result == 1` have legitimate uses (e.g.
    // constants, epoch-0 formulas).  We flag only boolean tautologies.
    // Normalise whitespace for comparison (parsed form may or may not have spaces around `==`).
    let parsed_norm: String = parsed.split_whitespace().collect::<Vec<_>>().join(" ");
    let parsed_norm = parsed_norm.trim();
    if parsed_norm != "result == true"
        && parsed_norm != "result==true"
        && parsed_norm != "result == false"
        && parsed_norm != "result==false"
    {
        return false;
    }
    // Accept the claim only if the spec text contains an implication or biconditional.
    // If neither is present the claim is a bare `result = true/false` with no guard.
    let raw_lc = raw.to_lowercase();
    let has_antecedent = raw_lc.contains("\\implies")
        || raw_lc.contains("\\rightarrow")
        || raw_lc.contains("\\iff")
        || raw_lc.contains("\\land")
        || raw_lc.contains("=>")
        || raw_lc.contains("\\neg");
    !has_antecedent
}

/// Same gate as **`spec_enrich`** for **`F_*`** bodies: **`extract_parseable_condition`** plus **`syn::Expr`** parse.
pub(crate) fn formula_latex_parseable_for_verify(latex_body: &str) -> bool {
    use crate::parser::condition;

    let cond = latex_body.trim();
    if cond.is_empty() {
        return false;
    }
    let Some(parseable) = condition::extract_parseable_condition(cond) else {
        return false;
    };
    syn::parse_str::<syn::Expr>(&parseable).is_ok()
}

fn trim_preview(s: &str, max_chars: usize) -> String {
    let t = s.split_whitespace().collect::<Vec<_>>().join(" ");
    let n = t.chars().count();
    if n <= max_chars {
        return t;
    }
    let take = max_chars.saturating_sub(3);
    let short: String = t.chars().take(take).collect();
    format!("{short}...")
}

/// `spec_section` is in scope if it equals or extends any `#[spec_locked]` section (dot-separated prefix).
fn unparseable_in_scope(
    spec_section: &str,
    locked_sections: &std::collections::HashSet<String>,
) -> bool {
    locked_sections
        .iter()
        .any(|lock| spec_section_matches_lock(spec_section, lock))
}

fn spec_section_matches_lock(spec_section: &str, lock: &str) -> bool {
    let spec_parts: Vec<&str> = spec_section.split('.').collect();
    let lock_parts: Vec<&str> = lock.split('.').collect();
    if spec_parts.len() < lock_parts.len() {
        return false;
    }
    spec_parts[..lock_parts.len()] == lock_parts[..]
}

/// Convert Rust snake_case to PascalCase
fn rust_to_pascal_case(rust_name: &str) -> String {
    rust_name
        .split('_')
        .map(|word| {
            let mut chars = word.chars();
            match chars.next() {
                None => String::new(),
                Some(first) => first.to_uppercase().collect::<String>() + chars.as_str(),
            }
        })
        .collect()
}

/// Check if two contracts are similar (allows for minor formatting differences)
fn contracts_similar(spec: &str, impl_contract: &str) -> bool {
    // Normalize both contracts
    let spec_norm = normalize_contract(spec);
    let impl_norm = normalize_contract(impl_contract);

    // Spec `Defined: true` / literal true is the weakest postcondition — any tighter
    // inline #[ensures] on the implementation is a valid refinement, not drift.
    if spec_norm == "true" {
        return true;
    }

    // Check for exact match
    if spec_norm == impl_norm {
        return true;
    }

    // Check if one contains the other (for partial matches)
    spec_norm.contains(&impl_norm) || impl_norm.contains(&spec_norm)
}

/// Normalize contract string for comparison
fn normalize_contract(contract: &str) -> String {
    contract.to_lowercase().replace(' ', "")
}

/// Find theorems in Orange Paper without corresponding implementations
/// Note: Implementation pending - requires SpecParser access from binary
fn _find_missing_implementations(_functions: &[FunctionToVerify]) -> Vec<String> {
    Vec::new()
}

/// Format drift report as human-readable text
pub fn format_drift_human(result: &DriftResult) -> String {
    let mut output = String::new();

    output.push_str("=== Spec Drift Detection Report ===\n\n");

    // Mismatched contracts
    if !result.mismatched_contracts.is_empty() {
        output.push_str("⚠️  Mismatched Contracts:\n");
        output.push_str("------------------------\n");
        for mismatch in &result.mismatched_contracts {
            output.push_str(&format!(
                "  Function: {} (Section {})\n",
                mismatch.function.function_name, mismatch.section
            ));
            output.push_str(&format!(
                "    Orange Paper: {}\n",
                mismatch.orange_paper_contract
            ));
            output.push_str(&format!(
                "    Implementation: {}\n",
                mismatch.implementation_contract
            ));
            output.push('\n');
        }
    }

    // Missing from spec
    if !result.missing_from_spec.is_empty() {
        output.push_str("❌ Functions Missing from Orange Paper:\n");
        output.push_str("--------------------------------------\n");
        for func in &result.missing_from_spec {
            output.push_str(&format!(
                "  {} ({})\n",
                func.function_name,
                func.file_path.display()
            ));
        }
        output.push('\n');
    }

    // Auto-inferred
    if !result.auto_inferred.is_empty() {
        output.push_str("ℹ️  Auto-Inferred Functions (verify manually):\n");
        output.push_str("---------------------------------------------\n");
        for func in &result.auto_inferred {
            output.push_str(&format!(
                "  {} ({})\n",
                func.function_name,
                func.file_path.display()
            ));
        }
        output.push('\n');
    }

    if !result.unparseable_spec_contracts.is_empty() {
        output.push_str("⚠️  Unparseable Spec Contracts (can't verify):\n");
        output.push_str("--------------------------------------------\n");
        for u in result.unparseable_spec_contracts.iter().take(10) {
            output.push_str(&format!(
                "  {}::{}: {}\n",
                u.section, u.function, u.condition
            ));
        }
        if result.unparseable_spec_contracts.len() > 10 {
            output.push_str(&format!(
                "  ... and {} more\n",
                result.unparseable_spec_contracts.len() - 10
            ));
        }
        output.push('\n');
    }

    if !result.unparseable_formulas.is_empty() {
        output.push_str(
            "⚠️  Unparseable **Formula** (`F_*`) bodies (enrich/verify parse gate failed):\n",
        );
        output.push_str("------------------------------------------------------------------\n");
        for u in result.unparseable_formulas.iter().take(10) {
            output.push_str(&format!("  {} §{}: {}\n", u.id, u.section, u.body_preview));
        }
        if result.unparseable_formulas.len() > 10 {
            output.push_str(&format!(
                "  ... and {} more\n",
                result.unparseable_formulas.len() - 10
            ));
        }
        output.push('\n');
    }

    if !result.suspect_universal_claims.is_empty() {
        output
            .push_str("🔍 Suspect Universal Claims (`result == true/false` with no antecedent):\n");
        output
            .push_str("------------------------------------------------------------------------\n");
        output.push_str(
            "   These may be missing conditionals, e.g. `A \\implies result = \\text{true}`.\n",
        );
        for u in result.suspect_universal_claims.iter().take(10) {
            output.push_str(&format!(
                "  {}::{}: {}\n",
                u.section, u.function, u.condition
            ));
        }
        if result.suspect_universal_claims.len() > 10 {
            output.push_str(&format!(
                "  ... and {} more\n",
                result.suspect_universal_claims.len() - 10
            ));
        }
        output.push('\n');
    }

    output.push_str("Summary:\n");
    output.push_str("--------\n");
    output.push_str(&format!(
        "  Mismatched contracts: {}\n",
        result.mismatched_contracts.len()
    ));
    output.push_str(&format!(
        "  Missing from spec: {}\n",
        result.missing_from_spec.len()
    ));
    output.push_str(&format!(
        "  Unparseable spec contracts: {}\n",
        result.unparseable_spec_contracts.len()
    ));
    output.push_str(&format!(
        "  Unparseable **Formula** (`F_*`): {}\n",
        result.unparseable_formulas.len()
    ));
    if result.unparseable_omitted_outside_scope > 0 {
        output.push_str(&format!(
            "  Unparseable contracts outside scoped sections (omitted): {}\n",
            result.unparseable_omitted_outside_scope
        ));
    }
    if result.unparseable_formulas_omitted_outside_scope > 0 {
        output.push_str(&format!(
            "  Unparseable formulas outside scoped sections (omitted): {}\n",
            result.unparseable_formulas_omitted_outside_scope
        ));
    }
    output.push_str(&format!(
        "  Auto-inferred: {}\n",
        result.auto_inferred.len()
    ));
    output.push_str(&format!(
        "  Missing implementations: {}\n",
        result.missing_implementations.len()
    ));
    if !result.suspect_universal_claims.is_empty() {
        output.push_str(&format!(
            "  Suspect universal claims (lint): {}\n",
            result.suspect_universal_claims.len()
        ));
    }

    if result.mismatched_contracts.is_empty()
        && result.missing_from_spec.is_empty()
        && result.missing_implementations.is_empty()
        && result.unparseable_spec_contracts.is_empty()
        && result.unparseable_formulas.is_empty()
        && result.suspect_universal_claims.is_empty()
    {
        output.push_str("\n✅ No drift detected! Spec and implementation are in sync.\n");
    }

    output
}

/// Format drift report as JSON
pub fn format_drift_json(result: &DriftResult) -> String {
    serde_json::json!({
        "mismatched_contracts": result.mismatched_contracts.iter().map(|m| serde_json::json!({
            "function": m.function.function_name,
            "file": m.function.file_path.display().to_string(),
            "section": m.section,
            "orange_paper_contract": m.orange_paper_contract,
            "implementation_contract": m.implementation_contract,
        })).collect::<Vec<_>>(),
        "missing_from_spec": result.missing_from_spec.iter().map(|f| serde_json::json!({
            "function": f.function_name,
            "file": f.file_path.display().to_string(),
        })).collect::<Vec<_>>(),
        "unparseable_spec_contracts": result.unparseable_spec_contracts.iter().map(|u| serde_json::json!({
            "section": u.section,
            "function": u.function,
            "condition": u.condition,
        })).collect::<Vec<_>>(),
        "auto_inferred": result.auto_inferred.iter().map(|f| serde_json::json!({
            "function": f.function_name,
            "file": f.file_path.display().to_string(),
        })).collect::<Vec<_>>(),
        "missing_implementations": result.missing_implementations,
        "unparseable_omitted_outside_scope": result.unparseable_omitted_outside_scope,
        "unparseable_formulas": result.unparseable_formulas.iter().map(|u| serde_json::json!({
            "id": u.id,
            "section": u.section,
            "body_preview": u.body_preview,
        })).collect::<Vec<_>>(),
        "unparseable_formulas_omitted_outside_scope": result.unparseable_formulas_omitted_outside_scope,
        "suspect_universal_claims": result.suspect_universal_claims.iter().map(|u| serde_json::json!({
            "section": u.section,
            "function": u.function,
            "condition": u.condition,
        })).collect::<Vec<_>>(),
    })
    .to_string()
}

#[cfg(test)]
mod tests {
    use super::{formula_latex_parseable_for_verify, spec_section_matches_lock};

    #[test]
    fn formula_parse_gate_accepts_known_witness_style_body() {
        assert!(formula_latex_parseable_for_verify("true"));
        assert!(formula_latex_parseable_for_verify(r" x \leq y "));
    }

    #[test]
    fn formula_parse_gate_accepts_cdot_times_unicode_comparison() {
        assert!(formula_latex_parseable_for_verify(r"w \cdot h \leq z"));
        assert!(formula_latex_parseable_for_verify(r"a × b ≤ c")); // × and ≤ Unicode
        assert!(formula_latex_parseable_for_verify(r"\mathrm{X} >= 0"));
    }

    #[test]
    fn formula_parse_gate_accepts_unicode_logic_ne_minus_implication() {
        assert!(formula_latex_parseable_for_verify(r"p ≠ q")); // U+2260
        assert!(formula_latex_parseable_for_verify(r"a − b ≤ c")); // U+2212 minus
        assert!(formula_latex_parseable_for_verify(r"x ∧ y ≤ z")); // U+2227
        assert!(formula_latex_parseable_for_verify(r"m ∨ n ≥ k")); // U+2228
        assert!(formula_latex_parseable_for_verify(r"a ⇒ x ≤ y")); // Unicode ⇒ → conclusion `x <= y`
    }

    #[test]
    fn formula_parse_gate_rejects_empty_or_pure_noise() {
        assert!(!formula_latex_parseable_for_verify(""));
        assert!(!formula_latex_parseable_for_verify("   "));
        assert!(!formula_latex_parseable_for_verify(
            "\\notProbablyValidRust blah"
        ));
    }

    #[test]
    fn section_prefix_does_not_match_sibling_minor() {
        assert!(!spec_section_matches_lock("5.10", "5.1"));
        assert!(!spec_section_matches_lock("5.1", "5.1.1"));
    }

    #[test]
    fn section_prefix_matches_descendants() {
        assert!(spec_section_matches_lock("5.1.1", "5.1"));
        assert!(spec_section_matches_lock("5.1", "5.1"));
    }
}
