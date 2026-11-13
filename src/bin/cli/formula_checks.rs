//! Shared **`F_*`** registry analysis for **`check-formulas`** and **`verify-formulas`**:
//! static LaTeX → Rust gate; optional Z3 SAT smoke (no Rust implementation).

use crate::parser::orange_paper::{FormulaSpec, SpecParser};

/// Whether to run Z3 satisfiability smoke after the static gate (per **`F_*`**).
#[derive(Clone, Copy, Debug)]
pub struct FormulaAnalyzeConfig {
    /// When false, **`z3_phase`** rows are **`Z3FormulaPhase::NotRequested`**.
    pub request_z3_sat: bool,
    /// Per-formula Z3 solver budget (milliseconds).
    pub timeout_ms: u64,
}

/// Outcomes for **`SpecParser::formulas()`**: one row per merged **`Formula`** id.
#[derive(Debug, Clone)]
pub struct FormulaRegistryAnalysis {
    pub rows: Vec<FormulaAnalysisRow>,
}

#[derive(Debug, Clone)]
pub struct FormulaAnalysisRow {
    pub formula_id: String,
    pub section: String,
    pub static_gate: FormulaStaticOutcome,
    pub z3_phase: Z3FormulaPhase,
}

#[derive(Debug, Clone)]
pub enum FormulaStaticOutcome {
    Passed,
    Failed { message: String },
}

#[derive(Debug, Clone)]
pub enum Z3FormulaPhase {
    NotRequested,
    SkippedDueToStatic,
    SkippedNoZ3Feature,
    SatSmokeOk,
    UnsatContradiction,
    Unknown { reason: String },
    Error { message: String },
}

/// Unbounded `∀` is a Lean sentence. `extract_parseable_condition` returns
/// `None` for it on purpose, and Z3 has no universal quantifier here.
fn latex_is_lean_only_forall(latex: &str) -> bool {
    latex.contains(r"\forall") || latex.contains('∀')
}

fn evaluate_static_gate(fs: &FormulaSpec) -> FormulaStaticOutcome {
    use crate::cli::drift::formula_latex_parseable_for_verify;
    use crate::parser::condition;

    if latex_is_lean_only_forall(&fs.latex_body) {
        return FormulaStaticOutcome::Passed;
    }
    if !formula_latex_parseable_for_verify(&fs.latex_body) {
        return FormulaStaticOutcome::Failed {
            message: "fails verify/enrich latex parse gate".into(),
        };
    }
    let cond = fs.latex_body.trim();
    match condition::extract_parseable_condition(cond) {
        Some(s) => match syn::parse_str::<syn::Expr>(&s) {
            Ok(_expr) => FormulaStaticOutcome::Passed,
            Err(_) => FormulaStaticOutcome::Failed {
                message: "parseable-condition is invalid Rust Expr".into(),
            },
        },
        None => FormulaStaticOutcome::Failed {
            message: "extract_parseable_condition returned None".into(),
        },
    }
}

#[cfg(feature = "z3")]
fn z3_sat_smoke(fs: &FormulaSpec, timeout_ms: u64) -> Z3FormulaPhase {
    use crate::parser::condition;
    use crate::parser::contracts::{Contract, ContractType};
    use crate::translator::z3_verifier::{VerificationResult, Z3Verifier};

    let cond = fs.latex_body.trim();
    let Some(s) = condition::extract_parseable_condition(cond) else {
        return Z3FormulaPhase::Error {
            message: "extract_parseable_condition None (unexpected after static pass)".into(),
        };
    };
    let Ok(expr) = syn::parse_str::<syn::Expr>(&s) else {
        return Z3FormulaPhase::Error {
            message: "invalid Expr (unexpected after static pass)".into(),
        };
    };
    let contract = Contract {
        contract_type: ContractType::Ensures,
        condition: expr,
        comment: None,
    };
    let mut verifier = Z3Verifier::new(timeout_ms.max(1));
    match verifier.check_ensures_formula_sat_smoke(&contract) {
        VerificationResult::Verified { .. } => Z3FormulaPhase::SatSmokeOk,
        VerificationResult::Failed { .. } => Z3FormulaPhase::UnsatContradiction,
        VerificationResult::Unknown { reason } => Z3FormulaPhase::Unknown { reason },
        VerificationResult::Error { error } => Z3FormulaPhase::Error { message: error },
    }
}

/// Sort-stable scan of merged **`Formula`** registry: static gate always; optional Z3 SAT smoke.
pub fn analyze_formula_registry(
    parser: &SpecParser,
    cfg: FormulaAnalyzeConfig,
) -> FormulaRegistryAnalysis {
    let mut formulas: Vec<&FormulaSpec> = parser.formulas().values().collect();
    formulas.sort_by(|a, b| a.id.cmp(&b.id));

    let mut rows = Vec::with_capacity(formulas.len());

    for fs in formulas {
        let static_gate = evaluate_static_gate(fs);
        let z3_phase = match &static_gate {
            FormulaStaticOutcome::Failed { .. } => {
                if cfg.request_z3_sat {
                    Z3FormulaPhase::SkippedDueToStatic
                } else {
                    Z3FormulaPhase::NotRequested
                }
            }
            FormulaStaticOutcome::Passed => {
                if latex_is_lean_only_forall(&fs.latex_body) || !cfg.request_z3_sat {
                    Z3FormulaPhase::NotRequested
                } else {
                    #[cfg(feature = "z3")]
                    {
                        z3_sat_smoke(fs, cfg.timeout_ms)
                    }
                    #[cfg(not(feature = "z3"))]
                    {
                        Z3FormulaPhase::SkippedNoZ3Feature
                    }
                }
            }
        };

        rows.push(FormulaAnalysisRow {
            formula_id: fs.id.clone(),
            section: fs.section.clone(),
            static_gate,
            z3_phase,
        });
    }

    FormulaRegistryAnalysis { rows }
}

/// **`check-formulas`** / **`verify-formulas`** failure: any **`F_*`** failed the static enrich/verify gate.
pub fn registry_has_blocking_static_failure(analysis: &FormulaRegistryAnalysis) -> bool {
    analysis
        .rows
        .iter()
        .any(|r| matches!(r.static_gate, FormulaStaticOutcome::Failed { .. }))
}

/// Caller requested Z3 SAT smoke (**`verify-formulas`** without **`--skip-z3`**, or **`check-formulas --z3-sat`**)
/// any row blocked on SAT / Unknown / tooling, or toolchain lacks **`--features z3`** (**`SkippedNoZ3Feature`**).
pub fn registry_has_blocking_z3_outcome(analysis: &FormulaRegistryAnalysis) -> bool {
    analysis.rows.iter().any(|r| {
        matches!(
            &r.z3_phase,
            Z3FormulaPhase::SkippedNoZ3Feature
                | Z3FormulaPhase::UnsatContradiction
                | Z3FormulaPhase::Unknown { .. }
                | Z3FormulaPhase::Error { .. }
        )
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::orange_paper::SpecParser;

    #[test]
    fn forall_formula_passes_static_and_skips_z3() {
        let md = r"## 5.1.1 Sighash

**Formula** (**F_SighashBase**):

$$\forall byte: \text{SighashBase}(byte) = byte \% 32$$
";
        let mut parser = SpecParser::new(md.to_string());
        parser.parse().expect("parse");
        let analysis = analyze_formula_registry(
            &parser,
            FormulaAnalyzeConfig {
                request_z3_sat: true,
                timeout_ms: 1_000,
            },
        );
        assert!(!registry_has_blocking_static_failure(&analysis));
        assert!(!registry_has_blocking_z3_outcome(&analysis));
        let row = analysis
            .rows
            .iter()
            .find(|r| r.formula_id == "F_SighashBase")
            .expect("row");
        assert!(matches!(row.static_gate, FormulaStaticOutcome::Passed));
        assert!(matches!(row.z3_phase, Z3FormulaPhase::NotRequested));
    }
}
