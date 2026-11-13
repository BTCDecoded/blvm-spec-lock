//! Body-edit gate. A passing check is proved from the body only when two
//! distinct edits of that body make the same check fail.
//!
//! The gate does not change the verify status and does not reject Partial.
//! That decision stays on `--reject-partial`.

use crate::cli::verify::{FunctionToVerify, PartialReason, VerificationResult, verify_function};
use crate::translator::body_edit;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProofBucket {
    ProvedFromBody,
    Vacuous,
    Partial,
    Failed,
}

impl ProofBucket {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::ProvedFromBody => "proved_from_body",
            Self::Vacuous => "vacuous",
            Self::Partial => "partial",
            Self::Failed => "failed",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GateRow {
    pub bucket: ProofBucket,
    pub reason: String,
}

type Edit = fn(&mut syn::ItemFn) -> bool;

const EDITORS: &[Edit] = &[
    body_edit::tighten_returned_le,
    body_edit::tighten_returned_ge,
    body_edit::increment_returned_cmp_literal,
    body_edit::flip_returned_eq,
    body_edit::flip_returned_neq,
    body_edit::drop_returned_and_left,
    body_edit::drop_returned_or_left,
    body_edit::replace_returned_and_with_or,
    body_edit::relax_returned_lt,
    body_edit::relax_returned_gt,
    body_edit::reverse_returned_lt,
    body_edit::reverse_returned_gt,
    body_edit::flip_returned_match_bool,
    body_edit::negate_returned_is_empty,
    body_edit::flip_early_ok_true,
    body_edit::drop_early_true_return,
    body_edit::increment_returned_if_literal,
    body_edit::false_first_le,
    body_edit::tighten_first_le,
    body_edit::zero_eq_lit,
];

fn rendered(func: &syn::ItemFn) -> String {
    quote::quote!(#func).to_string()
}

fn partial_text(reason: &Option<String>, kind: &Option<PartialReason>) -> String {
    let mut parts = Vec::new();
    if let Some(text) = reason {
        parts.push(text.clone());
    }
    if let Some(kind) = kind {
        parts.push(kind.as_str().to_string());
    }
    if parts.is_empty() {
        "verify returned Partial".to_string()
    } else {
        parts.join("; ")
    }
}

/// Classify one verify result. `timeout_secs` is the per-edit limit.
/// Failed and Partial are not edited. A passing result is edited until two
/// checks fail, or the editor list ends.
pub fn classify(
    func: &FunctionToVerify,
    result: &VerificationResult,
    timeout_secs: u64,
) -> GateRow {
    match result {
        VerificationResult::Failed { .. } => GateRow {
            bucket: ProofBucket::Failed,
            reason: "verify failed".to_string(),
        },
        VerificationResult::Partial {
            reason,
            partial_reason,
            ..
        } => GateRow {
            bucket: ProofBucket::Partial,
            reason: partial_text(reason, partial_reason),
        },
        VerificationResult::NoContracts { .. } | VerificationResult::NotImplemented => GateRow {
            bucket: ProofBucket::Partial,
            reason: "not a passing check".to_string(),
        },
        VerificationResult::Passed { .. } => classify_passed(func, timeout_secs),
    }
}

fn classify_passed(func: &FunctionToVerify, timeout_secs: u64) -> GateRow {
    let Some(original) = func.function_sig.as_ref() else {
        return GateRow {
            bucket: ProofBucket::Partial,
            reason: "no function body".to_string(),
        };
    };
    let original_src = rendered(original);
    let mut seen = std::collections::HashSet::new();
    let mut applied = 0usize;
    let mut flips = 0usize;
    for edit in EDITORS {
        let mut edited = original.clone();
        if !edit(&mut edited) {
            continue;
        }
        let next = rendered(&edited);
        if next == original_src || !seen.insert(next) {
            continue;
        }
        applied += 1;
        let mut trial = func.clone();
        trial.function_sig = Some(edited);
        if matches!(
            verify_function(&trial, timeout_secs, &[]),
            VerificationResult::Failed { .. }
        ) {
            flips += 1;
            if flips >= 2 {
                break;
            }
        }
    }
    if flips >= 2 {
        return GateRow {
            bucket: ProofBucket::ProvedFromBody,
            reason: "at least two body edits make the check fail".to_string(),
        };
    }
    if applied >= 2 && flips == 0 {
        return GateRow {
            bucket: ProofBucket::Vacuous,
            reason: "body edits still pass the check".to_string(),
        };
    }
    if flips == 1 {
        return GateRow {
            bucket: ProofBucket::Partial,
            reason: "only one body edit makes the check fail".to_string(),
        };
    }
    GateRow {
        bucket: ProofBucket::Partial,
        reason: "no applicable body edit".to_string(),
    }
}

#[cfg(all(test, feature = "z3"))]
mod tests {
    use super::{ProofBucket, classify};
    use crate::cli::verify::{
        Contract, ContractType, VerificationResult, make_function_to_verify, verify_function,
    };
    use crate::parser::spec_expr::consensus_workspace_present;

    fn item(src: &str, name: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).unwrap_or_else(|err| panic!("parse {name}: {err}"));
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == name => Some(func),
                _ => None,
            })
            .unwrap_or_else(|| panic!("{name}"))
    }

    fn with_clause(
        file: &str,
        name: &str,
        func: syn::ItemFn,
        clause: &str,
    ) -> crate::cli::verify::FunctionToVerify {
        let mut function =
            make_function_to_verify(std::path::Path::new(file), name, &func.attrs, &func);
        function.contracts = vec![Contract {
            contract_type: ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        function
    }

    #[test]
    fn failed_stays_failed_without_a_body() {
        let row = classify(
            &crate::cli::verify::FunctionToVerify {
                file_path: std::path::PathBuf::from("t.rs"),
                function_name: "t".to_string(),
                contracts: Vec::new(),
                section: None,
                spec_name_override: None,
                formula_anchor: None,
                constant_anchor: None,
                formulas: Vec::new(),
                function_sig: None,
                parse_gap: false,
            },
            &VerificationResult::Failed {
                contract: "result == true".to_string(),
                reason: "counterexample".to_string(),
                kind: crate::cli::verify::FailureKind::Counterexample,
                partial_reason: None,
            },
            5,
        );
        assert_eq!(row.bucket, ProofBucket::Failed);
    }

    #[test]
    fn sigop_push_is_proved_from_the_body() {
        if !consensus_workspace_present() {
            return;
        }
        let path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../blvm-consensus/src/sigop.rs");
        let src = std::fs::read_to_string(&path).expect("sigop.rs");
        let func = item(&src, "sigop_count_push_opcode");
        let function = with_clause(
            "src/sigop.rs",
            "sigop_count_push_opcode",
            func,
            "result == (op <= 96)",
        );
        let result = verify_function(&function, 15, &[]);
        assert!(
            matches!(
                result,
                VerificationResult::Passed {
                    body_translated: true
                }
            ),
            "sigop push must pass from the body, got {result:?}"
        );
        let row = classify(&function, &result, 15);
        assert_eq!(
            row.bucket,
            ProofBucket::ProvedFromBody,
            "sigop push is the reference body proof: {}",
            row.reason
        );
    }
}
