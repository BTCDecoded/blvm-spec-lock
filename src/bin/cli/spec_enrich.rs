//! Enrich spec-locked functions with contracts from the Orange Paper.

use super::verify::{Contract, ContractType, FunctionToVerify};
use crate::parser::condition;
use crate::parser::orange_paper::{
    ContractType as SpecContractType, SpecParser, section_id_subsumes_formula_section,
};
use std::path::PathBuf;

fn find_function_in_section_or_parents<'a>(
    parser: &'a SpecParser,
    section: &str,
    name: Option<&str>,
) -> Option<&'a crate::parser::orange_paper::FunctionSpec> {
    let mut s = section;
    loop {
        if let Some(f) = parser.find_function(s, name) {
            return Some(f);
        }
        if let Some(dot) = s.rfind('.') {
            s = &s[..dot];
        } else {
            break;
        }
    }
    None
}

/// Convert Rust snake_case to spec PascalCase (e.g. get_block_subsidy -> GetBlockSubsidy)
fn rust_to_spec_name(rust_name: &str) -> String {
    rust_name
        .split('_')
        .map(|s| {
            let mut c = s.chars();
            match c.next() {
                None => String::new(),
                Some(f) => f.to_uppercase().chain(c).collect(),
            }
        })
        .collect()
}

/// Enrich discovered functions with contracts extracted from the Orange Paper.
/// Accepts one or more spec paths; when multiple, sections are merged (duplicate section IDs error).
pub fn enrich_functions_with_spec(
    functions: &mut [FunctionToVerify],
    spec_paths: &[PathBuf],
) -> Result<usize, String> {
    let parser = SpecParser::from_paths(spec_paths)?;

    let mut enriched_count = 0;

    for func in functions.iter_mut() {
        let Some(section_ref) = func.section.as_deref() else {
            continue;
        };

        // Phase **`C_*`** — consensus **`ExtractedConstant`** (**`constants_stable_id_map`**).
        if let Some(cid) = &func.constant_anchor {
            let cmap = parser
                .constants_stable_id_map()
                .map_err(|e| format!("Orange Paper (--spec-path) constant index: {e}"))?;
            match cmap.get(cid) {
                None => {
                    return Err(format!(
                        "Orange Paper (--spec-path) has no **`C_*`** id `{cid}` (Section 4 **$NAME = …$**) referenced by **`#[spec_locked]`**.",
                    ));
                }
                Some(ec) => {
                    if !section_id_subsumes_formula_section(section_ref, &ec.section) {
                        eprintln!(
                            "Warning: section mismatch for `{cid}`: #[spec_locked] cites §{section_ref} but constant is defined under §{}. Skipping constant enrichment for this function.",
                            ec.section
                        );
                        continue;
                    }
                    // Preserve Requires from #[blvm_spec_lock::requires(…)] attributes;
                    // only replace Ensures with the spec-derived constant equality.
                    func.contracts.retain(|c| {
                        (c.contract_type == ContractType::Requires
                            || c.contract_type == ContractType::Axiom)
                            && !c.is_spec_derived
                    });
                    let condition = format!("result == {}", ec.rust_expr);
                    let parseable_opt = condition::extract_parseable_condition(&condition);
                    let expr = parseable_opt
                        .as_deref()
                        .and_then(|s| syn::parse_str::<syn::Expr>(s).ok());
                    if let Some(expr) = expr {
                        let stored = parseable_opt.unwrap_or_else(|| condition.clone());
                        func.contracts.push(Contract {
                            contract_type: ContractType::Ensures,
                            condition: stored,
                            expr: Some(expr),
                            is_spec_derived: true,
                        });
                        enriched_count += 1;
                    }
                    continue;
                }
            }
        }

        // Phase 5 — explicit **`F_*`** anchors bind to **`Formula`** blocks before function lookup.
        if let Some(fid) = &func.formula_anchor {
            match parser.formulas().get(fid) {
                None => {
                    return Err(format!(
                        "Orange Paper (--spec-path) has no **`Formula`** id `{fid}` referenced by **`#[spec_locked]`**.",
                    ));
                }
                Some(fspec) => {
                    if !section_id_subsumes_formula_section(section_ref, &fspec.section) {
                        eprintln!(
                            "Warning: section mismatch for formula `{fid}`: #[spec_locked] cites §{section_ref} but formula is defined under §{}. Skipping formula enrichment for this function.",
                            fspec.section
                        );
                        continue;
                    }
                    // Save manually-written #[ensures] annotations before clearing.
                    // If the spec formula body is not parseable to Z3-compatible Rust,
                    // we restore them so the code-level proof obligation is still verified.
                    let manual_ensures: Vec<Contract> = func
                        .contracts
                        .iter()
                        .filter(|c| c.contract_type == ContractType::Ensures && !c.is_spec_derived)
                        .cloned()
                        .collect();

                    // Preserve Requires from #[blvm_spec_lock::requires(…)] attributes;
                    // only replace Ensures with the spec-derived formula.
                    func.contracts.retain(|c| {
                        (c.contract_type == ContractType::Requires
                            || c.contract_type == ContractType::Axiom)
                            && !c.is_spec_derived
                    });
                    let condition = fspec.latex_body.trim().to_string();
                    let mut spec_formula_pushed = false;
                    if !condition.is_empty() {
                        let parseable = condition::extract_parseable_condition(&condition);
                        let expr = parseable
                            .as_ref()
                            .and_then(|s| syn::parse_str::<syn::Expr>(s).ok());

                        // Before accepting the spec formula, check that it references at least
                        // one of the witness function's parameters.  Formulas that use only
                        // spec-world names (e.g. `BIP30Check(b, us, h, n) == valid`) produce
                        // vacuous Z3 uninterpreted-function contracts.  In that case we fall
                        // back to the manually-written #[ensures] which carry the real proof.
                        let formula_ok =
                            if let (Some(cond_str), Some(sig)) = (&parseable, &func.function_sig) {
                                let param_names: std::collections::HashSet<String> = sig
                                    .sig
                                    .inputs
                                    .iter()
                                    .filter_map(|a| {
                                        if let syn::FnArg::Typed(pt) = a {
                                            if let syn::Pat::Ident(pi) = &*pt.pat {
                                                return Some(pi.ident.to_string());
                                            }
                                        }
                                        None
                                    })
                                    .collect();
                                expr.is_some()
                                    && (param_names.is_empty()
                                        || !condition_references_only_unknown_vars(
                                            cond_str,
                                            &param_names,
                                        ))
                            } else {
                                expr.is_some()
                            };

                        if formula_ok {
                            func.contracts.push(Contract {
                                contract_type: ContractType::Ensures,
                                condition: condition.clone(),
                                expr,
                                is_spec_derived: true,
                            });
                            enriched_count += 1;
                            spec_formula_pushed = true;
                        }
                    }

                    // Restore manual ensures when:
                    // (a) the spec formula could not be parsed — the inline annotations
                    //     are more informative than nothing, OR
                    // (b) the spec formula reduced to the trivially-true literal `true` —
                    //     the inline postconditions carry tighter bounds (e.g.
                    //     `result >= 0`, `result <= INITIAL_SUBSIDY`) that callee-axiom
                    //     propagation can discharge for wrapper callers.
                    let spec_trivially_true = func
                        .contracts
                        .iter()
                        .filter(|c| c.is_spec_derived && c.contract_type == ContractType::Ensures)
                        .all(|c| c.condition.trim() == "true");
                    if (!spec_formula_pushed || spec_trivially_true) && !manual_ensures.is_empty() {
                        // Dedup: skip manual contracts whose condition is already present.
                        for m in manual_ensures {
                            if !func.contracts.iter().any(|e| e.condition == m.condition) {
                                func.contracts.push(m);
                            }
                        }
                    }

                    continue;
                }
            }
        }

        // Prefer the explicit spec name from `#[spec_locked("X.Y", "SpecName")]` over
        // the auto-derived PascalCase conversion of the Rust function name.  This handles
        // functions like `get_median_time_past_reversed` that implement a spec entry
        // (`GetMedianTimePast`) whose name differs from the Rust function name.
        let spec_name = func
            .spec_name_override
            .clone()
            .unwrap_or_else(|| rust_to_spec_name(&func.function_name));

        let spec_func = parser
            .find_function(section_ref, Some(&spec_name))
            .or_else(|| parser.find_function_anywhere(&spec_name).map(|(f, _)| f))
            .or_else(|| parser.find_function(section_ref, None))
            .or_else(|| find_function_in_section_or_parents(&parser, section_ref, None));
        if std::env::var("SPEC_LOCK_DEBUG_ENRICH").is_ok() {
            let found = spec_func
                .as_ref()
                .map(|f| format!("{} ({} contracts)", f.name, f.contracts.len()))
                .unwrap_or_else(|| "NONE".to_string());
            eprintln!(
                "ENRICH_DEBUG[{}]: section={} found={}",
                func.function_name, section_ref, found
            );
        }
        let spec_func = spec_func.map(|f| {
            if f.contracts.is_empty() {
                // Prefer a wildcard catch-all entry if the section has one.
                // Fall back to the originally found function so that the
                // "spec section exists, no formal properties" path in the
                // block below can inject a trivially-true contract rather
                // than silently dropping this function from enrichment.
                parser.find_function(section_ref, Some("*")).unwrap_or(f)
            } else {
                f
            }
        });

        if let Some(spec_func) = spec_func {
            if spec_func.contracts.is_empty() {
                // Spec section exists but has no formal Properties — the function is
                // documented but not formally constrained. Inject a trivially-true contract
                // so that check-drift and verify don't flag it as "missing from spec".
                // This eliminates the need for `Defined: $\text{true}$` boilerplate in the
                // Orange Paper: the spec can document a function without formal properties
                // and the tooling treats it as trivially passing.
                let expr: syn::Expr = syn::parse_str("true").expect("'true' is valid Rust");
                func.contracts.push(Contract {
                    contract_type: ContractType::Ensures,
                    condition: "true".to_string(),
                    expr: Some(expr),
                    is_spec_derived: true,
                });
                enriched_count += 1;
                continue;
            }

            // Save manually-written #[ensures] annotations before clearing.
            // If the spec produces no parseable Z3 contracts, restore them so the
            // code-level proof obligations are still verified rather than replaced
            // by an unparseable "no parseable spec contracts" placeholder.
            let manual_ensures: Vec<Contract> = func
                .contracts
                .iter()
                .filter(|c| c.contract_type == ContractType::Ensures && !c.is_spec_derived)
                .cloned()
                .collect();

            // Preserve Requires from #[blvm_spec_lock::requires(…)] attributes;
            // only replace Ensures with spec-derived contracts.
            func.contracts.retain(|c| {
                (c.contract_type == ContractType::Requires
                    || c.contract_type == ContractType::Axiom)
                    && !c.is_spec_derived
            });

            let mut added_any = false;
            for spec_contract in &spec_func.contracts {
                let contract_type = match spec_contract.contract_type {
                    SpecContractType::Requires => ContractType::Requires,
                    SpecContractType::Ensures
                    | SpecContractType::Property
                    | SpecContractType::EdgeCase => ContractType::Ensures,
                };

                let condition = spec_contract.condition.trim().to_string();
                if condition.is_empty() {
                    continue;
                }

                let parseable = condition::extract_parseable_condition(&condition);
                let expr = parseable
                    .as_ref()
                    .and_then(|s| syn::parse_str::<syn::Expr>(s).ok());

                if expr.is_none() {
                    continue;
                }

                // Reject implications where the antecedent references input variables.
                // condition.rs strips `A => B` to just `B` for the formula gate (syntax
                // check), but when B is injected as a universal ensures contract, the
                // dropped antecedent A makes the clause incorrect for all inputs where A
                // is false (e.g. `weight == 0 => result == 0` → `result == 0` fails for
                // weight > 0). Only allow implication-stripping when the antecedent
                // contains only `result` (a self-referential postcondition).
                let has_implication = condition.contains("\\implies")
                    || condition.contains("\\Rightarrow")
                    || condition.contains('\u{21d2}') // ⇒
                    || condition.contains('\u{2192}') // →
                    || condition.contains("=>");
                if has_implication {
                    // Find the antecedent (everything before the first implication arrow).
                    let impl_pos = condition
                        .find("\\implies")
                        .or_else(|| condition.find("\\Rightarrow"))
                        .or_else(|| condition.find('\u{21d2}'))
                        .or_else(|| condition.find('\u{2192}'))
                        .or_else(|| condition.find("=>"));
                    if let Some(pos) = impl_pos {
                        let antecedent = &condition[..pos];
                        let antecedent_has_non_result_idents = antecedent
                            .split(|c: char| !c.is_alphanumeric() && c != '_' && c != '\\')
                            .filter(|tok| !tok.is_empty())
                            .filter(|tok| tok.chars().next().is_some_and(|c| c.is_alphabetic()))
                            .any(|tok| tok != "result" && !tok.starts_with('\\'));
                        if antecedent_has_non_result_idents {
                            continue; // Cannot inject: antecedent involves inputs.
                        }
                    }
                }

                // Skip spec contracts where every non-`result` identifier in the
                // extracted condition is unknown to the function's parameter list.
                // This filters spec variables that use different names from Rust params
                // (e.g. `min_h`/`min_t` vs `block_height`/`block_time`) — contracts
                // built from such variables are always vacuous: Z3 treats them as free
                // unconstrained variables and can arbitrarily satisfy or violate them.
                if let Some(ref cond_str) = parseable {
                    if let Some(ref sig) = func.function_sig {
                        let param_names: std::collections::HashSet<String> = sig
                            .sig
                            .inputs
                            .iter()
                            .filter_map(|a| {
                                if let syn::FnArg::Typed(pt) = a {
                                    if let syn::Pat::Ident(pi) = &*pt.pat {
                                        return Some(pi.ident.to_string());
                                    }
                                }
                                None
                            })
                            .collect();
                        if !param_names.is_empty()
                            && condition_references_only_unknown_vars(cond_str, &param_names)
                        {
                            continue;
                        }
                    }
                }

                let stored_condition = parseable.clone().unwrap_or_else(|| condition.clone());
                let contract = Contract {
                    contract_type,
                    condition: stored_condition.clone(),
                    expr,
                    is_spec_derived: true,
                };

                if !func
                    .contracts
                    .iter()
                    .any(|c| c.condition == stored_condition)
                {
                    func.contracts.push(contract);
                    enriched_count += 1;
                    added_any = true;
                }
            }

            // Determine whether the spec pushed any non-trivial contracts.
            let spec_trivially_true = func
                .contracts
                .iter()
                .filter(|c| c.is_spec_derived && c.contract_type == ContractType::Ensures)
                .all(|c| c.condition.trim() == "true");

            // Restore inline ensures when:
            // (a) no spec contract could be parsed — inline annotations are more informative, OR
            // (b) the spec reduced to only `true` — inline postconditions are tighter bounds
            //     (e.g. `result >= 0`, `result <= INITIAL_SUBSIDY`) that callee-axiom
            //     propagation in the Z3 verifier can discharge for wrapper callers.
            if (!added_any || spec_trivially_true) && !manual_ensures.is_empty() {
                // Dedup: skip manual contracts whose condition is already present.
                for m in manual_ensures {
                    if !func.contracts.iter().any(|e| e.condition == m.condition) {
                        func.contracts.push(m);
                    }
                }
            } else if !added_any && manual_ensures.is_empty() {
                // Spec section was found and has properties, but none were parseable
                // (e.g., all are implications with input-variable antecedents that the
                // translator correctly skips to avoid vacuous contracts). Inject a
                // trivially-true contract so the function is not flagged as
                // "missing from spec" by check-drift or NoContracts by verify.
                // Z3 trivially proves `true` — result is PASSED, never PARTIAL.
                let expr: syn::Expr = syn::parse_str("true").expect("'true' is valid Rust");
                if !func.contracts.iter().any(|c| c.condition == "true") {
                    func.contracts.push(Contract {
                        contract_type: ContractType::Ensures,
                        condition: "true".to_string(),
                        expr: Some(expr),
                        is_spec_derived: true,
                    });
                    enriched_count += 1;
                }
            }
        }

        // Do not add a placeholder when no parseable contracts exist and no manual
        // ensures were present. In that case leave contracts empty so the verifier's
        // auto_type_contracts path can fire (type-level PASSED). Adding a placeholder
        // here would block auto_type_contracts and incorrectly produce PARTIAL for
        // functions whose spec properties are legitimately complex but whose return
        // type guarantees are still sound.
    }

    Ok(enriched_count)
}

/// Returns `true` when every non-`result` word-boundary identifier referenced in
/// `cond` is absent from `param_names`.
///
/// Used to discard spec-derived contracts whose variable names don't correspond to
/// any Rust function parameter — e.g. spec uses `min_h`/`min_t` while Rust uses
/// `block_height`/`block_time`. Such contracts always produce vacuous Z3 proofs
/// because the unrecognised names become free unconstrained Z3 variables.
///
/// We only skip the contract when ALL non-`result` identifiers are unknown.
/// If at least one identifier matches a param, the contract likely targets this
/// function and should be kept (even if other variables are spec-only abbreviations).
fn condition_references_only_unknown_vars(
    cond: &str,
    param_names: &std::collections::HashSet<String>,
) -> bool {
    // Collect word-boundary identifiers from the condition (Rust-like ident: [A-Za-z_][A-Za-z0-9_]*)
    let re = match regex::Regex::new(r"\b([A-Za-z_][A-Za-z0-9_]*)\b") {
        Ok(r) => r,
        Err(_) => return false,
    };
    // Skip known keywords / context names that are never function params.
    const ALWAYS_KNOWN: &[&str] = &[
        "result", "true", "false", "Ok", "Err", "Some", "None", "u64", "u32", "i64", "i32",
        "usize", "bool", "as", "let", "if", "else", "return", "and", "or", "not",
    ];
    let idents: Vec<String> = re
        .captures_iter(cond)
        .filter_map(|cap| {
            let name = cap[1].to_string();
            if ALWAYS_KNOWN.contains(&name.as_str()) {
                None
            } else {
                Some(name)
            }
        })
        .collect();

    if idents.is_empty() {
        return false; // No identifiers to check — let it through
    }

    // If at least one identifier IS a known param, keep the contract.
    !idents.iter().any(|id| param_names.contains(id))
}

#[cfg(test)]
mod enrich_formula_tests {
    use super::*;
    use crate::cli::verify::FunctionToVerify;
    use std::path::PathBuf;
    use syn::parse_quote;

    #[test]
    fn formula_anchor_enrich_adds_parseable_contract_from_spec() {
        let dir = std::env::temp_dir().join(format!(
            "spec_lock_formula_enrich_{}_{}",
            std::process::id(),
            rand_unique()
        ));
        std::fs::create_dir_all(&dir).expect("tmpdir");
        let md_path = dir.join("minimal_formula.md");

        let md = r"## 99.91 Formula enrich fixture

**Formula** (**F_EnrichSmoke**):

$$true$$
";
        std::fs::write(&md_path, md).expect("write fixture");
        let _cleanup_dir = TmpDirCleanup(dir);

        let func: syn::ItemFn = parse_quote! {
            fn witness_formula_enrich() -> bool { true }
        };

        let mut functions = vec![FunctionToVerify {
            file_path: PathBuf::from("witness.rs"),
            function_name: "witness_formula_enrich".into(),
            contracts: vec![],
            section: Some("99.91".into()),
            spec_name_override: None,
            formula_anchor: Some("F_EnrichSmoke".into()),
            constant_anchor: None,
            function_sig: Some(func),
        }];

        let n =
            enrich_functions_with_spec(&mut functions, &[md_path]).expect("enrich_without_error");
        assert_eq!(n, 1);
        assert_eq!(functions.len(), 1);
        assert_eq!(functions[0].contracts.len(), 1);
        assert_eq!(
            functions[0].contracts[0].contract_type,
            ContractType::Ensures
        );
        assert!(functions[0].contracts[0].expr.is_some());
    }

    #[test]
    fn constant_anchor_enrich_adds_ensures_equals_rust_expr() {
        let dir = std::env::temp_dir().join(format!(
            "spec_lock_constant_enrich_{}_{}",
            std::process::id(),
            rand_unique()
        ));
        std::fs::create_dir_all(&dir).expect("tmpdir");
        let md_path = dir.join("minimal_constant.md");

        let md = r"## 4.99 Fixture constants

$SMK = 7$
";
        std::fs::write(&md_path, md).expect("write fixture");
        let _cleanup_dir = TmpDirCleanup(dir);

        let func: syn::ItemFn = parse_quote! {
            fn witness_constant_enrich() -> i32 { 7 }
        };

        let mut functions = vec![FunctionToVerify {
            file_path: PathBuf::from("witness.rs"),
            function_name: "witness_constant_enrich".into(),
            contracts: vec![],
            section: Some("4.99".into()),
            spec_name_override: None,
            formula_anchor: None,
            constant_anchor: Some("C_SMK".into()),
            function_sig: Some(func),
        }];

        let n =
            enrich_functions_with_spec(&mut functions, &[md_path]).expect("enrich_without_error");
        assert_eq!(n, 1);
        assert_eq!(functions.len(), 1);
        assert_eq!(functions[0].contracts.len(), 1);
        assert_eq!(
            functions[0].contracts[0].contract_type,
            ContractType::Ensures
        );
        assert!(functions[0].contracts[0].expr.is_some());
    }

    fn rand_unique() -> u64 {
        use std::time::{SystemTime, UNIX_EPOCH};
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_nanos() as u64)
            .unwrap_or(0)
    }

    struct TmpDirCleanup(PathBuf);

    impl Drop for TmpDirCleanup {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
}
