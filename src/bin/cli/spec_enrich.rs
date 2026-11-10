//! Enrich spec-locked functions with contracts from the Orange Paper.

use super::verify::{Contract, ContractType, FunctionToVerify};
use crate::parser::condition;
use crate::parser::orange_paper::{
    ContractType as SpecContractType, SpecParser, section_id_subsumes_formula_section,
};
use std::path::PathBuf;

/// The section's only named function, else the same rule on parent sections.
///
/// A section with several named functions does not lend its first function to
/// an unmatched name. A section with no named function climbs to its parent.
fn sole_named_in_section_or_parents<'a>(
    parser: &'a SpecParser,
    section: &str,
) -> Option<&'a crate::parser::orange_paper::FunctionSpec> {
    let mut s = section;
    loop {
        let named: Vec<_> = parser
            .get_section_functions(s)
            .into_iter()
            .filter(|f| f.name != "*")
            .collect();
        if named.len() == 1 {
            return Some(named[0]);
        }
        if named.len() > 1 {
            return None;
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
                    for assumption in crate::parser::spec_expr::when_assumptions(&fspec.trailing) {
                        if func.contracts.iter().any(|c| c.condition == assumption) {
                            continue;
                        }
                        let Ok(expr) = syn::parse_str::<syn::Expr>(&assumption) else {
                            continue;
                        };
                        func.contracts.push(Contract {
                            contract_type: ContractType::Requires,
                            condition: assumption,
                            expr: Some(expr),
                            is_spec_derived: true,
                        });
                    }

                    if (!spec_formula_pushed || spec_trivially_true) && !manual_ensures.is_empty() {
                        // Dedup: skip manual contracts whose condition is already present.
                        for m in manual_ensures {
                            if !func.contracts.iter().any(|e| e.condition == m.condition) {
                                func.contracts.push(m);
                            }
                        }
                    } else if !spec_formula_pushed && manual_ensures.is_empty() {
                        // The formula was found and nothing in it parsed.
                        func.parse_gap = true;
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

        let named = parser
            .find_function(section_ref, Some(&spec_name))
            .or_else(|| parser.find_function_anywhere(&spec_name).map(|(f, _)| f));
        // An explicit spec name that is not in the spec must not inherit another
        // function. An omitted name still uses the section's only named function.
        let spec_func = if named.is_some() {
            named
        } else if func.spec_name_override.is_some() {
            None
        } else {
            sole_named_in_section_or_parents(&parser, section_ref)
        };
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
                // Fall back to the originally found function so a section
                // with no formal properties stays a gap rather than a drop.
                parser.find_function(section_ref, Some("*")).unwrap_or(f)
            } else {
                f
            }
        });

        if let Some(spec_func) = spec_func {
            if spec_func.contracts.is_empty() {
                // The section exists and has no formal Properties. A manual
                // ensures stays. Otherwise this is a gap: no `ensures(true)`.
                let has_manual_ensures = func
                    .contracts
                    .iter()
                    .any(|c| c.contract_type == ContractType::Ensures && !c.is_spec_derived);
                if !has_manual_ensures {
                    func.parse_gap = true;
                }
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
                    if let Some(parsed) = crate::parser::formula::parse_sentence(&condition) {
                        func.formulas.push(parsed);
                    }
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
                            if let Some(parsed) = crate::parser::formula::parse_sentence(&condition)
                            {
                                func.formulas.push(parsed);
                            }
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
                // Properties were found and none parsed. Partial, not `ensures(true)`.
                func.parse_gap = true;
            }
        }

        // Leave an empty list only when the function was not found in the spec.
        // An empty list there is "missing from spec". A found section with no
        // parseable property is handled above.
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
            formulas: Vec::new(),
            function_sig: Some(func),
            parse_gap: false,
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
            formulas: Vec::new(),
            function_sig: Some(func),
            parse_gap: false,
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

    fn gap_fn(name: &str, section: &str) -> FunctionToVerify {
        let func: syn::ItemFn = parse_quote! {
            fn gap() -> i64 { 0 }
        };
        FunctionToVerify {
            file_path: PathBuf::from("witness.rs"),
            function_name: name.into(),
            contracts: vec![],
            section: Some(section.into()),
            spec_name_override: Some(name.into()),
            formula_anchor: None,
            constant_anchor: None,
            formulas: Vec::new(),
            function_sig: Some(func),
            parse_gap: false,
        }
    }

    #[test]
    fn empty_section_is_a_gap_not_true() {
        let dir = std::env::temp_dir().join(format!(
            "spec_lock_empty_section_{}_{}",
            std::process::id(),
            rand_unique()
        ));
        std::fs::create_dir_all(&dir).expect("tmpdir");
        let md_path = dir.join("empty.md");
        std::fs::write(&md_path, "## 99.92 Gap\n\n**GapFunc**: $h \\to r$\n")
            .expect("write fixture");
        let _cleanup_dir = TmpDirCleanup(dir);
        let mut functions = vec![gap_fn("GapFunc", "99.92")];
        let n = enrich_functions_with_spec(&mut functions, &[md_path]).expect("enrich");
        assert_eq!(n, 0);
        assert!(functions[0].parse_gap);
        assert!(functions[0].contracts.is_empty());
    }

    #[test]
    fn unparsed_property_is_a_gap_not_true() {
        let dir = std::env::temp_dir().join(format!(
            "spec_lock_prose_section_{}_{}",
            std::process::id(),
            rand_unique()
        ));
        std::fs::create_dir_all(&dir).expect("tmpdir");
        let md_path = dir.join("prose.md");
        std::fs::write(
            &md_path,
            "## 99.93 Prose\n\n**ProseFunc**: $h \\to r$\n\n**Properties**:\n- DER: enforces strict DER encoding\n",
        )
        .expect("write fixture");
        let _cleanup_dir = TmpDirCleanup(dir);
        let mut functions = vec![gap_fn("ProseFunc", "99.93")];
        let n = enrich_functions_with_spec(&mut functions, &[md_path]).expect("enrich");
        assert_eq!(n, 0);
        assert!(functions[0].parse_gap);
        assert!(
            functions[0]
                .contracts
                .iter()
                .all(|c| c.condition.trim() != "true")
        );
    }

    #[test]
    fn literal_true_property_stays_a_contract() {
        let dir = std::env::temp_dir().join(format!(
            "spec_lock_literal_true_{}_{}",
            std::process::id(),
            rand_unique()
        ));
        std::fs::create_dir_all(&dir).expect("tmpdir");
        let md_path = dir.join("literal.md");
        std::fs::write(
            &md_path,
            "## 99.94 Literal\n\n**TrueFunc**: $h \\to r$\n\n**Properties**:\n- Holds: $true$\n",
        )
        .expect("write fixture");
        let _cleanup_dir = TmpDirCleanup(dir);
        let mut functions = vec![gap_fn("TrueFunc", "99.94")];
        let n = enrich_functions_with_spec(&mut functions, &[md_path]).expect("enrich");
        assert_eq!(n, 1);
        assert!(!functions[0].parse_gap);
        assert_eq!(functions[0].contracts[0].condition.trim(), "true");
    }

    #[test]
    fn empty_section_keeps_manual_ensures() {
        let dir = std::env::temp_dir().join(format!(
            "spec_lock_manual_keep_{}_{}",
            std::process::id(),
            rand_unique()
        ));
        std::fs::create_dir_all(&dir).expect("tmpdir");
        let md_path = dir.join("manual.md");
        std::fs::write(&md_path, "## 99.95 Manual\n\n**ManualFunc**: $h \\to r$\n")
            .expect("write fixture");
        let _cleanup_dir = TmpDirCleanup(dir);
        let mut function = gap_fn("ManualFunc", "99.95");
        function.contracts.push(Contract {
            contract_type: ContractType::Ensures,
            condition: "result >= 0".into(),
            expr: syn::parse_str("result >= 0").ok(),
            is_spec_derived: false,
        });
        let mut functions = vec![function];
        let n = enrich_functions_with_spec(&mut functions, &[md_path]).expect("enrich");
        assert_eq!(n, 0);
        assert!(!functions[0].parse_gap);
        assert_eq!(functions[0].contracts.len(), 1);
        assert_eq!(functions[0].contracts[0].condition, "result >= 0");
    }

    #[test]
    fn unmatched_name_does_not_take_the_first_of_several_functions() {
        let dir = std::env::temp_dir().join(format!(
            "spec_lock_multi_unmatched_{}_{}",
            std::process::id(),
            rand_unique()
        ));
        std::fs::create_dir_all(&dir).expect("tmpdir");
        let md_path = dir.join("multi.md");
        std::fs::write(
            &md_path,
            "## 99.96 Several\n\n**GetBlockSubsidy**: $h \\to r$\n\n**Properties**:\n- Non-negative: $result \\geq 0$\n\n**OtherFunc**: $h \\to r$\n\n**Properties**:\n- Exact: $result = 7$\n",
        )
        .expect("write fixture");
        let _cleanup_dir = TmpDirCleanup(dir);
        let mut functions = vec![gap_fn("NotInTheSpec", "99.96"), gap_fn("OtherFunc", "99.96")];
        let n = enrich_functions_with_spec(&mut functions, &[md_path]).expect("enrich");
        assert_eq!(n, 1);
        assert!(functions[0].contracts.is_empty());
        assert!(!functions[0].parse_gap);
        assert_eq!(functions[1].contracts.len(), 1);
        assert!(functions[1].contracts[0].condition.replace(' ', "").contains("result==7"));
    }

    #[test]
    fn unmatched_name_uses_the_only_function_in_the_section() {
        let dir = std::env::temp_dir().join(format!(
            "spec_lock_sole_unmatched_{}_{}",
            std::process::id(),
            rand_unique()
        ));
        std::fs::create_dir_all(&dir).expect("tmpdir");
        let md_path = dir.join("sole.md");
        std::fs::write(
            &md_path,
            "## 99.97 Sole\n\n**OnlyFunc**: $h \\to r$\n\n**Properties**:\n- Non-negative: $result \\geq 0$\n",
        )
        .expect("write fixture");
        let _cleanup_dir = TmpDirCleanup(dir);
        let mut only = gap_fn("not_the_only_name", "99.97");
        only.spec_name_override = None;
        let mut functions = vec![only];
        let n = enrich_functions_with_spec(&mut functions, &[md_path]).expect("enrich");
        assert_eq!(n, 1);
        assert_eq!(functions[0].contracts.len(), 1);
        assert!(
            functions[0].contracts[0]
                .condition
                .replace(' ', "")
                .contains("result>=0")
        );
    }

    #[test]
    fn explicit_missing_name_does_not_take_the_only_function() {
        let dir = std::env::temp_dir().join(format!(
            "spec_lock_explicit_miss_{}_{}",
            std::process::id(),
            rand_unique()
        ));
        std::fs::create_dir_all(&dir).expect("tmpdir");
        let md_path = dir.join("sole.md");
        std::fs::write(
            &md_path,
            "## 99.97b Explicit\n\n**OnlyFunc**: $h \\to r$\n\n**Properties**:\n- Non-negative: $result \\geq 0$\n",
        )
        .expect("write fixture");
        let _cleanup_dir = TmpDirCleanup(dir);
        let mut functions = vec![gap_fn("IsP2SH", "99.97b")];
        let n = enrich_functions_with_spec(&mut functions, &[md_path]).expect("enrich");
        assert_eq!(n, 0);
        assert!(functions[0].contracts.is_empty());
    }

    #[test]
    fn properties_heading_does_not_swallow_the_next_function() {
        let dir = std::env::temp_dir().join(format!(
            "spec_lock_swallow_{}_{}",
            std::process::id(),
            rand_unique()
        ));
        std::fs::create_dir_all(&dir).expect("tmpdir");
        let md_path = dir.join("swallow.md");
        std::fs::write(
            &md_path,
            "## 99.98 Swallow\n\n**FirstFunc**: $h \\to r$\n\n**Properties**:\n- Note: no dollar here\n\n**SecondFunc**: $h \\to r$\n\n**Properties**:\n- Exact: $result = 7$\n",
        )
        .expect("write fixture");
        let _cleanup_dir = TmpDirCleanup(dir);
        let mut functions = vec![gap_fn("SecondFunc", "99.98")];
        let n = enrich_functions_with_spec(&mut functions, &[md_path]).expect("enrich");
        assert_eq!(n, 1);
        assert_eq!(functions[0].contracts.len(), 1);
        assert!(
            functions[0].contracts[0]
                .condition
                .replace(' ', "")
                .contains("result==7")
        );
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
