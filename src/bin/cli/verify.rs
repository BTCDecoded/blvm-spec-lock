//! Verification orchestration
//!
//! Discovers functions, extracts contracts, and runs verification

use std::cell::RefCell;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;
use syn::{Attribute, File, ImplItem, ImplItemFn, ItemFn};

/// Convert ImplItemFn to ItemFn so Z3 can translate the function body.
/// Enables implementation validation for impl-block methods.
fn impl_item_fn_to_item_fn(impl_fn: &ImplItemFn) -> ItemFn {
    ItemFn {
        attrs: impl_fn.attrs.clone(),
        vis: impl_fn.vis.clone(),
        sig: impl_fn.sig.clone(),
        block: Box::new(impl_fn.block.clone()),
    }
}

/// Simplified contract structure for CLI
#[derive(Debug, Clone)]
pub struct Contract {
    pub contract_type: ContractType,
    pub condition: String,
    pub expr: Option<syn::Expr>, // Parsed expression for static checker
    /// True when this contract was auto-derived from the Orange Paper spec (not manually written).
    /// Spec-derived failures are demoted to Partial (see `demote_if_all_spec_derived`).
    pub is_spec_derived: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ContractType {
    Requires,
    Ensures,
    /// Trusted axiom — asserted as a hard constraint, not verified from the body.
    Axiom,
}

/// Extract contracts from a function
fn extract_contracts(func: &ItemFn) -> Vec<Contract> {
    let mut contracts = Vec::new();

    for attr in &func.attrs {
        let path = attr.path();

        // Also unwrap #[cfg_attr(feature = "...", ensures(...))] and
        // #[cfg_attr(feature = "...", blvm_spec_lock::ensures(...))] so that crates
        // that gate blvm-spec-lock behind a feature flag can still annotate contracts.
        if path.is_ident("cfg_attr") {
            if let Ok(meta) = attr.parse_args_with(
                syn::punctuated::Punctuated::<syn::Meta, syn::Token![,]>::parse_terminated,
            ) {
                // cfg_attr: first item is the cfg predicate, second is the inner attribute.
                if let Some(syn::Meta::List(inner_list)) = meta.iter().nth(1) {
                    let last_ident = inner_list.path.segments.last().map(|s| s.ident.to_string());
                    let contract_kind = match last_ident.as_deref() {
                        Some("ensures") => Some(ContractType::Ensures),
                        Some("requires") => Some(ContractType::Requires),
                        Some("axiom") => Some(ContractType::Axiom),
                        _ => None,
                    };
                    if let Some(kind) = contract_kind {
                        let arg_str = inner_list.tokens.to_string();
                        let expr = syn::parse_str::<syn::Expr>(&arg_str).ok();
                        contracts.push(Contract {
                            contract_type: kind,
                            condition: arg_str,
                            expr,
                            is_spec_derived: false,
                        });
                    }
                }
            }
            continue;
        }

        // Check for #[requires(...)] or #[ensures(...)]
        let is_requires = path.is_ident("requires")
            || (path.segments.len() == 2
                && path.segments[0].ident == "blvm_spec_lock"
                && path.segments[1].ident == "requires");

        let is_ensures = path.is_ident("ensures")
            || (path.segments.len() == 2
                && path.segments[0].ident == "blvm_spec_lock"
                && path.segments[1].ident == "ensures");

        let is_axiom = path.is_ident("axiom")
            || (path.segments.len() == 2
                && path.segments[0].ident == "blvm_spec_lock"
                && path.segments[1].ident == "axiom");

        if is_requires || is_ensures || is_axiom {
            let kind = if is_requires {
                ContractType::Requires
            } else if is_ensures {
                ContractType::Ensures
            } else {
                ContractType::Axiom
            };
            if let Ok(expr) = attr.parse_args::<syn::Expr>() {
                let condition_str = quote::quote!(#expr).to_string();
                contracts.push(Contract {
                    contract_type: kind,
                    condition: condition_str,
                    expr: Some(expr),
                    is_spec_derived: false,
                });
            } else {
                let condition_str = quote::quote!(#attr).to_string();
                contracts.push(Contract {
                    contract_type: kind,
                    condition: condition_str,
                    expr: None,
                    is_spec_derived: false,
                });
            }
        }
    }

    contracts
}

/// A function to verify
#[derive(Debug, Clone)]
pub struct FunctionToVerify {
    pub file_path: PathBuf,
    pub function_name: String,
    pub contracts: Vec<Contract>,
    pub section: Option<String>,
    /// Explicit spec function name from the second argument of `#[spec_locked("X.Y", "SpecName")]`.
    /// When set, used directly for spec lookup instead of the rust-to-pascal-case conversion.
    pub spec_name_override: Option<String>,
    /// When **`Some`**, **`#[spec_locked]`** named a **`F_*`** id (positional, combined, or `function =`).
    pub formula_anchor: Option<String>,
    /// When **`Some`**, **`#[spec_locked]`** named a **`C_*`** consensus-constant stable id (**`constants_stable_id_map`**).
    pub constant_anchor: Option<String>,
    /// Sentences the Z3 contract list does not take (forall, implication, sum).
    pub formulas: Vec<crate::parser::formula::Formula>,
    pub function_sig: Option<syn::ItemFn>, // Store function signature for type inference
    /// The spec section was found and contributed no parseable ensures.
    /// Verify records Partial. An empty contract list without this flag is NoContracts.
    pub parse_gap: bool,
}

/// A proven postcondition from a callee function, injected as a Z3 axiom when verifying callers.
///
/// The `condition` is the raw Rust-expression string of the postcondition (e.g. `"result >= 0"`,
/// `"result <= INITIAL_SUBSIDY"`).  When verifying a wrapper that delegates to `function_name`,
/// the verifier substitutes `result` with `call_{function_name}_result` in the condition and
/// asserts the resulting Z3 formula as an axiom — propagating the proven callee bound to the
/// caller without requiring body translation of the callee itself.
#[derive(Debug, Clone)]
pub struct CalleePostcond {
    pub function_name: String,
    pub condition: String,
}

/// Recursively collect all `.rs` files under `dir`, skipping `target/`, `.git/`, `.cargo/`.
fn collect_rs_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let path_str = path.to_string_lossy();
        if path_str.contains("/target/")
            || path_str.contains("/.git/")
            || path_str.contains("/.cargo/")
        {
            continue;
        }
        if path.is_dir() {
            collect_rs_files(&path, out);
        } else if path.extension().and_then(|s| s.to_str()) == Some("rs") {
            out.push(path);
        }
    }
}

/// Discover all functions with #[spec_locked] attributes
pub fn discover_functions(workspace_root: &Path) -> Result<Vec<FunctionToVerify>, String> {
    let mut functions = Vec::new();
    let mut errors = Vec::new();

    let mut rs_files = Vec::new();
    collect_rs_files(workspace_root, &mut rs_files);

    for path in &rs_files {
        // Only process .rs files
        if path.extension().and_then(|s| s.to_str()) == Some("rs") {
            match parse_file_for_functions(path) {
                Ok(mut file_functions) => {
                    functions.append(&mut file_functions);
                }
                Err(e) => {
                    // Collect errors but continue processing
                    errors.push(format!("{}: {}", path.display(), e));
                }
            }
        }
    }

    // If we have functions, return them even if there were some errors
    // (errors might be from files that don't have spec_locked functions)
    if !functions.is_empty() || errors.is_empty() {
        Ok(functions)
    } else {
        Err(format!(
            "Failed to discover functions:\n{}",
            errors.join("\n")
        ))
    }
}

/// Parse a Rust file for functions with #[spec_locked]
fn parse_file_for_functions(file_path: &std::path::Path) -> Result<Vec<FunctionToVerify>, String> {
    let content = std::fs::read_to_string(file_path)
        .map_err(|e| format!("Failed to read {}: {}", file_path.display(), e))?;

    let ast: File = syn::parse_file(&content)
        .map_err(|e| format!("Failed to parse {}: {}", file_path.display(), e))?;

    let mut functions = Vec::new();

    for item in ast.items {
        match item {
            syn::Item::Fn(func) if has_spec_locked(&func.attrs) => {
                functions.push(make_function_to_verify(
                    file_path,
                    &func.sig.ident.to_string(),
                    &func.attrs,
                    &func,
                ));
            }
            syn::Item::Impl(impl_item) => {
                for assoc_item in &impl_item.items {
                    if let ImplItem::Fn(impl_fn) = assoc_item {
                        if has_spec_locked(&impl_fn.attrs) {
                            if std::env::var("SPEC_LOCK_DEBUG_ATTR_PARSE").is_ok() {
                                eprintln!(
                                    "IMPL_FN: {} has {} attrs",
                                    impl_fn.sig.ident,
                                    impl_fn.attrs.len()
                                );
                            }
                            let contracts = extract_contracts_from_attrs(&impl_fn.attrs);
                            let section = extract_section(&impl_fn.attrs);
                            let item_fn = impl_item_fn_to_item_fn(impl_fn);
                            functions.push(FunctionToVerify {
                                file_path: file_path.to_path_buf(),
                                function_name: impl_fn.sig.ident.to_string(),
                                contracts,
                                section,
                                spec_name_override: extract_spec_name_override(&impl_fn.attrs),
                                formula_anchor: extract_formula_anchor(&impl_fn.attrs),
                                constant_anchor: extract_constant_anchor(&impl_fn.attrs),
                                formulas: Vec::new(),
                                function_sig: Some(item_fn),
                                parse_gap: false,
                            });
                        }
                    }
                }
            }
            _ => {}
        }
    }

    Ok(functions)
}

fn make_function_to_verify(
    file_path: &std::path::Path,
    function_name: &str,
    attrs: &[Attribute],
    func: &ItemFn,
) -> FunctionToVerify {
    let contracts = extract_contracts(func);
    let section = extract_section(attrs);
    FunctionToVerify {
        file_path: file_path.to_path_buf(),
        function_name: function_name.to_string(),
        contracts,
        section,
        spec_name_override: extract_spec_name_override(attrs),
        formula_anchor: extract_formula_anchor(attrs),
        constant_anchor: extract_constant_anchor(attrs),
        formulas: Vec::new(),
        function_sig: Some(func.clone()),
        parse_gap: false,
    }
}

/// Extract contracts from attributes (used for impl methods which use ImplItemFn)
fn extract_contracts_from_attrs(attrs: &[Attribute]) -> Vec<Contract> {
    let mut contracts = Vec::new();
    for attr in attrs {
        let path = attr.path();
        if std::env::var("SPEC_LOCK_DEBUG_ATTR_PARSE").is_ok() {
            let segs: Vec<String> = path.segments.iter().map(|s| s.ident.to_string()).collect();
            let is_ens_check = path.segments.len() == 2
                && path.segments[0].ident == "blvm_spec_lock"
                && path.segments[1].ident == "ensures";
            eprintln!(
                "ATTR_PARSE: path_segs={:?} is_ident_ensures={} 2seg_check={}",
                segs,
                path.is_ident("ensures"),
                is_ens_check
            );
        }

        // Unwrap #[cfg_attr(feature = "...", ensures(...))] and
        // #[cfg_attr(feature = "...", blvm_spec_lock::ensures(...))] so that crates
        // that gate blvm-spec-lock behind a feature flag can still annotate contracts.
        if path.is_ident("cfg_attr") {
            if let Ok(meta) = attr.parse_args_with(
                syn::punctuated::Punctuated::<syn::Meta, syn::Token![,]>::parse_terminated,
            ) {
                if let Some(syn::Meta::List(inner_list)) = meta.iter().nth(1) {
                    let last_ident = inner_list.path.segments.last().map(|s| s.ident.to_string());
                    let contract_kind = match last_ident.as_deref() {
                        Some("ensures") => Some(ContractType::Ensures),
                        Some("requires") => Some(ContractType::Requires),
                        Some("axiom") => Some(ContractType::Axiom),
                        _ => None,
                    };
                    if let Some(kind) = contract_kind {
                        let arg_str = inner_list.tokens.to_string();
                        let expr = syn::parse_str::<syn::Expr>(&arg_str).ok();
                        contracts.push(Contract {
                            contract_type: kind,
                            condition: arg_str,
                            expr,
                            is_spec_derived: false,
                        });
                    }
                }
            }
            continue;
        }

        let is_requires = path.is_ident("requires")
            || (path.segments.len() == 2
                && path.segments[0].ident == "blvm_spec_lock"
                && path.segments[1].ident == "requires");
        let is_ensures = path.is_ident("ensures")
            || (path.segments.len() == 2
                && path.segments[0].ident == "blvm_spec_lock"
                && path.segments[1].ident == "ensures");
        let is_axiom = path.is_ident("axiom")
            || (path.segments.len() == 2
                && path.segments[0].ident == "blvm_spec_lock"
                && path.segments[1].ident == "axiom");
        if is_requires || is_ensures || is_axiom {
            let kind = if is_requires {
                ContractType::Requires
            } else if is_ensures {
                ContractType::Ensures
            } else {
                ContractType::Axiom
            };
            if let Ok(expr) = attr.parse_args::<syn::Expr>() {
                contracts.push(Contract {
                    contract_type: kind,
                    condition: quote::quote!(#expr).to_string(),
                    expr: Some(expr),
                    is_spec_derived: false,
                });
            } else {
                contracts.push(Contract {
                    contract_type: kind,
                    condition: quote::quote!(#attr).to_string(),
                    expr: None,
                    is_spec_derived: false,
                });
            }
        }
    }
    contracts
}

/// Check if function has #[spec_locked] attribute (including inside #[cfg_attr(...)])
fn has_spec_locked(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|attr| {
        let path = attr.path();
        if path.is_ident("spec_locked")
            || (path.segments.len() == 2
                && path.segments[0].ident == "blvm_spec_lock"
                && path.segments[1].ident == "spec_locked")
        {
            return true;
        }
        // cfg_attr(feature = "...", spec_locked("10.1"))
        if path.is_ident("cfg_attr") {
            let tokens = quote::quote!(#attr).to_string();
            return tokens.contains("spec_locked");
        }
        false
    })
}

/// Second literal anchored to **`F_*`** or **`C_*`** (`spec_locked("§", "F_x"|"C_x")`, `§::Id`, **`function = "…"`**, **`cfg_attr`** nests).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SecondarySpecAnchor {
    Formula(String),
    Constant(String),
}

fn classify_secondary_anchor(id: &str) -> Option<SecondarySpecAnchor> {
    if id.starts_with("F_")
        && id.len() > 2
        && id[2..]
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '_')
    {
        return Some(SecondarySpecAnchor::Formula(id.to_string()));
    }
    if id.starts_with("C_")
        && id.len() > 2
        && id[2..]
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '_')
    {
        return Some(SecondarySpecAnchor::Constant(id.to_string()));
    }
    None
}

/// Extract **`F_*`** / **`C_*`** second anchor from **`#[spec_locked]`** / **`cfg_attr`**.
pub fn extract_secondary_spec_anchor(attrs: &[Attribute]) -> Option<SecondarySpecAnchor> {
    static RE_NAMED: OnceLock<regex::Regex> = OnceLock::new();
    static RE_COMBO: OnceLock<regex::Regex> = OnceLock::new();
    static RE_DUAL: OnceLock<regex::Regex> = OnceLock::new();

    fn re_named() -> &'static regex::Regex {
        RE_NAMED.get_or_init(|| {
            regex::Regex::new(r#"function\s*=\s*"((?:F_|C_)[A-Za-z0-9_]+)""#)
                .expect("secondary anchor named-regex")
        })
    }

    fn re_combo() -> &'static regex::Regex {
        RE_COMBO.get_or_init(|| {
            regex::Regex::new(
                r#"spec_locked\s*\(\s*"((?:\d+)(?:\.\d+)*)::((?:F_|C_)[A-Za-z0-9_]+)"\s*\)"#,
            )
            .expect("secondary anchor combo regex")
        })
    }

    fn re_dual() -> &'static regex::Regex {
        RE_DUAL.get_or_init(|| {
            regex::Regex::new(r#"spec_locked\s*\(\s*"[^"]*"\s*,\s*"((?:F_|C_)[A-Za-z0-9_]+)""#)
                .expect("secondary anchor dual regex")
        })
    }

    for attr in attrs {
        let path = attr.path();
        let tokens = quote::quote!(#attr).to_string();

        let is_direct = path.is_ident("spec_locked")
            || (path.segments.len() == 2
                && path.segments[0].ident == "blvm_spec_lock"
                && path.segments[1].ident == "spec_locked");

        let is_cfg_nested = path.is_ident("cfg_attr") && tokens.contains("spec_locked");

        if !(is_direct || is_cfg_nested) {
            continue;
        }

        if let Some(c) = re_named().captures(&tokens) {
            if let Some(id) = c.get(1).and_then(|m| classify_secondary_anchor(m.as_str())) {
                return Some(id);
            }
        }
        if let Some(c) = re_combo().captures(&tokens) {
            if let Some(id) = c.get(2).and_then(|m| classify_secondary_anchor(m.as_str())) {
                return Some(id);
            }
        }
        if let Some(c) = re_dual().captures(&tokens) {
            if let Some(id) = c.get(1).and_then(|m| classify_secondary_anchor(m.as_str())) {
                return Some(id);
            }
        }
    }
    None
}

/// Second literal anchored to **`F_*`** (`spec_locked("§", "F_x")`, `spec_locked("§::F_x")`,
/// `function = "F_x"`, **`cfg_attr`** nests included).
pub fn extract_formula_anchor(attrs: &[Attribute]) -> Option<String> {
    match extract_secondary_spec_anchor(attrs) {
        Some(SecondarySpecAnchor::Formula(id)) => Some(id),
        _ => None,
    }
}

/// **`#[spec_locked]`** second literal **`C_*`** (consensus stable id).
pub fn extract_constant_anchor(attrs: &[Attribute]) -> Option<String> {
    match extract_secondary_spec_anchor(attrs) {
        Some(SecondarySpecAnchor::Constant(id)) => Some(id),
        _ => None,
    }
}
/// Extract the explicit spec function name from the second argument of
/// `#[spec_locked("X.Y", "SpecName")]`. Returns `None` when no second string argument is present.
fn extract_spec_name_override(attrs: &[Attribute]) -> Option<String> {
    for attr in attrs {
        let path = attr.path();
        let tokens = quote::quote!(#attr).to_string();
        let is_spec_locked = path.is_ident("spec_locked")
            || (path.segments.len() == 2
                && path.segments[0].ident == "blvm_spec_lock"
                && path.segments[1].ident == "spec_locked")
            || (path.is_ident("cfg_attr") && tokens.contains("spec_locked"));
        if is_spec_locked {
            if let Some(spec_pos) = tokens.find("spec_locked") {
                let after_spec = &tokens[spec_pos..];
                // Find the first quoted argument (section number)
                if let Some(start1) = after_spec.find('"') {
                    if let Some(end1) = after_spec[start1 + 1..].find('"') {
                        // Find the second quoted argument (spec function name)
                        let after_first = &after_spec[start1 + 1 + end1 + 1..];
                        if let Some(start2) = after_first.find('"') {
                            if let Some(end2) = after_first[start2 + 1..].find('"') {
                                let name = &after_first[start2 + 1..start2 + 1 + end2];
                                // Only return if it's a plain function name (not a formula/constant anchor)
                                if !name.starts_with("F_")
                                    && !name.starts_with("C_")
                                    && !name.is_empty()
                                    && name.chars().all(|c| c.is_alphanumeric() || c == '_')
                                {
                                    return Some(name.to_string());
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    None
}

fn extract_section(attrs: &[Attribute]) -> Option<String> {
    for attr in attrs {
        let path = attr.path();
        let tokens = quote::quote!(#attr).to_string();
        let is_spec_locked = path.is_ident("spec_locked")
            || (path.segments.len() == 2
                && path.segments[0].ident == "blvm_spec_lock"
                && path.segments[1].ident == "spec_locked")
            || (path.is_ident("cfg_attr") && tokens.contains("spec_locked"));

        if is_spec_locked {
            // Try to parse the section from the attribute tokens
            // Format: #[spec_locked("6.1")] or #[cfg_attr(feature = "x", spec_locked("10.1"))]
            // Look for spec_locked("X.Y") pattern - section numbers after spec_locked
            if let Some(spec_pos) = tokens.find("spec_locked") {
                let after_spec = &tokens[spec_pos..];
                if let Some(start) = after_spec.find('"') {
                    if let Some(end) = after_spec[start + 1..].find('"') {
                        let section_raw = &after_spec[start + 1..start + 1 + end];
                        if section_raw.chars().any(|c| c.is_ascii_digit()) {
                            let section_normalized = section_raw.split_once("::").map_or_else(
                                || section_raw.to_string(),
                                |(lhs, rhs)| {
                                    if rhs.starts_with("F_") || rhs.starts_with("C_") {
                                        lhs.to_string()
                                    } else {
                                        section_raw.to_string()
                                    }
                                },
                            );
                            return Some(section_normalized);
                        }
                    }
                }
            }
        }
    }
    None
}

/// Verify a single function.
/// Extract the return type from a function signature, unwrapping `-> Result<T>` to `T`.
fn extract_return_type_from_sig(func: &syn::ItemFn) -> Option<syn::Type> {
    let output = match &func.sig.output {
        syn::ReturnType::Default => return None,
        syn::ReturnType::Type(_, ty) => ty.as_ref().clone(),
    };
    // Unwrap Result<T> / Option<T> to the inner type for type-level contract purposes,
    // so that e.g. `-> Result<Hash>` yields the same contract as `-> Hash`.
    if let syn::Type::Path(tp) = &output {
        if let Some(seg) = tp.path.segments.last() {
            if seg.ident == "Result" || seg.ident == "Option" {
                if let syn::PathArguments::AngleBracketed(args) = &seg.arguments {
                    if let Some(syn::GenericArgument::Type(inner)) = args.args.first() {
                        return Some(inner.clone());
                    }
                }
            }
        }
    }
    Some(output)
}

/// `timeout_secs`: Z3 solver timeout in seconds (0 = use default 5s).
#[allow(unused_variables)]
/// Verify a single function's contracts.
///
/// `callee_postconds` — proven postconditions of callee functions (from the same crate).
/// Each entry carries a `(function_name, condition)` pair; when the function body creates
/// a `call_{fn}_result` UF variable, the condition is injected as a Z3 axiom for callers.
pub fn verify_function(
    function: &FunctionToVerify,
    timeout_secs: u64,
    callee_postconds: &[CalleePostcond],
) -> VerificationResult {
    if std::env::var("SPEC_LOCK_DEBUG_CONTRACTS").is_ok() {
        eprintln!(
            "CONTRACTS_DEBUG[{}]: {} contracts",
            function.function_name,
            function.contracts.len()
        );
        for c in &function.contracts {
            eprintln!(
                "  {:?} sd={} cond={:?}",
                c.contract_type, c.is_spec_derived, c.condition
            );
        }
    }
    if function.parse_gap {
        // The section exists. Nothing in it parsed to an ensures. That is a
        // gap, not a pass and not a missing anchor.
        return VerificationResult::Partial {
            verified: 0,
            total: function.contracts.len().max(1),
            reason: Some("spec section has no parseable contract".to_string()),
            partial_reason: Some(PartialReason::UnsupportedTranslation),
        };
    }
    if function.contracts.is_empty() {
        // A missing clause is not a lock. Do not synthesize
        // `result == true || result == false` or `result >= 0` from the type.
        return VerificationResult::NoContracts {
            section: function.section.clone().unwrap_or_else(|| "?".to_string()),
        };
    }

    // Verification flow:
    // 1. Try static checks first (fast, no Z3 needed)
    // 2. If static checks can't verify, use Z3 (if available)
    // 3. Return appropriate result

    let mut verified_count = 0;
    // (contract_type_str, reason, is_spec_derived)
    let mut failed_contracts: Vec<(String, String, bool)> = Vec::new();
    let mut requires_z3_count = 0;
    let translation_error = RefCell::new(None::<String>);
    // True when at least one ensures contract was verified using the function body
    // (i.e. Z3 used body constraints). False means all passes are type-level only.
    let mut any_body_translated = false;

    // Separate requires, ensures, and axiom contracts
    let requires_contracts: Vec<_> = function
        .contracts
        .iter()
        .filter(|c| c.contract_type == ContractType::Requires)
        .collect();
    let ensures_contracts: Vec<_> = function
        .contracts
        .iter()
        .filter(|c| c.contract_type == ContractType::Ensures)
        .collect();
    let axiom_contracts: Vec<_> = function
        .contracts
        .iter()
        .filter(|c| c.contract_type == ContractType::Axiom)
        .collect();

    // Axiom contracts are trusted — count them as verified when their syntax is valid.
    // They are injected as hard constraints when verifying ensures rather than being
    // proved themselves; their correctness is declared by the annotation author.
    for contract in &axiom_contracts {
        if contract.expr.is_some() {
            verified_count += 1;
        } else {
            failed_contracts.push((
                "Axiom".to_string(),
                "Axiom condition could not be parsed".to_string(),
                contract.is_spec_derived,
            ));
        }
    }

    // Validate requires contracts (preconditions, NOT proof obligations).
    //
    // Requires are caller-supplied preconditions.  We validate their syntax but do
    // NOT ask Z3 to prove them always-true: a restrictive precondition like
    // `height >= HALVING_INTERVAL * 64` is intentionally not a tautology — that is
    // by design.  Z3 would trivially find a SAT counterexample (height=0) and
    // classify the result as Unknown/Failed, which is wrong.
    //
    // Requires are used as ASSUMPTIONS when verifying Ensures contracts below.
    for contract in &requires_contracts {
        if contract.condition.trim().is_empty() {
            failed_contracts.push((
                format!("{:?}", contract.contract_type),
                "Empty contract condition".to_string(),
                contract.is_spec_derived,
            ));
            continue;
        }
        // Syntactic validity: a parseable expression counts as verified.
        if contract.expr.is_some() {
            verified_count += 1;
        } else {
            failed_contracts.push((
                format!("{:?}", contract.contract_type),
                "Cannot verify: contract condition could not be parsed as expression".to_string(),
                contract.is_spec_derived,
            ));
        }
    }

    // Early return if requires contracts failed.
    if let Some(result) =
        demote_if_all_spec_derived(&failed_contracts, verified_count, function.contracts.len())
    {
        return result;
    }
    if !failed_contracts.is_empty() {
        let (contract_type, reason, _) = &failed_contracts[0];
        return failed_verification(contract_type, reason, failed_contracts.len());
    }

    // Now verify ensures contracts with the requires as context
    // We prove: requires && implementation => ensures
    for contract in &ensures_contracts {
        if contract.condition.trim().is_empty() {
            failed_contracts.push((
                format!("{:?}", contract.contract_type),
                "Empty contract condition".to_string(),
                contract.is_spec_derived,
            ));
            continue;
        }

        if crate::parser::condition::is_result_equality(&contract.condition) {
            #[cfg(feature = "z3")]
            {
                if let Some(ref func) = function.function_sig {
                    requires_z3_count += 1;
                    match verify_determinism(func, &requires_contracts, timeout_secs) {
                        Ok(()) => {
                            verified_count += 1;
                            any_body_translated = true;
                        }
                        Err(e) => {
                            failed_contracts.push((
                                format!("{:?}", contract.contract_type),
                                format!("Determinism: {e}"),
                                contract.is_spec_derived,
                            ));
                        }
                    }
                } else {
                    requires_z3_count += 1;
                    failed_contracts.push((
                        format!("{:?}", contract.contract_type),
                        "Determinism requires function signature".to_string(),
                        contract.is_spec_derived,
                    ));
                }
            }
            #[cfg(not(feature = "z3"))]
            {
                failed_contracts.push((
                    format!("{:?}", contract.contract_type),
                    "Z3 required for determinism verification. Build blvm-spec-lock with --features z3.".to_string(),
                    contract.is_spec_derived,
                ));
            }
            continue;
        }

        if let Some(ref expr) = contract.expr {
            match check_contract_statically(
                expr,
                contract.contract_type,
                function.function_sig.as_ref(),
            ) {
                StaticCheck::Passed => {
                    verified_count += 1;
                }
                StaticCheck::Failed(reason) => {
                    failed_contracts.push((
                        format!("{:?}", contract.contract_type),
                        reason,
                        contract.is_spec_derived,
                    ));
                }
                StaticCheck::RequiresZ3 => {
                    requires_z3_count += 1;
                    #[cfg(feature = "z3")]
                    {
                        match verify_with_z3(
                            contract,
                            function.function_sig.as_ref(),
                            &requires_contracts,
                            &axiom_contracts,
                            timeout_secs,
                            callee_postconds,
                        ) {
                            Err(e) => {
                                failed_contracts.push((
                                    format!("{:?}", contract.contract_type),
                                    format!("Z3: {e}"),
                                    contract.is_spec_derived,
                                ));
                            }
                            Ok(body_translated) => {
                                verified_count += 1;
                                if body_translated {
                                    any_body_translated = true;
                                }
                            }
                        }
                    }
                    #[cfg(not(feature = "z3"))]
                    {
                        failed_contracts.push((
                            format!("{:?}", contract.contract_type),
                            "Z3 required but not built. Build blvm-spec-lock with --features z3."
                                .to_string(),
                            contract.is_spec_derived,
                        ));
                    }
                }
            }
        } else {
            requires_z3_count += 1;
            failed_contracts.push((
                format!("{:?}", contract.contract_type),
                "Cannot verify: contract condition could not be parsed".to_string(),
                contract.is_spec_derived,
            ));
        }
    }

    // Report results.
    if let Some(result) =
        demote_if_all_spec_derived(&failed_contracts, verified_count, function.contracts.len())
    {
        return result;
    }
    if !failed_contracts.is_empty() {
        let (contract_type, reason, _) = &failed_contracts[0];
        return failed_verification(contract_type, reason, failed_contracts.len());
    }

    if verified_count == function.contracts.len() {
        VerificationResult::Passed {
            body_translated: any_body_translated,
        }
    } else if requires_z3_count > 0 {
        let trans_err = translation_error.into_inner();
        let reason_msg = format!(
            "Z3 verification required but unavailable or incomplete ({} of {} verified). {}",
            verified_count,
            function.contracts.len(),
            trans_err
                .as_deref()
                .unwrap_or("Build with --features z3 for full verification.")
        );
        #[cfg(not(feature = "z3"))]
        let partial_reason = PartialReason::MissingZ3Build;
        #[cfg(feature = "z3")]
        let partial_reason = if trans_err.is_some() {
            PartialReason::UnsupportedTranslation
        } else {
            PartialReason::IncompleteCoverage
        };
        VerificationResult::Partial {
            verified: verified_count,
            total: function.contracts.len(),
            reason: Some(reason_msg),
            partial_reason: Some(partial_reason),
        }
    } else {
        VerificationResult::Passed {
            body_translated: any_body_translated,
        }
    }
}

/// Result of static checking
enum StaticCheck {
    Passed,
    Failed(String),
    RequiresZ3,
}

/// Check a contract statically (simplified version for CLI)
fn check_contract_statically(
    expr: &syn::Expr,
    _contract_type: ContractType,
    func_sig: Option<&syn::ItemFn>,
) -> StaticCheck {
    // ── Tautology fast-paths (no Z3 needed) ──────────────────────────────
    //
    // 0. Literal `true`: spec-derived conditions that reduce to `"true"` via
    //    extract_parseable_condition (e.g. determinism annotations, noise phrases).
    //    The negation is `false` (UNSAT trivially); skip Z3 entirely.
    if let syn::Expr::Lit(lit) = expr {
        if let syn::Lit::Bool(b) = &lit.lit {
            if b.value {
                return StaticCheck::Passed;
            }
        }
    }
    //
    // 1. Bool-exhaustion: `X == true || X == false` (or reverse operand order).
    //    By the law of excluded middle this is always true for boolean X.
    //    These contracts appear on spec-locked functions returning `bool`,
    //    `ValidationResult`, `MempoolResult`, etc., and on many wrapper fns in
    //    lib.rs.  Z3 models `result` as Int when the body can't be translated
    //    (e.g. complex struct returns), so it trivially finds SAT for the negation
    //    (`result == 2`) and emits PARTIAL.  We bypass Z3 entirely.
    if is_bool_exhaustion_tautology(expr) {
        return StaticCheck::Passed;
    }

    // 2. Non-negative for unsigned return types: `result >= 0` / `result_N >= 0`.
    //    Only safe when the function returns an unsigned primitive (u8..usize,
    //    Natural) or a type that maps to a non-negative Z3 Int (opaque structs,
    //    Hash, Block, etc.).  We use the same `is_unsigned_type` logic as the
    //    Z3 translator.
    if let Some(func) = func_sig {
        if is_nonneg_tautology_for_return_type(expr, func) {
            return StaticCheck::Passed;
        }
    }

    // ── Fall-through: simple pattern matching ────────────────────────────
    match expr {
        // Non-negative checks: x >= 0 or 0 <= x
        syn::Expr::Binary(bin) if matches!(bin.op, syn::BinOp::Ge(_)) => {
            if is_zero_literal(&bin.right) || is_zero_literal(&bin.left) {
                return StaticCheck::RequiresZ3;
            }
        }
        // Equality checks: x == CONSTANT
        syn::Expr::Binary(bin) if matches!(bin.op, syn::BinOp::Eq(_)) => {
            if is_literal(&bin.left) || is_literal(&bin.right) {
                return StaticCheck::RequiresZ3;
            }
        }
        // Comparison checks: x < y, x > y, etc.
        syn::Expr::Binary(bin)
            if matches!(
                bin.op,
                syn::BinOp::Lt(_) | syn::BinOp::Le(_) | syn::BinOp::Gt(_) | syn::BinOp::Ge(_)
            ) =>
        {
            return StaticCheck::RequiresZ3;
        }
        // Boolean operations: x && y, x || y
        syn::Expr::Binary(bin) if matches!(bin.op, syn::BinOp::And(_) | syn::BinOp::Or(_)) => {
            return StaticCheck::RequiresZ3;
        }
        _ => {
            return StaticCheck::RequiresZ3;
        }
    }

    StaticCheck::RequiresZ3
}

/// Return `true` when `expr` is the bool-exhaustion tautology `X == true || X == false`
/// (or the reverse: `X == false || X == true`).
///
/// The law of excluded middle guarantees this is true for any boolean value.
/// We match it syntactically so Z3 is never needed, regardless of return type.
/// Outer parentheses (as produced by `extract_parseable_condition`) are stripped first.
fn is_bool_exhaustion_tautology(expr: &syn::Expr) -> bool {
    // Strip one level of outer parentheses; extract_parseable_condition wraps with `(...)`.
    let inner = match expr {
        syn::Expr::Paren(p) => p.expr.as_ref(),
        other => other,
    };
    let syn::Expr::Binary(or_bin) = inner else {
        return false;
    };
    if !matches!(or_bin.op, syn::BinOp::Or(_)) {
        return false;
    }
    // Both sides must be equality comparisons.
    let (syn::Expr::Binary(left_eq), syn::Expr::Binary(right_eq)) =
        (or_bin.left.as_ref(), or_bin.right.as_ref())
    else {
        return false;
    };
    if !matches!(left_eq.op, syn::BinOp::Eq(_)) || !matches!(right_eq.op, syn::BinOp::Eq(_)) {
        return false;
    }
    // Identify whether each side checks `== true` or `== false`.
    let left_true = is_bool_true(&left_eq.right) || is_bool_true(&left_eq.left);
    let left_false = is_bool_false(&left_eq.right) || is_bool_false(&left_eq.left);
    let right_true = is_bool_true(&right_eq.right) || is_bool_true(&right_eq.left);
    let right_false = is_bool_false(&right_eq.right) || is_bool_false(&right_eq.left);
    // One arm must test `true`, the other `false`.
    (left_true && right_false) || (left_false && right_true)
}

/// Return `true` if `expr` is `result >= 0` / `result_N >= 0` AND the function's
/// return type (or its Nth tuple element) is known to be non-negative.
fn is_nonneg_tautology_for_return_type(expr: &syn::Expr, func: &syn::ItemFn) -> bool {
    use crate::translator::z3_translator::auto_type_contracts;

    // Only match `X >= 0` / `0 <= X`.
    let syn::Expr::Binary(bin) = expr else {
        return false;
    };
    if !matches!(bin.op, syn::BinOp::Ge(_)) {
        return false;
    }
    let (lhs, _rhs) = if is_zero_literal(&bin.right) {
        (bin.left.as_ref(), bin.right.as_ref())
    } else if is_zero_literal(&bin.left) {
        (bin.right.as_ref(), bin.left.as_ref())
    } else {
        return false;
    };
    // LHS must be `result` or `result_N`.
    let var_name = match lhs {
        syn::Expr::Path(p) => p
            .path
            .get_ident()
            .map(|id| id.to_string())
            .unwrap_or_default(),
        _ => return false,
    };
    if var_name != "result" && !var_name.starts_with("result_") {
        return false;
    }
    // Derive the same contracts the auto-type machinery would generate for this function.
    let return_ty = extract_return_type_from_sig(func);
    let Some(ret) = return_ty else { return false };
    let type_contracts = auto_type_contracts(&ret);
    // If `var_name >= 0` is among the auto-derived contracts, it is a type tautology.
    let needle = format!("{var_name} >= 0");
    type_contracts.iter().any(|c| c.as_str() == needle.as_str())
}

/// Return `true` if `expr` is the `true` boolean literal.
fn is_bool_true(expr: &syn::Expr) -> bool {
    if let syn::Expr::Lit(lit) = expr {
        if let syn::Lit::Bool(b) = &lit.lit {
            return b.value;
        }
    }
    false
}

/// Return `true` if `expr` is the `false` boolean literal.
fn is_bool_false(expr: &syn::Expr) -> bool {
    if let syn::Expr::Lit(lit) = expr {
        if let syn::Lit::Bool(b) = &lit.lit {
            return !b.value;
        }
    }
    false
}

/// Check if expression is a zero literal
fn is_zero_literal(expr: &syn::Expr) -> bool {
    if let syn::Expr::Lit(lit) = expr {
        if let syn::Lit::Int(int_lit) = &lit.lit {
            return int_lit.base10_digits() == "0";
        }
    }
    false
}

/// Check if expression is a literal
fn is_literal(expr: &syn::Expr) -> bool {
    matches!(expr, syn::Expr::Lit(_))
}

/// Verify determinism (two-run Z3: a==b => f(a)==f(b))
#[cfg(feature = "z3")]
fn verify_determinism(
    func: &syn::ItemFn,
    requires_contracts: &[&Contract],
    timeout_secs: u64,
) -> Result<(), String> {
    use crate::parser::contracts::{
        Contract as LibraryContract, ContractType as LibraryContractType,
    };
    use crate::translator::z3_verifier::{VerificationResult, Z3Verifier};

    let timeout_ms = if timeout_secs > 0 {
        timeout_secs * 1000
    } else {
        10000
    };
    let mut verifier = Z3Verifier::new(timeout_ms);

    let requires_library: Vec<_> = requires_contracts
        .iter()
        .filter_map(|c| {
            c.expr.as_ref().map(|expr| LibraryContract {
                contract_type: LibraryContractType::Requires,
                condition: expr.clone(),
                comment: None,
            })
        })
        .collect();

    match verifier.verify_determinism(func, &requires_library) {
        VerificationResult::Verified { .. } => Ok(()),
        VerificationResult::Failed { counterexample } => {
            let msg = if let Some(ce) = counterexample {
                format!("Non-deterministic. Counterexample: {:?}", ce.assignments)
            } else {
                "Non-deterministic (counterexample not extracted)".to_string()
            };
            Err(msg)
        }
        VerificationResult::Unknown { reason } => Err(format!("Z3 unknown: {reason}")),
        VerificationResult::Error { error } => Err(format!("Z3 error: {error}")),
    }
}

/// Verify contract with Z3 (if feature enabled)
#[cfg(feature = "z3")]
/// Returns `Ok(body_translated)` where `body_translated` is `true` when Z3 used
/// the function body in its proof (semantic pass) and `false` when the proof relied
/// only on type-level axioms or preconditions (type-level pass).
///
/// `callee_postconds` — proven postconditions of callee functions; injected as axioms
/// on `call_{fn}_result` variables so wrapper functions can discharge their obligations
/// without body translation.  Named constants such as `INITIAL_SUBSIDY` are resolved
/// by the Z3 translator via `resolve_constant`.
fn verify_with_z3(
    contract: &Contract,
    func_sig: Option<&syn::ItemFn>,
    requires_contracts: &[&Contract],
    axiom_contracts: &[&Contract],
    timeout_secs: u64,
    callee_postconds: &[CalleePostcond],
) -> Result<bool, String> {
    use crate::parser::contracts::{
        Contract as LibraryContract, ContractType as LibraryContractType,
    };
    use crate::translator::z3_verifier::{VerificationResult, Z3Verifier};

    let expr = contract
        .expr
        .as_ref()
        .ok_or_else(|| "Cannot verify: missing parsed expression".to_string())?;

    let library_contract = LibraryContract {
        contract_type: match contract.contract_type {
            ContractType::Requires => LibraryContractType::Requires,
            ContractType::Ensures => LibraryContractType::Ensures,
            ContractType::Axiom => LibraryContractType::Requires,
        },
        condition: expr.clone(),
        comment: None,
    };

    let timeout_ms = if timeout_secs > 0 {
        timeout_secs * 1000
    } else {
        5000
    };
    let mut verifier = Z3Verifier::new(timeout_ms);

    // Combine requires and axiom contracts — both are asserted as assumptions
    // when verifying ensures.  Axioms differ from requires only semantically:
    // requires are caller-supplied preconditions; axioms are trusted properties
    // of the result that the body translator cannot independently derive.
    // An axiom that copies the ensures under check does not prove that ensures.
    let restates_axiom = axiom_contracts
        .iter()
        .any(|c| c.condition.trim() == contract.condition.trim());
    let requires_library: Vec<_> = requires_contracts
        .iter()
        .chain(
            axiom_contracts
                .iter()
                .filter(|c| c.condition.trim() != contract.condition.trim()),
        )
        .filter_map(|c| {
            c.expr.as_ref().map(|expr| LibraryContract {
                contract_type: LibraryContractType::Requires,
                condition: expr.clone(),
                comment: None,
            })
        })
        .collect();

    let callee_refs: Vec<(&str, &str)> = callee_postconds
        .iter()
        .map(|cp| (cp.function_name.as_str(), cp.condition.as_str()))
        .collect();
    match verifier.verify_contract_with_context(
        &library_contract,
        func_sig,
        &requires_library,
        &callee_refs,
    ) {
        VerificationResult::Verified { body_translated } => Ok(body_translated),
        VerificationResult::Failed { counterexample } => {
            let msg = if let Some(ce) = counterexample {
                format!("Contract violated. Counterexample: {:?}", ce.assignments)
            } else {
                "Contract violated (no counterexample available)".to_string()
            };
            Err(restated_axiom_message(restates_axiom, msg))
        }
        VerificationResult::Unknown { reason } => Err(restated_axiom_message(
            restates_axiom,
            format!("Z3 verification unknown: {reason}"),
        )),
        VerificationResult::Error { error } => Err(restated_axiom_message(
            restates_axiom,
            format!("Z3 verification error: {error}"),
        )),
    }
}

#[cfg(feature = "z3")]
fn restated_axiom_message(restates: bool, msg: String) -> String {
    if restates {
        format!("ensures restates an axiom; body did not discharge it: {msg}")
    } else {
        msg
    }
}

#[cfg(not(feature = "z3"))]
fn verify_with_z3(
    _contract: &Contract,
    _func_sig: Option<&syn::ItemFn>,
    _requires: &[&Contract],
    _axioms: &[&Contract],
    _timeout_secs: u64,
    _callee_postconds: &[CalleePostcond],
) -> Result<bool, String> {
    Err("Z3 feature not enabled. Build with --features z3 to enable Z3 verification.".to_string())
}

/// High-level classification for failed verification (JSON **`detail.failure_kind`**).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FailureKind {
    /// Z3 found a satisfying assignment refuting the obligation (or static counterexample path).
    Counterexample,
    /// Contract text did not parse to a Rust expression / unsupported surface syntax.
    ParseError,
    /// Z3 returned **unknown** (including typical timeout wording from the solver wrapper).
    SolverUnknown,
    /// Z3 or translator returned an explicit error (not unknown/sat).
    SolverError,
    /// Build or feature issue (e.g. Z3 feature disabled).
    Tooling,
    /// Everything else (static messages, mixed failures).
    Other,
}

impl FailureKind {
    pub fn as_str(self) -> &'static str {
        match self {
            FailureKind::Counterexample => "counterexample",
            FailureKind::ParseError => "parse_error",
            FailureKind::SolverUnknown => "solver_unknown",
            FailureKind::SolverError => "solver_error",
            FailureKind::Tooling => "tooling",
            FailureKind::Other => "other",
        }
    }
}

/// Why a function is **partial** (JSON **`detail.partial_reason`** when set).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PartialReason {
    /// Wrapper reports Z3 unknown (may include timeout phrasing).
    Z3Unknown,
    /// Z3 **unknown** with timeout-style wording (**`failure_kind`** is still **`solver_unknown`**).
    Z3Timeout,
    /// Body or contract could not be translated to the solver (e.g. unimplemented MIR path).
    UnsupportedTranslation,
    /// Built without `z3` feature but obligations need the solver.
    MissingZ3Build,
    /// Solver available but not all contracts completed (budget / incomplete path).
    IncompleteCoverage,
    /// Z3 counterexample or solver error on an auto-enriched (spec-derived) contract.
    /// Does not block CI exit 0 — LaTeX→Z3 translation is best-effort; manual contracts
    /// with counterexamples still produce **Failed**.
    SpecDerivedCounterexample,
    Other,
}

impl PartialReason {
    pub fn as_str(self) -> &'static str {
        match self {
            PartialReason::Z3Unknown => "z3_unknown",
            PartialReason::Z3Timeout => "z3_timeout",
            PartialReason::UnsupportedTranslation => "unsupported_translation",
            PartialReason::MissingZ3Build => "missing_z3_build",
            PartialReason::IncompleteCoverage => "incomplete_coverage",
            PartialReason::SpecDerivedCounterexample => "spec_derived_counterexample",
            PartialReason::Other => "other",
        }
    }
}

fn solver_unknown_partial_reason(reason: &str) -> PartialReason {
    let r = reason.to_lowercase();
    if r.contains("timeout") || r.contains("timed out") || r.contains("time out") {
        PartialReason::Z3Timeout
    } else {
        PartialReason::Z3Unknown
    }
}

/// When every failure is on a spec-derived (auto-enriched) contract **and** the failure
/// is a LaTeX→Z3 translation gap (could not be parsed), demote to **Partial** so CI is
/// not blocked by approximation limits in the spec parser.
///
/// Z3 counterexamples on spec-derived contracts are **not** demoted — they indicate that
/// the implementation contradicts the enriched contract, which is a real signal regardless
/// of whether the contract was auto-generated. Those remain **Failed** (returns `None`).
fn demote_if_all_spec_derived(
    failed_contracts: &[(String, String, bool)],
    verified_count: usize,
    total: usize,
) -> Option<VerificationResult> {
    if failed_contracts.is_empty() {
        return None;
    }

    // A failure is a translator gap when Z3 cannot produce a concrete counterexample.
    // An untranslated body, an empty assignment map, and a type error in the
    // translator are that gap. A model whose names are all parameters is not.
    let is_translator_gap = |reason: &str| -> bool {
        reason.contains("could not be parsed")
            || reason.contains("Could not translate function body")
            || reason.contains("counterexample model has no named variable assignments")
            || reason.contains("Translation error")
            || reason.contains("ensures restates an axiom")
    };

    let all_gaps = failed_contracts
        .iter()
        .all(|(_, r, _)| is_translator_gap(r));
    if std::env::var("SPEC_LOCK_DEBUG_DEMOTE").is_ok() {
        for (ct, reason, sd) in failed_contracts {
            eprintln!(
                "DEMOTE_DEBUG: ct={ct} sd={sd} gap={} reason_snippet={}",
                is_translator_gap(reason),
                &reason[..reason.len().min(80)]
            );
        }
        eprintln!("DEMOTE_DEBUG: all_gaps={all_gaps}");
    }
    if !all_gaps {
        // At least one failure has a concrete counterexample — keep as Failed.
        // Only demote when every failing contract is also spec-derived (not a manually
        // written contract that we want the developer to see as a real gap).
        let all_spec_derived = failed_contracts.iter().all(|(_, _, sd)| *sd);
        if !all_spec_derived {
            return None;
        }
        // Even if all spec-derived, a concrete counterexample means Z3 proved a real
        // violation — do not demote.
        return None;
    }

    Some(VerificationResult::Partial {
        verified: verified_count,
        total,
        reason: Some(failed_contracts[0].1.clone()),
        partial_reason: Some(PartialReason::UnsupportedTranslation),
    })
}

/// Build **`VerificationResult::Failed`** with optional **`partial_reason`** for **`solver_unknown`** rows.
pub(crate) fn failed_verification(
    contract_type: &str,
    primary_reason: &str,
    failed_contracts_len: usize,
) -> VerificationResult {
    let reason = format!("{primary_reason} ({failed_contracts_len} total failures)");
    let kind = failure_kind(contract_type, &reason);
    let partial_reason = if kind == FailureKind::SolverUnknown {
        Some(solver_unknown_partial_reason(&reason))
    } else {
        None
    };
    VerificationResult::Failed {
        contract: contract_type.to_string(),
        reason,
        kind,
        partial_reason,
    }
}

fn failure_kind(contract_type: &str, reason: &str) -> FailureKind {
    let r = reason.to_lowercase();
    let determinism_z3_unknown = r.contains("determinism")
        && (r.contains("z3 unknown") || r.contains("z3 verification unknown"));
    if r.contains("counterexample")
        || r.contains("contract violated")
        || r.contains("non-deterministic")
        || ((r.contains("determinism") && !r.contains("could not translate"))
            && !determinism_z3_unknown)
    {
        return FailureKind::Counterexample;
    }
    if r.contains("could not be parsed")
        || r.contains("could not parse")
        || r.contains("cannot verify: contract condition could not be parsed")
        || reason.contains("Cannot verify: contract condition could not be parsed as expression")
    {
        return FailureKind::ParseError;
    }
    if r.contains("z3 unknown") || r.contains("z3 verification unknown") {
        return FailureKind::SolverUnknown;
    }
    if r.contains("z3 error") || r.contains("z3 verification error") {
        return FailureKind::SolverError;
    }
    if r.contains("z3 required but not built")
        || r.contains("build blvm-spec-lock with --features z3")
        || r.contains("z3 feature not enabled")
    {
        return FailureKind::Tooling;
    }
    if contract_type == "Z3" && r.contains("unknown") {
        return FailureKind::SolverUnknown;
    }
    FailureKind::Other
}

/// Result of function verification
#[derive(Debug, Clone)]
pub enum VerificationResult {
    /// All contracts verified.
    /// `body_translated` is `true` when at least one ensures contract was proved
    /// using the function body (semantic pass).  `false` means every pass relied
    /// on type-level axioms or preconditions only (type-level pass).
    Passed {
        body_translated: bool,
    },
    Failed {
        contract: String,
        reason: String,
        kind: FailureKind,
        /// When **`kind`** is **`solver_unknown`**: **`z3_unknown`** vs **`z3_timeout`** heuristic from message text (**JSON **`detail.partial_reason`**).
        partial_reason: Option<PartialReason>,
    },
    Partial {
        verified: usize,
        total: usize,
        reason: Option<String>,
        /// When **`Some`**, included in machine JSON under **`detail.partial_reason`**.
        partial_reason: Option<PartialReason>,
    },
    /// No contracts from spec or code - cannot verify (add to Orange Paper or #[requires]/#[ensures])
    NoContracts {
        section: String,
    },
    NotImplemented,
}

#[cfg(test)]
mod spec_locked_anchor_extract_tests {
    use super::{extract_constant_anchor, extract_formula_anchor, extract_section};
    use syn::{ItemFn, parse_quote};

    #[test]
    fn dual_literal_extracts_formula_and_section() {
        let f: ItemFn = parse_quote! {
            #[spec_locked("9.91", "F_X")]
            pub fn dummy() {}
        };
        assert_eq!(extract_formula_anchor(&f.attrs).as_deref(), Some("F_X"));
        assert_eq!(extract_constant_anchor(&f.attrs), None);
        assert_eq!(extract_section(&f.attrs).as_deref(), Some("9.91"));
    }

    #[test]
    fn dual_literal_extracts_constant_and_section() {
        let f: ItemFn = parse_quote! {
            #[spec_locked("4.91", "C_SMK")]
            pub fn dummy() {}
        };
        assert_eq!(extract_formula_anchor(&f.attrs), None);
        assert_eq!(extract_constant_anchor(&f.attrs).as_deref(), Some("C_SMK"));
        assert_eq!(extract_section(&f.attrs).as_deref(), Some("4.91"));
    }

    #[test]
    fn combined_literal_section_and_formula() {
        let f: ItemFn = parse_quote! {
            #[spec_locked("44.44::F_C")]
            pub fn dummy() {}
        };
        assert_eq!(extract_formula_anchor(&f.attrs).as_deref(), Some("F_C"));
        assert_eq!(extract_constant_anchor(&f.attrs), None);
        assert_eq!(extract_section(&f.attrs).as_deref(), Some("44.44"));
    }

    #[test]
    fn combined_literal_section_and_constant() {
        let f: ItemFn = parse_quote! {
            #[spec_locked("44.44::C_K")]
            pub fn dummy() {}
        };
        assert_eq!(extract_formula_anchor(&f.attrs), None);
        assert_eq!(extract_constant_anchor(&f.attrs).as_deref(), Some("C_K"));
        assert_eq!(extract_section(&f.attrs).as_deref(), Some("44.44"));
    }

    #[test]
    fn named_function_param_extracts_formula() {
        let f: ItemFn = parse_quote! {
            #[spec_locked(section = "8.82", function = "F_Z")]
            pub fn z() {}
        };
        assert_eq!(extract_formula_anchor(&f.attrs).as_deref(), Some("F_Z"));
        assert_eq!(extract_constant_anchor(&f.attrs), None);
        assert_eq!(extract_section(&f.attrs).as_deref(), Some("8.82"));
    }

    #[test]
    fn named_function_param_extracts_constant() {
        let f: ItemFn = parse_quote! {
            #[spec_locked(section = "4.82", function = "C_Z")]
            pub fn z() {}
        };
        assert_eq!(extract_formula_anchor(&f.attrs), None);
        assert_eq!(extract_constant_anchor(&f.attrs).as_deref(), Some("C_Z"));
        assert_eq!(extract_section(&f.attrs).as_deref(), Some("4.82"));
    }
}

#[cfg(test)]
mod failure_kind_tests {
    use super::{
        FailureKind, FunctionToVerify, PartialReason, VerificationResult,
        demote_if_all_spec_derived, failed_verification, failure_kind, verify_function,
    };
    use std::path::PathBuf;

    #[test]
    fn parse_gap_is_partial_and_a_missing_anchor_is_not() {
        let gap = FunctionToVerify {
            file_path: PathBuf::from("src/x.rs"),
            function_name: "gap".into(),
            contracts: vec![],
            section: Some("1.0".into()),
            spec_name_override: None,
            formula_anchor: None,
            constant_anchor: None,
            function_sig: None,
            parse_gap: true,
        };
        match verify_function(&gap, 1, &[]) {
            VerificationResult::Partial { partial_reason, .. } => {
                assert_eq!(partial_reason, Some(PartialReason::UnsupportedTranslation));
            }
            other => panic!("gap must be Partial, got {other:?}"),
        }
        let missing = FunctionToVerify {
            parse_gap: false,
            ..gap
        };
        assert!(matches!(
            verify_function(&missing, 1, &[]),
            VerificationResult::NoContracts { .. }
        ));
    }

    #[test]
    fn determinism_z3_unknown_is_solver_unknown_not_counterexample() {
        let msg = "Determinism: Z3 unknown: Try --timeout 30. (1 total failures)";
        assert_eq!(failure_kind("Ensures", msg), FailureKind::SolverUnknown);

        match failed_verification("Ensures", "Determinism: Z3 unknown: Try --timeout 30.", 1) {
            VerificationResult::Failed {
                kind,
                partial_reason,
                ..
            } => {
                assert_eq!(kind, FailureKind::SolverUnknown);
                assert_eq!(partial_reason, Some(PartialReason::Z3Timeout));
            }
            _ => panic!("expected Failed"),
        }
    }

    #[test]
    fn determinism_non_deterministic_stays_counterexample() {
        let msg = "Determinism: Non-deterministic. Counterexample: [] (1 total failures)";
        assert_eq!(failure_kind("Ensures", msg), FailureKind::Counterexample);
    }

    #[test]
    fn spec_derived_counterexample_stays_failed() {
        // A Z3 counterexample on a spec-derived contract is a real finding — it must NOT
        // be demoted to Partial.  demote_if_all_spec_derived returns None so the caller
        // falls through to failed_verification.
        let failed = vec![(
            "Ensures".to_string(),
            "Z3: Contract violated. Counterexample: {}".to_string(),
            true,
        )];
        assert!(
            demote_if_all_spec_derived(&failed, 0, 1).is_none(),
            "spec-derived Z3 counterexample must not be demoted to Partial"
        );
    }

    #[test]
    fn spec_derived_translation_gap_demotes_to_partial() {
        // A parse/translation gap (not a Z3 result) should still demote to Partial.
        let failed = vec![(
            "Ensures".to_string(),
            "Contract could not be parsed: unsupported LaTeX expression".to_string(),
            true,
        )];
        let result =
            demote_if_all_spec_derived(&failed, 0, 1).expect("translation gap should demote");
        match result {
            VerificationResult::Partial { partial_reason, .. } => {
                assert_eq!(partial_reason, Some(PartialReason::UnsupportedTranslation));
            }
            _ => panic!("expected Partial"),
        }
    }

    #[test]
    fn manual_counterexample_stays_failed() {
        let failed = vec![(
            "Ensures".to_string(),
            "Z3: Contract violated.".to_string(),
            false,
        )];
        assert!(demote_if_all_spec_derived(&failed, 0, 1).is_none());
    }

    #[test]
    fn spec_derived_body_translation_failure_demotes_to_partial() {
        let failed = vec![(
            "Ensures".to_string(),
            "Z3: Z3 verification unknown: Could not translate function body to Z3 constraints; \
             SAT result without body constraints is not meaningful"
                .to_string(),
            true,
        )];
        let result = demote_if_all_spec_derived(&failed, 0, 1)
            .expect("body-translation gap should demote to Partial");
        match result {
            VerificationResult::Partial { partial_reason, .. } => {
                assert_eq!(partial_reason, Some(PartialReason::UnsupportedTranslation));
            }
            other => panic!("expected Partial, got {other:?}"),
        }
    }

    #[test]
    fn spec_derived_empty_assignments_demotes_to_partial() {
        let failed = vec![(
            "Ensures".to_string(),
            "Z3: Z3 verification unknown: Z3 found SAT but counterexample model has no named \
             variable assignments (incomplete translator); result is not a concrete witness \
             against the implementation"
                .to_string(),
            true,
        )];
        let result = demote_if_all_spec_derived(&failed, 0, 1)
            .expect("empty assignment map should demote to Partial");
        match result {
            VerificationResult::Partial { partial_reason, .. } => {
                assert_eq!(partial_reason, Some(PartialReason::UnsupportedTranslation));
            }
            other => panic!("expected Partial, got {other:?}"),
        }
    }

    #[test]
    fn spec_derived_translation_type_error_demotes_to_partial() {
        let failed = vec![(
            "Ensures".to_string(),
            "Z3: Z3 verification error: Translation error: Type error: Expected Bool".to_string(),
            true,
        )];
        let result = demote_if_all_spec_derived(&failed, 0, 1)
            .expect("translation type error should demote to Partial");
        match result {
            VerificationResult::Partial { partial_reason, .. } => {
                assert_eq!(partial_reason, Some(PartialReason::UnsupportedTranslation));
            }
            other => panic!("expected Partial, got {other:?}"),
        }
    }

    #[test]
    fn spec_derived_counterexample_with_concrete_assignments_stays_failed() {
        // A spec-derived failure with a non-empty counterexample message (concrete assignments)
        // must remain Failed — that is a real verification finding.
        let failed = vec![(
            "Ensures".to_string(),
            "Z3: Contract violated. Counterexample: {\"x\": \"5\", \"y\": \"-1\"} (1 total failures)"
                .to_string(),
            true,
        )];
        assert!(
            demote_if_all_spec_derived(&failed, 0, 1).is_none(),
            "spec-derived failure with concrete counterexample must not be demoted"
        );
    }

    #[test]
    fn manual_no_named_assignments_demotes_to_partial() {
        let failed = vec![(
            "Ensures".to_string(),
            "Z3: Z3 verification unknown: Z3 found SAT but counterexample model has no named \
             variable assignments (incomplete translator); result is not a concrete witness \
             against the implementation (3 total failures)"
                .to_string(),
            false,
        )];
        let result = demote_if_all_spec_derived(&failed, 0, 1)
            .expect("an unnamed model is a translator gap for a manual contract too");
        match result {
            VerificationResult::Partial { partial_reason, .. } => {
                assert_eq!(partial_reason, Some(PartialReason::UnsupportedTranslation));
            }
            other => panic!("expected Partial, got {other:?}"),
        }
    }

    #[test]
    fn restated_axiom_does_not_stay_failed() {
        let failed = vec![(
            "Ensures".to_string(),
            "Z3: ensures restates an axiom; body did not discharge it: Contract violated"
                .to_string(),
            false,
        )];
        let result = demote_if_all_spec_derived(&failed, 0, 1).expect("restated axiom is partial");
        assert!(matches!(
            result,
            VerificationResult::Partial {
                partial_reason: Some(PartialReason::UnsupportedTranslation),
                ..
            }
        ));
    }
}

#[cfg(all(test, feature = "z3"))]
mod weight_to_vsize_identity {
    use super::{VerificationResult, make_function_to_verify, verify_function};
    use crate::cli::spec_enrich::enrich_functions_with_spec;
    use crate::parser::spec_expr::{consensus_workspace_present, vsize_ceiling};
    use std::path::PathBuf;

    #[test]
    fn identity_passes_from_the_translated_body() {
        if !consensus_workspace_present() {
            return;
        }
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("blvm-consensus/src/witness.rs"))
            .expect("witness.rs");
        let file = syn::parse_file(&src).expect("parse witness.rs");
        let func = file
            .items
            .iter()
            .find_map(|item| match item {
                syn::Item::Fn(f) if f.sig.ident == "weight_to_vsize" => Some(f),
                _ => None,
            })
            .expect("weight_to_vsize");
        let mut functions = vec![make_function_to_verify(
            std::path::Path::new("src/witness.rs"),
            "weight_to_vsize",
            &func.attrs,
            func,
        )];
        enrich_functions_with_spec(&mut functions, &[root.join("blvm-spec/PROTOCOL.md")])
            .expect("enrich");
        let (add, div) = vsize_ceiling();
        let identity = format!("result == (weight + {add}) / {div}");
        assert!(
            functions[0]
                .contracts
                .iter()
                .any(|c| c.condition == identity),
            "identity missing from {:?}",
            functions[0]
                .contracts
                .iter()
                .map(|c| c.condition.as_str())
                .collect::<Vec<_>>()
        );
        assert!(
            functions[0]
                .contracts
                .iter()
                .all(|c| c.condition != "result * 4 >= weight"),
            "manual ceiling bound must not be the contract"
        );
        match verify_function(&functions[0], 10, &[]) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "the identity must use the body");
            }
            other => panic!("weight_to_vsize must pass on the identity, got {other:?}"),
        }
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        let (add, div) = vsize_ceiling();
        let identity = format!("result == (weight + {add}) / {div}");
        let mut function = make_function_to_verify(
            std::path::Path::new("src/witness.rs"),
            "weight_to_vsize",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.clone(),
            expr: syn::parse_str(&identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    #[test]
    fn a_body_edit_flips_the_identity() {
        if !consensus_workspace_present() {
            return;
        }
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("blvm-consensus/src/witness.rs"))
            .expect("witness.rs");
        let file = syn::parse_file(&src).expect("parse witness.rs");
        let func = file
            .items
            .iter()
            .find_map(|item| match item {
                syn::Item::Fn(f) if f.sig.ident == "weight_to_vsize" => Some(f.clone()),
                _ => None,
            })
            .expect("weight_to_vsize");
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "unpatched identity must use the body");
            }
            other => panic!("unpatched identity must pass, got {other:?}"),
        }

        let mut literal = func.clone();
        assert!(
            crate::translator::body_edit::replace_returned_call_literal(&mut literal),
            "the returned call has an integer literal"
        );
        let literal_src = quote::quote!(#literal).to_string();
        assert!(
            literal_src.contains("div_ceil (8)"),
            "doubling the call literal must be the predicate edit, got {literal_src}"
        );
        let literal_result = identity_query(&literal);
        assert!(
            matches!(
                literal_result,
                VerificationResult::Failed {
                    kind: super::FailureKind::Counterexample,
                    ..
                }
            ),
            "div_ceil literal edit must flip the identity, got {literal_result:?}"
        );

        let mut divided = func;
        assert!(
            crate::translator::body_edit::replace_returned_call_with_div(&mut divided),
            "the returned call can become division"
        );
        let divided_src = quote::quote!(#divided).to_string();
        assert!(
            !divided_src.contains("div_ceil"),
            "the call must be binary division, got {divided_src}"
        );
        let divided_result = identity_query(&divided);
        assert!(
            matches!(
                divided_result,
                VerificationResult::Failed {
                    kind: super::FailureKind::Counterexample,
                    ..
                }
            ),
            "floor division must flip the identity, got {divided_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod witness_program_length_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::{consensus_workspace_present, witness_program_lengths};
    use std::path::PathBuf;

    fn length_fn() -> syn::ItemFn {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("blvm-consensus/src/witness.rs"))
            .expect("witness.rs");
        let file = syn::parse_file(&src).expect("parse witness.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(f) if f.sig.ident == "validate_witness_program_length" => Some(f),
                _ => None,
            })
            .expect("validate_witness_program_length")
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        let (short, long) = witness_program_lengths();
        let identity = format!(
            "result == match version {{ WitnessVersion::SegWitV0 => program.len() == {short} || program.len() == {long}, WitnessVersion::TaprootV1 => program.len() == {long} }}"
        );
        let mut function = make_function_to_verify(
            std::path::Path::new("src/witness.rs"),
            "validate_witness_program_length",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.clone(),
            expr: syn::parse_str(&identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    #[test]
    fn lengths_pass_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let func = length_fn();
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(
                    body_translated,
                    "the witness-length identity must use the body"
                );
            }
            other => panic!("unpatched witness length must pass, got {other:?}"),
        }

        let mut collapsed = func.clone();
        assert!(
            crate::translator::body_edit::collapse_returned_or_eq(&mut collapsed),
            "the version-0 arm is an or of equalities"
        );
        let collapsed_src = quote::quote!(#collapsed).to_string();
        assert!(
            collapsed_src
                .contains("SEGWIT_P2WSH_LENGTH || program . len () == SEGWIT_P2WSH_LENGTH"),
            "both version-0 lengths must be the long program, got {collapsed_src}"
        );
        let collapsed_result = identity_query(&collapsed);
        assert!(
            matches!(
                collapsed_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "collapsing the lengths must flip the identity, got {collapsed_result:?}"
        );

        let mut zeroed = func;
        assert!(
            crate::translator::body_edit::zero_last_returned_eq(&mut zeroed),
            "the last arm is an equality"
        );
        let zeroed_src = quote::quote!(#zeroed).to_string();
        assert!(
            zeroed_src.contains("== 0"),
            "the last length must be zero, got {zeroed_src}"
        );
        let zeroed_result = identity_query(&zeroed);
        assert!(
            matches!(
                zeroed_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "zeroing the last length must flip the identity, got {zeroed_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod bip65_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::{consensus_workspace_present, locktime_threshold};
    use std::path::PathBuf;

    fn bip65_fn() -> syn::ItemFn {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("blvm-consensus/src/locktime.rs"))
            .expect("locktime.rs");
        let file = syn::parse_file(&src).expect("parse locktime.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(f) if f.sig.ident == "check_bip65" => Some(f),
                _ => None,
            })
            .expect("check_bip65")
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        let threshold = locktime_threshold();
        let identity = format!(
            "result == (((tx_locktime < {threshold}) == (stack_locktime < {threshold})) && tx_locktime >= stack_locktime)"
        );
        let mut function = make_function_to_verify(
            std::path::Path::new("src/locktime.rs"),
            "check_bip65",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.clone(),
            expr: syn::parse_str(&identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    #[test]
    fn order_and_type_pass_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let func = bip65_fn();
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "the BIP65 identity must use the body");
            }
            other => panic!("unpatched BIP65 must pass, got {other:?}"),
        }

        let mut tightened = func.clone();
        assert!(
            crate::translator::body_edit::tighten_returned_ge(&mut tightened),
            "the returned comparison is >="
        );
        let tightened_src = quote::quote!(#tightened).to_string();
        assert!(
            tightened_src.contains('>') && !tightened_src.contains(">="),
            "the order edit must be strict, got {tightened_src}"
        );
        let tightened_result = identity_query(&tightened);
        assert!(
            matches!(
                tightened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "order edit must flip the identity, got {tightened_result:?}"
        );

        let mut dropped = func;
        assert!(
            crate::translator::body_edit::drop_returned_and_left(&mut dropped),
            "the function returns a conjunction"
        );
        let dropped_src = quote::quote!(#dropped).to_string();
        assert!(
            !dropped_src.contains("locktime_types_match"),
            "the type conjunct must be gone, got {dropped_src}"
        );
        let dropped_result = identity_query(&dropped);
        assert!(
            matches!(
                dropped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "dropping the type conjunct must flip the identity, got {dropped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod locktime_type_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::{consensus_workspace_present, locktime_threshold};
    use std::path::PathBuf;

    fn kind_fn() -> syn::ItemFn {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("blvm-consensus/src/locktime.rs"))
            .expect("locktime.rs");
        let file = syn::parse_file(&src).expect("parse locktime.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(f) if f.sig.ident == "get_locktime_type" => Some(f),
                _ => None,
            })
            .expect("get_locktime_type")
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        let threshold = locktime_threshold();
        let identity = format!(
            "result == if locktime < {threshold} {{ LocktimeType::BlockHeight }} else {{ LocktimeType::Timestamp }}"
        );
        let mut function = make_function_to_verify(
            std::path::Path::new("src/locktime.rs"),
            "get_locktime_type",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.clone(),
            expr: syn::parse_str(&identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    #[test]
    fn threshold_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let func = kind_fn();
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(
                    body_translated,
                    "the locktime-type identity must use the body"
                );
            }
            other => panic!("unpatched locktime type must pass, got {other:?}"),
        }

        let mut relaxed = func.clone();
        assert!(
            crate::translator::body_edit::relax_returned_lt(&mut relaxed),
            "the returned if compares with <"
        );
        let relaxed_src = quote::quote!(#relaxed).to_string();
        assert!(
            relaxed_src.contains("<="),
            "the boundary edit must be <=, got {relaxed_src}"
        );
        let relaxed_result = identity_query(&relaxed);
        assert!(
            matches!(
                relaxed_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "boundary edit must flip the identity, got {relaxed_result:?}"
        );

        let mut reversed = func;
        assert!(
            crate::translator::body_edit::reverse_returned_lt(&mut reversed),
            "the returned if compares with <"
        );
        let reversed_src = quote::quote!(#reversed).to_string();
        assert!(
            reversed_src.contains(">"),
            "the direction edit must be >, got {reversed_src}"
        );
        let reversed_result = identity_query(&reversed);
        assert!(
            matches!(
                reversed_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "direction edit must flip the identity, got {reversed_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod sequence_locktime_value_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::{consensus_workspace_present, mask_in};
    use std::path::PathBuf;

    fn value_fn() -> syn::ItemFn {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("blvm-consensus/src/locktime.rs"))
            .expect("locktime.rs");
        let file = syn::parse_file(&src).expect("parse locktime.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(f) if f.sig.ident == "extract_sequence_locktime_value" => Some(f),
                _ => None,
            })
            .expect("extract_sequence_locktime_value")
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        let mask = mask_in("ExtractSequenceLocktimeValue");
        let identity = format!("result == (sequence & {mask})");
        let mut function = make_function_to_verify(
            std::path::Path::new("src/locktime.rs"),
            "extract_sequence_locktime_value",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.clone(),
            expr: syn::parse_str(&identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    #[test]
    fn mask_and_or_pass_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let func = value_fn();
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(
                    body_translated,
                    "the locktime-value identity must use the body"
                );
            }
            other => panic!("unpatched locktime value must pass, got {other:?}"),
        }

        let mask = mask_in("ExtractSequenceLocktimeValue");
        let smaller = mask - 1;
        let mut narrowed = func.clone();
        assert!(
            crate::translator::body_edit::decrement_and_literal(&mut narrowed),
            "the returned mask is an integer literal"
        );
        let narrowed_src = quote::quote!(#narrowed).to_string();
        assert!(
            narrowed_src.contains(&smaller.to_string()),
            "decrementing the mask must clear the low bit, got {narrowed_src}"
        );
        let narrowed_result = identity_query(&narrowed);
        assert!(
            matches!(
                narrowed_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "mask edit must flip the identity, got {narrowed_result:?}"
        );

        let mut ored = func;
        assert!(
            crate::translator::body_edit::replace_returned_and_with_or(&mut ored),
            "the function returns a bitwise and"
        );
        let ored_src = quote::quote!(#ored).to_string();
        assert!(
            ored_src.contains('|'),
            "the operator edit must be bitwise or, got {ored_src}"
        );
        let ored_result = identity_query(&ored);
        assert!(
            matches!(
                ored_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "or edit must flip the identity, got {ored_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod sequence_type_flag_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::{consensus_workspace_present, mask_in};
    use std::path::PathBuf;

    fn type_flag_fn() -> syn::ItemFn {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("blvm-consensus/src/locktime.rs"))
            .expect("locktime.rs");
        let file = syn::parse_file(&src).expect("parse locktime.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(f) if f.sig.ident == "extract_sequence_type_flag" => Some(f),
                _ => None,
            })
            .expect("extract_sequence_type_flag")
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        let mask = mask_in("ExtractSequenceTypeFlag");
        let identity = format!("result == ((sequence & {mask}) != 0)");
        let mut function = make_function_to_verify(
            std::path::Path::new("src/locktime.rs"),
            "extract_sequence_type_flag",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.clone(),
            expr: syn::parse_str(&identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    #[test]
    fn mask_and_polarity_pass_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let func = type_flag_fn();
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "the type-flag identity must use the body");
            }
            other => panic!("unpatched type flag must pass, got {other:?}"),
        }

        let mask = mask_in("ExtractSequenceTypeFlag");
        let half = mask / 2;
        let mut halved = func.clone();
        assert!(
            crate::translator::body_edit::halve_and_literal(&mut halved),
            "the returned mask is an integer literal"
        );
        let halved_src = quote::quote!(#halved).to_string();
        assert!(
            halved_src.contains(&half.to_string()),
            "halving the mask must be the bit edit, got {halved_src}"
        );
        let halved_result = identity_query(&halved);
        assert!(
            matches!(
                halved_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "mask edit must flip the identity, got {halved_result:?}"
        );

        let mut flipped = func;
        assert!(
            crate::translator::body_edit::flip_returned_neq(&mut flipped),
            "the function returns an inequality"
        );
        let flipped_src = quote::quote!(#flipped).to_string();
        assert!(
            flipped_src.contains("=="),
            "the polarity edit must be equality, got {flipped_src}"
        );
        let flipped_result = identity_query(&flipped);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "polarity edit must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod sequence_disabled_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::{consensus_workspace_present, mask_in};
    use std::path::PathBuf;

    fn disabled_fn() -> syn::ItemFn {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("blvm-consensus/src/locktime.rs"))
            .expect("locktime.rs");
        let file = syn::parse_file(&src).expect("parse locktime.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(f) if f.sig.ident == "is_sequence_disabled" => Some(f),
                _ => None,
            })
            .expect("is_sequence_disabled")
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        let mask = mask_in("IsSequenceDisabled");
        let identity = format!("result == ((sequence & {mask}) != 0)");
        let mut function = make_function_to_verify(
            std::path::Path::new("src/locktime.rs"),
            "is_sequence_disabled",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.clone(),
            expr: syn::parse_str(&identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    #[test]
    fn mask_and_polarity_pass_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let func = disabled_fn();
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(
                    body_translated,
                    "the disable-bit identity must use the body"
                );
            }
            other => panic!("unpatched disable bit must pass, got {other:?}"),
        }

        let mask = mask_in("IsSequenceDisabled");
        let half = mask / 2;
        let mut halved = func.clone();
        assert!(
            crate::translator::body_edit::halve_and_literal(&mut halved),
            "the returned mask is an integer literal"
        );
        let halved_src = quote::quote!(#halved).to_string();
        assert!(
            halved_src.contains(&half.to_string()),
            "halving the mask must be the bit edit, got {halved_src}"
        );
        let halved_result = identity_query(&halved);
        assert!(
            matches!(
                halved_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "mask edit must flip the identity, got {halved_result:?}"
        );

        let mut flipped = func;
        assert!(
            crate::translator::body_edit::flip_returned_neq(&mut flipped),
            "the function returns an inequality"
        );
        let flipped_src = quote::quote!(#flipped).to_string();
        assert!(
            flipped_src.contains("=="),
            "the polarity edit must be equality, got {flipped_src}"
        );
        let flipped_result = identity_query(&flipped);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "polarity edit must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod transaction_weight_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::{consensus_workspace_present, weight_base_coeff};
    use std::path::PathBuf;

    fn weight_fn() -> syn::ItemFn {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("blvm-consensus/src/witness.rs"))
            .expect("witness.rs");
        let file = syn::parse_file(&src).expect("parse witness.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(f) if f.sig.ident == "calculate_transaction_weight_segwit" => Some(f),
                _ => None,
            })
            .expect("calculate_transaction_weight_segwit")
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        let coeff = weight_base_coeff();
        let identity = format!("result == {coeff} * base_size + total_size");
        let mut function = make_function_to_verify(
            std::path::Path::new("src/witness.rs"),
            "calculate_transaction_weight_segwit",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.clone(),
            expr: syn::parse_str(&identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    #[test]
    fn factor_and_sum_pass_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let func = weight_fn();
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "the weight identity must use the body");
            }
            other => panic!("unpatched weight must pass, got {other:?}"),
        }

        let coeff = weight_base_coeff();
        let smaller = coeff - 1;
        let mut factored = func.clone();
        assert!(
            crate::translator::body_edit::decrement_mul_literal(&mut factored),
            "the returned product has an integer factor"
        );
        let factored_src = quote::quote!(#factored).to_string();
        assert!(
            factored_src.contains(&format!("{smaller} * base_size")),
            "decrementing the factor must be the coefficient edit, got {factored_src}"
        );
        let factored_result = identity_query(&factored);
        assert!(
            matches!(
                factored_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "factor edit must flip the identity, got {factored_result:?}"
        );

        let mut biased = func;
        assert!(
            crate::translator::body_edit::subtract_one_from_returned_sum(&mut biased),
            "the function returns a sum"
        );
        let biased_src = quote::quote!(#biased).to_string();
        assert!(
            biased_src.contains("- 1"),
            "the sum edit must subtract one, got {biased_src}"
        );
        let biased_result = identity_query(&biased);
        assert!(
            matches!(
                biased_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "sum edit must flip the identity, got {biased_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod get_block_subsidy_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::{
        consensus_workspace_present, initial_subsidy, protocol_u64, subsidy_shift_guard,
    };
    use std::path::PathBuf;

    fn subsidy_fn() -> syn::ItemFn {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("blvm-consensus/src/economic.rs"))
            .expect("economic.rs");
        let file = syn::parse_file(&src).expect("parse economic.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(f) if f.sig.ident == "get_block_subsidy" => Some(f),
                _ => None,
            })
            .expect("get_block_subsidy")
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        let interval = protocol_u64("H");
        let initial = initial_subsidy();
        let guard = subsidy_shift_guard();
        let identity = format!(
            "result == if (height / {interval}) >= {guard} {{ 0 }} else {{ {initial} >> (height / {interval}) }}"
        );
        let mut function = make_function_to_verify(
            std::path::Path::new("src/economic.rs"),
            "get_block_subsidy",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.clone(),
            expr: syn::parse_str(&identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    #[test]
    fn shift_and_guard_pass_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let func = subsidy_fn();
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "the subsidy identity must use the body");
            }
            other => panic!("unpatched subsidy must pass, got {other:?}"),
        }

        let guard = subsidy_shift_guard();
        let half = guard / 2;
        let mut halved = func.clone();
        assert!(
            crate::translator::body_edit::halve_guard_literal(&mut halved),
            "the early return has an integer guard"
        );
        let halved_src = quote::quote!(#halved).to_string();
        assert!(
            halved_src.contains(&format!(">= {half}")),
            "halving the guard must be the boundary edit, got {halved_src}"
        );
        let halved_result = identity_query(&halved);
        assert!(
            matches!(
                halved_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "guard edit must flip the identity, got {halved_result:?}"
        );

        let mut shifted = func;
        assert!(
            crate::translator::body_edit::increment_returned_shift(&mut shifted),
            "the returned value is a shift"
        );
        let shifted_src = quote::quote!(#shifted).to_string();
        assert!(
            shifted_src.contains("+ 1"),
            "the shift amount must increase, got {shifted_src}"
        );
        let shifted_result = identity_query(&shifted);
        assert!(
            matches!(
                shifted_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "shift edit must flip the identity, got {shifted_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod axiom_restatement {
    use super::{Contract, ContractType, verify_with_z3};
    use syn::parse_quote;

    fn ctr(kind: ContractType, cond: &str) -> Contract {
        Contract {
            contract_type: kind,
            condition: cond.to_string(),
            expr: Some(syn::parse_str(cond).unwrap()),
            is_spec_derived: false,
        }
    }

    #[test]
    fn copied_axiom_does_not_prove_ensures() {
        let func: syn::ItemFn = parse_quote! {
            fn f(x: i64) -> i64 { x }
        };
        let ensures = ctr(ContractType::Ensures, "result >= 0");
        let axiom = ctr(ContractType::Axiom, "result >= 0");
        let err = verify_with_z3(&ensures, Some(&func), &[], &[&axiom], 5, &[])
            .expect_err("the body is the identity");
        assert!(err.contains("ensures restates an axiom"), "{err}");
    }

    #[test]
    fn distinct_axiom_is_still_assumed() {
        let func: syn::ItemFn = parse_quote! {
            fn g(x: i64) -> i64 { x }
        };
        let ensures = ctr(ContractType::Ensures, "result >= 0");
        let axiom = ctr(ContractType::Axiom, "x >= 0");
        let body_translated =
            verify_with_z3(&ensures, Some(&func), &[], &[&axiom], 5, &[]).expect("proved");
        assert!(body_translated);
    }
}

#[cfg(all(test, feature = "z3"))]
mod taproot_activation_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::{
        consensus_workspace_present, taproot_height, taproot_regtest_height,
    };
    use std::path::PathBuf;

    fn activation_fn() -> syn::ItemFn {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("blvm-consensus/src/activation.rs"))
            .expect("activation.rs");
        let file = syn::parse_file(&src).expect("parse activation.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(f) if f.sig.ident == "taproot_activation_height" => Some(f),
                _ => None,
            })
            .expect("taproot_activation_height")
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        let main = taproot_height("mainnet");
        let test = taproot_height("testnet");
        let regtest = taproot_regtest_height();
        // Signet and Testnet4 return 1. The three TaprootActivation formulas do not state it.
        let identity = format!(
            "result == if network == Network::Mainnet {{ {main} }} else if network == Network::Testnet {{ {test} }} else if network == Network::Signet || network == Network::Testnet4 {{ 1 }} else {{ {regtest} }}"
        );
        let mut function = make_function_to_verify(
            std::path::Path::new("src/activation.rs"),
            "taproot_activation_height",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.clone(),
            expr: syn::parse_str(&identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    #[test]
    fn heights_pass_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let func = activation_fn();
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "the activation identity must use the body");
            }
            other => panic!("unpatched activation identity must pass, got {other:?}"),
        }

        let mut copied = func.clone();
        assert!(
            crate::translator::body_edit::copy_next_if_arm(&mut copied),
            "the returned if has a next arm"
        );
        let copied_src = quote::quote!(#copied).to_string();
        assert!(
            copied_src.contains("Network :: Mainnet { TAPROOT_ACTIVATION_TESTNET }"),
            "the mainnet arm must return the testnet height, got {copied_src}"
        );
        let copied_result = identity_query(&copied);
        assert!(
            matches!(
                copied_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "copying the next arm must flip the identity, got {copied_result:?}"
        );

        let mut incremented = func;
        assert!(
            crate::translator::body_edit::increment_returned_if_literal(&mut incremented),
            "a returned arm is an integer literal"
        );
        let incremented_src = quote::quote!(#incremented).to_string();
        assert!(
            incremented_src.contains("Testnet4 { 2 }"),
            "the signet arm must be 2, got {incremented_src}"
        );
        let incremented_result = identity_query(&incremented);
        assert!(
            matches!(
                incremented_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "incrementing the signet height must flip the identity, got {incremented_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod push_opcode_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::{consensus_workspace_present, push_opcode_max};
    use std::path::PathBuf;

    fn push_fn() -> syn::ItemFn {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("blvm-consensus/src/script/mod.rs"))
            .expect("script/mod.rs");
        let file = syn::parse_file(&src).expect("parse script/mod.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(f) if f.sig.ident == "is_push_opcode" => Some(f),
                _ => None,
            })
            .expect("is_push_opcode")
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        let max = push_opcode_max();
        let identity = format!("result == (opcode <= {max})");
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "is_push_opcode",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.clone(),
            expr: syn::parse_str(&identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    #[test]
    fn bound_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let func = push_fn();
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(
                    body_translated,
                    "the push-opcode identity must use the body"
                );
            }
            other => panic!("unpatched push opcode must pass, got {other:?}"),
        }

        let mut tightened = func.clone();
        assert!(
            crate::translator::body_edit::tighten_returned_le(&mut tightened),
            "the returned comparison is <="
        );
        let tightened_src = quote::quote!(#tightened).to_string();
        assert!(
            tightened_src.contains("opcode < 0x60"),
            "the bound must be strict, got {tightened_src}"
        );
        let tightened_result = identity_query(&tightened);
        assert!(
            matches!(
                tightened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "tightening <= must flip the identity, got {tightened_result:?}"
        );

        let mut widened = func;
        assert!(
            crate::translator::body_edit::increment_returned_cmp_literal(&mut widened),
            "the comparison has an integer literal"
        );
        let widened_src = quote::quote!(#widened).to_string();
        assert!(
            widened_src.contains("opcode <= 97"),
            "the bound must be one higher, got {widened_src}"
        );
        let widened_result = identity_query(&widened);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "widening the bound must flip the identity, got {widened_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod minimal_if_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn minimal_fn() -> syn::ItemFn {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("blvm-consensus/src/script/control_flow.rs"))
            .expect("control_flow.rs");
        let file = syn::parse_file(&src).expect("parse control_flow.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(f) if f.sig.ident == "is_minimal_if_condition" => Some(f),
                _ => None,
            })
            .expect("is_minimal_if_condition")
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        // Empty and longer than one byte are the two formulas. The single byte
        // `0x01` is the body's comparison; those formulas do not state it.
        let identity =
            "result == (bytes.len() == 0 || (bytes.len() == 1 && bytes[0] == 1))".to_string();
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/control_flow.rs"),
            "is_minimal_if_condition",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.clone(),
            expr: syn::parse_str(&identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    #[test]
    fn arms_pass_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let func = minimal_fn();
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "the minimal-if identity must use the body");
            }
            other => panic!("unpatched minimal if must pass, got {other:?}"),
        }

        let mut flipped = func.clone();
        assert!(
            crate::translator::body_edit::flip_returned_match_bool(&mut flipped),
            "the empty arm is a boolean literal"
        );
        let flipped_src = quote::quote!(#flipped).to_string();
        assert!(
            flipped_src.contains("0 => false"),
            "the empty arm must be false, got {flipped_src}"
        );
        let flipped_result = identity_query(&flipped);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "flipping the empty arm must flip the identity, got {flipped_result:?}"
        );

        let mut widened = func;
        assert!(
            crate::translator::body_edit::increment_returned_cmp_literal(&mut widened),
            "the one-byte arm compares with an integer"
        );
        let widened_src = quote::quote!(#widened).to_string();
        assert!(
            widened_src.contains("== 2"),
            "the one-byte value must be one higher, got {widened_src}"
        );
        let widened_result = identity_query(&widened);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "changing the one-byte value must flip the identity, got {widened_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod reorganize_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn reorg_fn() -> syn::ItemFn {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("blvm-consensus/src/reorganization.rs"))
            .expect("reorganization.rs");
        let file = syn::parse_file(&src).expect("parse reorganization.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(f) if f.sig.ident == "should_reorganize" => Some(f),
                _ => None,
            })
            .expect("should_reorganize")
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        // Section 11.3 says strictly more cumulative work. It does not write the comparison.
        let identity =
            "result == (calculate_chain_work(new_chain) > calculate_chain_work(current_chain))"
                .to_string();
        let mut function = make_function_to_verify(
            std::path::Path::new("src/reorganization.rs"),
            "should_reorganize",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.clone(),
            expr: syn::parse_str(&identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    #[test]
    fn comparison_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let func = reorg_fn();
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "the reorganize identity must use the body");
            }
            other => panic!("unpatched reorganize must pass, got {other:?}"),
        }

        let mut relaxed = func.clone();
        assert!(
            crate::translator::body_edit::relax_returned_gt(&mut relaxed),
            "the returned comparison is >"
        );
        let relaxed_src = quote::quote!(#relaxed).to_string();
        assert!(
            relaxed_src.contains("new_work >= current_work"),
            "the comparison must be >=, got {relaxed_src}"
        );
        let relaxed_result = identity_query(&relaxed);
        assert!(
            matches!(
                relaxed_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "relaxing > must flip the identity, got {relaxed_result:?}"
        );

        let mut reversed = func;
        assert!(
            crate::translator::body_edit::reverse_returned_gt(&mut reversed),
            "the returned comparison is >"
        );
        let reversed_src = quote::quote!(#reversed).to_string();
        assert!(
            reversed_src.contains("new_work < current_work"),
            "the comparison must be <, got {reversed_src}"
        );
        let reversed_result = identity_query(&reversed);
        assert!(
            matches!(
                reversed_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "reversing > must flip the identity, got {reversed_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_success_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::{consensus_workspace_present, op_success_ranges};
    use std::path::PathBuf;

    fn success_fn() -> syn::ItemFn {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("blvm-consensus/src/script/mod.rs"))
            .expect("script/mod.rs");
        let file = syn::parse_file(&src).expect("parse script/mod.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(f) if f.sig.ident == "is_op_success" => Some(f),
                _ => None,
            })
            .expect("is_op_success")
    }

    fn identity() -> String {
        let parts: Vec<String> = op_success_ranges()
            .into_iter()
            .map(|(lo, hi)| {
                if lo == hi {
                    format!("opcode == {lo}")
                } else {
                    format!("(opcode >= {lo} && opcode <= {hi})")
                }
            })
            .collect();
        format!("result == ({})", parts.join(" || "))
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        let identity = identity();
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "is_op_success",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.clone(),
            expr: syn::parse_str(&identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    #[test]
    fn ranges_pass_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let func = success_fn();
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(
                    body_translated,
                    "the immediate-success identity must use the body"
                );
            }
            other => panic!("unpatched immediate success must pass, got {other:?}"),
        }

        let mut widened = func.clone();
        assert!(
            crate::translator::body_edit::increment_returned_matches_lit(&mut widened),
            "the pattern has an integer literal"
        );
        let widened_src = quote::quote!(#widened).to_string();
        assert!(
            widened_src.contains("81 | 98"),
            "the first opcode must be one higher, got {widened_src}"
        );
        let widened_result = identity_query(&widened);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the first opcode must flip the identity, got {widened_result:?}"
        );

        let mut shifted = func;
        assert!(
            crate::translator::body_edit::increment_returned_matches_range_start(&mut shifted),
            "the pattern has a range"
        );
        let shifted_src = quote::quote!(#shifted).to_string();
        assert!(
            shifted_src.contains("188"),
            "the last range must start one higher, got {shifted_src}"
        );
        let shifted_result = identity_query(&shifted);
        assert!(
            matches!(
                shifted_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the last range must flip the identity, got {shifted_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod coinbase_maturity_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::{consensus_workspace_present, protocol_u64};
    use std::path::PathBuf;

    fn coinbase_maturity_fn() -> syn::ItemFn {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("blvm-consensus/src/transaction.rs"))
            .expect("transaction.rs");
        let file = syn::parse_file(&src).expect("parse transaction.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "check_coinbase_maturity" => Some(func),
                _ => None,
            })
            .expect("check_coinbase_maturity")
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        let maturity = protocol_u64("R");
        let identity = format!(
            "result == (!is_coinbase || spend_height >= utxo_creation_height.saturating_add({maturity}))"
        );
        let mut function = make_function_to_verify(
            std::path::Path::new("src/transaction.rs"),
            "check_coinbase_maturity",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.clone(),
            expr: syn::parse_str(&identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    #[test]
    fn skip_and_bound_pass_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let func = coinbase_maturity_fn();
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "the maturity identity must use the body");
            }
            other => panic!("unpatched maturity must pass, got {other:?}"),
        }

        let mut tightened = func.clone();
        assert!(crate::translator::body_edit::tighten_returned_ge(
            &mut tightened
        ));
        let tightened_result = identity_query(&tightened);
        assert!(
            matches!(
                tightened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "a stricter comparison must flip the identity, got {tightened_result:?}"
        );

        let mut dropped = func;
        assert!(crate::translator::body_edit::drop_early_true_return(
            &mut dropped
        ));
        let dropped_src = quote::quote!(#dropped).to_string();
        assert!(
            !dropped_src.contains("return true"),
            "the skip must be gone, got {dropped_src}"
        );
        let dropped_result = identity_query(&dropped);
        assert!(
            matches!(
                dropped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "dropping the non-coinbase skip must flip the identity, got {dropped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod witness_stack_null_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn null_fn() -> syn::ItemFn {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("blvm-consensus/src/witness.rs"))
            .expect("witness.rs");
        let file = syn::parse_file(&src).expect("parse witness.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "witness_stack_is_null" => Some(func),
                _ => None,
            })
            .expect("witness_stack_is_null")
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        // F_WitnessStackNullByLength: (len == 0) == result. The parameter is the stack.
        let identity = "result == (witness.len() == 0)".to_string();
        let mut function = make_function_to_verify(
            std::path::Path::new("src/witness.rs"),
            "witness_stack_is_null",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.clone(),
            expr: syn::parse_str(&identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    #[test]
    fn length_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let func = null_fn();
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "the null-stack identity must use the body");
            }
            other => panic!("unpatched null stack must pass, got {other:?}"),
        }

        let mut negated = func.clone();
        assert!(
            crate::translator::body_edit::negate_returned_is_empty(&mut negated),
            "the body returns is_empty"
        );
        let negated_result = identity_query(&negated);
        assert!(
            matches!(
                negated_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "negating emptiness must flip the identity, got {negated_result:?}"
        );

        let mut one = func;
        assert!(crate::translator::body_edit::returned_empty_becomes_len_one(&mut one));
        let one_src = quote::quote!(#one).to_string();
        assert!(
            one_src.contains("== 1"),
            "the length comparison must be 1, got {one_src}"
        );
        let one_result = identity_query(&one);
        assert!(
            matches!(
                one_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring one item must flip the identity, got {one_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod sequence_locks_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn eval_fn() -> syn::ItemFn {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("blvm-consensus/src/sequence_locks.rs"))
            .expect("sequence_locks.rs");
        let file = syn::parse_file(&src).expect("parse sequence_locks.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "evaluate_sequence_locks" => Some(func),
                _ => None,
            })
            .expect("evaluate_sequence_locks")
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        // EvaluateSequenceLocks: (min_h < 0 ∨ height > min_h) ∧ (min_t < 0 ∨ time > min_t).
        // The body compares the u64 cast. That cast is the minimum when it is active.
        let identity = "result == ((min_height < 0 || block_height > (min_height as u64)) && (min_time < 0 || block_time > (min_time as u64)))"
            .to_string();
        let mut function = make_function_to_verify(
            std::path::Path::new("src/sequence_locks.rs"),
            "evaluate_sequence_locks",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.clone(),
            expr: syn::parse_str(&identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    #[test]
    fn guards_pass_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let func = eval_fn();
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(
                    body_translated,
                    "the sequence-lock identity must use the body"
                );
            }
            other => panic!("unpatched sequence locks must pass, got {other:?}"),
        }

        let mut relaxed = func.clone();
        assert!(
            crate::translator::body_edit::relax_first_guard_le(&mut relaxed),
            "a guard uses <="
        );
        let relaxed_result = identity_query(&relaxed);
        assert!(
            matches!(
                relaxed_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "a stricter height fail must flip the identity, got {relaxed_result:?}"
        );

        let mut dropped = func;
        assert!(crate::translator::body_edit::drop_first_guard_and_left(
            &mut dropped
        ));
        let dropped_src = quote::quote!(#dropped).to_string();
        assert!(
            !dropped_src.contains("min_height >= 0 &&"),
            "the height guard must be gone, got {dropped_src}"
        );
        let dropped_result = identity_query(&dropped);
        assert!(
            matches!(
                dropped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "dropping the disabled-height guard must flip the identity, got {dropped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod bip90_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::{consensus_workspace_present, min_version_floors};
    use std::path::PathBuf;

    fn bip90_fn() -> syn::ItemFn {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("blvm-consensus/src/bip_validation.rs"))
            .expect("bip_validation.rs");
        let file = syn::parse_file(&src).expect("parse bip_validation.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "check_bip90" => Some(func),
                _ => None,
            })
            .expect("check_bip90")
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        let (bip65, bip66, bip34, _) = min_version_floors();
        let identity = format!(
            "result == (\
                !(activation.is_fork_active(ForkId::Bip34, height) && block_version < {bip34}) \
                && !(activation.is_fork_active(ForkId::Bip66, height) && block_version < {bip66}) \
                && !(activation.is_fork_active(ForkId::Bip65, height) && block_version < {bip65}))"
        );
        let mut function = make_function_to_verify(
            std::path::Path::new("src/bip_validation.rs"),
            "check_bip90",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.clone(),
            expr: syn::parse_str(&identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    #[test]
    fn floors_pass_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let func = bip90_fn();
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "the BIP90 identity must use the body");
            }
            other => panic!("unpatched BIP90 must pass, got {other:?}"),
        }

        let mut relaxed = func.clone();
        assert!(crate::translator::body_edit::relax_first_guard_lt(
            &mut relaxed
        ));
        let relaxed_result = identity_query(&relaxed);
        assert!(
            matches!(
                relaxed_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "widening the first floor must flip the identity, got {relaxed_result:?}"
        );

        let mut lowered = func;
        assert!(crate::translator::body_edit::decrement_first_guard_lt_literal(&mut lowered));
        let lowered_src = quote::quote!(#lowered).to_string();
        assert!(
            lowered_src.contains("< 1"),
            "the first floor must drop by one, got {lowered_src}"
        );
        let lowered_result = identity_query(&lowered);
        assert!(
            matches!(
                lowered_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "lowering the first floor must flip the identity, got {lowered_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod stripped_size_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::{consensus_workspace_present, stripped_size_rejected};
    use std::path::PathBuf;

    fn stripped_fn() -> syn::ItemFn {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("blvm-consensus/src/bip_validation.rs"))
            .expect("bip_validation.rs");
        let file = syn::parse_file(&src).expect("parse bip_validation.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "check_bip54_tx_stripped_size" => {
                    Some(func)
                }
                _ => None,
            })
            .expect("check_bip54_tx_stripped_size")
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        let rejected = stripped_size_rejected();
        let identity =
            format!("result == (is_coinbase(tx) || calculate_transaction_size(tx) != {rejected})");
        let mut function = make_function_to_verify(
            std::path::Path::new("src/bip_validation.rs"),
            "check_bip54_tx_stripped_size",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.clone(),
            expr: syn::parse_str(&identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    #[test]
    fn disjunction_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let func = stripped_fn();
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(
                    body_translated,
                    "the stripped-size identity must use the body"
                );
            }
            other => panic!("unpatched stripped size must pass, got {other:?}"),
        }

        let mut dropped = func.clone();
        assert!(crate::translator::body_edit::drop_returned_or_left(
            &mut dropped
        ));
        let dropped_src = quote::quote!(#dropped).to_string();
        assert!(
            !dropped_src.contains("is_coinbase"),
            "the coinbase disjunct must be gone, got {dropped_src}"
        );
        let dropped_result = identity_query(&dropped);
        assert!(
            matches!(
                dropped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "dropping the coinbase disjunct must flip the identity, got {dropped_result:?}"
        );

        let mut flipped = func;
        assert!(crate::translator::body_edit::flip_nested_neq(&mut flipped));
        let flipped_src = quote::quote!(#flipped).to_string();
        assert!(
            flipped_src.contains("== 64"),
            "the size test must become equality, got {flipped_src}"
        );
        let flipped_result = identity_query(&flipped);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "turning the size test into equality must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod bip66_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn bip66_fn() -> syn::ItemFn {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("blvm-consensus/src/bip_validation.rs"))
            .expect("bip_validation.rs");
        let file = syn::parse_file(&src).expect("parse bip_validation.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "check_bip66" => Some(func),
                _ => None,
            })
            .expect("check_bip66")
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        let identity = "result == (!activation.is_fork_active(ForkId::Bip66, height) || is_strict_der(signature))";
        let mut function = make_function_to_verify(
            std::path::Path::new("src/bip_validation.rs"),
            "check_bip66",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.to_string(),
            expr: syn::parse_str(identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    #[test]
    fn gate_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let func = bip66_fn();
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "the BIP66 identity must use the body");
            }
            other => panic!("unpatched BIP66 must pass, got {other:?}"),
        }

        let mut flipped = func.clone();
        assert!(crate::translator::body_edit::flip_early_ok_true(
            &mut flipped
        ));
        let flipped_src = quote::quote!(#flipped).to_string();
        assert!(
            flipped_src.contains("Ok (false)"),
            "the inactive arm must return false, got {flipped_src}"
        );
        let flipped_result = identity_query(&flipped);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "returning false before activation must flip the identity, got {flipped_result:?}"
        );

        let mut dropped = func;
        assert!(crate::translator::body_edit::drop_early_ok_true(
            &mut dropped
        ));
        let dropped_src = quote::quote!(#dropped).to_string();
        assert!(
            !dropped_src.contains("return Ok"),
            "the inactive arm must be gone, got {dropped_src}"
        );
        let dropped_result = identity_query(&dropped);
        assert!(
            matches!(
                dropped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "dropping the inactive arm must flip the identity, got {dropped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod strict_der_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn der_fn() -> syn::ItemFn {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("blvm-consensus/src/bip_validation.rs"))
            .expect("bip_validation.rs");
        let file = syn::parse_file(&src).expect("parse bip_validation.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "is_strict_der" => Some(func),
                _ => None,
            })
            .expect("is_strict_der")
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        // PROTOCOL.md IsStrictDER: length 9..=73, tag 0x30, length byte n-3,
        // both integers tagged 0x02, neither empty, lengths sum to n, neither
        // high bit set, and no unnecessary leading zero.
        let identity = "result == (\
            signature.len() >= 9 && signature.len() <= 73 \
            && signature[0] == 0x30 \
            && signature[1] == (signature.len() - 3) as u8 \
            && signature[2] == 0x02 \
            && (signature[3] as usize) != 0 \
            && (5 + (signature[3] as usize)) < signature.len() \
            && signature[(signature[3] as usize) + 4] == 0x02 \
            && (signature[5 + (signature[3] as usize)] as usize) != 0 \
            && ((signature[3] as usize) + (signature[5 + (signature[3] as usize)] as usize) + 7) == signature.len() \
            && (signature[4] & 0x80) == 0 \
            && (signature[(signature[3] as usize) + 6] & 0x80) == 0 \
            && !((signature[3] as usize) > 1 && signature[4] == 0x00 && (signature[5] & 0x80) == 0) \
            && !((signature[5 + (signature[3] as usize)] as usize) > 1 \
                && signature[(signature[3] as usize) + 6] == 0x00 \
                && (signature[(signature[3] as usize) + 7] & 0x80) == 0))";
        let mut function = make_function_to_verify(
            std::path::Path::new("src/bip_validation.rs"),
            "is_strict_der",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.to_string(),
            expr: syn::parse_str(identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    #[test]
    fn encoding_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let func = der_fn();
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "the DER identity must use the body");
            }
            other => panic!("unpatched strict DER must pass, got {other:?}"),
        }

        let mut widened = func.clone();
        assert!(crate::translator::body_edit::increment_first_guard_gt_literal(&mut widened));
        let widened_src = quote::quote!(#widened).to_string();
        assert!(
            widened_src.contains("> 74"),
            "the length cap must rise by one, got {widened_src}"
        );
        let widened_result = identity_query(&widened);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the length cap must flip the identity, got {widened_result:?}"
        );

        let mut tagged = func;
        assert!(crate::translator::body_edit::flip_first_guard_neq(
            &mut tagged
        ));
        let tagged_src = quote::quote!(#tagged).to_string();
        assert!(
            tagged_src.contains("signature [0] == 0x30"),
            "the compound tag must be required to differ, got {tagged_src}"
        );
        let tagged_result = identity_query(&tagged);
        assert!(
            matches!(
                tagged_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "rejecting the compound tag must flip the identity, got {tagged_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod cast_to_bool_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn cast_fn() -> syn::ItemFn {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("blvm-consensus/src/script/stack.rs"))
            .expect("stack.rs");
        let file = syn::parse_file(&src).expect("parse stack.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "cast_to_bool" => Some(func),
                _ => None,
            })
            .expect("cast_to_bool")
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        // PROTOCOL.md F_CastToBoolSummary: some byte before the last is nonzero,
        // or the last byte is neither 0 nor 0x80. The loop returns false only
        // for that negative zero, and only at the last index.
        let identity = "result == {\
            for i in 0..v.len() {\
                if v[i] != 0 {\
                    if i == v.len() - 1 && v[i] == 0x80 {\
                        return false;\
                    }\
                    return true;\
                }\
            }\
            false\
        }";
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/stack.rs"),
            "cast_to_bool",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.to_string(),
            expr: syn::parse_str(identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    #[test]
    fn negative_zero_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let func = cast_fn();
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "the cast identity must use the body");
            }
            other => panic!("unpatched cast to bool must pass, got {other:?}"),
        }

        let mut raised = func.clone();
        assert!(crate::translator::body_edit::increment_eq_lit_in_for(
            &mut raised
        ));
        let raised_src = quote::quote!(#raised).to_string();
        assert!(
            raised_src.contains("== 129"),
            "the negative-zero byte must rise by one, got {raised_src}"
        );
        let raised_result = identity_query(&raised);
        assert!(
            matches!(
                raised_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the negative-zero byte must flip the identity, got {raised_result:?}"
        );

        let mut dropped = func;
        assert!(crate::translator::body_edit::eq_lit_in_for_becomes_false(
            &mut dropped
        ));
        let dropped_src = quote::quote!(#dropped).to_string();
        assert!(
            dropped_src.contains("&& false"),
            "the negative-zero test must be gone, got {dropped_src}"
        );
        let dropped_result = identity_query(&dropped);
        assert!(
            matches!(
                dropped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "dropping the negative-zero test must flip the identity, got {dropped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod bip54_coinbase_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn coinbase_fn() -> syn::ItemFn {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("blvm-consensus/src/bip_validation.rs"))
            .expect("bip_validation.rs");
        let file = syn::parse_file(&src).expect("parse bip_validation.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "check_bip54_coinbase" => Some(func),
                _ => None,
            })
            .expect("check_bip54_coinbase")
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        // PROTOCOL.md §5.4.9: coinbase lockTime is height - 1, and the first
        // input's sequence is not 0xffffffff. An empty input list has no sequence.
        let identity = "result == (coinbase.lock_time == height.saturating_sub(1) \
            && !coinbase.inputs.is_empty() \
            && coinbase.inputs[0].sequence != 0xffff_ffff)";
        let mut function = make_function_to_verify(
            std::path::Path::new("src/bip_validation.rs"),
            "check_bip54_coinbase",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.to_string(),
            expr: syn::parse_str(identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    #[test]
    fn lock_and_sequence_pass_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let func = coinbase_fn();
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "the coinbase identity must use the body");
            }
            other => panic!("unpatched BIP54 coinbase must pass, got {other:?}"),
        }

        let mut shifted = func.clone();
        assert!(crate::translator::body_edit::increment_saturating_sub_lit(
            &mut shifted
        ));
        let shifted_src = quote::quote!(#shifted).to_string();
        assert!(
            shifted_src.contains("saturating_sub (2)"),
            "the lock time must be height minus two, got {shifted_src}"
        );
        let shifted_result = identity_query(&shifted);
        assert!(
            matches!(
                shifted_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "shifting the lock time must flip the identity, got {shifted_result:?}"
        );

        let mut cleared = func;
        assert!(crate::translator::body_edit::zero_eq_lit(&mut cleared));
        let cleared_src = quote::quote!(#cleared).to_string();
        assert!(
            cleared_src.contains("sequence == 0"),
            "the final sequence must become zero, got {cleared_src}"
        );
        let cleared_result = identity_query(&cleared);
        assert!(
            matches!(
                cleared_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "accepting sequence zero must flip the identity, got {cleared_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod prev_block_hash_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn prev_fn() -> syn::ItemFn {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("blvm-consensus/src/block/header.rs"))
            .expect("header.rs");
        let file = syn::parse_file(&src).expect("parse header.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "validate_prev_block_hash" => Some(func),
                _ => None,
            })
            .expect("validate_prev_block_hash")
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        // PROTOCOL.md §5.3.1: child.prev_block_hash = BlockHeaderHash(parent).
        let identity = "result == (child.prev_block_hash == block_header_hash(parent))";
        let mut function = make_function_to_verify(
            std::path::Path::new("src/block/header.rs"),
            "validate_prev_block_hash",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.to_string(),
            expr: syn::parse_str(identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    #[test]
    fn equality_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let func = prev_fn();
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(
                    body_translated,
                    "the parent-hash identity must use the body"
                );
            }
            other => panic!("unpatched parent hash must pass, got {other:?}"),
        }

        let mut flipped = func.clone();
        assert!(crate::translator::body_edit::flip_returned_eq(&mut flipped));
        let flipped_src = quote::quote!(#flipped).to_string();
        assert!(
            flipped_src.contains("!="),
            "the comparison must become inequality, got {flipped_src}"
        );
        let flipped_result = identity_query(&flipped);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "flipping equality must flip the identity, got {flipped_result:?}"
        );

        let mut swapped = func;
        assert!(crate::translator::body_edit::swap_returned_call_param(
            &mut swapped
        ));
        let swapped_src = quote::quote!(#swapped).to_string();
        assert!(
            swapped_src.contains("block_header_hash (child)"),
            "the hash must be of the child, got {swapped_src}"
        );
        let swapped_result = identity_query(&swapped);
        assert!(
            matches!(
                swapped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "hashing the child must flip the identity, got {swapped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod final_tx_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn final_fn() -> syn::ItemFn {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("blvm-consensus/src/mempool.rs"))
            .expect("mempool.rs");
        let file = syn::parse_file(&src).expect("parse mempool.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "is_final_tx" => Some(func),
                _ => None,
            })
            .expect("is_final_tx")
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        // CheckFinalTxAtTip: lock time 0 is final, a height or time lock that has
        // passed is final, and so is every input sequence being final.
        let identity = "result == (tx.lock_time == 0 || (if (tx.lock_time as u32) < LOCKTIME_THRESHOLD { (tx.lock_time as Natural) < height } else { (tx.lock_time as Natural) < block_time }) || { for input in &tx.inputs { if (input.sequence as u32) != SEQUENCE_FINAL { return false; } } true })";
        let mut function = make_function_to_verify(
            std::path::Path::new("src/mempool.rs"),
            "is_final_tx",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.to_string(),
            expr: syn::parse_str(identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    #[test]
    fn lock_and_sequence_pass_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let func = final_fn();
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "finality must use the body");
            }
            other => panic!("unpatched finality must pass, got {other:?}"),
        }

        let mut shifted = func.clone();
        assert!(crate::translator::body_edit::increment_first_eq_lit(
            &mut shifted
        ));
        let shifted_src = quote::quote!(#shifted).to_string();
        assert!(
            shifted_src.contains("== 1"),
            "lock time zero must become one, got {shifted_src}"
        );
        let shifted_result = identity_query(&shifted);
        assert!(
            matches!(
                shifted_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising lock time zero must flip the identity, got {shifted_result:?}"
        );

        let mut relaxed = func;
        assert!(crate::translator::body_edit::relax_first_lt(&mut relaxed));
        let relaxed_src = quote::quote!(#relaxed).to_string();
        assert!(
            relaxed_src.contains("<= LOCKTIME_THRESHOLD"),
            "the threshold comparison must relax, got {relaxed_src}"
        );
        let relaxed_result = identity_query(&relaxed);
        assert!(
            matches!(
                relaxed_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "relaxing the threshold must flip the identity, got {relaxed_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod bip54_timewarp_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn timewarp_fn() -> syn::ItemFn {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("blvm-consensus/src/bip_validation.rs"))
            .expect("bip_validation.rs");
        let file = syn::parse_file(&src).expect("parse bip_validation.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "check_bip54_timewarp" => Some(func),
                _ => None,
            })
            .expect("check_bip54_timewarp")
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        // PROTOCOL.md §5.4.9: at the last block of a period the timestamp is at least
        // the first block of the period; at the first block it is at least the previous
        // timestamp minus 7200. Off those boundaries, and before activation, the check passes.
        // A missing boundary on those heights fails.
        let identity = "result == (!bip54_active || ((height % 2016) != 2015 && (height % 2016) != 0) || ((height % 2016) == 2015 && boundary_is_some && header.timestamp >= boundary.timestamp_n_minus_2015) || ((height % 2016) == 0 && boundary_is_some && header.timestamp >= boundary.timestamp_n_minus_1.saturating_sub(7200)))";
        let mut function = make_function_to_verify(
            std::path::Path::new("src/bip_validation.rs"),
            "check_bip54_timewarp",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.to_string(),
            expr: syn::parse_str(identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    #[test]
    fn bounds_pass_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let func = timewarp_fn();
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "timewarp must use the body");
            }
            other => panic!("unpatched timewarp must pass, got {other:?}"),
        }

        let mut tightened = func.clone();
        assert!(crate::translator::body_edit::tighten_first_ge(
            &mut tightened
        ));
        let tightened_src = quote::quote!(#tightened).to_string();
        assert!(
            tightened_src.contains("timestamp > b . timestamp_n_minus_2015"),
            "the period-start comparison must tighten, got {tightened_src}"
        );
        let tightened_result = identity_query(&tightened);
        assert!(
            matches!(
                tightened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "tightening the period-start bound must flip the identity, got {tightened_result:?}"
        );

        let mut halved = func;
        assert!(crate::translator::body_edit::halve_const_item(&mut halved));
        let halved_src = quote::quote!(#halved).to_string();
        assert!(
            halved_src.contains("3600"),
            "two hours must become one hour, got {halved_src}"
        );
        let halved_result = identity_query(&halved);
        assert!(
            matches!(
                halved_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "halving the grace must flip the identity, got {halved_result:?}"
        );
    }
}

mod header_mtp_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn header_fn() -> syn::ItemFn {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("blvm-consensus/src/block/header.rs"))
            .expect("header.rs");
        let file = syn::parse_file(&src).expect("parse header.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "validate_block_header" => Some(func),
                _ => None,
            })
            .expect("validate_block_header")
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        // PROTOCOL.md H05: a header timestamp is past the median of the previous
        // eleven blocks. With no time context the check does not reject.
        let identity = "result == false || !time_context_is_some || header.timestamp > time_context.median_time_past";
        let mut function = make_function_to_verify(
            std::path::Path::new("src/block/header.rs"),
            "validate_block_header",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.to_string(),
            expr: syn::parse_str(identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    #[test]
    fn median_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let func = header_fn();
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "median time must use the body");
            }
            other => panic!("unpatched median time must pass, got {other:?}"),
        }

        let mut tightened = func.clone();
        assert!(crate::translator::body_edit::tighten_first_le(
            &mut tightened
        ));
        let tightened_src = quote::quote!(#tightened).to_string();
        assert!(
            tightened_src.contains("timestamp < ctx . median_time_past"),
            "the median bound must tighten, got {tightened_src}"
        );
        let tightened_result = identity_query(&tightened);
        assert!(
            matches!(
                tightened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "tightening the median bound must flip the identity, got {tightened_result:?}"
        );

        let mut dropped = func;
        assert!(crate::translator::body_edit::false_first_le(&mut dropped));
        let dropped_src = quote::quote!(#dropped).to_string();
        assert!(
            !dropped_src.contains("<="),
            "the median comparison must become false, got {dropped_src}"
        );
        let dropped_result = identity_query(&dropped);
        assert!(
            matches!(
                dropped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "dropping the median comparison must flip the identity, got {dropped_result:?}"
        );
    }
}

mod coinbase_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use crate::translator::production_lock::retain_production;
    use std::path::PathBuf;

    fn coinbase_fn() -> syn::ItemFn {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("blvm-consensus/src/transaction.rs"))
            .expect("transaction.rs");
        let file = syn::parse_file(&src).expect("parse transaction.rs");
        let func = file
            .items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "is_coinbase" => Some(func),
                _ => None,
            })
            .expect("is_coinbase");
        retain_production(func)
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        let identity = "result == (tx.inputs.len() == 1 && tx.inputs[0].prevout.hash == 0 && tx.inputs[0].prevout.index == 0xffffffff)";
        let mut function = make_function_to_verify(
            std::path::Path::new("src/transaction.rs"),
            "is_coinbase",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.to_string(),
            expr: syn::parse_str(identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    #[test]
    fn coinbase_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let func = coinbase_fn();
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "coinbase must use the body");
            }
            other => panic!("unpatched coinbase must pass, got {other:?}"),
        }

        let boundary_src = quote::quote!(#func)
            .to_string()
            .replace("0xffffffff", "0xfffffffe");
        let boundary: syn::ItemFn = syn::parse_str(&boundary_src).expect("boundary");
        let boundary_result = identity_query(&boundary);
        assert!(
            matches!(
                boundary_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "changing the null index must flip the identity, got {boundary_result:?}"
        );

        let predicate_src = quote::quote!(#func)
            .to_string()
            .replace("is_zero_hash", "not_zero_hash");
        let predicate: syn::ItemFn = syn::parse_str(&predicate_src).expect("predicate");
        let predicate_result = identity_query(&predicate);
        assert!(
            matches!(
                predicate_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "renaming the zero-hash check must flip the identity, got {predicate_result:?}"
        );
    }
}

mod bip54_active_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn active_fn() -> syn::ItemFn {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("blvm-consensus/src/bip_validation.rs"))
            .expect("bip_validation.rs");
        let file = syn::parse_file(&src).expect("parse bip_validation.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "is_bip54_active_at" => Some(func),
                _ => None,
            })
            .expect("is_bip54_active_at")
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        let identity = "result == (height >= match activation_override { \
            Some(h) => h, \
            None => match network { \
                crate::types::Network::Mainnet => crate::constants::BIP54_ACTIVATION_MAINNET, \
                crate::types::Network::Testnet => crate::constants::BIP54_ACTIVATION_TESTNET, \
                crate::types::Network::Regtest \
                | crate::types::Network::Signet \
                | crate::types::Network::Testnet4 => crate::constants::BIP54_ACTIVATION_REGTEST, \
            }, \
        })";
        let mut function = make_function_to_verify(
            std::path::Path::new("src/bip_validation.rs"),
            "is_bip54_active_at",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.to_string(),
            expr: syn::parse_str(identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    #[test]
    fn bip54_active_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let func = active_fn();
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "BIP54 activation must use the body");
            }
            other => panic!("unpatched BIP54 activation must pass, got {other:?}"),
        }

        let boundary_src = quote::quote!(#func)
            .to_string()
            .replace("height >= activation", "height > activation");
        assert!(
            boundary_src.contains("height > activation"),
            "the comparison must tighten, got {boundary_src}"
        );
        let boundary: syn::ItemFn = syn::parse_str(&boundary_src).expect("boundary");
        let boundary_result = identity_query(&boundary);
        assert!(
            matches!(
                boundary_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "tightening the activation bound must flip the identity, got {boundary_result:?}"
        );

        let predicate_src = quote::quote!(#func)
            .to_string()
            .replace("height >= activation", "height == activation");
        let predicate: syn::ItemFn = syn::parse_str(&predicate_src).expect("predicate");
        let predicate_result = identity_query(&predicate);
        assert!(
            matches!(
                predicate_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "changing the activation bound to equality must flip the identity, got {predicate_result:?}"
        );
    }
}

mod header_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn header_fn() -> syn::ItemFn {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("blvm-consensus/src/block/header.rs"))
            .expect("header.rs");
        let file = syn::parse_file(&src).expect("parse header.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "validate_block_header" => Some(func),
                _ => None,
            })
            .expect("validate_block_header")
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        let identity = "result == (header.version >= 1 && header.timestamp != 0 && header.bits != 0 && header.merkle_root != 0 && (!time_context_is_some || header.timestamp <= time_context.network_time.saturating_add(7200)) && (!time_context_is_some || header.timestamp > time_context.median_time_past))";
        let mut function = make_function_to_verify(
            std::path::Path::new("src/block/header.rs"),
            "validate_block_header",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.to_string(),
            expr: syn::parse_str(identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    #[test]
    fn header_passes_and_both_version_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let func = header_fn();
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "the header check must use the body");
            }
            other => panic!("unpatched header check must pass, got {other:?}"),
        }

        let boundary_src = quote::quote!(#func)
            .to_string()
            .replace("version < 1", "version < 0");
        assert!(
            boundary_src.contains("version < 0"),
            "the version floor must drop, got {boundary_src}"
        );
        let boundary: syn::ItemFn = syn::parse_str(&boundary_src).expect("boundary");
        let boundary_result = identity_query(&boundary);
        assert!(
            matches!(
                boundary_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "dropping the version floor must flip the identity, got {boundary_result:?}"
        );

        let predicate_src = quote::quote!(#func)
            .to_string()
            .replace("version < 1", "version <= 1");
        let predicate: syn::ItemFn = syn::parse_str(&predicate_src).expect("predicate");
        let predicate_result = identity_query(&predicate);
        assert!(
            matches!(
                predicate_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "rejecting version 1 must flip the identity, got {predicate_result:?}"
        );
    }

    #[test]
    fn header_fields_edits_flip_the_same_body() {
        if !consensus_workspace_present() {
            return;
        }
        let func = header_fn();
        let timestamp_src = quote::quote!(#func)
            .to_string()
            .replace("timestamp == 0", "timestamp == 1");
        assert!(
            timestamp_src.contains("timestamp == 1"),
            "the zero timestamp reject must move, got {timestamp_src}"
        );
        let timestamp: syn::ItemFn = syn::parse_str(&timestamp_src).expect("timestamp");
        let timestamp_result = identity_query(&timestamp);
        assert!(
            matches!(
                timestamp_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "rejecting timestamp 1 must flip the identity, got {timestamp_result:?}"
        );

        let bits_src = quote::quote!(#func)
            .to_string()
            .replace("bits == 0", "bits == 1");
        let bits: syn::ItemFn = syn::parse_str(&bits_src).expect("bits");
        let bits_result = identity_query(&bits);
        assert!(
            matches!(
                bits_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "rejecting bits 1 must flip the identity, got {bits_result:?}"
        );
    }
}

mod witness_commitment_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn commitment_fn() -> syn::ItemFn {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src =
            std::fs::read_to_string(root.join("blvm-consensus/src/segwit.rs")).expect("segwit.rs");
        let file = syn::parse_file(&src).expect("parse segwit.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "extract_witness_commitment" => Some(func),
                _ => None,
            })
            .expect("extract_witness_commitment")
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        // 0xaa, 0x21, 0xa9, 0xed packed least-significant byte first.
        let magic = 0xaa_i64 + 0x21_i64 * 256 + 0xa9_i64 * 256 * 256 + 0xed_i64 * 256 * 256 * 256;
        let identity = format!(
            "result == if script.len() >= 38 && script[0] == 0x6a && script[1] == 0x24 && script[2..6] == {magic} {{ script[6..38] }} else {{ -1 }}"
        );
        let mut function = make_function_to_verify(
            std::path::Path::new("src/segwit.rs"),
            "extract_witness_commitment",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.clone(),
            expr: syn::parse_str(&identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    #[test]
    fn commitment_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let func = commitment_fn();
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "the commitment check must use the body");
            }
            other => panic!("unpatched commitment must pass, got {other:?}"),
        }

        let magic_src = quote::quote!(#func).to_string().replace("0xaa", "0xab");
        assert!(
            magic_src.contains("0xab"),
            "the magic byte must change, got {magic_src}"
        );
        let magic: syn::ItemFn = syn::parse_str(&magic_src).expect("magic");
        let magic_result = identity_query(&magic);
        assert!(
            matches!(
                magic_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "changing the magic byte must flip the identity, got {magic_result:?}"
        );

        let slice_src = quote::quote!(#func)
            .to_string()
            .replace("6 .. 38", "7 .. 39")
            .replace("6..38", "7..39");
        assert!(
            slice_src.contains("7 .. 39") || slice_src.contains("7..39"),
            "the commitment slice must move, got {slice_src}"
        );
        let slice: syn::ItemFn = syn::parse_str(&slice_src).expect("slice");
        let slice_result = identity_query(&slice);
        assert!(
            matches!(
                slice_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "moving the commitment slice must flip the identity, got {slice_result:?}"
        );
    }
}

mod signet_image_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn pow256(bytes: u32) -> String {
        if bytes == 0 {
            "1".to_string()
        } else {
            std::iter::repeat_n("256", bytes as usize)
                .collect::<Vec<_>>()
                .join(" * ")
        }
    }

    fn low32(name: &str) -> String {
        format!(
            "(if {name} >= 0 {{ {name} }} else {{ {name} + {} }})",
            pow256(4)
        )
    }

    fn image_fn() -> syn::ItemFn {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src =
            std::fs::read_to_string(root.join("blvm-consensus/src/signet.rs")).expect("signet.rs");
        let file = syn::parse_file(&src).expect("parse signet.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "serialize_signet_block_data" => {
                    Some(func)
                }
                _ => None,
            })
            .expect("serialize_signet_block_data")
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        let identity = format!(
            "result == ({} + prev_hash * ({}) + signet_merkle * ({}) + ({}) * ({}))",
            low32("version"),
            pow256(4),
            pow256(36),
            low32("timestamp"),
            pow256(68)
        );
        let mut function = make_function_to_verify(
            std::path::Path::new("src/signet.rs"),
            "serialize_signet_block_data",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.clone(),
            expr: syn::parse_str(&identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    fn quoted(func: &syn::ItemFn) -> String {
        quote::quote!(#func).to_string()
    }

    #[test]
    fn signet_image_passes_and_each_edit_flips() {
        if !consensus_workspace_present() {
            return;
        }
        let func = image_fn();
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "the header image must use the body");
            }
            other => panic!("unpatched signet image must pass, got {other:?}"),
        }

        let src = quoted(&func);
        let swapped = src
            .replace("version . to_le_bytes", "VERSION_ENDIAN")
            .replace("timestamp . to_le_bytes", "version . to_le_bytes")
            .replace("VERSION_ENDIAN", "timestamp . to_le_bytes")
            .replace("version.to_le_bytes", "VERSION_ENDIAN")
            .replace("timestamp.to_le_bytes", "version.to_le_bytes")
            .replace("VERSION_ENDIAN", "timestamp.to_le_bytes");
        assert_ne!(
            swapped, src,
            "swapping version and timestamp must change the body"
        );
        let swapped: syn::ItemFn = syn::parse_str(&swapped).expect("swap");
        let swapped_result = identity_query(&swapped);
        assert!(
            matches!(
                swapped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "swapping version and timestamp must flip the identity, got {swapped_result:?}"
        );

        let endian = src
            .replacen("version . to_le_bytes", "version . to_be_bytes", 1)
            .replacen("version.to_le_bytes", "version.to_be_bytes", 1);
        assert!(
            endian.contains("to_be_bytes"),
            "version must become big-endian, got {endian}"
        );
        let endian: syn::ItemFn = syn::parse_str(&endian).expect("endian");
        let endian_result = identity_query(&endian);
        assert!(
            matches!(
                endian_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "big-endian version must flip the identity, got {endian_result:?}"
        );

        let dropped = src
            .replace("out . extend_from_slice (& version . to_le_bytes ()) ;", "")
            .replace("out.extend_from_slice(&version.to_le_bytes());", "");
        assert_ne!(
            dropped, src,
            "dropping version must change the body, got {dropped}"
        );
        let dropped: syn::ItemFn = syn::parse_str(&dropped).expect("drop");
        let dropped_result = identity_query(&dropped);
        assert!(
            matches!(
                dropped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "dropping version must flip the identity, got {dropped_result:?}"
        );
    }
}

mod header_image_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn pow256(bytes: u32) -> String {
        if bytes == 0 {
            "1".to_string()
        } else {
            std::iter::repeat_n("256", bytes as usize)
                .collect::<Vec<_>>()
                .join(" * ")
        }
    }

    fn low32(name: &str) -> String {
        format!(
            "(if {name} >= 0 {{ {name} }} else {{ {name} + {} }})",
            pow256(4)
        )
    }

    fn header_fn() -> syn::ItemFn {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("blvm-primitives/src/serialization/block.rs"))
            .expect("block.rs");
        let file = syn::parse_file(&src).expect("parse block.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "serialize_block_header" => Some(func),
                _ => None,
            })
            .expect("serialize_block_header")
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        let identity = format!(
            "result == ({} + header.prev_block_hash * ({}) + header.merkle_root * ({}) + ({}) * ({}) + ({}) * ({}) + ({}) * ({}))",
            low32("header.version"),
            pow256(4),
            pow256(36),
            low32("header.timestamp"),
            pow256(68),
            low32("header.bits"),
            pow256(72),
            low32("header.nonce"),
            pow256(76)
        );
        let mut function = make_function_to_verify(
            std::path::Path::new("src/serialization/block.rs"),
            "serialize_block_header",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.clone(),
            expr: syn::parse_str(&identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    fn quoted(func: &syn::ItemFn) -> String {
        quote::quote!(#func).to_string()
    }

    #[test]
    fn header_image_passes_and_each_edit_flips() {
        if !consensus_workspace_present() {
            return;
        }
        let func = header_fn();
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "the header image must use the body");
            }
            other => panic!("unpatched header image must pass, got {other:?}"),
        }

        let src = quoted(&func);
        let swapped = src
            .replace("header . version", "VERSION_FIELD")
            .replace("header . prev_block_hash", "header . version")
            .replace("VERSION_FIELD", "header . prev_block_hash")
            .replace("header.version", "VERSION_FIELD")
            .replace("header.prev_block_hash", "header.version")
            .replace("VERSION_FIELD", "header.prev_block_hash");
        assert_ne!(
            swapped, src,
            "swapping version and prev hash must change the body"
        );
        let swapped: syn::ItemFn = syn::parse_str(&swapped).expect("swap");
        let swapped_result = identity_query(&swapped);
        assert!(
            matches!(
                swapped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "swapping version and the previous hash must flip the identity, got {swapped_result:?}"
        );

        let endian = src
            .replacen(
                "(header . version as i32) . to_le_bytes",
                "(header . version as i32) . to_be_bytes",
                1,
            )
            .replacen(
                "(header.version as i32).to_le_bytes",
                "(header.version as i32).to_be_bytes",
                1,
            );
        assert!(
            endian.contains("to_be_bytes"),
            "version must become big-endian, got {endian}"
        );
        let endian: syn::ItemFn = syn::parse_str(&endian).expect("endian");
        let endian_result = identity_query(&endian);
        assert!(
            matches!(
                endian_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "big-endian version must flip the identity, got {endian_result:?}"
        );

        let dropped = src
            .replace(
                "result . extend_from_slice (& (header . nonce as u32) . to_le_bytes ()) ;",
                "",
            )
            .replace(
                "result.extend_from_slice(&(header.nonce as u32).to_le_bytes());",
                "",
            );
        assert_ne!(
            dropped, src,
            "dropping the nonce must change the body, got {dropped}"
        );
        let dropped: syn::ItemFn = syn::parse_str(&dropped).expect("drop");
        let dropped_result = identity_query(&dropped);
        assert!(
            matches!(
                dropped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "dropping the nonce must flip the identity, got {dropped_result:?}"
        );
    }
}

mod compact_target_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn pow256(bytes: i64) -> String {
        if bytes <= 0 {
            "1".to_string()
        } else {
            std::iter::repeat_n("256", bytes as usize)
                .collect::<Vec<_>>()
                .join(" * ")
        }
    }

    fn scale_div(mant: &str, k: &str, max_k: i64) -> String {
        let mut acc = format!("({mant} / ({}))", pow256(max_k));
        for shift in (0..max_k).rev() {
            acc = format!(
                "(if {k} == {shift} {{ {mant} / ({}) }} else {{ {acc} }})",
                pow256(shift)
            );
        }
        acc
    }

    fn scale_mul(mant: &str, k: &str, limit: i64) -> String {
        let mut acc = format!("({mant} * ({}))", pow256(limit - 1));
        for shift in (1..limit - 1).rev() {
            acc = format!(
                "(if {k} == {shift} {{ {mant} * ({}) }} else {{ {acc} }})",
                pow256(shift)
            );
        }
        acc
    }

    fn target_fn() -> syn::ItemFn {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("blvm-consensus/src/pow.rs")).expect("pow.rs");
        let file = syn::parse_file(&src).expect("parse pow.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "expand_target" => Some(func),
                _ => None,
            })
            .expect("expand_target")
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        let exp = "((bits / 16777216) % 256)";
        let mant = "(bits % 8388608)";
        let right = scale_div(mant, "(3 - ((bits / 16777216) % 256))", 3);
        let left = scale_mul(mant, "(((bits / 16777216) % 256) - 3)", 32);
        let err =
            format!("{exp} < 3 || {exp} > 32 || ({mant} != 0 && {exp} > 3 && ({exp} - 3) >= 32)");
        let identity = format!(
            "result_is_err == (if {err} {{ 1 }} else {{ 0 }}) && result == (if {err} {{ 0 }} else if {mant} == 0 {{ 0 }} else if {exp} <= 3 {{ {right} }} else {{ {left} }})"
        );
        let mut function = make_function_to_verify(
            std::path::Path::new("src/pow.rs"),
            "expand_target",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.clone(),
            expr: syn::parse_str(&identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 15, &[])
    }

    #[test]
    fn target_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let func = target_fn();
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "the compact target must use the body");
            }
            other => panic!("unpatched target must pass, got {other:?}"),
        }

        let src = quote::quote!(#func).to_string();
        let range = src
            .replace("3 ..= 32", "4 ..= 32")
            .replace("3..=32", "4..=32");
        assert_ne!(range, src, "the exponent floor must change, got {src}");
        let range: syn::ItemFn = syn::parse_str(&range).expect("range");
        let range_result = identity_query(&range);
        assert!(
            matches!(
                range_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the exponent floor must flip the identity, got {range_result:?}"
        );

        let mask = src
            .replace("0x007fffff", "0x00ffffff")
            .replace("8388607", "16777215");
        assert_ne!(mask, src, "the mantissa mask must change, got {src}");
        let mask: syn::ItemFn = syn::parse_str(&mask).expect("mask");
        let mask_result = identity_query(&mask);
        assert!(
            matches!(
                mask_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "widening the mantissa mask must flip the identity, got {mask_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod compress_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn compress_fn() -> syn::ItemFn {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("blvm-consensus/src/pow.rs")).expect("pow.rs");
        let file = syn::parse_file(&src).expect("parse pow.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "compress_target" => Some(func),
                _ => None,
            })
            .expect("compress_target")
    }

    fn identity_query(func: &syn::ItemFn) -> VerificationResult {
        let identity = crate::translator::z3_translator::compress_identity_clause(
            &crate::translator::z3_translator::CompressTarget {
                param: "target".to_string(),
                zero_bits: 0x1d00_0000,
                byte: 8,
                base: 256,
                small_at: 3,
                sign_mask: 0x0080_0000,
                sign_shift: 8,
                mant_mask: 0x007f_ffff,
                exp_shift: 24,
                size_limit: 32,
            },
        );
        let mut function = make_function_to_verify(
            std::path::Path::new("src/pow.rs"),
            "compress_target",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: identity.clone(),
            expr: syn::parse_str(&identity).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn compress_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let func = compress_fn();
        match identity_query(&func) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "the compact encoding must use the body");
            }
            other => panic!("unpatched compress must pass, got {other:?}"),
        }
        let src = quote::quote!(#func).to_string();
        let sign = src
            .replace("(n_compact & 0x00800000)", "(n_compact & 0x00000000)")
            .replace("(n_compact & 8388608)", "(n_compact & 0)");
        assert_ne!(sign, src, "the sign mask must change");
        let sign: syn::ItemFn = syn::parse_str(&sign).expect("sign");
        let sign_result = identity_query(&sign);
        assert!(
            matches!(
                sign_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "clearing the sign mask must flip the identity, got {sign_result:?}"
        );
        let shift = src
            .replace("n_size_final << 24", "n_size_final << 16")
            .replace("n_size_final << 24", "n_size_final << 16");
        assert_ne!(shift, src, "the exponent shift must change");
        let shift: syn::ItemFn = syn::parse_str(&shift).expect("shift");
        let shift_result = identity_query(&shift);
        assert!(
            matches!(
                shift_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "moving the exponent must flip the identity, got {shift_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod sigop_limit_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn sigop_fn_from(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).expect("parse bip_validation.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "check_bip54_sigop_limit" => Some(func),
                _ => None,
            })
            .expect("check_bip54_sigop_limit")
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/bip_validation.rs"),
            "check_bip54_sigop_limit",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    #[test]
    fn sigop_limit_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../blvm-consensus/src/bip_validation.rs");
        let src = std::fs::read_to_string(&path).expect("bip_validation.rs");
        let func = sigop_fn_from(&src);
        let spec_cap = crate::parser::spec_expr::bip54_sigop_cap();
        let source_cap =
            crate::translator::z3_translator::bip54_sigop_cap_u64().expect("source cap") as u64;
        assert_eq!(
            spec_cap, source_cap,
            "the spec cap and the source cap differ"
        );
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "the sigop cap must use the body");
            }
            other => panic!("unpatched sigop limit must pass, got {other:?}"),
        }
        let ge = src.replace("sigop_count > ", "sigop_count >= ");
        assert_ne!(ge, src, "the comparison must change");
        let ge_result = identity_query(&sigop_fn_from(&ge), &clause);
        assert!(
            matches!(
                ge_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "relaxing the cap to >= must flip the identity, got {ge_result:?}"
        );
        let coin = src.replace("!bip54_active || is_coinbase(tx)", "!bip54_active");
        assert_ne!(coin, src, "the coinbase skip must change");
        let coin_result = identity_query(&sigop_fn_from(&coin), &clause);
        assert!(
            matches!(
                coin_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "dropping the coinbase skip must flip the identity, got {coin_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod median_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn median_fn_from(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).expect("parse bip113.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "get_median_time_past" => Some(func),
                _ => None,
            })
            .expect("get_median_time_past")
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/bip113.rs"),
            "get_median_time_past",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 15, &[])
    }

    #[test]
    fn median_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/bip113.rs");
        let src = std::fs::read_to_string(&path).expect("bip113.rs");
        let func = median_fn_from(&src);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "the median must use the body");
            }
            other => panic!("unpatched median must pass, got {other:?}"),
        }
        let lower = src.replace("/ 2]", "/ 2 - 1]");
        assert_ne!(lower, src, "the median index must change");
        let lower_result = identity_query(&median_fn_from(&lower), &clause);
        assert!(
            matches!(
                lower_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "lowering the index must flip the identity, got {lower_result:?}"
        );
        let unsorted = src.replace("timestamps.sort_unstable();", "");
        assert_ne!(unsorted, src, "the sort must change");
        let unsorted_result = identity_query(&median_fn_from(&unsorted), &clause);
        assert!(
            matches!(
                unsorted_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "dropping the sort must flip the identity, got {unsorted_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod annex_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::{annex_rule, consensus_workspace_present};
    use std::path::PathBuf;

    fn annex_fn_from(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).expect("parse taproot.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "strip_taproot_annex" => Some(func),
                _ => None,
            })
            .expect("strip_taproot_annex")
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/taproot.rs"),
            "strip_taproot_annex",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    #[test]
    fn annex_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let (tag, min) = annex_rule();
        assert_eq!(tag, 0x50, "the spec annex tag");
        assert_eq!(min, 2, "the spec annex length");
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/taproot.rs");
        let src = std::fs::read_to_string(&path).expect("taproot.rs");
        assert!(
            src.contains("TAPROOT_ANNEX_TAG: u8 = 0x50"),
            "the source tag is the spec tag"
        );
        let func = annex_fn_from(&src);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "the annex strip must use the body");
            }
            other => panic!("unpatched annex strip must pass, got {other:?}"),
        }
        let longer = src.replace("witness.len() >= 2", "witness.len() >= 3");
        assert_ne!(longer, src, "the stack length must change");
        let longer_result = identity_query(&annex_fn_from(&longer), &clause);
        assert!(
            matches!(
                longer_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the stack length must flip the identity, got {longer_result:?}"
        );
        // The tag lives in the const the census edits. The comparison names that const,
        // so the edited value has to appear in the body the solver sees.
        let retagged = src
            .replace(
                "TAPROOT_ANNEX_TAG: u8 = 0x50",
                "TAPROOT_ANNEX_TAG: u8 = 0x51",
            )
            .replace("b == TAPROOT_ANNEX_TAG", "b == 0x51");
        assert_ne!(retagged, src, "the annex tag must change");
        let retagged_result = identity_query(&annex_fn_from(&retagged), &clause);
        assert!(
            matches!(
                retagged_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the tag must flip the identity, got {retagged_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod block_proof_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn proof_fn_from(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).expect("parse pow.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "get_block_proof" => Some(func),
                _ => None,
            })
            .expect("get_block_proof")
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/pow.rs"),
            "get_block_proof",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 20, &[])
    }

    #[test]
    fn block_proof_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/pow.rs");
        let src = std::fs::read_to_string(&path).expect("pow.rs");
        let func = proof_fn_from(&src);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "the block proof must use the body");
            }
            other => panic!("unpatched block proof must pass, got {other:?}"),
        }
        let one = src.replace("return Ok(U256::zero());", "return Ok(U256::one());");
        assert_ne!(one, src, "the zero target must change");
        let one_result = identity_query(&proof_fn_from(&one), &clause);
        assert!(
            matches!(
                one_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "a zero target returning one must flip the identity, got {one_result:?}"
        );
        let bare = src.replace(
            "Ok(quotient\n        .checked_add(U256::one())\n        .unwrap_or(U256([u64::MAX; 4])))",
            "Ok(quotient)",
        );
        assert_ne!(bare, src, "the trailing one must change");
        let bare_result = identity_query(&proof_fn_from(&bare), &clause);
        assert!(
            matches!(
                bare_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "dropping the trailing one must flip the identity, got {bare_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod bip34_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn bip34_fn_from(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).expect("parse bip_validation.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "check_bip34" => Some(func),
                _ => None,
            })
            .expect("check_bip34")
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/bip_validation.rs"),
            "check_bip34",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 15, &[])
    }

    #[test]
    fn bip34_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../blvm-consensus/src/bip_validation.rs");
        let src = std::fs::read_to_string(&path).expect("bip_validation.rs");
        let func = bip34_fn_from(&src);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "BIP34 must use the body");
            }
            other => panic!("unpatched BIP34 must pass, got {other:?}"),
        }
        let flipped = src.replace(
            "script_sig_starts_with_height(&tx.inputs[0].script_sig, height)",
            "false && script_sig_starts_with_height(&tx.inputs[0].script_sig, height)",
        );
        assert_ne!(flipped, src, "the height prefix must change");
        let flipped_result = identity_query(&bip34_fn_from(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "inverting the height prefix must flip the identity, got {flipped_result:?}"
        );
        let open = src.replace("!activation.is_fork_active(ForkId::Bip34, height)", "false");
        assert_ne!(open, src, "the activation skip must change");
        let open_result = identity_query(&bip34_fn_from(&open), &clause);
        assert!(
            matches!(
                open_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "dropping the activation skip must flip the identity, got {open_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod bip30_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn bip30_fn_from(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).expect("parse bip_validation.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "check_bip30" => Some(func),
                _ => None,
            })
            .expect("check_bip30")
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/bip_validation.rs"),
            "check_bip30",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 20, &[])
    }

    #[test]
    fn bip30_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../blvm-consensus/src/bip_validation.rs");
        let src = std::fs::read_to_string(&path).expect("bip_validation.rs");
        let func = bip30_fn_from(&src);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "BIP30 must use the body");
            }
            other => panic!("unpatched BIP30 must pass, got {other:?}"),
        }
        let flipped = src.replace("c > 0", "c > 1");
        assert_ne!(flipped, src, "the duplicate count must change");
        let flipped_result = identity_query(&bip30_fn_from(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the duplicate count must flip the identity, got {flipped_result:?}"
        );
        let open = src.replace("!activation.is_fork_active(ForkId::Bip30, height)", "false");
        assert_ne!(open, src, "the activation skip must change");
        let open_result = identity_query(&bip30_fn_from(&open), &clause);
        assert!(
            matches!(
                open_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "dropping the activation skip must flip the identity, got {open_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod script_flags_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn flags_fn_from(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).expect("parse script_cache.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "get_block_script_verify_flags_core" => {
                    Some(func)
                }
                _ => None,
            })
            .expect("get_block_script_verify_flags_core")
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/block/script_cache.rs"),
            "get_block_script_verify_flags_core",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 20, &[])
    }

    #[test]
    fn script_flags_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../blvm-consensus/src/block/script_cache.rs");
        let src = std::fs::read_to_string(&path).expect("script_cache.rs");
        let func = flags_fn_from(&src);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "script flags must use the body");
            }
            other => panic!("unpatched script flags must pass, got {other:?}"),
        }
        let dropped = src.replace("flags = v;", "");
        assert_ne!(dropped, src, "the exception replacement must change");
        let dropped_result = identity_query(&flags_fn_from(&dropped), &clause);
        assert!(
            matches!(
                dropped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "dropping the exception replacement must flip the identity, got {dropped_result:?}"
        );
        let first = src.find("flags |= 0x04").expect("DERSIG bit");
        let second = src[first + "flags |= 0x04".len()..]
            .find("flags |= 0x04")
            .expect("core DERSIG bit")
            + first
            + "flags |= 0x04".len();
        let mut widened = src.clone();
        widened.replace_range(second..second + "flags |= 0x04".len(), "flags |= 0x08");
        assert_ne!(widened, src, "the DERSIG bit must change");
        let widened_result = identity_query(&flags_fn_from(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "changing the DERSIG bit must flip the identity, got {widened_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod script_num_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn decode_fn_from(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).expect("parse script/mod.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "script_num_decode" => Some(func),
                _ => None,
            })
            .expect("script_num_decode")
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "script_num_decode",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 20, &[])
    }

    #[test]
    fn script_num_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let src = std::fs::read_to_string(&path).expect("script/mod.rs");
        let func = decode_fn_from(&src);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "script number decode must use the body");
            }
            other => panic!("unpatched script number decode must pass, got {other:?}"),
        }
        let emptied = {
            let start = src.find("pub(crate) fn script_num_decode").expect("fn");
            let at = src[start..].find("data.is_empty()").expect("empty check") + start;
            let mut out = src.clone();
            out.replace_range(at..at + "data.is_empty()".len(), "data.len() > usize::MAX");
            out
        };
        assert_ne!(emptied, src, "the empty check must change");
        let emptied_result = identity_query(&decode_fn_from(&emptied), &clause);
        assert!(
            matches!(
                emptied_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "disabling the empty check must flip the identity, got {emptied_result:?}"
        );
        let masked = src.replace("if byte & 0x80 != 0", "if byte & 0x01 != 0");
        assert_ne!(masked, src, "the one-byte sign test must change");
        let masked_result = identity_query(&decode_fn_from(&masked), &clause);
        assert!(
            matches!(
                masked_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "changing the one-byte sign test must flip the identity, got {masked_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_dup_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn arm_body(src: &str) -> String {
        let mut from = 0;
        while let Some(rel) = src[from..].find("OP_DUP =>") {
            let at = from + rel;
            let rest = &src[at..];
            let brace = rest.find('{').expect("arm brace");
            let mut depth = 0i32;
            for (i, byte) in rest[brace..].bytes().enumerate() {
                if byte == b'{' {
                    depth += 1;
                } else if byte == b'}' {
                    depth -= 1;
                    if depth == 0 {
                        let inner = rest[brace + 1..brace + i].to_string();
                        if inner.contains("stack.last().cloned()")
                            && inner.contains("stack.push(item)")
                            && !inner.contains("cast_to_bool")
                        {
                            return inner;
                        }
                        break;
                    }
                }
            }
            from = at + "OP_DUP =>".len();
        }
        panic!("OP_DUP arm");
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src =
            format!("fn op_dup(stack: &mut Vec<Vec<u8>>) -> Result<bool, String> {{\n{body}\n}}\n");
        let file = syn::parse_file(&src).expect("parse OP_DUP");
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_DUP fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_DUP",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 10, &[])
    }

    #[test]
    fn op_dup_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let src = std::fs::read_to_string(&path).expect("script/mod.rs");
        let body = arm_body(&src);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_DUP must use the body");
            }
            other => panic!("unpatched OP_DUP must pass, got {other:?}"),
        }
        let gated = format!("if stack.len() < 99 {{ return Ok(false); }}\n{body}");
        assert_ne!(gated, body, "the length gate must change");
        let gated_result = identity_query(&decode_fn(&gated), &clause);
        assert!(
            matches!(
                gated_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "the length gate must flip the identity, got {gated_result:?}"
        );
        let emptied = body.replace("stack.push(item)", "stack.push(Vec::new())");
        assert_ne!(emptied, body, "the pushed element must change");
        let emptied_result = identity_query(&decode_fn(&emptied), &clause);
        assert!(
            matches!(
                emptied_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "pushing an empty element must flip the identity, got {emptied_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod cltv_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn arm_body(src: &str) -> String {
        let mut from = 0;
        while let Some(rel) = src[from..].find("OP_CHECKLOCKTIMEVERIFY =>") {
            let at = from + rel;
            let rest = &src[at..];
            let brace = rest.find('{').expect("arm brace");
            let mut depth = 0i32;
            for (i, byte) in rest[brace..].bytes().enumerate() {
                if byte == b'{' {
                    depth += 1;
                } else if byte == b'}' {
                    depth -= 1;
                    if depth == 0 {
                        let inner = rest[brace + 1..brace + i].to_string();
                        if inner.contains("check_bip65(")
                            && inner.contains("input_seq == 0xffffffff")
                        {
                            return inner;
                        }
                        break;
                    }
                }
            }
            from = at + "OP_CHECKLOCKTIMEVERIFY =>".len();
        }
        panic!("OP_CHECKLOCKTIMEVERIFY arm");
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_cltv(stack: &mut Vec<Vec<u8>>, flags: u32, tx: Tx, input_index: usize) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).expect("parse CLTV");
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("CLTV fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_CHECKLOCKTIMEVERIFY",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 20, &[])
    }

    #[test]
    fn cltv_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let src = std::fs::read_to_string(&path).expect("script/mod.rs");
        let body = arm_body(&src);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "CLTV must use the body");
            }
            other => panic!("unpatched CLTV must pass, got {other:?}"),
        }
        let emptied = body.replacen("stack.is_empty()", "stack.len() < 2", 1);
        assert_ne!(emptied, body, "the empty check must change");
        let emptied_result = identity_query(&decode_fn(&emptied), &clause);
        assert!(
            matches!(
                emptied_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "widening the empty check must flip the identity, got {emptied_result:?}"
        );
        let renamed = body.replacen("check_bip65(", "check_bip65_gone(", 1);
        assert_ne!(renamed, body, "the BIP65 call must change");
        let renamed_result = identity_query(&decode_fn(&renamed), &clause);
        assert!(
            matches!(
                renamed_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "renaming check_bip65 must flip the identity, got {renamed_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_equal_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn arm_body(src: &str) -> String {
        let mut from = 0;
        while let Some(rel) = src[from..].find("OP_EQUAL =>") {
            let at = from + rel;
            let rest = &src[at..];
            let brace = rest.find('{').expect("arm brace");
            let mut depth = 0i32;
            for (i, byte) in rest[brace..].bytes().enumerate() {
                if byte == b'{' {
                    depth += 1;
                } else if byte == b'}' {
                    depth -= 1;
                    if depth == 0 {
                        let inner = rest[brace + 1..brace + i].to_string();
                        if inner.contains("if a == b { &[1u8] }")
                            && inner.contains("stack.len() < 2")
                        {
                            return inner;
                        }
                        break;
                    }
                }
            }
            from = at + "OP_EQUAL =>".len();
        }
        panic!("OP_EQUAL arm");
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_equal(stack: &mut Vec<Vec<u8>>) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).expect("parse OP_EQUAL");
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_EQUAL fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_EQUAL",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 20, &[])
    }

    #[test]
    fn op_equal_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let src = std::fs::read_to_string(&path).expect("script/mod.rs");
        let body = arm_body(&src);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_EQUAL must use the body");
            }
            other => panic!("unpatched OP_EQUAL must pass, got {other:?}"),
        }
        let widened = body.replacen("stack.len() < 2", "stack.len() < 3", 1);
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the length gate must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replacen("a == b", "a != b", 1);
        assert_ne!(flipped, body, "the comparison must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "flipping equality must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_equalverify_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn arm_body(src: &str) -> String {
        let mut from = 0;
        while let Some(rel) = src[from..].find("OP_EQUALVERIFY =>") {
            let at = from + rel;
            let rest = &src[at..];
            let brace = rest.find('{').expect("arm brace");
            let mut depth = 0i32;
            for (i, byte) in rest[brace..].bytes().enumerate() {
                if byte == b'{' {
                    depth += 1;
                } else if byte == b'}' {
                    depth -= 1;
                    if depth == 0 {
                        let inner = rest[brace + 1..brace + i].to_string();
                        if inner.contains("script_bool_bytes(f_equal)")
                            && inner.contains("let f_equal = a == b")
                            && inner.contains("stack.len() < 2")
                        {
                            return inner;
                        }
                        break;
                    }
                }
            }
            from = at + "OP_EQUALVERIFY =>".len();
        }
        panic!("OP_EQUALVERIFY arm");
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_equalverify(stack: &mut Vec<Vec<u8>>) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).expect("parse OP_EQUALVERIFY");
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_EQUALVERIFY fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_EQUALVERIFY",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 20, &[])
    }

    #[test]
    fn op_equalverify_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let src = std::fs::read_to_string(&path).expect("script/mod.rs");
        let body = arm_body(&src);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_EQUALVERIFY must use the body");
            }
            other => panic!("unpatched OP_EQUALVERIFY must pass, got {other:?}"),
        }
        let widened = body.replacen("stack.len() < 2", "stack.len() < 3", 1);
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the length gate must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replacen("a == b", "a != b", 1);
        assert_ne!(flipped, body, "the comparison must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "flipping equality must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod calculate_sequence_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn decode_fn_from(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).expect("parse sequence_locks.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "calculate_sequence_locks" => Some(func),
                _ => None,
            })
            .expect("calculate_sequence_locks")
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/sequence_locks.rs"),
            "calculate_sequence_locks",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn sequence_locks_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../blvm-consensus/src/sequence_locks.rs");
        let src = std::fs::read_to_string(&path).expect("sequence_locks.rs");
        let func = decode_fn_from(&src);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "sequence locks must use the body");
            }
            other => panic!("unpatched sequence locks must pass, got {other:?}"),
        }
        let raised = src.replacen("min_height: i64 = -1", "min_height: i64 = 0", 1);
        assert_ne!(raised, src, "the height initializer must change");
        let raised_result = identity_query(&decode_fn_from(&raised), &clause);
        assert!(
            matches!(
                raised_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the height initializer must flip the identity, got {raised_result:?}"
        );
        let unshifted = src.replacen(
            "locktime_value << SEQUENCE_LOCKTIME_GRANULARITY",
            "locktime_value",
            1,
        );
        assert_ne!(unshifted, src, "the granularity shift must change");
        let unshifted_result = identity_query(&decode_fn_from(&unshifted), &clause);
        assert!(
            matches!(
                unshifted_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "dropping the granularity shift must flip the identity, got {unshifted_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod coinbase_subsidy_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn decode_fn_from(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).expect("parse economic.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "check_coinbase_subsidy" => Some(func),
                _ => None,
            })
            .expect("check_coinbase_subsidy")
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/economic.rs"),
            "check_coinbase_subsidy",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn coinbase_subsidy_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/economic.rs");
        let src = std::fs::read_to_string(&path).expect("economic.rs");
        let func = decode_fn_from(&src);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "coinbase subsidy must use the body");
            }
            other => panic!("unpatched coinbase subsidy must pass, got {other:?}"),
        }
        let widened = src.replacen(
            "coinbase_output <= max_coinbase",
            "coinbase_output < max_coinbase",
            1,
        );
        assert_ne!(widened, src, "the subsidy comparison must change");
        let widened_result = identity_query(&decode_fn_from(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "making the subsidy bound strict must flip the identity, got {widened_result:?}"
        );
        let dropped = src
            .replace(
                "if total_fees < 0 || subsidy < 0 {\n        return false;\n    }\n",
                "",
            )
            .replace("output.value < 0 || ", "")
            .replace(
                "if coinbase_output < 0 {\n        return false;\n    }\n",
                "",
            );
        assert_ne!(dropped, src, "the sign checks must change");
        let dropped_result = identity_query(&decode_fn_from(&dropped), &clause);
        assert!(
            matches!(
                dropped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "dropping the sign checks must flip the identity, got {dropped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod calculate_fee_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn decode_fn_from(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).expect("parse economic.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "calculate_fee" => Some(func),
                _ => None,
            })
            .expect("calculate_fee")
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/economic.rs"),
            "calculate_fee",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn calculate_fee_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/economic.rs");
        let src = std::fs::read_to_string(&path).expect("economic.rs");
        let func = decode_fn_from(&src);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "calculate_fee must use the body");
            }
            other => panic!("unpatched calculate_fee must pass, got {other:?}"),
        }
        let added = src.replacen("checked_sub(total_output)", "checked_add(total_output)", 1);
        assert_ne!(added, src, "the fee subtraction must change");
        let added_result = identity_query(&decode_fn_from(&added), &clause);
        assert!(
            matches!(
                added_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "adding the output total must flip the identity, got {added_result:?}"
        );
        let dropped = src.replacen("is_coinbase(tx)", "false", 1);
        assert_ne!(dropped, src, "the coinbase guard must change");
        let dropped_result = identity_query(&decode_fn_from(&dropped), &clause);
        assert!(
            matches!(
                dropped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "dropping the coinbase guard must flip the identity, got {dropped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod utxo_supply_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn decode_fn_from(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).expect("parse economic.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "verify_utxo_supply" => Some(func),
                _ => None,
            })
            .expect("verify_utxo_supply")
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/economic.rs"),
            "verify_utxo_supply",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn utxo_supply_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/economic.rs");
        let src = std::fs::read_to_string(&path).expect("economic.rs");
        let func = decode_fn_from(&src);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "utxo supply must use the body");
            }
            other => panic!("unpatched utxo supply must pass, got {other:?}"),
        }
        let widened = src.replacen("actual == expected", "actual >= expected", 1);
        assert_ne!(widened, src, "the supply comparison must change");
        let widened_result = identity_query(&decode_fn_from(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "relaxing supply equality must flip the identity, got {widened_result:?}"
        );
        let subtracted = src.replacen("checked_add(utxo.value)", "checked_sub(utxo.value)", 1);
        assert_ne!(subtracted, src, "the utxo fold must change");
        let subtracted_result = identity_query(&decode_fn_from(&subtracted), &clause);
        assert!(
            matches!(
                subtracted_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "subtracting utxo values must flip the identity, got {subtracted_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod sigop_cost_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn decode_fn_from(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).expect("parse sigop.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func)
                    if func.sig.ident == "get_transaction_sigop_cost_with_utxos" =>
                {
                    Some(func)
                }
                _ => None,
            })
            .expect("get_transaction_sigop_cost_with_utxos")
    }

    fn edit_fn(src: &str, from: &str, to: &str) -> String {
        let start = src
            .find("pub fn get_transaction_sigop_cost_with_utxos")
            .expect("function");
        let end = start
            + src[start..]
                .find("\npub fn get_transaction_sigop_cost_with_witness_slices")
                .expect("next function");
        let body = src[start..end].replace(from, to);
        assert_ne!(
            body,
            &src[start..end],
            "{from} must change inside the function"
        );
        let mut edited = src.to_string();
        edited.replace_range(start..end, &body);
        edited
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/sigop.rs"),
            "get_transaction_sigop_cost_with_utxos",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn sigop_cost_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/sigop.rs");
        let src = std::fs::read_to_string(&path).expect("sigop.rs");
        let func = decode_fn_from(&src);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "sigop cost must use the body");
            }
            other => panic!("unpatched sigop cost must pass, got {other:?}"),
        }
        let scaled = edit_fn(
            &src,
            "saturating_mul(WITNESS_SCALE_FACTOR)",
            "saturating_mul(1)",
        );
        let scaled_result = identity_query(&decode_fn_from(&scaled), &clause);
        assert!(
            matches!(
                scaled_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "changing the witness scale must flip the identity, got {scaled_result:?}"
        );
        let flagged = edit_fn(&src, "flags & 0x01", "flags & 0x02");
        let flagged_result = identity_query(&decode_fn_from(&flagged), &clause);
        assert!(
            matches!(
                flagged_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "moving the P2SH flag must flip the identity, got {flagged_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_add_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let mut from = 0;
        while let Some(rel) = src[from..].find("OP_ADD =>") {
            let at = from + rel;
            let inner = brace_inner(&src[at..]);
            if inner.contains("arithmetic::op_add(stack)")
                && inner.contains("SCRIPT_VERIFY_MINIMALDATA")
            {
                return inner;
            }
            from = at + "OP_ADD =>".len();
        }
        panic!("OP_ADD arm");
    }

    fn combined(script: &str, arith: &str) -> String {
        let arm = arm_body(script);
        let marker = arith.find("fn op_add(").expect("op_add");
        let inner = brace_inner(&arith[marker..]);
        let body = arm.replace("arithmetic::op_add(stack)", &format!("{{{inner}}}"));
        assert_ne!(body, arm, "op_add must be inlined");
        body
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_add(stack: &mut Vec<Vec<u8>>, flags: u32) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_ADD: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_ADD fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_ADD",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_add_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script");
        let script = std::fs::read_to_string(root.join("mod.rs")).expect("script/mod.rs");
        let arith = std::fs::read_to_string(root.join("arithmetic.rs")).expect("arithmetic.rs");
        let body = combined(&script, &arith);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_ADD must use the body");
            }
            other => panic!("unpatched OP_ADD must pass, got {other:?}"),
        }
        let widened = body.replacen("stack.len() < 2", "stack.len() < 3", 1);
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the length gate must flip the identity, got {widened_result:?}"
        );
        let subtracted = body.replace("b + a", "b - a");
        assert_ne!(subtracted, body, "the sum must change");
        let subtracted_result = identity_query(&decode_fn(&subtracted), &clause);
        assert!(
            matches!(
                subtracted_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "subtracting the operands must flip the identity, got {subtracted_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_sub_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let mut from = 0;
        while let Some(rel) = src[from..].find("OP_SUB =>") {
            let at = from + rel;
            let inner = brace_inner(&src[at..]);
            if inner.contains("arithmetic::op_sub(stack)")
                && inner.contains("SCRIPT_VERIFY_MINIMALDATA")
            {
                return inner;
            }
            from = at + "OP_SUB =>".len();
        }
        panic!("OP_SUB arm");
    }

    fn combined(script: &str, arith: &str) -> String {
        let arm = arm_body(script);
        let marker = arith.find("fn op_sub(").expect("op_sub");
        let inner = brace_inner(&arith[marker..]);
        let body = arm.replace("arithmetic::op_sub(stack)", &format!("{{{inner}}}"));
        assert_ne!(body, arm, "op_sub must be inlined");
        body
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_sub(stack: &mut Vec<Vec<u8>>, flags: u32) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_SUB: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_SUB fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_SUB",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_sub_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script");
        let script = std::fs::read_to_string(root.join("mod.rs")).expect("script/mod.rs");
        let arith = std::fs::read_to_string(root.join("arithmetic.rs")).expect("arithmetic.rs");
        let body = combined(&script, &arith);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_SUB must use the body");
            }
            other => panic!("unpatched OP_SUB must pass, got {other:?}"),
        }
        let widened = body.replacen("stack.len() < 2", "stack.len() < 3", 1);
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the length gate must flip the identity, got {widened_result:?}"
        );
        let added = body.replace("b - a", "b + a");
        assert_ne!(added, body, "the difference must change");
        let added_result = identity_query(&decode_fn(&added), &clause);
        assert!(
            matches!(
                added_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "adding the operands must flip the identity, got {added_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_booland_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let mut from = 0;
        while let Some(rel) = src[from..].find("OP_BOOLAND =>") {
            let at = from + rel;
            let inner = brace_inner(&src[at..]);
            if inner.contains("arithmetic::op_booland(stack)")
                && inner.contains("SCRIPT_VERIFY_MINIMALDATA")
            {
                return inner;
            }
            from = at + "OP_BOOLAND =>".len();
        }
        panic!("OP_BOOLAND arm");
    }

    fn combined(script: &str, arith: &str) -> String {
        let arm = arm_body(script);
        let marker = arith.find("fn op_booland(").expect("op_booland");
        let inner = brace_inner(&arith[marker..]);
        let body = arm.replace("arithmetic::op_booland(stack)", &format!("{{{inner}}}"));
        assert_ne!(body, arm, "op_booland must be inlined");
        body
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_booland(stack: &mut Vec<Vec<u8>>, flags: u32) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_BOOLAND: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_BOOLAND fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_BOOLAND",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_booland_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script");
        let script = std::fs::read_to_string(root.join("mod.rs")).expect("script/mod.rs");
        let arith = std::fs::read_to_string(root.join("arithmetic.rs")).expect("arithmetic.rs");
        let body = combined(&script, &arith);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_BOOLAND must use the body");
            }
            other => panic!("unpatched OP_BOOLAND must pass, got {other:?}"),
        }
        let widened = body.replacen("stack.len() < 2", "stack.len() < 3", 1);
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the length gate must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("if a != 0", "if a == 0");
        assert_ne!(flipped, body, "the first comparison must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring a to be zero must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_boolor_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let mut from = 0;
        while let Some(rel) = src[from..].find("OP_BOOLOR =>") {
            let at = from + rel;
            let inner = brace_inner(&src[at..]);
            if inner.contains("arithmetic::op_boolor(stack)")
                && inner.contains("SCRIPT_VERIFY_MINIMALDATA")
            {
                return inner;
            }
            from = at + "OP_BOOLOR =>".len();
        }
        panic!("OP_BOOLOR arm");
    }

    fn combined(script: &str, arith: &str) -> String {
        let arm = arm_body(script);
        let marker = arith.find("fn op_boolor(").expect("op_boolor");
        let inner = brace_inner(&arith[marker..]);
        let body = arm.replace("arithmetic::op_boolor(stack)", &format!("{{{inner}}}"));
        assert_ne!(body, arm, "op_boolor must be inlined");
        body
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_boolor(stack: &mut Vec<Vec<u8>>, flags: u32) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_BOOLOR: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_BOOLOR fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_BOOLOR",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_boolor_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script");
        let script = std::fs::read_to_string(root.join("mod.rs")).expect("script/mod.rs");
        let arith = std::fs::read_to_string(root.join("arithmetic.rs")).expect("arithmetic.rs");
        let body = combined(&script, &arith);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_BOOLOR must use the body");
            }
            other => panic!("unpatched OP_BOOLOR must pass, got {other:?}"),
        }
        let widened = body.replacen("stack.len() < 2", "stack.len() < 3", 1);
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the length gate must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("if a != 0", "if a == 0");
        assert_ne!(flipped, body, "the first comparison must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring a to be zero must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_numequal_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let mut from = 0;
        while let Some(rel) = src[from..].find("OP_NUMEQUAL =>") {
            let at = from + rel;
            let inner = brace_inner(&src[at..]);
            if inner.contains("arithmetic::op_numequal(stack)")
                && inner.contains("SCRIPT_VERIFY_MINIMALDATA")
                && !inner.contains("OP_NUMEQUALVERIFY")
            {
                return inner;
            }
            from = at + "OP_NUMEQUAL =>".len();
        }
        panic!("OP_NUMEQUAL arm");
    }

    fn combined(script: &str, arith: &str) -> String {
        let arm = arm_body(script);
        let marker = arith.find("fn op_numequal(").expect("op_numequal");
        let inner = brace_inner(&arith[marker..]);
        let body = arm.replace("arithmetic::op_numequal(stack)", &format!("{{{inner}}}"));
        assert_ne!(body, arm, "op_numequal must be inlined");
        body
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_numequal(stack: &mut Vec<Vec<u8>>, flags: u32) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_NUMEQUAL: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_NUMEQUAL fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_NUMEQUAL",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_numequal_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script");
        let script = std::fs::read_to_string(root.join("mod.rs")).expect("script/mod.rs");
        let arith = std::fs::read_to_string(root.join("arithmetic.rs")).expect("arithmetic.rs");
        let body = combined(&script, &arith);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_NUMEQUAL must use the body");
            }
            other => panic!("unpatched OP_NUMEQUAL must pass, got {other:?}"),
        }
        let widened = body.replacen("stack.len() < 2", "stack.len() < 3", 1);
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the length gate must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("a == b", "a != b");
        assert_ne!(flipped, body, "the comparison must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "negating equality must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_lessthan_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let mut from = 0;
        while let Some(rel) = src[from..].find("OP_LESSTHAN =>") {
            let at = from + rel;
            let inner = brace_inner(&src[at..]);
            if inner.contains("arithmetic::op_lessthan(stack)")
                && inner.contains("SCRIPT_VERIFY_MINIMALDATA")
            {
                return inner;
            }
            from = at + "OP_LESSTHAN =>".len();
        }
        panic!("OP_LESSTHAN arm");
    }

    fn combined(script: &str, arith: &str) -> String {
        let arm = arm_body(script);
        let marker = arith.find("fn op_lessthan(").expect("op_lessthan");
        let inner = brace_inner(&arith[marker..]);
        let body = arm.replace("arithmetic::op_lessthan(stack)", &format!("{{{inner}}}"));
        assert_ne!(body, arm, "op_lessthan must be inlined");
        body
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_lessthan(stack: &mut Vec<Vec<u8>>, flags: u32) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_LESSTHAN: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_LESSTHAN fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_LESSTHAN",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_lessthan_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script");
        let script = std::fs::read_to_string(root.join("mod.rs")).expect("script/mod.rs");
        let arith = std::fs::read_to_string(root.join("arithmetic.rs")).expect("arithmetic.rs");
        let body = combined(&script, &arith);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_LESSTHAN must use the body");
            }
            other => panic!("unpatched OP_LESSTHAN must pass, got {other:?}"),
        }
        let widened = body.replacen("stack.len() < 2", "stack.len() < 3", 1);
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the length gate must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("b < a", "b > a");
        assert_ne!(flipped, body, "the ordering must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "reversing the order must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_greaterthan_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let mut from = 0;
        while let Some(rel) = src[from..].find("OP_GREATERTHAN =>") {
            let at = from + rel;
            let inner = brace_inner(&src[at..]);
            if inner.contains("arithmetic::op_greaterthan(stack)")
                && inner.contains("SCRIPT_VERIFY_MINIMALDATA")
            {
                return inner;
            }
            from = at + "OP_GREATERTHAN =>".len();
        }
        panic!("OP_GREATERTHAN arm");
    }

    fn combined(script: &str, arith: &str) -> String {
        let arm = arm_body(script);
        let marker = arith.find("fn op_greaterthan(").expect("op_greaterthan");
        let inner = brace_inner(&arith[marker..]);
        let body = arm.replace("arithmetic::op_greaterthan(stack)", &format!("{{{inner}}}"));
        assert_ne!(body, arm, "op_greaterthan must be inlined");
        body
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_greaterthan(stack: &mut Vec<Vec<u8>>, flags: u32) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file =
            syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_GREATERTHAN: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_GREATERTHAN fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_GREATERTHAN",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_greaterthan_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script");
        let script = std::fs::read_to_string(root.join("mod.rs")).expect("script/mod.rs");
        let arith = std::fs::read_to_string(root.join("arithmetic.rs")).expect("arithmetic.rs");
        let body = combined(&script, &arith);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_GREATERTHAN must use the body");
            }
            other => panic!("unpatched OP_GREATERTHAN must pass, got {other:?}"),
        }
        let widened = body.replacen("stack.len() < 2", "stack.len() < 3", 1);
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the length gate must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("b > a", "b < a");
        assert_ne!(flipped, body, "the ordering must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "reversing the order must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_lessthanorequal_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_LESSTHANOREQUAL =>";
        let mut from = 0;
        while let Some(rel) = src[from..].find(marker) {
            let at = from + rel;
            let inner = brace_inner(&src[at..]);
            if inner.contains("arithmetic::op_lessthanorequal(stack)")
                && inner.contains("SCRIPT_VERIFY_MINIMALDATA")
            {
                return inner;
            }
            from = at + marker.len();
        }
        panic!("OP_LESSTHANOREQUAL arm");
    }

    fn combined(script: &str, arith: &str) -> String {
        let arm = arm_body(script);
        let marker = arith
            .find("fn op_lessthanorequal(")
            .expect("op_lessthanorequal");
        let inner = brace_inner(&arith[marker..]);
        let body = arm.replace(
            "arithmetic::op_lessthanorequal(stack)",
            &format!("{{{inner}}}"),
        );
        assert_ne!(body, arm, "op_lessthanorequal must be inlined");
        body
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_lessthanorequal(stack: &mut Vec<Vec<u8>>, flags: u32) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file =
            syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_LESSTHANOREQUAL: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_LESSTHANOREQUAL fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_LESSTHANOREQUAL",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_lessthanorequal_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script");
        let script = std::fs::read_to_string(root.join("mod.rs")).expect("script/mod.rs");
        let arith = std::fs::read_to_string(root.join("arithmetic.rs")).expect("arithmetic.rs");
        let body = combined(&script, &arith);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_LESSTHANOREQUAL must use the body");
            }
            other => panic!("unpatched OP_LESSTHANOREQUAL must pass, got {other:?}"),
        }
        let widened = body.replacen("stack.len() < 2", "stack.len() < 3", 1);
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the length gate must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("b <= a", "b >= a");
        assert_ne!(flipped, body, "the ordering must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "reversing the order must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_greaterthanorequal_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_GREATERTHANOREQUAL =>";
        let mut from = 0;
        while let Some(rel) = src[from..].find(marker) {
            let at = from + rel;
            let inner = brace_inner(&src[at..]);
            if inner.contains("arithmetic::op_greaterthanorequal(stack)")
                && inner.contains("SCRIPT_VERIFY_MINIMALDATA")
            {
                return inner;
            }
            from = at + marker.len();
        }
        panic!("OP_GREATERTHANOREQUAL arm");
    }

    fn combined(script: &str, arith: &str) -> String {
        let arm = arm_body(script);
        let marker = arith
            .find("fn op_greaterthanorequal(")
            .expect("op_greaterthanorequal");
        let inner = brace_inner(&arith[marker..]);
        let body = arm.replace(
            "arithmetic::op_greaterthanorequal(stack)",
            &format!("{{{inner}}}"),
        );
        assert_ne!(body, arm, "op_greaterthanorequal must be inlined");
        body
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_greaterthanorequal(stack: &mut Vec<Vec<u8>>, flags: u32) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src)
            .unwrap_or_else(|err| panic!("parse OP_GREATERTHANOREQUAL: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_GREATERTHANOREQUAL fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_GREATERTHANOREQUAL",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_greaterthanorequal_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script");
        let script = std::fs::read_to_string(root.join("mod.rs")).expect("script/mod.rs");
        let arith = std::fs::read_to_string(root.join("arithmetic.rs")).expect("arithmetic.rs");
        let body = combined(&script, &arith);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_GREATERTHANOREQUAL must use the body");
            }
            other => panic!("unpatched OP_GREATERTHANOREQUAL must pass, got {other:?}"),
        }
        let widened = body.replacen("stack.len() < 2", "stack.len() < 3", 1);
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the length gate must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("b >= a", "b <= a");
        assert_ne!(flipped, body, "the ordering must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "reversing the order must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_min_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_MIN =>";
        let mut from = 0;
        while let Some(rel) = src[from..].find(marker) {
            let at = from + rel;
            let inner = brace_inner(&src[at..]);
            if inner.contains("arithmetic::op_min(stack)")
                && inner.contains("SCRIPT_VERIFY_MINIMALDATA")
            {
                return inner;
            }
            from = at + marker.len();
        }
        panic!("OP_MIN arm");
    }

    fn combined(script: &str, arith: &str) -> String {
        let arm = arm_body(script);
        let marker = arith.find("fn op_min(").expect("op_min");
        let inner = brace_inner(&arith[marker..]);
        let body = arm.replace("arithmetic::op_min(stack)", &format!("{{{inner}}}"));
        assert_ne!(body, arm, "op_min must be inlined");
        body
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_min(stack: &mut Vec<Vec<u8>>, flags: u32) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_MIN: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_MIN fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_MIN",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_min_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script");
        let script = std::fs::read_to_string(root.join("mod.rs")).expect("script/mod.rs");
        let arith = std::fs::read_to_string(root.join("arithmetic.rs")).expect("arithmetic.rs");
        let body = combined(&script, &arith);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_MIN must use the body");
            }
            other => panic!("unpatched OP_MIN must pass, got {other:?}"),
        }
        let widened = body.replacen("stack.len() < 2", "stack.len() < 3", 1);
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the length gate must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("std::cmp::min", "std::cmp::max");
        assert_ne!(flipped, body, "the extremum must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "swapping min for max must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_max_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_MAX =>";
        let mut from = 0;
        while let Some(rel) = src[from..].find(marker) {
            let at = from + rel;
            let inner = brace_inner(&src[at..]);
            if inner.contains("arithmetic::op_max(stack)")
                && inner.contains("SCRIPT_VERIFY_MINIMALDATA")
            {
                return inner;
            }
            from = at + marker.len();
        }
        panic!("OP_MAX arm");
    }

    fn combined(script: &str, arith: &str) -> String {
        let arm = arm_body(script);
        let marker = arith.find("fn op_max(").expect("op_max");
        let inner = brace_inner(&arith[marker..]);
        let body = arm.replace("arithmetic::op_max(stack)", &format!("{{{inner}}}"));
        assert_ne!(body, arm, "op_max must be inlined");
        body
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_max(stack: &mut Vec<Vec<u8>>, flags: u32) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_MAX: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_MAX fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_MAX",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_max_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script");
        let script = std::fs::read_to_string(root.join("mod.rs")).expect("script/mod.rs");
        let arith = std::fs::read_to_string(root.join("arithmetic.rs")).expect("arithmetic.rs");
        let body = combined(&script, &arith);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_MAX must use the body");
            }
            other => panic!("unpatched OP_MAX must pass, got {other:?}"),
        }
        let widened = body.replacen("stack.len() < 2", "stack.len() < 3", 1);
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the length gate must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("std::cmp::max", "std::cmp::min");
        assert_ne!(flipped, body, "the extremum must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "swapping max for min must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_within_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_WITHIN =>";
        let mut from = 0;
        while let Some(rel) = src[from..].find(marker) {
            let at = from + rel;
            let inner = brace_inner(&src[at..]);
            if inner.contains("arithmetic::op_within(stack)")
                && inner.contains("SCRIPT_VERIFY_MINIMALDATA")
            {
                return inner;
            }
            from = at + marker.len();
        }
        panic!("OP_WITHIN arm");
    }

    fn combined(script: &str, arith: &str) -> String {
        let arm = arm_body(script);
        let marker = arith.find("fn op_within(").expect("op_within");
        let inner = brace_inner(&arith[marker..]);
        let body = arm.replace("arithmetic::op_within(stack)", &format!("{{{inner}}}"));
        assert_ne!(body, arm, "op_within must be inlined");
        body
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_within(stack: &mut Vec<Vec<u8>>, flags: u32) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_WITHIN: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_WITHIN fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_WITHIN",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_within_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script");
        let script = std::fs::read_to_string(root.join("mod.rs")).expect("script/mod.rs");
        let arith = std::fs::read_to_string(root.join("arithmetic.rs")).expect("arithmetic.rs");
        let body = combined(&script, &arith);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_WITHIN must use the body");
            }
            other => panic!("unpatched OP_WITHIN must pass, got {other:?}"),
        }
        let widened = body.replacen("stack.len() < 3", "stack.len() < 4", 1);
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the length gate must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("x >= min_val && x < max_val", "x > min_val && x < max_val");
        assert_ne!(flipped, body, "the lower bound must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "excluding the lower bound must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_1add_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_1ADD =>";
        let mut from = 0;
        while let Some(rel) = src[from..].find(marker) {
            let at = from + rel;
            let inner = brace_inner(&src[at..]);
            if inner.contains("script_num_encode(a + 1)") && inner.contains("if let Some(item)") {
                return inner;
            }
            from = at + marker.len();
        }
        panic!("OP_1ADD arm");
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_1add(stack: &mut Vec<Vec<u8>>, flags: u32) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_1ADD: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_1ADD fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_1ADD",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_1add_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_1ADD must use the body");
            }
            other => panic!("unpatched OP_1ADD must pass, got {other:?}"),
        }
        let widened = format!("if stack.len() < 99 {{ return Ok(false); }}\n{body}");
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 99 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("a + 1", "a - 1");
        assert_ne!(flipped, body, "the step must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "decrementing must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_1sub_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_1SUB =>";
        let mut from = 0;
        while let Some(rel) = src[from..].find(marker) {
            let at = from + rel;
            let inner = brace_inner(&src[at..]);
            if inner.contains("script_num_encode(a - 1)") && inner.contains("if let Some(item)") {
                return inner;
            }
            from = at + marker.len();
        }
        panic!("OP_1SUB arm");
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_1sub(stack: &mut Vec<Vec<u8>>, flags: u32) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_1SUB: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_1SUB fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_1SUB",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_1sub_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_1SUB must use the body");
            }
            other => panic!("unpatched OP_1SUB must pass, got {other:?}"),
        }
        let widened = format!("if stack.len() < 99 {{ return Ok(false); }}\n{body}");
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 99 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("a - 1", "a + 1");
        assert_ne!(flipped, body, "the step must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "incrementing must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_not_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_NOT =>";
        let mut from = 0;
        while let Some(rel) = src[from..].find(marker) {
            let at = from + rel;
            let next = src[at + marker.len()..].chars().next();
            if next.is_some_and(|c| c.is_ascii_alphanumeric() || c == '_') {
                from = at + marker.len();
                continue;
            }
            let inner = brace_inner(&src[at..]);
            if inner.contains("if a == 0") && inner.contains("if let Some(item)") {
                return inner;
            }
            from = at + marker.len();
        }
        panic!("OP_NOT arm");
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_not(stack: &mut Vec<Vec<u8>>, flags: u32) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_NOT: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_NOT fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_NOT",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_not_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_NOT must use the body");
            }
            other => panic!("unpatched OP_NOT must pass, got {other:?}"),
        }
        let widened = format!("if stack.len() < 99 {{ return Ok(false); }}\n{body}");
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 99 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("if a == 0", "if a != 0");
        assert_ne!(flipped, body, "the zero test must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "flipping the zero test must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_0notequal_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_0NOTEQUAL =>";
        let mut from = 0;
        while let Some(rel) = src[from..].find(marker) {
            let at = from + rel;
            let inner = brace_inner(&src[at..]);
            if inner.contains("if a != 0") && inner.contains("if let Some(item)") {
                return inner;
            }
            from = at + marker.len();
        }
        panic!("OP_0NOTEQUAL arm");
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_0notequal(stack: &mut Vec<Vec<u8>>, flags: u32) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_0NOTEQUAL: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_0NOTEQUAL fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_0NOTEQUAL",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_0notequal_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_0NOTEQUAL must use the body");
            }
            other => panic!("unpatched OP_0NOTEQUAL must pass, got {other:?}"),
        }
        let widened = format!("if stack.len() < 99 {{ return Ok(false); }}\n{body}");
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 99 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("if a != 0", "if a == 0");
        assert_ne!(flipped, body, "the zero test must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "flipping the zero test must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_numequalverify_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_NUMEQUALVERIFY =>";
        let mut from = 0;
        while let Some(rel) = src[from..].find(marker) {
            let at = from + rel;
            let inner = brace_inner(&src[at..]);
            if inner.contains("arithmetic::op_numequalverify(stack)")
                && inner.contains("SCRIPT_VERIFY_MINIMALDATA")
            {
                return inner;
            }
            from = at + marker.len();
        }
        panic!("OP_NUMEQUALVERIFY arm");
    }

    fn combined(script: &str, arith: &str) -> String {
        let arm = arm_body(script);
        let marker = arith
            .find("fn op_numequalverify(")
            .expect("op_numequalverify");
        let inner = brace_inner(&arith[marker..]);
        let body = arm.replace(
            "arithmetic::op_numequalverify(stack)",
            &format!("{{{inner}}}"),
        );
        assert_ne!(body, arm, "op_numequalverify must be inlined");
        body
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_numequalverify(stack: &mut Vec<Vec<u8>>, flags: u32) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file =
            syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_NUMEQUALVERIFY: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_NUMEQUALVERIFY fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_NUMEQUALVERIFY",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_numequalverify_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script");
        let script = std::fs::read_to_string(root.join("mod.rs")).expect("script/mod.rs");
        let arith = std::fs::read_to_string(root.join("arithmetic.rs")).expect("arithmetic.rs");
        let body = combined(&script, &arith);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_NUMEQUALVERIFY must use the body");
            }
            other => panic!("unpatched OP_NUMEQUALVERIFY must pass, got {other:?}"),
        }
        let widened = body.replacen("stack.len() < 2", "stack.len() < 3", 1);
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the length gate must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("a == b", "a != b");
        assert_ne!(flipped, body, "the comparison must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "negating equality must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_1negate_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_1NEGATE =>";
        let mut from = 0;
        while let Some(rel) = src[from..].find(marker) {
            let at = from + rel;
            let next = src[at + marker.len()..].chars().next();
            if next.is_some_and(|c| c.is_ascii_alphanumeric() || c == '_') {
                from = at + marker.len();
                continue;
            }
            if !src[at..].contains('{') {
                from = at + marker.len();
                continue;
            }
            let inner = brace_inner(&src[at..]);
            if inner.contains("to_stack_element(&[0x81])") && inner.contains("Ok(true)") {
                return inner;
            }
            from = at + marker.len();
        }
        panic!("OP_1NEGATE arm");
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_1negate(stack: &mut Vec<Vec<u8>>) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_1NEGATE: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_1NEGATE fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_1NEGATE",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_1negate_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_1NEGATE must use the body");
            }
            other => panic!("unpatched OP_1NEGATE must pass, got {other:?}"),
        }
        let widened = format!("if stack.len() < 99 {{ return Ok(false); }}\n{body}");
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 99 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("0x81", "0x01");
        assert_ne!(flipped, body, "the pushed byte must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "pushing 1 must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_0_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_0 =>";
        let mut from = 0;
        while let Some(rel) = src[from..].find(marker) {
            let at = from + rel;
            let next = src[at + marker.len()..].chars().next();
            if next.is_some_and(|c| c.is_ascii_alphanumeric() || c == '_') {
                from = at + marker.len();
                continue;
            }
            if !src[at..].contains('{') {
                from = at + marker.len();
                continue;
            }
            let inner = brace_inner(&src[at..]);
            if inner.contains("to_stack_element(&[])") && inner.contains("Ok(true)") {
                return inner;
            }
            from = at + marker.len();
        }
        panic!("OP_0 arm");
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src =
            format!("fn op_0(stack: &mut Vec<Vec<u8>>) -> Result<bool, String> {{\n{body}\n}}\n");
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_0: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_0 fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_0",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_0_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_0 must use the body");
            }
            other => panic!("unpatched OP_0 must pass, got {other:?}"),
        }
        let widened = format!("if stack.len() < 99 {{ return Ok(false); }}\n{body}");
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 99 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("to_stack_element(&[])", "to_stack_element(&[1])");
        assert_ne!(flipped, body, "the pushed element must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "pushing 1 must flip the empty push, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_1_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_1..=OP_16 =>";
        let at = src.find(marker).expect("OP_1 arm");
        let inner = brace_inner(&src[at..]);
        assert!(
            inner.contains("opcode - OP_N_BASE") && inner.contains("Ok(true)"),
            "OP_1 arm must subtract the base and succeed"
        );
        inner
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_1(stack: &mut Vec<Vec<u8>>, opcode: u8) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_1: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_1 fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_1",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_1_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_1 must use the body");
            }
            other => panic!("unpatched OP_1 must pass, got {other:?}"),
        }
        let widened = format!("if stack.len() < 99 {{ return Ok(false); }}\n{body}");
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 99 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("OP_N_BASE", "OP_N_BASE_PLUS");
        assert_ne!(flipped, body, "the base must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the base must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_2_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_1..=OP_16 =>";
        let at = src.find(marker).expect("OP_2 arm");
        let inner = brace_inner(&src[at..]);
        assert!(
            inner.contains("opcode - OP_N_BASE") && inner.contains("Ok(true)"),
            "OP_2 arm must subtract the base and succeed"
        );
        inner
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_2(stack: &mut Vec<Vec<u8>>, opcode: u8) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_2: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_2 fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_2",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_2_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_2 must use the body");
            }
            other => panic!("unpatched OP_2 must pass, got {other:?}"),
        }
        let widened = format!("if stack.len() < 99 {{ return Ok(false); }}\n{body}");
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 99 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("OP_N_BASE", "OP_N_BASE_PLUS");
        assert_ne!(flipped, body, "the base must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the base must flip OP_2, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_3_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_1..=OP_16 =>";
        let at = src.find(marker).expect("OP_3 arm");
        let inner = brace_inner(&src[at..]);
        assert!(
            inner.contains("opcode - OP_N_BASE") && inner.contains("Ok(true)"),
            "OP_3 arm must subtract the base and succeed"
        );
        inner
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_3(stack: &mut Vec<Vec<u8>>, opcode: u8) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_3: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_3 fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_3",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_3_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_3 must use the body");
            }
            other => panic!("unpatched OP_3 must pass, got {other:?}"),
        }
        let widened = format!("if stack.len() < 99 {{ return Ok(false); }}\n{body}");
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 99 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("OP_N_BASE", "OP_N_BASE_PLUS");
        assert_ne!(flipped, body, "the base must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the base must flip OP_3, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_4_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_1..=OP_16 =>";
        let at = src.find(marker).expect("OP_4 arm");
        let inner = brace_inner(&src[at..]);
        assert!(
            inner.contains("opcode - OP_N_BASE") && inner.contains("Ok(true)"),
            "OP_4 arm must subtract the base and succeed"
        );
        inner
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_4(stack: &mut Vec<Vec<u8>>, opcode: u8) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_4: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_4 fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_4",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_4_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_4 must use the body");
            }
            other => panic!("unpatched OP_4 must pass, got {other:?}"),
        }
        let widened = format!("if stack.len() < 99 {{ return Ok(false); }}\n{body}");
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 99 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("OP_N_BASE", "OP_N_BASE_PLUS");
        assert_ne!(flipped, body, "the base must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the base must flip OP_4, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_5_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_1..=OP_16 =>";
        let at = src.find(marker).expect("OP_5 arm");
        let inner = brace_inner(&src[at..]);
        assert!(
            inner.contains("opcode - OP_N_BASE") && inner.contains("Ok(true)"),
            "OP_5 arm must subtract the base and succeed"
        );
        inner
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_5(stack: &mut Vec<Vec<u8>>, opcode: u8) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_5: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_5 fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_5",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_5_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_5 must use the body");
            }
            other => panic!("unpatched OP_5 must pass, got {other:?}"),
        }
        let widened = format!("if stack.len() < 99 {{ return Ok(false); }}\n{body}");
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 99 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("OP_N_BASE", "OP_N_BASE_PLUS");
        assert_ne!(flipped, body, "the base must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the base must flip OP_5, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_6_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_1..=OP_16 =>";
        let at = src.find(marker).expect("OP_6 arm");
        let inner = brace_inner(&src[at..]);
        assert!(
            inner.contains("opcode - OP_N_BASE") && inner.contains("Ok(true)"),
            "OP_6 arm must subtract the base and succeed"
        );
        inner
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_6(stack: &mut Vec<Vec<u8>>, opcode: u8) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_6: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_6 fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_6",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_6_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_6 must use the body");
            }
            other => panic!("unpatched OP_6 must pass, got {other:?}"),
        }
        let widened = format!("if stack.len() < 99 {{ return Ok(false); }}\n{body}");
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 99 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("OP_N_BASE", "OP_N_BASE_PLUS");
        assert_ne!(flipped, body, "the base must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the base must flip OP_6, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_7_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_1..=OP_16 =>";
        let at = src.find(marker).expect("OP_7 arm");
        let inner = brace_inner(&src[at..]);
        assert!(
            inner.contains("opcode - OP_N_BASE") && inner.contains("Ok(true)"),
            "OP_7 arm must subtract the base and succeed"
        );
        inner
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_7(stack: &mut Vec<Vec<u8>>, opcode: u8) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_7: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_7 fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_7",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_7_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_7 must use the body");
            }
            other => panic!("unpatched OP_7 must pass, got {other:?}"),
        }
        let widened = format!("if stack.len() < 99 {{ return Ok(false); }}\n{body}");
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 99 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("OP_N_BASE", "OP_N_BASE_PLUS");
        assert_ne!(flipped, body, "the base must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the base must flip OP_7, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_8_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_1..=OP_16 =>";
        let at = src.find(marker).expect("OP_8 arm");
        let inner = brace_inner(&src[at..]);
        assert!(
            inner.contains("opcode - OP_N_BASE") && inner.contains("Ok(true)"),
            "OP_8 arm must subtract the base and succeed"
        );
        inner
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_8(stack: &mut Vec<Vec<u8>>, opcode: u8) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_8: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_8 fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_8",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_8_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_8 must use the body");
            }
            other => panic!("unpatched OP_8 must pass, got {other:?}"),
        }
        let widened = format!("if stack.len() < 99 {{ return Ok(false); }}\n{body}");
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 99 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("OP_N_BASE", "OP_N_BASE_PLUS");
        assert_ne!(flipped, body, "the base must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the base must flip OP_8, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_9_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_1..=OP_16 =>";
        let at = src.find(marker).expect("OP_9 arm");
        let inner = brace_inner(&src[at..]);
        assert!(
            inner.contains("opcode - OP_N_BASE") && inner.contains("Ok(true)"),
            "OP_9 arm must subtract the base and succeed"
        );
        inner
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_9(stack: &mut Vec<Vec<u8>>, opcode: u8) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_9: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_9 fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_9",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_9_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_9 must use the body");
            }
            other => panic!("unpatched OP_9 must pass, got {other:?}"),
        }
        let widened = format!("if stack.len() < 99 {{ return Ok(false); }}\n{body}");
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 99 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("OP_N_BASE", "OP_N_BASE_PLUS");
        assert_ne!(flipped, body, "the base must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the base must flip OP_9, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_10_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_1..=OP_16 =>";
        let at = src.find(marker).expect("OP_10 arm");
        let inner = brace_inner(&src[at..]);
        assert!(
            inner.contains("opcode - OP_N_BASE") && inner.contains("Ok(true)"),
            "OP_10 arm must subtract the base and succeed"
        );
        inner
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_10(stack: &mut Vec<Vec<u8>>, opcode: u8) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_10: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_10 fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_10",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_10_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_10 must use the body");
            }
            other => panic!("unpatched OP_10 must pass, got {other:?}"),
        }
        let widened = format!("if stack.len() < 99 {{ return Ok(false); }}\n{body}");
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 99 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("OP_N_BASE", "OP_N_BASE_PLUS");
        assert_ne!(flipped, body, "the base must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the base must flip OP_10, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_11_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_1..=OP_16 =>";
        let at = src.find(marker).expect("OP_11 arm");
        let inner = brace_inner(&src[at..]);
        assert!(
            inner.contains("opcode - OP_N_BASE") && inner.contains("Ok(true)"),
            "OP_11 arm must subtract the base and succeed"
        );
        inner
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_11(stack: &mut Vec<Vec<u8>>, opcode: u8) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_11: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_11 fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_11",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_11_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_11 must use the body");
            }
            other => panic!("unpatched OP_11 must pass, got {other:?}"),
        }
        let widened = format!("if stack.len() < 99 {{ return Ok(false); }}\n{body}");
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 99 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("OP_N_BASE", "OP_N_BASE_PLUS");
        assert_ne!(flipped, body, "the base must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the base must flip OP_11, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_12_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_1..=OP_16 =>";
        let at = src.find(marker).expect("OP_12 arm");
        let inner = brace_inner(&src[at..]);
        assert!(
            inner.contains("opcode - OP_N_BASE") && inner.contains("Ok(true)"),
            "OP_12 arm must subtract the base and succeed"
        );
        inner
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_12(stack: &mut Vec<Vec<u8>>, opcode: u8) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_12: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_12 fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_12",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_12_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_12 must use the body");
            }
            other => panic!("unpatched OP_12 must pass, got {other:?}"),
        }
        let widened = format!("if stack.len() < 99 {{ return Ok(false); }}\n{body}");
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 99 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("OP_N_BASE", "OP_N_BASE_PLUS");
        assert_ne!(flipped, body, "the base must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the base must flip OP_12, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_13_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_1..=OP_16 =>";
        let at = src.find(marker).expect("OP_13 arm");
        let inner = brace_inner(&src[at..]);
        assert!(
            inner.contains("opcode - OP_N_BASE") && inner.contains("Ok(true)"),
            "OP_13 arm must subtract the base and succeed"
        );
        inner
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_13(stack: &mut Vec<Vec<u8>>, opcode: u8) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_13: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_13 fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_13",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_13_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_13 must use the body");
            }
            other => panic!("unpatched OP_13 must pass, got {other:?}"),
        }
        let widened = format!("if stack.len() < 99 {{ return Ok(false); }}\n{body}");
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 99 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("OP_N_BASE", "OP_N_BASE_PLUS");
        assert_ne!(flipped, body, "the base must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the base must flip OP_13, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_14_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_1..=OP_16 =>";
        let at = src.find(marker).expect("OP_14 arm");
        let inner = brace_inner(&src[at..]);
        assert!(
            inner.contains("opcode - OP_N_BASE") && inner.contains("Ok(true)"),
            "OP_14 arm must subtract the base and succeed"
        );
        inner
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_14(stack: &mut Vec<Vec<u8>>, opcode: u8) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_14: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_14 fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_14",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_14_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_14 must use the body");
            }
            other => panic!("unpatched OP_14 must pass, got {other:?}"),
        }
        let widened = format!("if stack.len() < 99 {{ return Ok(false); }}\n{body}");
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 99 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("OP_N_BASE", "OP_N_BASE_PLUS");
        assert_ne!(flipped, body, "the base must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the base must flip OP_14, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_15_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_1..=OP_16 =>";
        let at = src.find(marker).expect("OP_15 arm");
        let inner = brace_inner(&src[at..]);
        assert!(
            inner.contains("opcode - OP_N_BASE") && inner.contains("Ok(true)"),
            "OP_15 arm must subtract the base and succeed"
        );
        inner
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_15(stack: &mut Vec<Vec<u8>>, opcode: u8) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_15: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_15 fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_15",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_15_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_15 must use the body");
            }
            other => panic!("unpatched OP_15 must pass, got {other:?}"),
        }
        let widened = format!("if stack.len() < 99 {{ return Ok(false); }}\n{body}");
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 99 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("OP_N_BASE", "OP_N_BASE_PLUS");
        assert_ne!(flipped, body, "the base must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the base must flip OP_15, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_16_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_1..=OP_16 =>";
        let at = src.find(marker).expect("OP_16 arm");
        let inner = brace_inner(&src[at..]);
        assert!(
            inner.contains("opcode - OP_N_BASE") && inner.contains("Ok(true)"),
            "OP_16 arm must subtract the base and succeed"
        );
        inner
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_16(stack: &mut Vec<Vec<u8>>, opcode: u8) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_16: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_16 fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_16",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_16_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_16 must use the body");
            }
            other => panic!("unpatched OP_16 must pass, got {other:?}"),
        }
        let widened = format!("if stack.len() < 99 {{ return Ok(false); }}\n{body}");
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 99 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("OP_N_BASE", "OP_N_BASE_PLUS");
        assert_ne!(flipped, body, "the base must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the base must flip OP_16, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_swap_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_SWAP =>";
        let mut from = 0;
        while let Some(rel) = src[from..].find(marker) {
            let at = from + rel;
            let end = at + marker.len();
            let next = src[end..].chars().next();
            if next.is_some_and(|c| c.is_ascii_alphanumeric() || c == '_') {
                from = end;
                continue;
            }
            let inner = brace_inner(&src[at..]);
            assert!(
                inner.contains("stack.len() >= 2")
                    && inner.contains("let top = stack.pop().unwrap()")
                    && inner.contains("let second = stack.pop().unwrap()")
                    && inner.contains("stack.push(top)")
                    && inner.contains("stack.push(second)")
                    && inner.contains("Ok(true)")
                    && inner.contains("Ok(false)"),
                "OP_SWAP arm must swap the two top elements"
            );
            return inner;
        }
        panic!("OP_SWAP arm");
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_swap(stack: &mut Vec<Vec<u8>>) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_SWAP: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_SWAP fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_SWAP",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_swap_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_SWAP must use the body");
            }
            other => panic!("unpatched OP_SWAP must pass, got {other:?}"),
        }
        let widened = body.replacen("stack.len() >= 2", "stack.len() >= 3", 1);
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 3 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("stack.push(second)", "stack.push(top)");
        assert_ne!(flipped, body, "the second push must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "pushing the top twice must flip OP_SWAP, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_2dup_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_2DUP =>";
        let mut from = 0;
        while let Some(rel) = src[from..].find(marker) {
            let at = from + rel;
            let end = at + marker.len();
            let next = src[end..].chars().next();
            if next.is_some_and(|c| c.is_ascii_alphanumeric() || c == '_') {
                from = end;
                continue;
            }
            let inner = brace_inner(&src[at..]);
            assert!(
                inner.contains("stack.len() >= 2")
                    && inner.contains("stack[stack.len() - 1].clone()")
                    && inner.contains("stack[stack.len() - 2].clone()")
                    && inner.contains("stack.push(second)")
                    && inner.contains("stack.push(top)")
                    && inner.contains("Ok(true)")
                    && inner.contains("Ok(false)"),
                "OP_2DUP arm must copy the two top elements"
            );
            return inner;
        }
        panic!("OP_2DUP arm");
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_2dup(stack: &mut Vec<Vec<u8>>) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_2DUP: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_2DUP fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_2DUP",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_2dup_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_2DUP must use the body");
            }
            other => panic!("unpatched OP_2DUP must pass, got {other:?}"),
        }
        let widened = body.replacen("stack.len() >= 2", "stack.len() >= 3", 1);
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 3 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("stack.push(second)", "stack.push(top)");
        assert_ne!(flipped, body, "the first push must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "pushing the top first must flip OP_2DUP, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_2rot_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_2ROT =>";
        let mut from = 0;
        while let Some(rel) = src[from..].find(marker) {
            let at = from + rel;
            let end = at + marker.len();
            let next = src[end..].chars().next();
            if next.is_some_and(|c| c.is_ascii_alphanumeric() || c == '_') {
                from = end;
                continue;
            }
            let inner = brace_inner(&src[at..]);
            assert!(
                inner.contains("stack.len() >= 6")
                    && inner.contains("stack.remove(stack.len() - 6)")
                    && inner.contains("stack.remove(stack.len() - 5)")
                    && inner.contains("stack.push(sixth)")
                    && inner.contains("stack.push(fifth)")
                    && inner.contains("Ok(true)")
                    && inner.contains("Ok(false)"),
                "OP_2ROT arm must move the fifth and sixth items"
            );
            return inner;
        }
        panic!("OP_2ROT arm");
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_2rot(stack: &mut Vec<Vec<u8>>) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_2ROT: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_2ROT fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_2ROT",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_2rot_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_2ROT must use the body");
            }
            other => panic!("unpatched OP_2ROT must pass, got {other:?}"),
        }
        let widened = body.replacen("stack.len() >= 6", "stack.len() >= 7", 1);
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 7 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("stack.push(sixth)", "stack.push(fifth)");
        assert_ne!(flipped, body, "the first push must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "pushing the fifth item twice must flip OP_2ROT, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_2swap_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_2SWAP =>";
        let mut from = 0;
        while let Some(rel) = src[from..].find(marker) {
            let at = from + rel;
            let end = at + marker.len();
            let next = src[end..].chars().next();
            if next.is_some_and(|c| c.is_ascii_alphanumeric() || c == '_') {
                from = end;
                continue;
            }
            let inner = brace_inner(&src[at..]);
            assert!(
                inner.contains("stack.len() >= 4")
                    && inner.contains("let top = stack.pop().unwrap()")
                    && inner.contains("let second = stack.pop().unwrap()")
                    && inner.contains("let third = stack.pop().unwrap()")
                    && inner.contains("let fourth = stack.pop().unwrap()")
                    && inner.contains("stack.push(second)")
                    && inner.contains("stack.push(top)")
                    && inner.contains("stack.push(fourth)")
                    && inner.contains("stack.push(third)")
                    && inner.contains("Ok(true)")
                    && inner.contains("Ok(false)"),
                "OP_2SWAP arm must swap the two pairs"
            );
            return inner;
        }
        panic!("OP_2SWAP arm");
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_2swap(stack: &mut Vec<Vec<u8>>) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_2SWAP: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_2SWAP fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_2SWAP",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_2swap_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_2SWAP must use the body");
            }
            other => panic!("unpatched OP_2SWAP must pass, got {other:?}"),
        }
        let widened = body.replacen("stack.len() >= 4", "stack.len() >= 5", 1);
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 5 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("stack.push(second)", "stack.push(top)");
        assert_ne!(flipped, body, "the first push must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "pushing the top first must flip OP_2SWAP, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_3dup_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_3DUP =>";
        let mut from = 0;
        while let Some(rel) = src[from..].find(marker) {
            let at = from + rel;
            let end = at + marker.len();
            let next = src[end..].chars().next();
            if next.is_some_and(|c| c.is_ascii_alphanumeric() || c == '_') {
                from = end;
                continue;
            }
            let inner = brace_inner(&src[at..]);
            if inner.contains("stack[stack.len() - 1].clone()")
                && inner.contains("stack[stack.len() - 2].clone()")
                && inner.contains("stack[stack.len() - 3].clone()")
                && inner.contains("stack.push(third)")
                && inner.contains("stack.push(second)")
                && inner.contains("stack.push(top)")
                && inner.contains("stack.len() >= 3")
                && inner.contains("Ok(true)")
                && inner.contains("Ok(false)")
            {
                return inner;
            }
            from = end;
        }
        panic!("OP_3DUP arm");
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_3dup(stack: &mut Vec<Vec<u8>>) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_3DUP: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_3DUP fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_3DUP",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_3dup_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_3DUP must use the body");
            }
            other => panic!("unpatched OP_3DUP must pass, got {other:?}"),
        }
        let widened = body.replacen("stack.len() >= 3", "stack.len() >= 4", 1);
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 4 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("stack.push(second)", "stack.push(top)");
        assert_ne!(flipped, body, "the second push must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "pushing the top second must flip OP_3DUP, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_rot_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_ROT =>";
        let mut from = 0;
        while let Some(rel) = src[from..].find(marker) {
            let at = from + rel;
            let end = at + marker.len();
            let next = src[end..].chars().next();
            if next.is_some_and(|c| c.is_ascii_alphanumeric() || c == '_') {
                from = end;
                continue;
            }
            let inner = brace_inner(&src[at..]);
            if inner.contains("let top = stack.pop().unwrap()")
                && inner.contains("let second = stack.pop().unwrap()")
                && inner.contains("let third = stack.pop().unwrap()")
                && inner.contains("stack.push(second)")
                && inner.contains("stack.push(top)")
                && inner.contains("stack.push(third)")
                && inner.contains("stack.len() >= 3")
                && inner.contains("Ok(true)")
                && inner.contains("Ok(false)")
            {
                return inner;
            }
            from = end;
        }
        panic!("OP_ROT arm");
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src =
            format!("fn op_rot(stack: &mut Vec<Vec<u8>>) -> Result<bool, String> {{\n{body}\n}}\n");
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_ROT: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_ROT fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_ROT",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_rot_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_ROT must use the body");
            }
            other => panic!("unpatched OP_ROT must pass, got {other:?}"),
        }
        let widened = body.replacen("stack.len() >= 3", "stack.len() >= 4", 1);
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 4 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("stack.push(second)", "stack.push(top)");
        assert_ne!(flipped, body, "the first push must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "pushing the top first must flip OP_ROT, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_tuck_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_TUCK =>";
        let mut from = 0;
        while let Some(rel) = src[from..].find(marker) {
            let at = from + rel;
            let end = at + marker.len();
            let next = src[end..].chars().next();
            if next.is_some_and(|c| c.is_ascii_alphanumeric() || c == '_') {
                from = end;
                continue;
            }
            let inner = brace_inner(&src[at..]);
            if inner.contains("let top = stack.pop().unwrap()")
                && inner.contains("let second = stack.pop().unwrap()")
                && inner.contains("stack.push(top.clone())")
                && inner.contains("stack.push(second)")
                && inner.contains("stack.push(top)")
                && inner.contains("stack.len() >= 2")
                && inner.contains("Ok(true)")
                && inner.contains("Ok(false)")
            {
                return inner;
            }
            from = end;
        }
        panic!("OP_TUCK arm");
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_tuck(stack: &mut Vec<Vec<u8>>) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_TUCK: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_TUCK fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_TUCK",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_tuck_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_TUCK must use the body");
            }
            other => panic!("unpatched OP_TUCK must pass, got {other:?}"),
        }
        let widened = body.replacen("stack.len() >= 2", "stack.len() >= 3", 1);
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 3 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("stack.push(second)", "stack.push(top)");
        assert_ne!(flipped, body, "the middle push must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "pushing the top in the middle must flip OP_TUCK, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_nip_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_NIP =>";
        let mut from = 0;
        while let Some(rel) = src[from..].find(marker) {
            let at = from + rel;
            let end = at + marker.len();
            let next = src[end..].chars().next();
            if next.is_some_and(|c| c.is_ascii_alphanumeric() || c == '_') {
                from = end;
                continue;
            }
            let inner = brace_inner(&src[at..]);
            if inner.contains("let top = stack.pop().unwrap()")
                && inner.contains("stack.pop()")
                && inner.contains("stack.push(top)")
                && inner.contains("stack.len() >= 2")
                && inner.contains("Ok(true)")
                && inner.contains("Ok(false)")
            {
                return inner;
            }
            from = end;
        }
        panic!("OP_NIP arm");
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src =
            format!("fn op_nip(stack: &mut Vec<Vec<u8>>) -> Result<bool, String> {{\n{body}\n}}\n");
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_NIP: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_NIP fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_NIP",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_nip_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_NIP must use the body");
            }
            other => panic!("unpatched OP_NIP must pass, got {other:?}"),
        }
        let widened = body.replacen("stack.len() >= 2", "stack.len() >= 3", 1);
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 3 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("stack.push(top)", "stack.push(second)");
        assert_ne!(flipped, body, "the pushed item must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "pushing the removed item must flip OP_NIP, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_ifdup_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_IFDUP =>";
        let mut from = 0;
        while let Some(rel) = src[from..].find(marker) {
            let at = from + rel;
            let end = at + marker.len();
            let next = src[end..].chars().next();
            if next.is_some_and(|c| c.is_ascii_alphanumeric() || c == '_') {
                from = end;
                continue;
            }
            let inner = brace_inner(&src[at..]);
            if inner.contains("stack.last().cloned()")
                && inner.contains("cast_to_bool(&item)")
                && inner.contains("stack.push(item)")
                && inner.contains("Ok(true)")
                && inner.contains("Ok(false)")
            {
                return inner;
            }
            from = end;
        }
        panic!("OP_IFDUP arm");
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_ifdup(stack: &mut Vec<Vec<u8>>) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_IFDUP: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_IFDUP fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_IFDUP",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_ifdup_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_IFDUP must use the body");
            }
            other => panic!("unpatched OP_IFDUP must pass, got {other:?}"),
        }
        let widened = format!("if stack.len() < 99 {{ return Ok(false); }}\n{body}");
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 99 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("stack.push(item)", "stack.push(Vec::new())");
        assert_ne!(flipped, body, "the pushed element must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "pushing an empty element must flip OP_IFDUP, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_pick_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_PICK =>";
        let mut from = 0;
        while let Some(rel) = src[from..].find(marker) {
            let at = from + rel;
            let end = at + marker.len();
            let next = src[end..].chars().next();
            if next.is_some_and(|c| c.is_ascii_alphanumeric() || c == '_') {
                from = end;
                continue;
            }
            let inner = brace_inner(&src[at..]);
            if inner.contains("script_num_is_minimally_encoded")
                && inner.contains("script_num_decode")
                && inner.contains("n_val < 0")
                && inner.contains("get_unchecked")
                && inner.contains("len - 1 - n")
                && inner.contains("stack.len() - 1 - n")
                && inner.contains("Ok(true)")
                && inner.contains("Ok(false)")
            {
                return inner;
            }
            from = end;
        }
        panic!("OP_PICK arm");
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_pick(stack: &mut Vec<Vec<u8>>, flags: u32) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_PICK: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_PICK fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_PICK",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_pick_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_PICK must use the body");
            }
            other => panic!("unpatched OP_PICK must pass, got {other:?}"),
        }
        let widened = format!("if stack.len() < 99 {{ return Ok(false); }}\n{body}");
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 99 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("len - 1 - n", "len - 2 - n");
        assert_ne!(flipped, body, "the pick index must change");
        assert!(
            flipped.contains("stack.len() - 1 - n"),
            "the other cfg keeps its index"
        );
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "shifting the pick index must flip OP_PICK, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_roll_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_ROLL =>";
        let mut from = 0;
        while let Some(rel) = src[from..].find(marker) {
            let at = from + rel;
            let end = at + marker.len();
            let next = src[end..].chars().next();
            if next.is_some_and(|c| c.is_ascii_alphanumeric() || c == '_') {
                from = end;
                continue;
            }
            let inner = brace_inner(&src[at..]);
            if inner.contains("script_num_is_minimally_encoded")
                && inner.contains("script_num_decode")
                && inner.contains("n_val < 0")
                && inner.contains("stack.remove")
                && inner.contains("len - 1 - n")
                && inner.contains("stack.len() - 1 - n")
                && inner.contains("Ok(true)")
                && inner.contains("Ok(false)")
            {
                return inner;
            }
            from = end;
        }
        panic!("OP_ROLL arm");
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_roll(stack: &mut Vec<Vec<u8>>, flags: u32) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_ROLL: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_ROLL fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_ROLL",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_roll_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_ROLL must use the body");
            }
            other => panic!("unpatched OP_ROLL must pass, got {other:?}"),
        }
        let widened = format!("if stack.len() < 99 {{ return Ok(false); }}\n{body}");
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 99 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("len - 1 - n", "len - 2 - n");
        assert_ne!(flipped, body, "the roll index must change");
        assert!(
            flipped.contains("stack.len() - 1 - n"),
            "the other cfg keeps its index"
        );
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "shifting the roll index must flip OP_ROLL, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_verify_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_VERIFY =>";
        let mut from = 0;
        while let Some(rel) = src[from..].find(marker) {
            let at = from + rel;
            let end = at + marker.len();
            let next = src[end..].chars().next();
            if next.is_some_and(|c| c.is_ascii_alphanumeric() || c == '_') {
                from = end;
                continue;
            }
            let inner = brace_inner(&src[at..]);
            if inner.contains("cast_to_bool(&item)")
                && inner.contains("stack.pop()")
                && inner.contains("Ok(false)")
            {
                return inner;
            }
            from = end;
        }
        panic!("OP_VERIFY arm");
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_verify(stack: &mut Vec<Vec<u8>>) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_VERIFY: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_VERIFY fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_VERIFY",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_verify_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_VERIFY must use the body");
            }
            other => panic!("unpatched OP_VERIFY must pass, got {other:?}"),
        }
        let widened = format!("if stack.len() < 99 {{ return Ok(false); }}\n{body}");
        assert_ne!(widened, body, "the length gate must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 99 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = body.replace("cast_to_bool", "cast_to_true");
        assert_ne!(flipped, body, "the bool cast must change");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "renaming the bool cast must flip OP_VERIFY, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_hash160_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn hash160_fn() -> syn::ItemFn {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../blvm-consensus/src/script/crypto_ops.rs");
        let src = std::fs::read_to_string(path).expect("crypto_ops.rs");
        let file = syn::parse_file(&src).expect("parse crypto_ops.rs");
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "op_hash160" => Some(func),
                _ => None,
            })
            .expect("op_hash160")
    }

    fn reparse(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).unwrap_or_else(|err| panic!("parse OP_HASH160: {err}"));
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) => Some(func),
                _ => None,
            })
            .expect("OP_HASH160 fn")
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/crypto_ops.rs"),
            "OP_HASH160",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_hash160_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let func = hash160_fn();
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_HASH160 must use the body");
            }
            other => panic!("unpatched OP_HASH160 must pass, got {other:?}"),
        }
        let original = quote::quote!(#func).to_string();
        let brace = original.find('{').expect("fn brace");
        let widened = format!(
            "{} if stack.len() < 99 {{ return Ok(false); }}{}",
            &original[..=brace],
            &original[brace + 1..]
        );
        assert_ne!(widened, original, "the length gate must change");
        let widened_result = identity_query(&reparse(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 99 stack elements must flip the identity, got {widened_result:?}"
        );
        let flipped = original
            .replace("op_hash160", "op_sha256")
            .replace("Ripemd160", "GoneHash");
        assert!(
            flipped.contains("GoneHash"),
            "the digest must change, got {flipped}"
        );
        let flipped_result = identity_query(&reparse(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "replacing RIPEMD-160 must flip OP_HASH160, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_checksigadd_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_CHECKSIGADD =>";
        let mut from = 0;
        while let Some(rel) = src[from..].find(marker) {
            let at = from + rel;
            let end = at + marker.len();
            let next = src[end..].chars().next();
            if next.is_some_and(|c| c.is_ascii_alphanumeric() || c == '_') {
                from = end;
                continue;
            }
            let inner = brace_inner(&src[at..]);
            if inner.contains("SigVersion::Tapscript")
                && inner.contains("stack.len() < 3")
                && inner.contains("script_num_is_minimally_encoded")
                && inner.contains("script_num_decode")
                && inner.contains("eval_checksig_tapscript")
                && inner.contains("n + 1")
                && inner.contains("script_num_encode")
                && inner.contains("Ok(false)")
                && inner.contains("Ok(true)")
            {
                return inner;
            }
            from = end;
        }
        panic!("OP_CHECKSIGADD arm");
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_checksigadd(stack: &mut Vec<Vec<u8>>, flags: u32, sigversion: u8, ctx: u8) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file =
            syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_CHECKSIGADD: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_CHECKSIGADD fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_CHECKSIGADD",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_checksigadd_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_CHECKSIGADD must use the body");
            }
            other => panic!("unpatched OP_CHECKSIGADD must pass, got {other:?}"),
        }
        let widened = body.replacen("stack.len() < 3", "stack.len() < 4", 1);
        assert_ne!(widened, body, "the stack bound must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 4 stack elements must flip OP_CHECKSIGADD, got {widened_result:?}"
        );
        let flipped = body.replace("n + 1", "n + 2");
        assert_ne!(flipped, body, "the addend must change");
        assert!(flipped.contains("stack.len() < 3"), "the stack bound stays");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "raising the addend must flip OP_CHECKSIGADD, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_checksigverify_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_CHECKSIGVERIFY =>";
        let mut from = 0;
        while let Some(rel) = src[from..].find(marker) {
            let at = from + rel;
            let end = at + marker.len();
            let next = src[end..].chars().next();
            if next.is_some_and(|c| c.is_ascii_alphanumeric() || c == '_') {
                from = end;
                continue;
            }
            let inner = brace_inner(&src[at..]);
            if inner.contains("stack.len() >= 2")
                && inner.contains("SigVersion::Tapscript")
                && inner.contains("eval_checksig_tapscript")
                && inner.contains("signature_bytes.is_empty()")
                && inner.contains("eval_checksig_ecdsa")
                && inner.contains("Ok(is_valid)")
                && inner.contains("Ok(false)")
            {
                return inner;
            }
            from = end;
        }
        panic!("OP_CHECKSIGVERIFY arm");
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_checksigverify(stack: &mut Vec<Vec<u8>>, flags: u32, sigversion: u8, ctx: u8, redeem_script_for_sighash: &[u8]) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file =
            syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_CHECKSIGVERIFY: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_CHECKSIGVERIFY fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_CHECKSIGVERIFY",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_checksigverify_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_CHECKSIGVERIFY must use the body");
            }
            other => panic!("unpatched OP_CHECKSIGVERIFY must pass, got {other:?}"),
        }
        let widened = body.replacen("stack.len() >= 2", "stack.len() >= 3", 1);
        assert_ne!(widened, body, "the stack bound must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 3 stack elements must flip OP_CHECKSIGVERIFY, got {widened_result:?}"
        );
        let flipped = body.replace("eval_checksig_ecdsa(", "eval_checksig_gone(");
        assert_ne!(flipped, body, "the verifier must change");
        assert!(
            flipped.contains("stack.len() >= 2"),
            "the stack bound stays"
        );
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "renaming the ECDSA verifier must flip OP_CHECKSIGVERIFY, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_checksig_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced braces");
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_CHECKSIG =>";
        let mut from = 0;
        while let Some(rel) = src[from..].find(marker) {
            let at = from + rel;
            let end = at + marker.len();
            let next = src[end..].chars().next();
            if next.is_some_and(|c| c.is_ascii_alphanumeric() || c == '_') {
                from = end;
                continue;
            }
            let inner = brace_inner(&src[at..]);
            if inner.contains("stack.len() >= 2")
                && inner.contains("SigVersion::Tapscript")
                && inner.contains("eval_checksig_tapscript")
                && inner.contains("signature_bytes.is_empty()")
                && inner.contains("SCRIPT_VERIFY_STRICTENC")
                && inner.contains("SCRIPT_VERIFY_WITNESS_PUBKEYTYPE")
                && inner.contains("SCRIPT_VERIFY_NULLFAIL")
                && inner.contains("eval_checksig_ecdsa")
                && inner.contains("script_bool_bytes")
                && inner.contains("Ok(false)")
            {
                return inner;
            }
            from = end;
        }
        panic!("OP_CHECKSIG arm");
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_checksig(stack: &mut Vec<Vec<u8>>, flags: u32, sigversion: u8, ctx: u8, redeem_script_for_sighash: &[u8]) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_CHECKSIG: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_CHECKSIG fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_CHECKSIG",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_checksig_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let script = std::fs::read_to_string(path).expect("script/mod.rs");
        let body = arm_body(&script);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_CHECKSIG must use the body");
            }
            other => panic!("unpatched OP_CHECKSIG must pass, got {other:?}"),
        }
        let widened = body.replacen("stack.len() >= 2", "stack.len() >= 3", 1);
        assert_ne!(widened, body, "the stack bound must change");
        let widened_result = identity_query(&decode_fn(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 3 stack elements must flip OP_CHECKSIG, got {widened_result:?}"
        );
        let flipped = body.replace("eval_checksig_ecdsa(", "eval_checksig_gone(");
        assert_ne!(flipped, body, "the verifier must change");
        assert!(
            flipped.contains("stack.len() >= 2"),
            "the stack bound stays"
        );
        assert!(flipped.contains("SCRIPT_VERIFY_NULLFAIL"), "NULLFAIL stays");
        let flipped_result = identity_query(&decode_fn(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "renaming the ECDSA verifier must flip OP_CHECKSIG, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod sig_from_stack_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn function_src() -> String {
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/bip348.rs");
        let src = std::fs::read_to_string(path).expect("bip348.rs");
        let marker = "fn verify_signature_from_stack(";
        let start = src.find(marker).expect("fn");
        let rest = &src[start..];
        let bytes = rest.as_bytes();
        let mut depth = 0i32;
        let mut started = false;
        for (i, byte) in bytes.iter().enumerate() {
            if *byte == b'{' {
                depth += 1;
                started = true;
            } else if *byte == b'}' {
                depth -= 1;
                if started && depth == 0 {
                    return rest[..=i].to_string();
                }
            }
        }
        panic!("unbalanced verify_signature_from_stack");
    }

    fn extract(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).unwrap_or_else(|err| panic!("parse CSFS: {err}"));
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "verify_signature_from_stack" => {
                    Some(func)
                }
                _ => None,
            })
            .expect("verify_signature_from_stack")
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/bip348.rs"),
            "verify_signature_from_stack",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn sig_from_stack_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let src = function_src();
        let func = extract(&src);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(
                    body_translated,
                    "verify_signature_from_stack must use the body"
                );
            }
            other => panic!("unpatched verify_signature_from_stack must pass, got {other:?}"),
        }
        let widened = src.replace("signature.len() != 64", "signature.len() != 65");
        assert_ne!(widened, src, "the signature length must change");
        let widened_result = identity_query(&extract(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "rejecting a 64-byte signature must flip the identity, got {widened_result:?}"
        );
        let flipped = src.replace("pubkey.len() == 32", "pubkey.len() == 33");
        assert_ne!(flipped, src, "the pubkey length must change");
        assert!(
            flipped.contains("signature.len() != 64"),
            "the signature length stays"
        );
        let flipped_result = identity_query(&extract(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "moving the 32-byte key check must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod tap_schnorr_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn function_src() -> String {
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/bip348.rs");
        let src = std::fs::read_to_string(path).expect("bip348.rs");
        let marker = "fn verify_tapscript_schnorr_signature(";
        let start = src.find(marker).expect("fn");
        let rest = &src[start..];
        let bytes = rest.as_bytes();
        let mut depth = 0i32;
        let mut started = false;
        for (i, byte) in bytes.iter().enumerate() {
            if *byte == b'{' {
                depth += 1;
                started = true;
            } else if *byte == b'}' {
                depth -= 1;
                if started && depth == 0 {
                    return rest[..=i].to_string();
                }
            }
        }
        panic!("unbalanced verify_tapscript_schnorr_signature");
    }

    fn extract(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).unwrap_or_else(|err| panic!("parse tapscript: {err}"));
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "verify_tapscript_schnorr_signature" => {
                    Some(func)
                }
                _ => None,
            })
            .expect("verify_tapscript_schnorr_signature")
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/bip348.rs"),
            "verify_tapscript_schnorr_signature",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn tap_schnorr_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let src = function_src();
        let func = extract(&src);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(
                    body_translated,
                    "verify_tapscript_schnorr_signature must use the body"
                );
            }
            other => {
                panic!("unpatched verify_tapscript_schnorr_signature must pass, got {other:?}")
            }
        }
        let widened = src.replace("pubkey.len() != 32", "pubkey.len() != 33");
        assert_ne!(widened, src, "the pubkey length must change");
        assert!(
            widened.contains("signature.try_into()"),
            "the signature conversion stays"
        );
        let widened_result = identity_query(&extract(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "moving the 32-byte key check must flip the identity, got {widened_result:?}"
        );
        let flipped = src.replace("signature.try_into()", "signature.len()");
        assert_ne!(flipped, src, "the signature conversion must change");
        assert!(
            flipped.contains("pubkey.len() != 32"),
            "the pubkey length stays"
        );
        let flipped_result = identity_query(&extract(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "removing the 64-byte conversion must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod verify_signature_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn function_src() -> String {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../blvm-consensus/src/script/signature.rs");
        let src = std::fs::read_to_string(path).expect("signature.rs");
        let marker = "fn verify_signature(";
        let start = src.find(marker).expect("fn");
        let rest = &src[start..];
        let bytes = rest.as_bytes();
        let mut depth = 0i32;
        let mut started = false;
        for (i, byte) in bytes.iter().enumerate() {
            if *byte == b'{' {
                depth += 1;
                started = true;
            } else if *byte == b'}' {
                depth -= 1;
                if started && depth == 0 {
                    return rest[..=i].to_string();
                }
            }
        }
        panic!("unbalanced verify_signature");
    }

    fn extract(src: &str) -> syn::ItemFn {
        let file =
            syn::parse_file(src).unwrap_or_else(|err| panic!("parse verify_signature: {err}"));
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "verify_signature" => Some(func),
                _ => None,
            })
            .expect("verify_signature")
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/signature.rs"),
            "verify_signature",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn verify_signature_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let src = function_src();
        let func = extract(&src);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "verify_signature must use the body");
            }
            other => panic!("unpatched verify_signature must pass, got {other:?}"),
        }
        let widened = src.replace("signature_bytes.is_empty()", "false");
        assert_ne!(widened, src, "the empty-signature test must change");
        assert!(widened.contains("0x01..=0x03"), "the sighash range stays");
        let widened_result = identity_query(&extract(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "dropping the empty-signature test must flip the identity, got {widened_result:?}"
        );
        let flipped = src.replace("0x01..=0x03", "0x00..=0x03");
        assert_ne!(flipped, src, "the sighash range must change");
        assert!(
            flipped.contains("signature_bytes.is_empty()"),
            "the empty-signature test stays"
        );
        let flipped_result = identity_query(&extract(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "widening the sighash range must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod check_pow_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn slice_fn(src: &str, marker: &str) -> String {
        let start = src.find(marker).expect(marker);
        let rest = &src[start..];
        let mut depth = 0i32;
        let mut started = false;
        for (i, byte) in rest.bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
                started = true;
            } else if byte == b'}' {
                depth -= 1;
                if started && depth == 0 {
                    return rest[..=i].to_string();
                }
            }
        }
        panic!("unbalanced {marker}");
    }

    fn inner(src: &str) -> String {
        let brace = src.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in src[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return src[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced inner");
    }

    fn function_src() -> String {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/pow.rs");
        let src = std::fs::read_to_string(path).expect("pow.rs");
        let check = slice_fn(&src, "fn check_proof_of_work(");
        let meets = inner(&slice_fn(&src, "fn proof_hash_meets_target("));
        let call = "proof_hash_meets_target(header.bits, &U256::from_bytes(&hash_bytes))";
        assert!(check.contains(call), "the target call stays in the caller");
        let inline = format!(
            "{{ let bits = header.bits; let hash_value = U256::from_bytes(&hash_bytes); {meets} }}"
        );
        check.replace(call, &inline)
    }

    fn extract(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).unwrap_or_else(|err| panic!("parse pow: {err}"));
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "check_proof_of_work" => Some(func),
                _ => None,
            })
            .expect("check_proof_of_work")
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/pow.rs"),
            "check_proof_of_work",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn check_pow_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let src = function_src();
        let func = extract(&src);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "check_proof_of_work must use the body");
            }
            other => panic!("unpatched check_proof_of_work must pass, got {other:?}"),
        }
        let widened = src.replacen("Sha256::digest", "skipped_digest", 1);
        assert!(
            widened.contains("skipped_digest"),
            "the first round must change"
        );
        assert!(widened.contains("Sha256::digest"), "the second round stays");
        let widened_result = identity_query(&extract(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "skipping the first SHA-256 must flip the identity, got {widened_result:?}"
        );
        let flipped = src.replace("hash_value <= target", "hash_value < target");
        assert_ne!(flipped, src, "the comparison must change");
        assert!(flipped.contains("Sha256::digest"), "both hash rounds stay");
        let flipped_result = identity_query(&extract(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "tightening the target comparison must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod merkle_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    const MERKLE_CMP: &str = r#"        for pos in (0..hashes.len().saturating_sub(1)).step_by(2) {
            if hashes[pos] == hashes[pos + 1] {
                mutated = true;
            }
        }"#;
    const MERKLE_PAD: &str = r#"        if hashes.len() & 1 != 0 {
            hashes.push(hashes[hashes.len() - 1]);
        }"#;

    fn function_src() -> String {
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/mining.rs");
        let src = std::fs::read_to_string(path).expect("mining.rs");
        let marker = "fn merkle_tree_from_hashes(";
        let start = src.find(marker).expect("fn");
        let rest = &src[start..];
        let mut depth = 0i32;
        let mut started = false;
        for (i, byte) in rest.bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
                started = true;
            } else if byte == b'}' {
                depth -= 1;
                if started && depth == 0 {
                    return rest[..=i].to_string();
                }
            }
        }
        panic!("unbalanced merkle_tree_from_hashes");
    }

    fn extract(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).unwrap_or_else(|err| panic!("parse merkle: {err}"));
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "merkle_tree_from_hashes" => Some(func),
                _ => None,
            })
            .expect("merkle_tree_from_hashes")
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/mining.rs"),
            "merkle_tree_from_hashes",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn merkle_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let src = function_src();
        assert!(src.contains(MERKLE_CMP), "the duplicate scan stays");
        assert!(src.contains(MERKLE_PAD), "the odd-length pad stays");
        let func = extract(&src);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "merkle_tree_from_hashes must use the body");
            }
            other => panic!("unpatched merkle_tree_from_hashes must pass, got {other:?}"),
        }
        let widened = src.replace(MERKLE_CMP, "");
        assert_ne!(widened, src, "the duplicate scan must be removed");
        let widened_result = identity_query(&extract(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "removing the duplicate scan must flip the identity, got {widened_result:?}"
        );
        let flipped = src
            .replace(MERKLE_CMP, "")
            .replace(MERKLE_PAD, &format!("{MERKLE_PAD}\n{MERKLE_CMP}"));
        assert!(flipped.contains(MERKLE_CMP), "the scan moves below the pad");
        let flipped_result = identity_query(&extract(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "checking duplicates after the pad must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod chain_work_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn function_src() -> String {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../blvm-consensus/src/reorganization.rs");
        let src = std::fs::read_to_string(path).expect("reorganization.rs");
        let marker = "fn calculate_chain_work(";
        let start = src.find(marker).expect("fn");
        let rest = &src[start..];
        let mut depth = 0i32;
        let mut started = false;
        for (i, byte) in rest.bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
                started = true;
            } else if byte == b'}' {
                depth -= 1;
                if started && depth == 0 {
                    return rest[..=i].to_string();
                }
            }
        }
        panic!("unbalanced calculate_chain_work");
    }

    fn extract(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).unwrap_or_else(|err| panic!("parse chain work: {err}"));
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "calculate_chain_work" => Some(func),
                _ => None,
            })
            .expect("calculate_chain_work")
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/reorganization.rs"),
            "calculate_chain_work",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn chain_work_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let src = function_src();
        let func = extract(&src);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "calculate_chain_work must use the body");
            }
            other => panic!("unpatched calculate_chain_work must pass, got {other:?}"),
        }
        let widened = src.replace(
            "total_work = total_work.saturating_add(work_contribution);",
            "total_work = old_total;",
        );
        assert_ne!(widened, src, "the add must become the previous total");
        let widened_result = identity_query(&extract(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "keeping the previous total must flip the identity, got {widened_result:?}"
        );
        let flipped = src.replace(
            "saturating_add(work_contribution)",
            "saturating_add(work_contribution.saturating_add(U256::one()))",
        );
        assert_ne!(flipped, src, "each block must add one extra");
        let flipped_result = identity_query(&extract(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "adding one per block must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod retarget_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn item_src(name: &str) -> String {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/pow.rs");
        let src = std::fs::read_to_string(path).expect("pow.rs");
        let marker = format!("fn {name}(");
        let start = src.find(&marker).expect("fn");
        let rest = &src[start..];
        let mut depth = 0i32;
        let mut started = false;
        for (i, byte) in rest.bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
                started = true;
            } else if byte == b'}' {
                depth -= 1;
                if started && depth == 0 {
                    return rest[..=i].to_string();
                }
            }
        }
        panic!("unbalanced {name}");
    }

    fn interior(item: &str) -> String {
        let start = item.find('{').expect("body");
        let end = item.rfind('}').expect("end");
        item[start + 1..end].to_string()
    }

    fn stitch(mul: &str, div: &str) -> String {
        let mul_body = interior(mul)
            .replace("self", "this")
            .replace("rhs", "mul_rhs");
        let div_body = interior(div)
            .replace("self", "this")
            .replace("rhs", "div_rhs");
        format!(
            "fn retarget_mul_div(w0: u64, w1: u64, w2: u64, w3: u64, mul_rhs: u64, div_rhs: u64) -> Result<(bool, u64, u64, u64, u64, u64, u64, u64, u64)> {{\nlet _mul = {{{mul_body}}};\nlet _div = {{{div_body}}};\n}}"
        )
    }

    fn extract(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).unwrap_or_else(|err| panic!("parse retarget: {err}"));
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "retarget_mul_div" => Some(func),
                _ => None,
            })
            .expect("retarget_mul_div")
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/pow.rs"),
            "retarget_mul_div",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 60, &[])
    }

    #[test]
    fn retarget_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let mul = item_src("checked_mul_u64");
        let div = item_src("div_u64");
        let src = stitch(&mul, &div);
        let func = extract(&src);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "retarget_mul_div must use the body");
            }
            other => panic!("unpatched retarget_mul_div must pass, got {other:?}"),
        }
        let widened = stitch(&mul.replace("product >> 64", "product >> 32"), &div);
        assert_ne!(widened, src, "the carry shift must change");
        let widened_result = identity_query(&extract(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "shifting the carry by 32 must flip the identity, got {widened_result:?}"
        );
        let flipped = stitch(
            &mul,
            &div.replace(
                "(remainder << 64) | (self.0[3] as u128)",
                "(remainder << 64) | (self.0[0] as u128)",
            ),
        );
        assert_ne!(flipped, src, "the first dividend limb must change");
        let flipped_result = identity_query(&extract(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "reading the low limb first must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod nested_weight_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn function_src() -> String {
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/segwit.rs");
        let src = std::fs::read_to_string(path).expect("segwit.rs");
        let marker = "fn calculate_block_weight_from_nested(";
        let start = src.find(marker).expect("fn");
        let rest = &src[start..];
        let mut depth = 0i32;
        let mut started = false;
        for (i, byte) in rest.bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
                started = true;
            } else if byte == b'}' {
                depth -= 1;
                if started && depth == 0 {
                    return rest[..=i].to_string();
                }
            }
        }
        panic!("unbalanced calculate_block_weight_from_nested");
    }

    fn extract(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).unwrap_or_else(|err| panic!("parse nested weight: {err}"));
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "calculate_block_weight_from_nested" => {
                    Some(func)
                }
                _ => None,
            })
            .expect("calculate_block_weight_from_nested")
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/segwit.rs"),
            "calculate_block_weight_from_nested",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn nested_weight_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let file =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/segwit.rs");
        let full = std::fs::read_to_string(file).expect("segwit.rs");
        assert!(
            full.contains("fn compact_size_len(n: u64) -> u64 {\n    if n < 0xfd {\n        1\n    } else if n <= 0xffff {\n        3\n    } else if n <= 0xffff_ffff {\n        5\n    } else {\n        9\n    }"),
            "the compact-size arms stay"
        );
        let src = function_src();
        let func = extract(&src);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(
                    body_translated,
                    "calculate_block_weight_from_nested must use the body"
                );
            }
            other => panic!("unpatched nested weight must pass, got {other:?}"),
        }
        let widened = src.replace("checked_mul(4)", "checked_mul(0)");
        assert_ne!(widened, src, "the prefix scale must change");
        let widened_result = identity_query(&extract(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "scaling the prefix by zero must flip the identity, got {widened_result:?}"
        );
        let flipped = src.replace(".checked_add(", ".checked_sub(");
        assert_ne!(flipped, src, "the transaction weight must be subtracted");
        let flipped_result = identity_query(&extract(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "subtracting transaction weight must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod witness_commit_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn item_src(name: &str) -> String {
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/segwit.rs");
        let src = std::fs::read_to_string(path).expect("segwit.rs");
        let marker = format!("fn {name}(");
        let start = src.find(&marker).expect("fn");
        let rest = &src[start..];
        let mut depth = 0i32;
        let mut started = false;
        for (i, byte) in rest.bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
                started = true;
            } else if byte == b'}' {
                depth -= 1;
                if started && depth == 0 {
                    return rest[..=i].to_string();
                }
            }
        }
        panic!("unbalanced {name}");
    }

    fn interior(item: &str) -> String {
        let start = item.find('{').expect("body");
        let end = item.rfind('}').expect("end");
        item[start + 1..end].to_string()
    }

    fn stitch(commit: &str, nonce: &str) -> String {
        let commit_body = interior(commit);
        let nonce_body = interior(nonce);
        format!(
            "fn validate_witness_commitment(coinbase_tx: &Transaction, witness_merkle_root: &Hash, coinbase_witnesses: &[Witness]) -> Result<bool> {{\nlet _commit = {{{commit_body}}};\nlet _nonce = {{{nonce_body}}};\n}}"
        )
    }

    fn extract(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).unwrap_or_else(|err| panic!("parse witness commit: {err}"));
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "validate_witness_commitment" => {
                    Some(func)
                }
                _ => None,
            })
            .expect("validate_witness_commitment")
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/segwit.rs"),
            "validate_witness_commitment",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn witness_commit_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let commit = item_src("validate_witness_commitment");
        let nonce = item_src("coinbase_reserved_nonce");
        let src = stitch(&commit, &nonce);
        let func = extract(&src);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(
                    body_translated,
                    "validate_witness_commitment must use the body"
                );
            }
            other => panic!("unpatched witness commitment must pass, got {other:?}"),
        }
        let widened = stitch(
            &commit,
            &nonce.replace("stack[0].len() != 32", "stack[0].len() != 33"),
        );
        assert_ne!(widened, src, "the nonce length must change");
        let widened_result = identity_query(&extract(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "accepting a 33-byte nonce must flip the identity, got {widened_result:?}"
        );
        let flipped = stitch(
            &commit.replace(
                "commitment == expected_commitment",
                "commitment != expected_commitment",
            ),
            &nonce,
        );
        assert_ne!(flipped, src, "the commitment comparison must change");
        let flipped_result = identity_query(&extract(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "negating the commitment comparison must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod witness_sigops_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn item_src(name: &str) -> String {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/sigop.rs");
        let src = std::fs::read_to_string(path).expect("sigop.rs");
        let marker = format!("fn {name}");
        let start = src.find(&marker).expect(name);
        let rest = &src[start..];
        let mut depth = 0i32;
        let mut started = false;
        for (i, byte) in rest.bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
                started = true;
            } else if byte == b'}' {
                depth -= 1;
                if started && depth == 0 {
                    return rest[..=i].to_string();
                }
            }
        }
        panic!("unbalanced {name}");
    }

    fn interior(item: &str) -> String {
        let start = item.find('{').expect("body");
        let end = item.rfind('}').expect("end");
        item[start + 1..end].to_string()
    }

    fn stitch(count: &str, input: &str, prog: &str) -> String {
        format!(
            "fn count_witness_sigops() -> u64 {{\nlet _count = {{{}}};\nlet _input = {{{}}};\nlet _prog = {{{}}};\n}}",
            interior(count),
            interior(input),
            interior(prog)
        )
    }

    fn extract(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).unwrap_or_else(|err| panic!("parse witness sigops: {err}"));
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "count_witness_sigops" => Some(func),
                _ => None,
            })
            .expect("count_witness_sigops")
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/sigop.rs"),
            "count_witness_sigops",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn witness_sigops_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let count = item_src("count_witness_sigops");
        let input = item_src("input_witness_sigops");
        let prog = item_src("witness_program_sigops");
        let src = stitch(&count, &input, &prog);
        let func = extract(&src);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "count_witness_sigops must use the body");
            }
            other => panic!("unpatched witness sigops must pass, got {other:?}"),
        }
        let widened = stitch(
            &count,
            &input.replace("flags & 0x800", "flags & 0x801"),
            &prog,
        );
        assert_ne!(widened, src, "the witness flag mask must change");
        let widened_result = identity_query(&extract(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "widening the witness flag must flip the identity, got {widened_result:?}"
        );
        let flipped = stitch(
            &count,
            &input,
            &prog.replace("script.len() == 22", "script.len() == 21"),
        );
        assert_ne!(flipped, src, "the program length must change");
        let flipped_result = identity_query(&extract(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring 21 program bytes must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod opcode_bytes_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn file_src() -> String {
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-primitives/src/opcodes.rs");
        std::fs::read_to_string(path).expect("opcodes.rs")
    }

    fn consts(src: &str) -> String {
        src.lines()
            .filter(|line| line.trim_start().starts_with("pub const "))
            .map(str::trim)
            .collect::<Vec<_>>()
            .join("\n")
    }

    fn stitch(src: &str) -> String {
        format!("fn opcode_bytes() -> i64 {{\n{}\n}}", consts(src))
    }

    fn extract(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).unwrap_or_else(|err| panic!("parse opcode bytes: {err}"));
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "opcode_bytes" => Some(func),
                _ => None,
            })
            .expect("opcode_bytes")
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/opcodes.rs"),
            "opcode_bytes",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn opcode_bytes_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let src = file_src();
        let stitched = stitch(&src);
        let func = extract(&stitched);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "opcode_bytes must use the body");
            }
            other => panic!("unpatched opcode bytes must pass, got {other:?}"),
        }
        let widened = stitch(&src.replace("const OP_ADD: u8 = 0x93", "const OP_ADD: u8 = 0x94"));
        assert_ne!(widened, stitched, "OP_ADD must change");
        let widened_result = identity_query(&extract(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "changing OP_ADD must flip the identity, got {widened_result:?}"
        );
        let flipped = stitch(&src.replace(
            "const OP_CHECKSIG: u8 = 0xac",
            "const OP_CHECKSIG: u8 = 0xad",
        ));
        assert_ne!(flipped, stitched, "OP_CHECKSIG must change");
        let flipped_result = identity_query(&extract(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "changing OP_CHECKSIG must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod block_weight_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn segwit() -> String {
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/segwit.rs");
        std::fs::read_to_string(path).expect("segwit.rs")
    }

    fn item_src(src: &str) -> String {
        let marker = "fn calculate_block_weight(";
        let start = src.find(marker).expect(marker);
        let rest = &src[start..];
        let mut depth = 0i32;
        let mut started = false;
        for (i, byte) in rest.bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
                started = true;
            } else if byte == b'}' {
                depth -= 1;
                if started && depth == 0 {
                    return rest[..=i].to_string();
                }
            }
        }
        panic!("unbalanced calculate_block_weight");
    }

    fn extract(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).unwrap_or_else(|err| panic!("parse block weight: {err}"));
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "calculate_block_weight" => Some(func),
                _ => None,
            })
            .expect("calculate_block_weight")
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/segwit.rs"),
            "calculate_block_weight",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn block_weight_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let full = segwit();
        assert!(
            full.contains("fn compact_size_len(n: u64) -> u64 {\n    if n < 0xfd {\n        1\n    } else if n <= 0xffff {\n        3\n    } else if n <= 0xffff_ffff {\n        5\n    } else {\n        9\n    }"),
            "compact size arms drifted"
        );
        let src = item_src(&full);
        let func = extract(&src);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "calculate_block_weight must use the body");
            }
            other => panic!("unpatched block weight must pass, got {other:?}"),
        }
        let widened = src.replace(".checked_add(", ".checked_sub(");
        assert_ne!(widened, src, "transaction weight must be subtracted");
        let widened_result = identity_query(&extract(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "subtracting transaction weight must flip the identity, got {widened_result:?}"
        );
        let flipped = src.replace("calculate_transaction_weight(tx, witness)?", "0");
        assert_ne!(flipped, src, "the transaction weight call must become zero");
        let flipped_result = identity_query(&extract(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "dropping transaction weight must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_dispatch_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn read(rel: &str) -> String {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel);
        std::fs::read_to_string(path).expect(rel)
    }

    fn braces_from(src: &str, marker: &str) -> String {
        let start = src.find(marker).expect(marker);
        let rest = &src[start..];
        let mut depth = 0i32;
        let mut started = false;
        for (i, byte) in rest.bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
                started = true;
            } else if byte == b'}' {
                depth -= 1;
                if started && depth == 0 {
                    return rest[..=i].to_string();
                }
            }
        }
        panic!("unbalanced {marker}");
    }

    fn interior(item: &str) -> String {
        let start = item.find('{').expect("body");
        let end = item.rfind('}').expect("end");
        item[start + 1..end].to_string()
    }

    fn stitch(arm: &str, add: &str) -> String {
        format!(
            "fn opcode_dispatch() -> Result<(bool, i64)> {{\nlet _arm = {{{}}};\nlet _add = {{{}}};\n}}",
            interior(arm),
            interior(add)
        )
    }

    fn extract(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).unwrap_or_else(|err| panic!("parse dispatch: {err}"));
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "opcode_dispatch" => Some(func),
                _ => None,
            })
            .expect("opcode_dispatch")
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "opcode_dispatch",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn opcode_dispatch_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let flags = read("../blvm-consensus/src/script/flags.rs");
        assert!(
            flags.contains("pub const SCRIPT_VERIFY_MINIMALDATA: u32 = 1 << 6;"),
            "minimaldata bit drifted"
        );
        let arm = braces_from(&read("../blvm-consensus/src/script/mod.rs"), "OP_ADD => {");
        let add = braces_from(
            &read("../blvm-consensus/src/script/arithmetic.rs"),
            "fn op_add(",
        );
        assert!(!arm.contains("stack.len() < 2") && !arm.contains("b + a"));
        assert!(add.contains("stack.len() < 2") && add.contains("b + a"));
        let src = stitch(&arm, &add);
        let func = extract(&src);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "opcode_dispatch must use the body");
            }
            other => panic!("unpatched opcode dispatch must pass, got {other:?}"),
        }
        let widened = stitch(&arm, &add.replacen("stack.len() < 2", "stack.len() < 3", 1));
        assert_ne!(widened, src, "the stack bound must change");
        let widened_result = identity_query(&extract(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "requiring three stack items must flip the identity, got {widened_result:?}"
        );
        let flipped = stitch(&arm, &add.replace("b + a", "b - a"));
        assert_ne!(flipped, src, "the sum must become a difference");
        let flipped_result = identity_query(&extract(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "subtracting the stack values must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod if_chain_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn read(rel: &str) -> String {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel);
        std::fs::read_to_string(path).expect(rel)
    }

    fn longest_arm(src: &str, marker: &str) -> String {
        let mut best = String::new();
        let mut from = 0;
        while let Some(rel) = src[from..].find(marker) {
            let at = from + rel;
            let rest = &src[at..];
            let mut depth = 0i32;
            let mut started = false;
            for (i, byte) in rest.bytes().enumerate() {
                if byte == b'{' {
                    depth += 1;
                    started = true;
                } else if byte == b'}' {
                    depth -= 1;
                    if started && depth == 0 {
                        let arm = rest[..=i].to_string();
                        if arm.len() > best.len() {
                            best = arm;
                        }
                        break;
                    }
                }
            }
            from = at + marker.len();
        }
        assert!(!best.is_empty(), "missing {marker}");
        best
    }

    fn interior(item: &str) -> String {
        let start = item.find('{').expect("body");
        let end = item.rfind('}').expect("end");
        item[start + 1..end].to_string()
    }

    fn stitch(if_arm: &str, add_arm: &str, add: &str, end_arm: &str) -> String {
        format!(
            "fn if_body_endif() -> Result<(i64, i64)> {{\nlet _if = {{{}}};\nlet _arm = {{{}}};\nlet _add = {{{}}};\nlet _end = {{{}}};\n}}",
            interior(if_arm),
            interior(add_arm),
            interior(add),
            interior(end_arm)
        )
    }

    fn extract(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).unwrap_or_else(|err| panic!("parse if chain: {err}"));
        file.items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "if_body_endif" => Some(func),
                _ => None,
            })
            .expect("if_body_endif")
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "if_body_endif",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn if_chain_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let flags = read("../blvm-consensus/src/script/flags.rs");
        assert!(flags.contains("pub const SCRIPT_VERIFY_MINIMALDATA: u32 = 1 << 6;"));
        let script = read("../blvm-consensus/src/script/mod.rs");
        let if_arm = longest_arm(&script, "OP_IF =>");
        let end_arm = longest_arm(&script, "OP_ENDIF =>");
        let add_arm = longest_arm(&script, "OP_ADD =>");
        let add = longest_arm(
            &read("../blvm-consensus/src/script/arithmetic.rs"),
            "fn op_add(",
        );
        assert!(if_arm.contains("pop_if_condition") && if_arm.contains("i += 1"));
        assert!(end_arm.contains("control_stack.pop()") && !if_arm.contains("control_stack.pop()"));
        assert!(add.contains("b + a") && !add_arm.contains("b + a"));
        let src = stitch(&if_arm, &add_arm, &add, &end_arm);
        let func = extract(&src);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "if_body_endif must use the body");
            }
            other => panic!("unpatched if/endif chain must pass, got {other:?}"),
        }
        let widened = stitch(
            &if_arm,
            &add_arm,
            &add,
            &end_arm.replace("control_stack.pop()", "control_stack.len()"),
        );
        assert_ne!(widened, src, "endif must stop popping");
        let widened_result = identity_query(&extract(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "leaving the control frame must flip the identity, got {widened_result:?}"
        );
        let flipped = stitch(&if_arm, &add_arm, &add.replace("b + a", "b - a"), &end_arm);
        assert_ne!(flipped, src, "the sum must become a difference");
        let flipped_result = identity_query(&extract(&flipped), &clause);
        assert!(
            matches!(
                flipped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "subtracting the stack values must flip the identity, got {flipped_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod apply_tx_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn read(rel: &str) -> String {
        std::fs::read_to_string(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel)).expect(rel)
    }

    fn function_src(file: &str) -> String {
        let marker = "fn apply_transaction_with_id(";
        let start = file.find(marker).expect("apply_transaction_with_id");
        let rest = &file[start..];
        let mut depth = 0i32;
        let mut started = false;
        for (i, byte) in rest.bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
                started = true;
            } else if byte == b'}' {
                depth -= 1;
                if started && depth == 0 {
                    return rest[..=i].to_string();
                }
            }
        }
        panic!("unbalanced apply_transaction_with_id");
    }

    fn decode(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).unwrap_or_else(|err| panic!("parse apply: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("apply fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/block/apply.rs"),
            "apply_transaction_with_id",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn apply_tx_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let constants = read("../blvm-primitives/src/constants.rs");
        assert!(constants.contains("pub const MAX_MONEY: i64 = 21_000_000 * 100_000_000;"));
        let src = function_src(&read("../blvm-consensus/src/block/apply.rs"));
        assert_eq!(src.matches("utxo_set.remove(").count(), 1);
        assert_eq!(src.matches("utxo_set.insert(").count(), 1);
        let func = decode(&src);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(
                    body_translated,
                    "apply_transaction_with_id must use the body"
                );
            }
            other => panic!("unpatched apply must pass, got {other:?}"),
        }
        let blinded = src.replacen(
            "if let Some(arc) = utxo_set.remove(&input.prevout) {",
            "if let Some(arc) = None {",
            1,
        );
        assert_ne!(blinded, src, "remove must become None");
        let blinded_result = identity_query(&decode(&blinded), &clause);
        assert!(
            matches!(
                blinded_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "dropping spent outputs must flip the identity, got {blinded_result:?}"
        );
        let kept = src.replacen(
            "utxo_set.insert(outpoint, utxo_arc);",
            "let _kept = utxo_arc;",
            1,
        );
        assert_ne!(kept, src, "insert must be dropped");
        let kept_result = identity_query(&decode(&kept), &clause);
        assert!(
            matches!(
                kept_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "skipping the insert must flip the identity, got {kept_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_2div_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn read(rel: &str) -> String {
        std::fs::read_to_string(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel)).expect(rel)
    }

    fn disabled_code() -> i64 {
        let src = read("../blvm-primitives/src/error.rs");
        let start = src.find("pub enum ScriptErrorCode {").expect("enum");
        let rest = &src[start..];
        let end = rest.find('}').expect("end");
        let mut index = 0i64;
        for line in rest[..end].lines() {
            let name = line.trim().trim_end_matches(',');
            if name.is_empty()
                || name.starts_with("//")
                || name.starts_with("pub enum")
                || name.starts_with("///")
            {
                continue;
            }
            if name == "DisabledOpcode" {
                return index;
            }
            if name.chars().next().is_some_and(|c| c.is_ascii_uppercase()) {
                index += 1;
            }
        }
        panic!("DisabledOpcode missing");
    }

    fn arm_expr(src: &str) -> String {
        let marker = "OP_2DIV =>";
        let at = src.find(marker).expect("OP_2DIV");
        let rest = &src[at + marker.len()..];
        let err = rest.find("Err(").expect("Err");
        let bytes = &rest.as_bytes()[err..];
        let mut paren = 0i32;
        for (i, byte) in bytes.iter().enumerate() {
            if *byte == b'(' {
                paren += 1;
            } else if *byte == b')' {
                paren -= 1;
                if paren == 0 {
                    return rest[err..=err + i].to_string();
                }
            }
        }
        panic!("unbalanced OP_2DIV");
    }

    fn decode(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_2div(stack: &mut Vec<Vec<u8>>) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_2DIV: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_2DIV fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_2DIV",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_2div_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        assert_eq!(disabled_code(), 14);
        let script = read("../blvm-consensus/src/script/mod.rs");
        let body = arm_expr(&script);
        assert!(body.contains("ScriptErrorCode::DisabledOpcode"));
        assert!(body.contains("OP_2DIV is disabled"));
        assert!(!body.contains("stack.len()"));
        let func = decode(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_2DIV must use the body");
            }
            other => panic!("unpatched OP_2DIV must pass, got {other:?}"),
        }
        let widened = format!("if stack.len() < 99 {{ return Ok(false); }}\n{body}");
        let widened_result = identity_query(&decode(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "the short-stack success must flip the identity, got {widened_result:?}"
        );
        let renamed = body.replace("DisabledOpcode", "OkTrueBypass");
        assert_ne!(renamed, body, "the error code must change");
        let renamed_result = identity_query(&decode(&renamed), &clause);
        assert!(
            matches!(
                renamed_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "renaming the disabled code must flip the identity, got {renamed_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_2mul_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn read(rel: &str) -> String {
        std::fs::read_to_string(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel)).expect(rel)
    }

    fn arm_expr(src: &str) -> String {
        let marker = "OP_2MUL =>";
        let at = src.find(marker).expect("OP_2MUL");
        let rest = &src[at + marker.len()..];
        let err = rest.find("Err(").expect("Err");
        let bytes = &rest.as_bytes()[err..];
        let mut paren = 0i32;
        for (i, byte) in bytes.iter().enumerate() {
            if *byte == b'(' {
                paren += 1;
            } else if *byte == b')' {
                paren -= 1;
                if paren == 0 {
                    return rest[err..=err + i].to_string();
                }
            }
        }
        panic!("unbalanced OP_2MUL");
    }

    fn decode(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_2mul(stack: &mut Vec<Vec<u8>>) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_2MUL: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_2MUL fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_2MUL",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_2mul_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let script = read("../blvm-consensus/src/script/mod.rs");
        let body = arm_expr(&script);
        assert!(body.contains("ScriptErrorCode::DisabledOpcode"));
        assert!(body.contains("OP_2MUL is disabled"));
        assert!(!body.contains("stack.len()"));
        assert!(!body.contains("OP_2DIV"));
        let func = decode(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_2MUL must use the body");
            }
            other => panic!("unpatched OP_2MUL must pass, got {other:?}"),
        }
        let widened = format!("if stack.len() < 99 {{ return Ok(false); }}\n{body}");
        let widened_result = identity_query(&decode(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "the short-stack success must flip the identity, got {widened_result:?}"
        );
        let renamed = body.replace("DisabledOpcode", "OkTrueBypass");
        assert_ne!(renamed, body, "the error code must change");
        let renamed_result = identity_query(&decode(&renamed), &clause);
        assert!(
            matches!(
                renamed_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "renaming the disabled code must flip the identity, got {renamed_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_mul_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn read(rel: &str) -> String {
        std::fs::read_to_string(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel)).expect(rel)
    }

    fn fn_interior(src: &str, name: &str) -> String {
        let marker = format!("fn {name}(");
        let at = src.find(&marker).expect("fn");
        let rest = &src[at..];
        let brace = rest.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in rest[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return rest[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced {name}");
    }

    fn stitch(call: &str, body: &str) -> String {
        format!(
            "fn op_mul(stack: &mut Vec<Vec<u8>>) -> Result<bool, String> {{\nlet _call = {{ {call} }};\nlet _body = {{ {body} }};\n}}\n"
        )
    }

    fn decode(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).unwrap_or_else(|err| panic!("parse OP_MUL: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_MUL fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_MUL",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_mul_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let script = read("../blvm-consensus/src/script/mod.rs");
        let arith = read("../blvm-consensus/src/script/arithmetic.rs");
        assert!(script.contains("OP_MUL => arithmetic::op_mul_disabled(),"));
        let call = "arithmetic::op_mul_disabled()";
        let body = fn_interior(&arith, "op_mul_disabled");
        assert!(body.contains("ScriptErrorCode::DisabledOpcode"));
        assert!(body.contains("OP_MUL is disabled"));
        assert!(!call.contains("DisabledOpcode") && !call.contains("stack.len()"));
        let src = stitch(call, &body);
        let func = decode(&src);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_MUL must use the body");
            }
            other => panic!("unpatched OP_MUL must pass, got {other:?}"),
        }
        let widened = stitch(call, &body).replacen(
            "fn op_mul(stack: &mut Vec<Vec<u8>>) -> Result<bool, String> {",
            "fn op_mul(stack: &mut Vec<Vec<u8>>) -> Result<bool, String> {\nif stack.len() < 99 { return Ok(false); }",
            1,
        );
        assert_ne!(widened, src, "the short stack must return before the call");
        let widened_result = identity_query(&decode(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "the short-stack success must flip the identity, got {widened_result:?}"
        );
        let renamed = stitch(call, &body.replace("DisabledOpcode", "OkTrueBypass"));
        assert_ne!(renamed, src, "the error code must change");
        let renamed_result = identity_query(&decode(&renamed), &clause);
        assert!(
            matches!(
                renamed_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "renaming the disabled code must flip the identity, got {renamed_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_div_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn read(rel: &str) -> String {
        std::fs::read_to_string(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel)).expect(rel)
    }

    fn fn_interior(src: &str, name: &str) -> String {
        let marker = format!("fn {name}(");
        let at = src.find(&marker).expect("fn");
        let rest = &src[at..];
        let brace = rest.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in rest[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return rest[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced {name}");
    }

    fn stitch(call: &str, body: &str) -> String {
        format!(
            "fn op_div(stack: &mut Vec<Vec<u8>>) -> Result<bool, String> {{\nlet _call = {{ {call} }};\nlet _body = {{ {body} }};\n}}\n"
        )
    }

    fn decode(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).unwrap_or_else(|err| panic!("parse OP_DIV: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_DIV fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_DIV",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_div_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let script = read("../blvm-consensus/src/script/mod.rs");
        let arith = read("../blvm-consensus/src/script/arithmetic.rs");
        assert!(script.contains("OP_DIV => arithmetic::op_div_disabled(),"));
        let call = "arithmetic::op_div_disabled()";
        let body = fn_interior(&arith, "op_div_disabled");
        assert!(body.contains("ScriptErrorCode::DisabledOpcode"));
        assert!(body.contains("OP_DIV is disabled"));
        assert!(!body.contains("OP_MUL"));
        assert!(!call.contains("DisabledOpcode") && !call.contains("stack.len()"));
        let src = stitch(call, &body);
        let func = decode(&src);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_DIV must use the body");
            }
            other => panic!("unpatched OP_DIV must pass, got {other:?}"),
        }
        let widened = stitch(call, &body).replacen(
            "fn op_div(stack: &mut Vec<Vec<u8>>) -> Result<bool, String> {",
            "fn op_div(stack: &mut Vec<Vec<u8>>) -> Result<bool, String> {\nif stack.len() < 99 { return Ok(false); }",
            1,
        );
        assert_ne!(widened, src, "the short stack must return before the call");
        let widened_result = identity_query(&decode(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "the short-stack success must flip the identity, got {widened_result:?}"
        );
        let renamed = stitch(call, &body.replace("DisabledOpcode", "OkTrueBypass"));
        assert_ne!(renamed, src, "the error code must change");
        let renamed_result = identity_query(&decode(&renamed), &clause);
        assert!(
            matches!(
                renamed_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "renaming the disabled code must flip the identity, got {renamed_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_mod_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn read(rel: &str) -> String {
        std::fs::read_to_string(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel)).expect(rel)
    }

    fn fn_interior(src: &str, name: &str) -> String {
        let marker = format!("fn {name}(");
        let at = src.find(&marker).expect("fn");
        let rest = &src[at..];
        let brace = rest.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in rest[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return rest[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced {name}");
    }

    fn stitch(call: &str, body: &str) -> String {
        format!(
            "fn op_mod(stack: &mut Vec<Vec<u8>>) -> Result<bool, String> {{\nlet _call = {{ {call} }};\nlet _body = {{ {body} }};\n}}\n"
        )
    }

    fn decode(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).unwrap_or_else(|err| panic!("parse OP_MOD: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_MOD fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_MOD",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_mod_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let script = read("../blvm-consensus/src/script/mod.rs");
        let arith = read("../blvm-consensus/src/script/arithmetic.rs");
        assert!(script.contains("OP_MOD => arithmetic::op_mod_disabled(),"));
        let call = "arithmetic::op_mod_disabled()";
        let body = fn_interior(&arith, "op_mod_disabled");
        assert!(body.contains("ScriptErrorCode::DisabledOpcode"));
        assert!(body.contains("OP_MOD is disabled"));
        assert!(!body.contains("OP_DIV") && !body.contains("OP_MUL"));
        assert!(!call.contains("DisabledOpcode") && !call.contains("stack.len()"));
        let src = stitch(call, &body);
        let func = decode(&src);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_MOD must use the body");
            }
            other => panic!("unpatched OP_MOD must pass, got {other:?}"),
        }
        let widened = stitch(call, &body).replacen(
            "fn op_mod(stack: &mut Vec<Vec<u8>>) -> Result<bool, String> {",
            "fn op_mod(stack: &mut Vec<Vec<u8>>) -> Result<bool, String> {\nif stack.len() < 99 { return Ok(false); }",
            1,
        );
        assert_ne!(widened, src, "the short stack must return before the call");
        let widened_result = identity_query(&decode(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "the short-stack success must flip the identity, got {widened_result:?}"
        );
        let renamed = stitch(call, &body.replace("DisabledOpcode", "OkTrueBypass"));
        assert_ne!(renamed, src, "the error code must change");
        let renamed_result = identity_query(&decode(&renamed), &clause);
        assert!(
            matches!(
                renamed_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "renaming the disabled code must flip the identity, got {renamed_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_lshift_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn read(rel: &str) -> String {
        std::fs::read_to_string(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel)).expect(rel)
    }

    fn fn_interior(src: &str, name: &str) -> String {
        let marker = format!("fn {name}(");
        let at = src.find(&marker).expect("fn");
        let rest = &src[at..];
        let brace = rest.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in rest[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return rest[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced {name}");
    }

    fn stitch(call: &str, body: &str) -> String {
        format!(
            "fn op_lshift(stack: &mut Vec<Vec<u8>>) -> Result<bool, String> {{\nlet _call = {{ {call} }};\nlet _body = {{ {body} }};\n}}\n"
        )
    }

    fn decode(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).unwrap_or_else(|err| panic!("parse OP_LSHIFT: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_LSHIFT fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_LSHIFT",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_lshift_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let script = read("../blvm-consensus/src/script/mod.rs");
        let arith = read("../blvm-consensus/src/script/arithmetic.rs");
        assert!(script.contains("OP_LSHIFT => arithmetic::op_lshift_disabled(),"));
        let call = "arithmetic::op_lshift_disabled()";
        let body = fn_interior(&arith, "op_lshift_disabled");
        assert!(body.contains("ScriptErrorCode::DisabledOpcode"));
        assert!(body.contains("OP_LSHIFT is disabled"));
        assert!(!body.contains("OP_RSHIFT") && !body.contains("OP_MOD"));
        assert!(!call.contains("DisabledOpcode") && !call.contains("stack.len()"));
        let src = stitch(call, &body);
        let func = decode(&src);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_LSHIFT must use the body");
            }
            other => panic!("unpatched OP_LSHIFT must pass, got {other:?}"),
        }
        let widened = stitch(call, &body).replacen(
            "fn op_lshift(stack: &mut Vec<Vec<u8>>) -> Result<bool, String> {",
            "fn op_lshift(stack: &mut Vec<Vec<u8>>) -> Result<bool, String> {\nif stack.len() < 99 { return Ok(false); }",
            1,
        );
        assert_ne!(widened, src, "the short stack must return before the call");
        let widened_result = identity_query(&decode(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "the short-stack success must flip the identity, got {widened_result:?}"
        );
        let renamed = stitch(call, &body.replace("DisabledOpcode", "OkTrueBypass"));
        assert_ne!(renamed, src, "the error code must change");
        let renamed_result = identity_query(&decode(&renamed), &clause);
        assert!(
            matches!(
                renamed_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "renaming the disabled code must flip the identity, got {renamed_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_rshift_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn read(rel: &str) -> String {
        std::fs::read_to_string(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel)).expect(rel)
    }

    fn fn_interior(src: &str, name: &str) -> String {
        let marker = format!("fn {name}(");
        let at = src.find(&marker).expect("fn");
        let rest = &src[at..];
        let brace = rest.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in rest[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return rest[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unbalanced {name}");
    }

    fn stitch(call: &str, body: &str) -> String {
        format!(
            "fn op_rshift(stack: &mut Vec<Vec<u8>>) -> Result<bool, String> {{\nlet _call = {{ {call} }};\nlet _body = {{ {body} }};\n}}\n"
        )
    }

    fn decode(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).unwrap_or_else(|err| panic!("parse OP_RSHIFT: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_RSHIFT fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_RSHIFT",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_rshift_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let script = read("../blvm-consensus/src/script/mod.rs");
        let arith = read("../blvm-consensus/src/script/arithmetic.rs");
        assert!(script.contains("OP_RSHIFT => arithmetic::op_rshift_disabled(),"));
        let call = "arithmetic::op_rshift_disabled()";
        let body = fn_interior(&arith, "op_rshift_disabled");
        assert!(body.contains("ScriptErrorCode::DisabledOpcode"));
        assert!(body.contains("OP_RSHIFT is disabled"));
        assert!(!body.contains("OP_LSHIFT"));
        assert!(!call.contains("DisabledOpcode") && !call.contains("stack.len()"));
        let src = stitch(call, &body);
        let func = decode(&src);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_RSHIFT must use the body");
            }
            other => panic!("unpatched OP_RSHIFT must pass, got {other:?}"),
        }
        let widened = stitch(call, &body).replacen(
            "fn op_rshift(stack: &mut Vec<Vec<u8>>) -> Result<bool, String> {",
            "fn op_rshift(stack: &mut Vec<Vec<u8>>) -> Result<bool, String> {\nif stack.len() < 99 { return Ok(false); }",
            1,
        );
        assert_ne!(widened, src, "the short stack must return before the call");
        let widened_result = identity_query(&decode(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "the short-stack success must flip the identity, got {widened_result:?}"
        );
        let renamed = stitch(call, &body.replace("DisabledOpcode", "OkTrueBypass"));
        assert_ne!(renamed, src, "the error code must change");
        let renamed_result = identity_query(&decode(&renamed), &clause);
        assert!(
            matches!(
                renamed_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "renaming the disabled code must flip the identity, got {renamed_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod csv_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn read(rel: &str) -> String {
        std::fs::read_to_string(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel)).expect(rel)
    }

    fn variant_index(name: &str) -> i64 {
        let src = read("../blvm-primitives/src/error.rs");
        let start = src.find("pub enum ScriptErrorCode {").expect("enum");
        let rest = &src[start..];
        let end = rest.find('}').expect("end");
        let mut index = 0i64;
        for line in rest[..end].lines() {
            let variant = line.trim().trim_end_matches(',');
            if variant.is_empty()
                || variant.starts_with("//")
                || variant.starts_with("pub enum")
                || variant.starts_with("///")
            {
                continue;
            }
            if variant == name {
                return index;
            }
            if variant
                .chars()
                .next()
                .is_some_and(|c| c.is_ascii_uppercase())
            {
                index += 1;
            }
        }
        panic!("{name} missing");
    }

    fn longest_arm(src: &str) -> String {
        let marker = "OP_CHECKSEQUENCEVERIFY =>";
        let mut best = String::new();
        let mut from = 0;
        while let Some(rel) = src[from..].find(marker) {
            let at = from + rel;
            let rest = &src[at + marker.len()..];
            let brace = rest.find('{').expect("brace");
            let mut depth = 0i32;
            for (i, byte) in rest[brace..].bytes().enumerate() {
                if byte == b'{' {
                    depth += 1;
                } else if byte == b'}' {
                    depth -= 1;
                    if depth == 0 {
                        let arm = rest[brace + 1..brace + i].to_string();
                        if arm.len() > best.len() {
                            best = arm;
                        }
                        break;
                    }
                }
            }
            from = at + marker.len();
        }
        assert!(best.contains("is_sequence_disabled("), "the long arm");
        best
    }

    fn decode(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_checksequenceverify(stack: &mut Vec<Vec<u8>>, flags: u32, input_index: usize, tx: Tx) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse CSV: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("CSV fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_CHECKSEQUENCEVERIFY",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_checksequenceverify_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        assert_eq!(variant_index("MinimalData"), 20);
        assert_eq!(variant_index("NegativeLocktime"), 40);
        let flags = read("../blvm-consensus/src/script/flags.rs");
        assert!(flags.contains("SCRIPT_VERIFY_CHECKSEQUENCEVERIFY: u32 = 1 << 10"));
        assert!(flags.contains("SCRIPT_VERIFY_MINIMALDATA: u32 = 1 << 6"));
        let script = read("../blvm-consensus/src/script/mod.rs");
        let body = longest_arm(&script);
        assert_eq!(body.matches("is_sequence_disabled(").count(), 2);
        assert_eq!(body.matches("stack.is_empty()").count(), 1);
        assert!(body.contains("check_bip112(sequence_value, input_sequence)"));
        assert!(body.contains("tx.version < 2"));
        let func = decode(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_CHECKSEQUENCEVERIFY must use the body");
            }
            other => panic!("unpatched OP_CHECKSEQUENCEVERIFY must pass, got {other:?}"),
        }
        let widened = body.replacen("stack.is_empty()", "stack.len() < 2", 1);
        assert_ne!(widened, body);
        let widened_result = identity_query(&decode(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "the one-element stack must flip the identity, got {widened_result:?}"
        );
        let renamed = body.replace("is_sequence_disabled(", "is_sequence_disabled_gone(");
        assert_eq!(renamed.matches("is_sequence_disabled_gone(").count(), 2);
        assert!(renamed.contains(
            "use crate::locktime::{check_bip112, decode_locktime_value, is_sequence_disabled};"
        ));
        let renamed_result = identity_query(&decode(&renamed), &clause);
        assert!(
            matches!(
                renamed_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "renaming both disable calls must flip the identity, got {renamed_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod op_ver_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn read(rel: &str) -> String {
        std::fs::read_to_string(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel)).expect(rel)
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_VER =>";
        let mut best = String::new();
        let mut from = 0;
        while let Some(rel) = src[from..].find(marker) {
            let at = from + rel;
            let rest = &src[at + marker.len()..];
            let Some(brace) = rest.find('{') else {
                from = at + marker.len();
                continue;
            };
            let mut depth = 0i32;
            for (i, byte) in rest[brace..].bytes().enumerate() {
                if byte == b'{' {
                    depth += 1;
                } else if byte == b'}' {
                    depth -= 1;
                    if depth == 0 {
                        let arm = rest[brace + 1..brace + i].to_string();
                        if arm.len() > best.len() {
                            best = arm;
                        }
                        break;
                    }
                }
            }
            from = at + marker.len();
        }
        assert!(best.contains("in_false_branch"), "executing gate");
        best
    }

    fn decode(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_ver(stack: &mut Vec<Vec<u8>>, in_false_branch: bool) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_VER: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_VER fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_VER",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_ver_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let script = read("../blvm-consensus/src/script/mod.rs");
        let body = arm_body(&script);
        assert!(body.contains("ScriptErrorCode::DisabledOpcode"));
        assert!(body.contains("OP_VER is disabled"));
        assert!(!body.contains("stack.len()"));
        let func = decode(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_VER must use the body");
            }
            other => panic!("unpatched OP_VER must pass, got {other:?}"),
        }
        let widened = format!("if stack.len() < 99 {{ return Ok(false); }}\n{body}");
        let widened_result = identity_query(&decode(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "the short-stack success must flip the identity, got {widened_result:?}"
        );
        let renamed = body.replace("DisabledOpcode", "OkTrueBypass");
        assert_ne!(renamed, body);
        let renamed_result = identity_query(&decode(&renamed), &clause);
        assert!(
            matches!(
                renamed_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "renaming the disabled code must flip the identity, got {renamed_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod multisig_verify_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn read(rel: &str) -> String {
        std::fs::read_to_string(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel)).expect(rel)
    }

    fn arm_body(src: &str) -> String {
        let marker = "OP_CHECKMULTISIGVERIFY =>";
        let mut best = String::new();
        let mut from = 0;
        while let Some(rel) = src[from..].find(marker) {
            let at = from + rel;
            let rest = &src[at + marker.len()..];
            let Some(brace) = rest.find('{') else {
                from = at + marker.len();
                continue;
            };
            let mut depth = 0i32;
            for (i, byte) in rest[brace..].bytes().enumerate() {
                if byte == b'{' {
                    depth += 1;
                } else if byte == b'}' {
                    depth -= 1;
                    if depth == 0 {
                        let arm = rest[brace + 1..brace + i].to_string();
                        if arm.len() > best.len() {
                            best = arm;
                        }
                        break;
                    }
                }
            }
            from = at + marker.len();
        }
        assert!(
            best.contains("execute_opcode_with_context_full"),
            "the verify arm"
        );
        best
    }

    fn decode(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_checkmultisigverify(stack: &mut Vec<Vec<u8>>, flags: u32) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file =
            syn::parse_file(&src).unwrap_or_else(|err| panic!("parse multisig verify: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("multisig verify fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_CHECKMULTISIGVERIFY",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_checkmultisigverify_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let script = read("../blvm-consensus/src/script/mod.rs");
        let body = arm_body(&script);
        assert!(body.contains("cast_to_bool"));
        assert!(body.contains("taproot_annex_hash: None"));
        assert!(body.contains("schnorr_collector: None"));
        assert!(!body.contains("stack.len()"));
        assert_eq!(body.matches("execute_opcode_with_context_full").count(), 1);
        let func = decode(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_CHECKMULTISIGVERIFY must use the body");
            }
            other => panic!("unpatched OP_CHECKMULTISIGVERIFY must pass, got {other:?}"),
        }
        let widened = format!("if stack.len() < 99 {{ return Ok(false); }}\n{body}");
        let widened_result = identity_query(&decode(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "the short-stack success must flip the identity, got {widened_result:?}"
        );
        let renamed = body.replace("execute_opcode_with_context_full", "gone_exec");
        assert_ne!(renamed, body);
        let renamed_result = identity_query(&decode(&renamed), &clause);
        assert!(
            matches!(
                renamed_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "renaming the multisig call must flip the identity, got {renamed_result:?}"
        );
    }
}

mod bip143_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn read(rel: &str) -> String {
        std::fs::read_to_string(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel)).expect(rel)
    }

    fn fn_body(src: &str) -> String {
        let marker = "fn build_bip143_preimage";
        let at = src.find(marker).expect(marker);
        let rest = &src[at..];
        let brace = rest.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in rest[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return rest[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unclosed build_bip143_preimage");
    }

    fn decode(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn build_bip143_preimage(tx: &Transaction, input_index: usize, script_code: &[u8], amount: i64, sighash_type: u8, anyone_can_pay: bool, is_none: bool, is_single: bool, hashes: &Bip143PrecomputedHashes, preimage: &mut Vec<u8>) -> Result<i64, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse bip143: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("bip143 fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/transaction_hash.rs"),
            "build_bip143_preimage",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    fn counterexample(result: &VerificationResult) -> bool {
        matches!(
            result,
            VerificationResult::Failed {
                kind: FailureKind::Counterexample,
                ..
            }
        )
    }

    #[test]
    fn build_bip143_preimage_passes_and_each_edit_flips() {
        if !consensus_workspace_present() {
            return;
        }
        let hash = read("../blvm-consensus/src/transaction_hash.rs");
        let body = fn_body(&hash);
        let version = "preimage.extend_from_slice(&(tx.version as u32).to_le_bytes());\n";
        let lock = "preimage.extend_from_slice(&(tx.lock_time as u32).to_le_bytes());\n";
        assert_eq!(body.matches(version).count(), 1);
        assert_eq!(body.matches(lock).count(), 1);
        assert_eq!(body.matches("amount.to_le_bytes()").count(), 1);
        assert!(body.contains("double_sha256"));
        assert!(body.contains("write_varint_to_vec"));
        let func = decode(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "build_bip143_preimage must use the body");
            }
            other => panic!("unpatched build_bip143_preimage must pass, got {other:?}"),
        }
        let swapped = body
            .replace(version, "\u{0}")
            .replace(lock, version)
            .replace("\u{0}", lock);
        assert_ne!(swapped, body);
        let swapped_result = identity_query(&decode(&swapped), &clause);
        assert!(
            counterexample(&swapped_result),
            "swapping version and locktime must flip the identity, got {swapped_result:?}"
        );
        let endian = body.replacen("amount.to_le_bytes()", "amount.to_be_bytes()", 1);
        assert_ne!(endian, body);
        let endian_result = identity_query(&decode(&endian), &clause);
        assert!(
            counterexample(&endian_result),
            "a big-endian amount must flip the identity, got {endian_result:?}"
        );
        let dropped = body.replace(version, "");
        assert_ne!(dropped, body);
        let dropped_result = identity_query(&decode(&dropped), &clause);
        assert!(
            counterexample(&dropped_result),
            "dropping the version must flip the identity, got {dropped_result:?}"
        );
    }
}

mod legacy_sighash_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn read(rel: &str) -> String {
        std::fs::read_to_string(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel)).expect(rel)
    }

    fn fn_body(src: &str) -> String {
        let marker = "fn compute_legacy_sighash_nocache";
        let at = src.find(marker).expect(marker);
        let rest = &src[at..];
        let brace = rest.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in rest[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return rest[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unclosed compute_legacy_sighash_nocache");
    }

    fn decode(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn compute_legacy_sighash_nocache(tx: &Transaction, input_index: usize, script_code: &[u8], sighash_byte: u8) -> [u8; 32] {{\n{body}\n}}\n"
        );
        let file =
            syn::parse_file(&src).unwrap_or_else(|err| panic!("parse legacy sighash: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("legacy sighash fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/transaction_hash.rs"),
            "compute_legacy_sighash_nocache",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    fn counterexample(result: &VerificationResult) -> bool {
        matches!(
            result,
            VerificationResult::Failed {
                kind: FailureKind::Counterexample,
                ..
            }
        )
    }

    #[test]
    fn compute_legacy_sighash_nocache_passes_and_each_edit_flips() {
        if !consensus_workspace_present() {
            return;
        }
        let hash = read("../blvm-consensus/src/transaction_hash.rs");
        let body = fn_body(&hash);
        let version = "h.update((tx.version as u32).to_le_bytes());\n";
        let lock = "h.update((tx.lock_time as u32).to_le_bytes());\n";
        assert_eq!(body.matches(version).count(), 1);
        assert_eq!(body.matches(lock).count(), 1);
        assert_eq!(body.matches("(tx.version as u32).to_le_bytes()").count(), 1);
        assert!(body.contains("result[0] = 1"));
        assert!(body.contains("update_varint"));
        let func = decode(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(
                    body_translated,
                    "compute_legacy_sighash_nocache must use the body"
                );
            }
            other => panic!("unpatched compute_legacy_sighash_nocache must pass, got {other:?}"),
        }
        let swapped = body
            .replace(version, "\u{0}")
            .replace(lock, version)
            .replace("\u{0}", lock);
        assert_ne!(swapped, body);
        let swapped_result = identity_query(&decode(&swapped), &clause);
        assert!(
            counterexample(&swapped_result),
            "swapping version and locktime must flip the identity, got {swapped_result:?}"
        );
        let endian = body.replacen(
            "(tx.version as u32).to_le_bytes()",
            "(tx.version as u32).to_be_bytes()",
            1,
        );
        assert_ne!(endian, body);
        let endian_result = identity_query(&decode(&endian), &clause);
        assert!(
            counterexample(&endian_result),
            "a big-endian version must flip the identity, got {endian_result:?}"
        );
        let dropped = body.replace(version, "");
        assert_ne!(dropped, body);
        let dropped_result = identity_query(&decode(&dropped), &clause);
        assert!(
            counterexample(&dropped_result),
            "dropping the version must flip the identity, got {dropped_result:?}"
        );
    }

    #[test]
    fn sighash_single_quirk_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let hash = read("../blvm-consensus/src/transaction_hash.rs");
        let body = fn_body(&hash);
        assert_eq!(body.matches("result[0] = 1").count(), 1);
        let func = decode(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "the single quirk must use the body");
            }
            other => panic!("unpatched sighash single quirk must pass, got {other:?}"),
        }
        let zeroed = body.replace("result[0] = 1", "result[0] = 0");
        assert_ne!(zeroed, body);
        let zeroed_result = identity_query(&decode(&zeroed), &clause);
        assert!(
            counterexample(&zeroed_result),
            "clearing the quirk byte must flip the identity, got {zeroed_result:?}"
        );
        let dropped = body.replace("result[0] = 1;", "");
        assert_ne!(dropped, body);
        let dropped_result = identity_query(&decode(&dropped), &clause);
        assert!(
            counterexample(&dropped_result),
            "dropping the quirk byte must flip the identity, got {dropped_result:?}"
        );
    }
}

mod find_delete_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn read(rel: &str) -> String {
        std::fs::read_to_string(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel)).expect(rel)
    }

    fn fn_body(src: &str) -> String {
        let marker = "fn find_and_delete";
        let at = src.find(marker).expect(marker);
        let rest = &src[at..];
        let brace = rest.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in rest[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return rest[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unclosed find_and_delete");
    }

    fn decode(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn find_and_delete<'a>(script: &'a [u8], pattern: &[u8]) -> i64 {{\n{body}\n}}\n"
        );
        let file =
            syn::parse_file(&src).unwrap_or_else(|err| panic!("parse find_and_delete: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("find_and_delete fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "find_and_delete",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    fn counterexample(result: &VerificationResult) -> bool {
        matches!(
            result,
            VerificationResult::Failed {
                kind: FailureKind::Counterexample,
                ..
            }
        )
    }

    #[test]
    fn find_and_delete_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let script = read("../blvm-consensus/src/script/mod.rs");
        let body = fn_body(&script);
        assert_eq!(body.matches("pattern.is_empty()").count(), 1);
        assert_eq!(body.matches("pc += pattern.len()").count(), 1);
        assert!(body.contains("script.windows(pattern.len())"));
        assert!(body.contains("script_get_op_advance"));
        let func = decode(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "find_and_delete must use the body");
            }
            other => panic!("unpatched find_and_delete must pass, got {other:?}"),
        }
        let empty = body.replace("pattern.is_empty()", "pattern.len() < 0");
        assert_ne!(empty, body);
        let empty_result = identity_query(&decode(&empty), &clause);
        assert!(
            counterexample(&empty_result),
            "dropping the empty-pattern return must flip the identity, got {empty_result:?}"
        );
        let stride = body.replace("pc += pattern.len()", "pc += 1");
        assert_ne!(stride, body);
        let stride_result = identity_query(&decode(&stride), &clause);
        assert!(
            counterexample(&stride_result),
            "a unit stride must flip the identity, got {stride_result:?}"
        );
    }
}

mod tap_sigmsg_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn read(rel: &str) -> String {
        std::fs::read_to_string(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel)).expect(rel)
    }

    fn extract(src: &str) -> String {
        let marker = "fn append_bip341_sigmsg";
        let at = src.find(marker).expect(marker);
        let rest = &src[at..];
        let brace = rest.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in rest[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return rest[..=brace + i].to_string();
                }
            }
        }
        panic!("unclosed append_bip341_sigmsg");
    }

    fn decode(src: &str) -> syn::ItemFn {
        let file =
            syn::parse_file(src).unwrap_or_else(|err| panic!("parse append_bip341_sigmsg: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("append_bip341_sigmsg fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/taproot.rs"),
            "append_bip341_sigmsg",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    fn counterexample(result: &VerificationResult) -> bool {
        matches!(
            result,
            VerificationResult::Failed {
                kind: FailureKind::Counterexample,
                ..
            }
        )
    }

    fn swap_fields(src: &str) -> String {
        let token = "__FIELD_tx.version__";
        src.replace("tx.version", token)
            .replace("tx.lock_time", "tx.version")
            .replace(token, "tx.lock_time")
    }

    #[test]
    fn append_bip341_sigmsg_passes_and_each_edit_flips() {
        if !consensus_workspace_present() {
            return;
        }
        let tap = read("../blvm-consensus/src/taproot.rs");
        let plain = extract(&tap);
        assert_eq!(plain.matches("tx.version").count(), 1);
        assert_eq!(plain.matches("tx.lock_time").count(), 1);
        assert_eq!(plain.matches("sigmsg.push(0x00u8);\n").count(), 1);
        let func = decode(&plain);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "append_bip341_sigmsg must use the body");
            }
            other => panic!("unpatched append_bip341_sigmsg must pass, got {other:?}"),
        }
        let swapped = swap_fields(&plain);
        assert_ne!(swapped, plain);
        let swapped_result = identity_query(&decode(&swapped), &clause);
        assert!(
            counterexample(&swapped_result),
            "swapping version and locktime must flip the identity, got {swapped_result:?}"
        );
        let endian = plain.replacen(
            "(tx.version as u32).to_le_bytes()",
            "(tx.version as u32).to_be_bytes()",
            1,
        );
        assert_ne!(endian, plain);
        let endian_result = identity_query(&decode(&endian), &clause);
        assert!(
            counterexample(&endian_result),
            "a big-endian version must flip the identity, got {endian_result:?}"
        );
        let dropped = plain.replace("sigmsg.push(0x00u8);\n", "");
        assert_ne!(dropped, plain);
        let dropped_result = identity_query(&decode(&dropped), &clause);
        assert!(
            counterexample(&dropped_result),
            "dropping the epoch byte must flip the identity, got {dropped_result:?}"
        );
        let epoch = plain.replacen("sigmsg.push(0x00u8)", "sigmsg.push(0x01u8)", 1);
        assert_ne!(epoch, plain);
        let epoch_result = identity_query(&decode(&epoch), &clause);
        assert!(
            counterexample(&epoch_result),
            "epoch 0x01 must flip the identity, got {epoch_result:?}"
        );
        assert_eq!(plain.matches("to_le_bytes()").count(), 7);
        let be = plain.replace("to_le_bytes()", "to_be_bytes()");
        assert!(!be.contains("to_le_bytes()"));
        let be_result = identity_query(&decode(&be), &clause);
        assert!(
            counterexample(&be_result),
            "big-endian integer words must flip the identity, got {be_result:?}"
        );
    }
}

mod work_required_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn read(rel: &str) -> String {
        std::fs::read_to_string(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel)).expect(rel)
    }

    fn extract(src: &str, name: &str) -> String {
        let marker = format!("fn {name}(");
        let at = src
            .find(&marker)
            .unwrap_or_else(|| panic!("missing {name}"));
        let rest = &src[at..];
        let brace = rest.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in rest[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return rest[..=brace + i].to_string();
                }
            }
        }
        panic!("unclosed {name}");
    }

    fn inner(func: &str) -> String {
        let brace = func.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in func[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return func[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unclosed inner");
    }

    fn stitch(wrapper: &str, internal: &str) -> String {
        let call = inner(wrapper).trim().trim_end_matches(';').to_string();
        format!(
            "fn get_next_work_required(_current_header: &BlockHeader, prev_headers: &[BlockHeader], use_corrected: bool) -> i64 {{\n{call};\n{}\n}}\n",
            inner(internal)
        )
    }

    fn decode(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).unwrap_or_else(|err| panic!("parse retarget: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("retarget fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/pow.rs"),
            "get_next_work_required",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    fn counterexample(result: &VerificationResult) -> bool {
        matches!(
            result,
            VerificationResult::Failed {
                kind: FailureKind::Counterexample,
                ..
            }
        )
    }

    #[test]
    fn get_next_work_required_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let pow = read("../blvm-consensus/src/pow.rs");
        let wrapper = extract(&pow, "get_next_work_required");
        let internal = extract(&pow, "get_next_work_required_internal");
        let plain = format!("{wrapper}\n{internal}");
        assert_eq!(plain.matches(", false)").count(), 1);
        assert_eq!(plain.matches("time_span.max(expected_time / 4)").count(), 1);
        let func = decode(&stitch(&wrapper, &internal));
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "get_next_work_required must use the body");
            }
            other => panic!("unpatched get_next_work_required must pass, got {other:?}"),
        }
        let floor = plain.replace(
            "time_span.max(expected_time / 4)",
            "time_span.max(expected_time / 1)",
        );
        let floor_at = floor
            .find("fn get_next_work_required_internal")
            .expect("internal");
        let floor_result = identity_query(
            &decode(&stitch(&floor[..floor_at], &floor[floor_at..])),
            &clause,
        );
        assert!(
            counterexample(&floor_result),
            "a unit floor must flip the identity, got {floor_result:?}"
        );
        let corrected = plain.replace(", false)", ", true)");
        let corrected_at = corrected
            .find("fn get_next_work_required_internal")
            .expect("internal");
        let corrected_result = identity_query(
            &decode(&stitch(
                &corrected[..corrected_at],
                &corrected[corrected_at..],
            )),
            &clause,
        );
        assert!(
            counterexample(&corrected_result),
            "the corrected interval count must flip the identity, got {corrected_result:?}"
        );
        let capped = plain.replace("new_bits.min(MAX_TARGET", "new_bits.max(MAX_TARGET");
        let capped_at = capped
            .find("fn get_next_work_required_internal")
            .expect("internal");
        let capped_result = identity_query(
            &decode(&stitch(&capped[..capped_at], &capped[capped_at..])),
            &clause,
        );
        assert!(
            counterexample(&capped_result),
            "max instead of min must flip the identity, got {capped_result:?}"
        );
    }
}

mod data_push_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn read(rel: &str) -> String {
        std::fs::read_to_string(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel)).expect(rel)
    }

    fn extract(src: &str, name: &str) -> String {
        let marker = format!("fn {name}(");
        let at = src
            .find(&marker)
            .unwrap_or_else(|| panic!("missing {name}"));
        let rest = &src[at..];
        let brace = rest.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in rest[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return rest[..=brace + i].to_string();
                }
            }
        }
        panic!("unclosed {name}");
    }

    fn signed(func: &str) -> String {
        func.replacen("-> Result<Option<usize>>", "-> i64", 1)
    }

    fn decode(src: &str) -> syn::ItemFn {
        let wrapped = format!("{src}\n");
        let file = syn::parse_file(&wrapped).unwrap_or_else(|err| panic!("parse push: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("push fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "apply_data_push",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    fn counterexample(result: &VerificationResult) -> bool {
        matches!(
            result,
            VerificationResult::Failed {
                kind: FailureKind::Counterexample,
                ..
            }
        )
    }

    #[test]
    fn push_advance_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let src = read("../blvm-consensus/src/script/mod.rs");
        assert_eq!(src.matches(", 1 + len)").count(), 1);
        assert_eq!(src.matches(", 2 + len)").count(), 1);
        let plain = signed(&extract(&src, "apply_data_push"));
        let func = decode(&plain);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "push advance must use the body");
            }
            other => panic!("unpatched push advance must pass, got {other:?}"),
        }
        let boundary = signed(&extract(
            &src.replace(", 1 + len)", ", len)"),
            "apply_data_push",
        ));
        assert_ne!(boundary, plain);
        let boundary_result = identity_query(&decode(&boundary), &clause);
        assert!(
            counterexample(&boundary_result),
            "a direct advance of len must flip the identity, got {boundary_result:?}"
        );
        let predicate = signed(&extract(
            &src.replace(", 2 + len)", ", 1 + len)"),
            "apply_data_push",
        ));
        assert_ne!(predicate, plain);
        let predicate_result = identity_query(&decode(&predicate), &clause);
        assert!(
            counterexample(&predicate_result),
            "a one-byte PUSHDATA1 advance must flip the identity, got {predicate_result:?}"
        );
    }
}

mod activation_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn read(rel: &str) -> String {
        std::fs::read_to_string(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel)).expect(rel)
    }

    fn extract(src: &str) -> String {
        let marker = "fn activation_height_from_headers";
        let at = src.find(marker).expect("activation");
        let rest = &src[at..];
        let brace = rest.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in rest[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return rest[..=brace + i].to_string();
                }
            }
        }
        panic!("unclosed activation");
    }

    fn signed(func: &str) -> String {
        func.replacen("-> Option<u64>", "-> i64", 1)
    }

    fn decode(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).unwrap_or_else(|err| panic!("parse activation: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("activation fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/version_bits.rs"),
            "activation_height_from_headers",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    fn counterexample(result: &VerificationResult) -> bool {
        matches!(
            result,
            VerificationResult::Failed {
                kind: FailureKind::Counterexample,
                ..
            }
        )
    }

    #[test]
    fn activation_height_from_headers_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let src = read("../blvm-consensus/src/version_bits.rs");
        let plain = signed(&extract(&src));
        assert_eq!(plain.matches("(period_index + 2)").count(), 2);
        assert_eq!(
            plain.matches("current_time >= deployment.timeout").count(),
            1
        );
        let func = decode(&plain);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "activation height must use the body");
            }
            other => panic!("unpatched activation height must pass, got {other:?}"),
        }
        let offset = signed(&extract(
            &src.replace("(period_index + 2)", "(period_index + 1)"),
        ));
        assert_ne!(offset, plain);
        let offset_result = identity_query(&decode(&offset), &clause);
        assert!(
            counterexample(&offset_result),
            "one fewer period must flip the identity, got {offset_result:?}"
        );
        let timeout = signed(&extract(&src.replace(
            "current_time >= deployment.timeout",
            "current_time > deployment.timeout",
        )));
        assert_ne!(timeout, plain);
        let timeout_result = identity_query(&decode(&timeout), &clause);
        assert!(
            counterexample(&timeout_result),
            "a strict timeout must flip the identity, got {timeout_result:?}"
        );
    }
}

mod sigop_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn read(rel: &str) -> String {
        std::fs::read_to_string(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel)).expect(rel)
    }

    fn extract(src: &str, name: &str) -> String {
        let at = [format!("fn {name}("), format!("fn {name}<")]
            .into_iter()
            .find_map(|marker| src.find(&marker))
            .unwrap_or_else(|| panic!("missing {name}"));
        let rest = &src[at..];
        let brace = rest.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in rest[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return rest[..=brace + i].to_string();
                }
            }
        }
        panic!("unclosed {name}");
    }

    fn inner(func: &str) -> String {
        let brace = func.find('{').expect("brace");
        let mut depth = 0i32;
        for (i, byte) in func[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return func[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unclosed inner");
    }

    fn max_line(src: &str) -> String {
        let needle = "const MAX_PUBKEYS_PER_MULTISIG: u32 =";
        let at = src.find(needle).expect("max");
        let rest = &src[at..];
        let end = rest.find(';').expect("semi");
        rest[..=end].to_string()
    }

    fn stitch(src: &str) -> String {
        let legacy = inner(&extract(src, "count_sigops_in_script"));
        let tap = inner(&extract(src, "count_tapscript_sigops"));
        format!(
            "fn count_sigops_in_script(script: &ByteString, accurate: bool) -> i64 {{\n{}\n{};\n{}\n}}\n",
            max_line(src),
            legacy.trim(),
            tap.trim()
        )
    }

    fn decode(src: &str) -> syn::ItemFn {
        let file = syn::parse_file(src).unwrap_or_else(|err| panic!("parse sigops: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("sigops fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/sigop.rs"),
            "count_sigops_in_script",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    fn counterexample(result: &VerificationResult) -> bool {
        matches!(
            result,
            VerificationResult::Failed {
                kind: FailureKind::Counterexample,
                ..
            }
        )
    }

    #[test]
    fn count_sigops_in_script_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let src = read("../blvm-consensus/src/sigop.rs");
        assert_eq!(src.matches("saturating_add(1)").count(), 2);
        assert_eq!(
            src.matches("const MAX_PUBKEYS_PER_MULTISIG: u32 = 20;")
                .count(),
            1
        );
        let plain = stitch(&src);
        let func = decode(&plain);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "sigop count must use the body");
            }
            other => panic!("unpatched sigop count must pass, got {other:?}"),
        }
        let addend = stitch(&src.replace("saturating_add(1)", "saturating_add(0)"));
        assert_ne!(addend, plain);
        let addend_result = identity_query(&decode(&addend), &clause);
        assert!(
            counterexample(&addend_result),
            "a zero checksig weight must flip the identity, got {addend_result:?}"
        );
        let cap = stitch(&src.replace(
            "const MAX_PUBKEYS_PER_MULTISIG: u32 = 20;",
            "const MAX_PUBKEYS_PER_MULTISIG: u32 = 21;",
        ));
        assert_ne!(cap, plain);
        let cap_result = identity_query(&decode(&cap), &clause);
        assert!(
            counterexample(&cap_result),
            "a 21-key multisig cap must flip the identity, got {cap_result:?}"
        );
    }
}

mod checkmultisig_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn arm_body(src: &str) -> String {
        let mut from = 0;
        while let Some(rel) = src[from..].find("OP_CHECKMULTISIG =>") {
            let at = from + rel;
            let rest = &src[at..];
            let brace = rest.find('{').expect("arm brace");
            let mut depth = 0i32;
            for (i, byte) in rest[brace..].bytes().enumerate() {
                if byte == b'{' {
                    depth += 1;
                } else if byte == b'}' {
                    depth -= 1;
                    if depth == 0 {
                        let inner = rest[brace + 1..brace + i].to_string();
                        if inner.contains("batch_verify_signatures(")
                            && inner.contains("stack.len() < 2")
                            && inner.contains("failed_multisig_nullfail(")
                        {
                            return inner;
                        }
                        break;
                    }
                }
            }
            from = at + "OP_CHECKMULTISIG =>".len();
        }
        panic!("OP_CHECKMULTISIG arm");
    }

    fn decode_fn(body: &str) -> syn::ItemFn {
        let src = format!(
            "fn op_checkmultisig(stack: &mut Vec<Vec<u8>>) -> Result<bool, String> {{\n{body}\n}}\n"
        );
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse multisig: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("multisig fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_CHECKMULTISIG",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_checkmultisig_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let src = std::fs::read_to_string(&path).expect("script/mod.rs");
        let body = arm_body(&src);
        let func = decode_fn(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_CHECKMULTISIG must use the body");
            }
            other => panic!("unpatched OP_CHECKMULTISIG must pass, got {other:?}"),
        }
        let raised = body.replacen("stack.len() < 2", "stack.len() < 3", 1);
        assert_ne!(raised, body);
        let raised_result = identity_query(&decode_fn(&raised), &clause);
        assert!(
            matches!(
                raised_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "a taller stack floor must flip the identity, got {raised_result:?}"
        );
        let renamed = body.replace("batch_verify_signatures(", "batch_gone_signatures(");
        assert_ne!(renamed, body);
        let renamed_result = identity_query(&decode_fn(&renamed), &clause);
        assert!(
            matches!(
                renamed_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "renaming the batch verifier must flip the identity, got {renamed_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod check_transaction_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn fn_body(src: &str, name: &str) -> String {
        let marker = format!("fn {name}(");
        let at = src
            .find(&marker)
            .unwrap_or_else(|| panic!("missing {name}"));
        let rest = &src[at..];
        let brace = rest.find('{').expect("fn brace");
        let mut depth = 0i32;
        for (i, byte) in rest[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return rest[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unclosed {name}");
    }

    fn stitch(fast: &str, check: &str) -> syn::ItemFn {
        let src =
            format!("fn check_transaction(tx: &Transaction) -> i64 {{\n{fast};\n{check}\n}}\n");
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse check: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("check fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/transaction.rs"),
            "check_transaction",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    fn money_edit(src: &str) -> String {
        src.replace(
            "output.value < 0 || value_u64 > MAX_MONEY_U64",
            "output.value > MAX_MONEY",
        )
        .replace(
            "total_output_value < 0 || total_u64 > MAX_MONEY_U64",
            "total_output_value > MAX_MONEY",
        )
    }

    #[test]
    fn check_transaction_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/transaction.rs");
        let src = std::fs::read_to_string(&path).expect("transaction.rs");
        let fast = fn_body(&src, "check_transaction_fast_path");
        let check = fn_body(&src, "check_transaction");
        let func = stitch(&fast, &check);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "check_transaction must use the body");
            }
            other => panic!("unpatched check_transaction must pass, got {other:?}"),
        }
        let boundary = stitch(&money_edit(&fast), &money_edit(&check));
        let boundary_result = identity_query(&boundary, &clause);
        assert!(
            matches!(
                boundary_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "dropping the negative money test must flip the identity, got {boundary_result:?}"
        );
        let predicate = stitch(
            &fast,
            &check.replace("&input.prevout)", "&input.prevout.txid)"),
        );
        let predicate_result = identity_query(&predicate, &clause);
        assert!(
            matches!(
                predicate_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "keying duplicates by txid must flip the identity, got {predicate_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod tx_inputs_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn fn_body(src: &str, name: &str) -> String {
        let marker = format!("fn {name}");
        let at = src
            .find(&marker)
            .unwrap_or_else(|| panic!("missing {name}"));
        let rest = &src[at..];
        let brace = rest.find('{').expect("fn brace");
        let mut depth = 0i32;
        for (i, byte) in rest[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return rest[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unclosed {name}");
    }

    fn stitch(body: &str) -> syn::ItemFn {
        let src = format!("fn check_tx_inputs(tx: &Transaction) -> i64 {{\n{body}\n}}\n");
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse inputs: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("inputs fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/transaction.rs"),
            "check_tx_inputs",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn check_tx_inputs_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/transaction.rs");
        let src = std::fs::read_to_string(&path).expect("transaction.rs");
        let body = fn_body(&src, "check_tx_inputs_with_utxos");
        let func = stitch(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "check_tx_inputs must use the body");
            }
            other => panic!("unpatched check_tx_inputs must pass, got {other:?}"),
        }
        let boundary = stitch(&body.replace("0xffffffff", "0xfffffffe"));
        let boundary_result = identity_query(&boundary, &clause);
        assert!(
            matches!(
                boundary_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "relaxing the null prevout index must flip the identity, got {boundary_result:?}"
        );
        let predicate = stitch(&body.replace(
            "checked_sub(total_output_value)",
            "checked_add(total_output_value)",
        ));
        let predicate_result = identity_query(&predicate, &clause);
        assert!(
            matches!(
                predicate_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "adding the fee instead of subtracting it must flip the identity, got {predicate_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod weight_limit_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn fn_body(src: &str, name: &str) -> String {
        let marker = format!("fn {name}");
        let at = src
            .find(&marker)
            .unwrap_or_else(|| panic!("missing {name}"));
        let rest = &src[at..];
        let brace = rest.find('{').expect("fn brace");
        let mut depth = 0i32;
        for (i, byte) in rest[brace..].bytes().enumerate() {
            if byte == b'{' {
                depth += 1;
            } else if byte == b'}' {
                depth -= 1;
                if depth == 0 {
                    return rest[brace + 1..brace + i].to_string();
                }
            }
        }
        panic!("unclosed {name}");
    }

    fn stitch(body: &str) -> syn::ItemFn {
        let src = format!("fn connect_block_inner(block: &Block) -> i64 {{\n{body}\n}}\n");
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse weight: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("weight fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/block/connect.rs"),
            "connect_block_inner",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn block_weight_limit_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../blvm-consensus/src/block/connect.rs");
        let src = std::fs::read_to_string(&path).expect("connect.rs");
        let body = fn_body(&src, "connect_block_inner");
        let func = stitch(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "block_weight_limit must use the body");
            }
            other => panic!("unpatched block_weight_limit must pass, got {other:?}"),
        }
        let needle = "block_weight > crate::constants::MAX_BLOCK_WEIGHT as u64 {";
        let boundary = stitch(&body.replace(
            needle,
            "block_weight >= crate::constants::MAX_BLOCK_WEIGHT as u64 {",
        ));
        let boundary_result = identity_query(&boundary, &clause);
        assert!(
            matches!(
                boundary_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "accepting the weight limit must flip the identity, got {boundary_result:?}"
        );
        let predicate = stitch(&body.replace(needle, "block_weight > 1 {"));
        let predicate_result = identity_query(&predicate, &clause);
        assert!(
            matches!(
                predicate_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "rejecting every weight above 1 must flip the identity, got {predicate_result:?}"
        );
    }

    #[test]
    fn block_sigop_limit_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../blvm-consensus/src/block/connect.rs");
        let src = std::fs::read_to_string(&path).expect("connect.rs");
        let body = fn_body(&src, "connect_block_inner");
        let func = stitch(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "block_sigop_limit must use the body");
            }
            other => panic!("unpatched block_sigop_limit must pass, got {other:?}"),
        }
        let needle = "total_sigop_cost > MAX_BLOCK_SIGOPS_COST";
        let boundary = stitch(&body.replace(needle, "total_sigop_cost >= MAX_BLOCK_SIGOPS_COST"));
        let boundary_result = identity_query(&boundary, &clause);
        assert!(
            matches!(
                boundary_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "accepting the sigop cap must flip the identity, got {boundary_result:?}"
        );
        let predicate = stitch(&body.replace(needle, "total_sigop_cost > 1"));
        let predicate_result = identity_query(&predicate, &clause);
        assert!(
            matches!(
                predicate_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "rejecting every sigop cost above 1 must flip the identity, got {predicate_result:?}"
        );
    }

    #[test]
    fn coinbase_scriptsig_len_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../blvm-consensus/src/block/connect.rs");
        let src = std::fs::read_to_string(&path).expect("connect.rs");
        let body = fn_body(&src, "connect_block_inner");
        let func = stitch(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "coinbase_scriptsig_len must use the body");
            }
            other => panic!("unpatched coinbase_scriptsig_len must pass, got {other:?}"),
        }
        let needle = "(2..=100)";
        let boundary = stitch(&body.replace(needle, "(1..=100)"));
        let boundary_result = identity_query(&boundary, &clause);
        assert!(
            matches!(
                boundary_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "accepting a 1-byte coinbase scriptSig must flip the identity, got {boundary_result:?}"
        );
        let predicate = stitch(&body.replace(needle, "(2..=101)"));
        let predicate_result = identity_query(&predicate, &clause);
        assert!(
            matches!(
                predicate_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "accepting a 101-byte coinbase scriptSig must flip the identity, got {predicate_result:?}"
        );
    }

    #[test]
    fn enforce_tx_finality_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../blvm-consensus/src/block/connect.rs");
        let src = std::fs::read_to_string(&path).expect("connect.rs");
        let body = format!(
            "{};\n{}",
            fn_body(&src, "connect_block_inner"),
            fn_body(&src, "enforce_tx_finality")
        );
        let func = stitch(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "enforce_tx_finality must use the body");
            }
            other => panic!("unpatched enforce_tx_finality must pass, got {other:?}"),
        }
        let boundary = stitch(&body.replace("is_final_tx(", "is_final_gone("));
        let boundary_result = identity_query(&boundary, &clause);
        assert!(
            matches!(
                boundary_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "dropping the finality check must flip the identity, got {boundary_result:?}"
        );
        let predicate = stitch(&body.replace("ForkId::Bip112", "ForkId::Bip66"));
        let predicate_result = identity_query(&predicate, &clause);
        assert!(
            matches!(
                predicate_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "activating CSV on BIP66 must flip the identity, got {predicate_result:?}"
        );
    }
}

#[cfg(all(test, feature = "z3"))]
mod script_limits_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn fn_interior(src: &str, name: &str) -> String {
        let marker = format!("fn {name}");
        let at = src
            .find(&marker)
            .unwrap_or_else(|| panic!("missing {name}"));
        let rest = &src[at..];
        let brace = rest.find('{').expect("fn brace");
        let bytes = rest.as_bytes();
        let mut i = brace;
        let mut depth = 0i32;
        while i < bytes.len() {
            if bytes[i] == b'"' {
                i += 1;
                while i < bytes.len() {
                    if bytes[i] == b'\\' {
                        i += 2;
                        continue;
                    }
                    if bytes[i] == b'"' {
                        break;
                    }
                    i += 1;
                }
            } else if bytes[i] == b'{' {
                depth += 1;
            } else if bytes[i] == b'}' {
                depth -= 1;
                if depth == 0 {
                    return rest[brace + 1..i].to_string();
                }
            }
            i += 1;
        }
        panic!("unclosed {name}");
    }

    fn stitch(body: &str) -> syn::ItemFn {
        let src = format!("fn eval_script_inner(script: &[u8]) -> i64 {{\n{body}\n}}\n");
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse limits: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("limits fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "eval_script_inner",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn eval_script_limits_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let src = std::fs::read_to_string(&path).expect("script/mod.rs");
        let body = format!(
            "{};\n{}",
            fn_interior(&src, "eval_script_inner"),
            fn_interior(&src, "apply_data_push")
        );
        let func = stitch(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "eval_script_limits must use the body");
            }
            other => panic!("unpatched eval_script_limits must pass, got {other:?}"),
        }
        let boundary = stitch(&body.replace(
            "script.len() > MAX_SCRIPT_SIZE",
            "script.len() >= MAX_SCRIPT_SIZE",
        ));
        let boundary_result = identity_query(&boundary, &clause);
        assert!(
            matches!(
                boundary_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "accepting a script at the size cap must flip the identity, got {boundary_result:?}"
        );
        let predicate = stitch(&body.replace("> MAX_STACK_SIZE", ">= MAX_STACK_SIZE"));
        let predicate_result = identity_query(&predicate, &clause);
        assert!(
            matches!(
                predicate_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "accepting a stack at the cap must flip the identity, got {predicate_result:?}"
        );
    }

    #[test]
    fn eval_script_pc_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let src = std::fs::read_to_string(&path).expect("script/mod.rs");
        let body = fn_interior(&src, "eval_script_inner");
        let func = stitch(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "eval_script_pc must use the body");
            }
            other => panic!("unpatched eval_script_pc must pass, got {other:?}"),
        }
        let boundary = stitch(&body.replace("i += 1;", "i += 2;"));
        let boundary_result = identity_query(&boundary, &clause);
        assert!(
            matches!(
                boundary_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "advancing the program counter by 2 must flip the identity, got {boundary_result:?}"
        );
        let predicate = stitch(&body.replace("i += 1;", "i += 0;"));
        let predicate_result = identity_query(&predicate, &clause);
        assert!(
            matches!(
                predicate_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "leaving the program counter in place must flip the identity, got {predicate_result:?}"
        );
    }

    #[test]
    fn eval_script_control_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let src = std::fs::read_to_string(&path).expect("script/mod.rs");
        let body = fn_interior(&src, "eval_script_inner");
        let func = stitch(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "eval_script_control must use the body");
            }
            other => panic!("unpatched eval_script_control must pass, got {other:?}"),
        }
        let edited = body.replace("control_stack.push", "control_stack.len");
        let boundary = stitch(&edited);
        let boundary_result = identity_query(&boundary, &clause);
        assert!(
            matches!(
                boundary_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "replacing control pushes with length must flip the identity, got {boundary_result:?}"
        );
        let predicate = stitch(&edited);
        let predicate_result = identity_query(&predicate, &clause);
        assert!(
            matches!(
                predicate_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "the predicate control edit must flip the identity, got {predicate_result:?}"
        );
    }
}

mod ecdsa_helper_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn fn_interior(src: &str, name: &str) -> String {
        let marker = format!("fn {name}");
        let at = src
            .find(&marker)
            .unwrap_or_else(|| panic!("missing {name}"));
        let rest = &src[at..];
        let brace = rest.find('{').expect("fn brace");
        let bytes = rest.as_bytes();
        let mut i = brace;
        let mut depth = 0i32;
        while i < bytes.len() {
            if bytes[i] == b'"' {
                i += 1;
                while i < bytes.len() {
                    if bytes[i] == b'\\' {
                        i += 2;
                        continue;
                    }
                    if bytes[i] == b'"' {
                        break;
                    }
                    i += 1;
                }
            } else if bytes[i] == b'{' {
                depth += 1;
            } else if bytes[i] == b'}' {
                depth -= 1;
                if depth == 0 {
                    return rest[brace + 1..i].to_string();
                }
            }
            i += 1;
        }
        panic!("unclosed {name}");
    }

    fn stitch(body: &str) -> syn::ItemFn {
        let src = format!("fn eval_checksig_ecdsa(signature_bytes: &[u8]) -> i64 {{\n{body}\n}}\n");
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse ecdsa: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("ecdsa fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "eval_checksig_ecdsa",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn eval_checksig_ecdsa_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let src = std::fs::read_to_string(&path).expect("script/mod.rs");
        let body = fn_interior(&src, "eval_checksig_ecdsa");
        let func = stitch(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "eval_checksig_ecdsa must use the body");
            }
            other => panic!("unpatched eval_checksig_ecdsa must pass, got {other:?}"),
        }
        let boundary_src = body.replace("verify_signature(", "verify_signature_skipped(");
        assert_ne!(boundary_src, body);
        let boundary = stitch(&boundary_src);
        let boundary_result = identity_query(&boundary, &clause);
        assert!(
            matches!(
                boundary_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "renaming verify_signature must flip the identity, got {boundary_result:?}"
        );
        let predicate_src = body.replace(
            "signature::verify_signature(",
            "signature::verify_signature_skipped(",
        );
        assert_ne!(predicate_src, body);
        let predicate = stitch(&predicate_src);
        let predicate_result = identity_query(&predicate, &clause);
        assert!(
            matches!(
                predicate_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "renaming signature::verify_signature must flip the identity, got {predicate_result:?}"
        );
    }
}

mod signet_solution_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn fn_interior(src: &str, name: &str) -> String {
        let marker = format!("fn {name}");
        let at = src
            .find(&marker)
            .unwrap_or_else(|| panic!("missing {name}"));
        let rest = &src[at..];
        let brace = rest.find('{').expect("fn brace");
        let bytes = rest.as_bytes();
        let mut i = brace;
        let mut depth = 0i32;
        while i < bytes.len() {
            if bytes[i] == b'"' {
                i += 1;
                while i < bytes.len() {
                    if bytes[i] == b'\\' {
                        i += 2;
                        continue;
                    }
                    if bytes[i] == b'"' {
                        break;
                    }
                    i += 1;
                }
            } else if bytes[i] == b'{' {
                depth += 1;
            } else if bytes[i] == b'}' {
                depth -= 1;
                if depth == 0 {
                    return rest[brace + 1..i].to_string();
                }
            }
            i += 1;
        }
        panic!("unclosed {name}");
    }

    fn stitch(body: &str) -> syn::ItemFn {
        let src = format!("fn build_signet_solution_txs(block: &Block) -> i64 {{\n{body}\n}}\n");
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse signet: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("signet fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/signet.rs"),
            "build_signet_solution_txs",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn build_signet_solution_txs_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/signet.rs");
        let src = std::fs::read_to_string(&path).expect("signet.rs");
        let body = [
            "build_signet_solution_txs",
            "signet_to_spend_script_sig",
            "read_script_op",
            "fetch_and_clear_commitment_section",
        ]
        .into_iter()
        .map(|name| fn_interior(&src, name))
        .collect::<Vec<_>>()
        .join(";\n");
        let func = stitch(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(
                    body_translated,
                    "build_signet_solution_txs must use the body"
                );
            }
            other => panic!("unpatched build_signet_solution_txs must pass, got {other:?}"),
        }
        let boundary_src = body.replacen("index: 0xffff_ffff", "index: 0", 1);
        assert_ne!(boundary_src, body);
        let boundary = stitch(&boundary_src);
        let boundary_result = identity_query(&boundary, &clause);
        assert!(
            matches!(
                boundary_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "a zero null-outpoint index must flip the identity, got {boundary_result:?}"
        );
        let predicate_src = body.replace("script_sig.push(OP_0);\n", "");
        assert_ne!(predicate_src, body);
        let predicate = stitch(&predicate_src);
        let predicate_result = identity_query(&predicate, &clause);
        assert!(
            matches!(
                predicate_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "dropping the OP_0 push must flip the identity, got {predicate_result:?}"
        );
    }
}

mod p2pk_fast_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn fn_interior(src: &str, name: &str) -> String {
        let marker = format!("fn {name}");
        let at = src
            .find(&marker)
            .unwrap_or_else(|| panic!("missing {name}"));
        let rest = &src[at..];
        let brace = rest.find('{').expect("fn brace");
        let bytes = rest.as_bytes();
        let mut i = brace;
        let mut depth = 0i32;
        while i < bytes.len() {
            if bytes[i] == b'"' {
                i += 1;
                while i < bytes.len() {
                    if bytes[i] == b'\\' {
                        i += 2;
                        continue;
                    }
                    if bytes[i] == b'"' {
                        break;
                    }
                    i += 1;
                }
            } else if bytes[i] == b'{' {
                depth += 1;
            } else if bytes[i] == b'}' {
                depth -= 1;
                if depth == 0 {
                    return rest[brace + 1..i].to_string();
                }
            }
            i += 1;
        }
        panic!("unclosed {name}");
    }

    fn stitch(body: &str) -> syn::ItemFn {
        let src =
            format!("fn try_verify_p2pk_fast_path(script_pubkey: &[u8]) -> i64 {{\n{body}\n}}\n");
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse p2pk: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("p2pk fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "try_verify_p2pk_fast_path",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn try_verify_p2pk_fast_path_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let src = std::fs::read_to_string(&path).expect("script/mod.rs");
        let body = format!(
            "{};\n{}",
            fn_interior(&src, "try_verify_p2pk_fast_path"),
            fn_interior(&src, "canonical_p2pk_pubkey")
        );
        let func = stitch(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(
                    body_translated,
                    "try_verify_p2pk_fast_path must use the body"
                );
            }
            other => panic!("unpatched try_verify_p2pk_fast_path must pass, got {other:?}"),
        }
        let boundary_src = body.replace("canonical_p2pk_pubkey(", "canonical_p2pk_gone(");
        assert_ne!(boundary_src, body);
        let boundary = stitch(&boundary_src);
        let boundary_result = identity_query(&boundary, &clause);
        assert!(
            matches!(
                boundary_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "dropping the canonical pubkey gate must flip the identity, got {boundary_result:?}"
        );
        let predicate_src = body.replace("verify_signature(", "verify_signature_skipped(");
        assert_ne!(predicate_src, body);
        let predicate = stitch(&predicate_src);
        let predicate_result = identity_query(&predicate, &clause);
        assert!(
            matches!(
                predicate_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "renaming verify_signature must flip the identity, got {predicate_result:?}"
        );
    }
}

mod p2pkh_fast_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn fn_interior(src: &str, name: &str) -> String {
        let marker = format!("fn {name}");
        let at = src
            .find(&marker)
            .unwrap_or_else(|| panic!("missing {name}"));
        let rest = &src[at..];
        let brace = rest.find('{').expect("fn brace");
        let bytes = rest.as_bytes();
        let mut i = brace;
        let mut depth = 0i32;
        while i < bytes.len() {
            if bytes[i] == b'"' {
                i += 1;
                while i < bytes.len() {
                    if bytes[i] == b'\\' {
                        i += 2;
                        continue;
                    }
                    if bytes[i] == b'"' {
                        break;
                    }
                    i += 1;
                }
            } else if bytes[i] == b'{' {
                depth += 1;
            } else if bytes[i] == b'}' {
                depth -= 1;
                if depth == 0 {
                    return rest[brace + 1..i].to_string();
                }
            }
            i += 1;
        }
        panic!("unclosed {name}");
    }

    fn stitch(body: &str) -> syn::ItemFn {
        let src =
            format!("fn try_verify_p2pkh_fast_path(script_pubkey: &[u8]) -> i64 {{\n{body}\n}}\n");
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse p2pkh: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("p2pkh fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "try_verify_p2pkh_fast_path",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn try_verify_p2pkh_fast_path_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let src = std::fs::read_to_string(&path).expect("script/mod.rs");
        let body = fn_interior(&src, "try_verify_p2pkh_fast_path");
        let func = stitch(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(
                    body_translated,
                    "try_verify_p2pkh_fast_path must use the body"
                );
            }
            other => panic!("unpatched try_verify_p2pkh_fast_path must pass, got {other:?}"),
        }
        let boundary_src = body.replace("script_pubkey.len() != 25", "script_pubkey.len() != 26");
        assert_ne!(boundary_src, body);
        let boundary = stitch(&boundary_src);
        let boundary_result = identity_query(&boundary, &clause);
        assert!(
            matches!(
                boundary_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "moving the P2PKH length gate must flip the identity, got {boundary_result:?}"
        );
        let predicate_src = body.replace("verify_ecdsa_direct(", "verify_ecdsa_gone(");
        assert_ne!(predicate_src, body);
        let predicate = stitch(&predicate_src);
        let predicate_result = identity_query(&predicate, &clause);
        assert!(
            matches!(
                predicate_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "renaming verify_ecdsa_direct must flip the identity, got {predicate_result:?}"
        );
    }
}

mod p2sh_fast_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn fn_interior(src: &str, name: &str) -> String {
        let marker = format!("fn {name}");
        let at = src
            .find(&marker)
            .unwrap_or_else(|| panic!("missing {name}"));
        let rest = &src[at..];
        let brace = rest.find('{').expect("fn brace");
        let bytes = rest.as_bytes();
        let mut i = brace;
        let mut depth = 0i32;
        while i < bytes.len() {
            if bytes[i] == b'"' {
                i += 1;
                while i < bytes.len() {
                    if bytes[i] == b'\\' {
                        i += 2;
                        continue;
                    }
                    if bytes[i] == b'"' {
                        break;
                    }
                    i += 1;
                }
            } else if bytes[i] == b'{' {
                depth += 1;
            } else if bytes[i] == b'}' {
                depth -= 1;
                if depth == 0 {
                    return rest[brace + 1..i].to_string();
                }
            }
            i += 1;
        }
        panic!("unclosed {name}");
    }

    fn stitch(body: &str) -> syn::ItemFn {
        let src =
            format!("fn try_verify_p2sh_fast_path(script_pubkey: &[u8]) -> i64 {{\n{body}\n}}\n");
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse p2sh: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("p2sh fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "try_verify_p2sh_fast_path",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn try_verify_p2sh_fast_path_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let src = std::fs::read_to_string(&path).expect("script/mod.rs");
        let body = [
            "try_verify_p2sh_fast_path",
            "verify_p2sh_p2pkh_redeem",
            "verify_p2sh_p2pk_redeem",
        ]
        .into_iter()
        .map(|name| fn_interior(&src, name))
        .collect::<Vec<_>>()
        .join(";\n");
        let func = stitch(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(
                    body_translated,
                    "try_verify_p2sh_fast_path must use the body"
                );
            }
            other => panic!("unpatched try_verify_p2sh_fast_path must pass, got {other:?}"),
        }
        let boundary_src = body.replace("script_pubkey.len() != 23", "script_pubkey.len() != 24");
        assert_ne!(boundary_src, body);
        let boundary = stitch(&boundary_src);
        let boundary_result = identity_query(&boundary, &clause);
        assert!(
            matches!(
                boundary_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "moving the P2SH length gate must flip the identity, got {boundary_result:?}"
        );
        let predicate_src = body.replace("verify_signature(", "verify_signature_skipped(");
        assert_ne!(predicate_src, body);
        let predicate = stitch(&predicate_src);
        let predicate_result = identity_query(&predicate, &clause);
        assert!(
            matches!(
                predicate_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "renaming verify_signature must flip the identity, got {predicate_result:?}"
        );
    }
}

mod p2wpkh_fast_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn fn_interior(src: &str, name: &str) -> String {
        let marker = format!("fn {name}");
        let at = src
            .find(&marker)
            .unwrap_or_else(|| panic!("missing {name}"));
        let rest = &src[at..];
        let brace = rest.find('{').expect("fn brace");
        let bytes = rest.as_bytes();
        let mut i = brace;
        let mut depth = 0i32;
        while i < bytes.len() {
            if bytes[i] == b'"' {
                i += 1;
                while i < bytes.len() {
                    if bytes[i] == b'\\' {
                        i += 2;
                        continue;
                    }
                    if bytes[i] == b'"' {
                        break;
                    }
                    i += 1;
                }
            } else if bytes[i] == b'{' {
                depth += 1;
            } else if bytes[i] == b'}' {
                depth -= 1;
                if depth == 0 {
                    return rest[brace + 1..i].to_string();
                }
            }
            i += 1;
        }
        panic!("unclosed {name}");
    }

    fn stitch(body: &str) -> syn::ItemFn {
        let src =
            format!("fn try_verify_p2wpkh_fast_path(script_pubkey: &[u8]) -> i64 {{\n{body}\n}}\n");
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse p2wpkh: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("p2wpkh fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "try_verify_p2wpkh_fast_path",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn try_verify_p2wpkh_fast_path_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let src = std::fs::read_to_string(&path).expect("script/mod.rs");
        let body = [
            "try_verify_p2wpkh_fast_path",
            "verify_p2wpkh_inline",
            "finish_p2wpkh_ecdsa",
        ]
        .into_iter()
        .map(|name| fn_interior(&src, name))
        .collect::<Vec<_>>()
        .join(";\n");
        let func = stitch(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(
                    body_translated,
                    "try_verify_p2wpkh_fast_path must use the body"
                );
            }
            other => panic!("unpatched try_verify_p2wpkh_fast_path must pass, got {other:?}"),
        }
        let boundary_src = body.replace("script_pubkey.len() != 22", "script_pubkey.len() != 23");
        assert_ne!(boundary_src, body);
        let boundary = stitch(&boundary_src);
        let boundary_result = identity_query(&boundary, &clause);
        assert!(
            matches!(
                boundary_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "moving the P2WPKH length gate must flip the identity, got {boundary_result:?}"
        );
        let predicate_src = body.replace("verify_signature(", "verify_signature_skipped(");
        assert_ne!(predicate_src, body);
        let predicate = stitch(&predicate_src);
        let predicate_result = identity_query(&predicate, &clause);
        assert!(
            matches!(
                predicate_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "renaming verify_signature must flip the identity, got {predicate_result:?}"
        );
    }
}

mod script_cache_key_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn fn_interior(src: &str, name: &str) -> String {
        let marker = format!("fn {name}");
        let at = src
            .find(&marker)
            .unwrap_or_else(|| panic!("missing {name}"));
        let rest = &src[at..];
        let brace = rest.find('{').expect("fn brace");
        let bytes = rest.as_bytes();
        let mut i = brace;
        let mut depth = 0i32;
        while i < bytes.len() {
            if bytes[i] == b'"' {
                i += 1;
                while i < bytes.len() {
                    if bytes[i] == b'\\' {
                        i += 2;
                        continue;
                    }
                    if bytes[i] == b'"' {
                        break;
                    }
                    i += 1;
                }
            } else if bytes[i] == b'{' {
                depth += 1;
            } else if bytes[i] == b'}' {
                depth -= 1;
                if depth == 0 {
                    return rest[brace + 1..i].to_string();
                }
            }
            i += 1;
        }
        panic!("unclosed {name}");
    }

    fn stitch(body: &str) -> syn::ItemFn {
        let src = format!("fn compute_script_cache_key(script_sig: &[u8]) -> u64 {{\n{body}\n}}\n");
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse cache key: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("cache key fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "compute_script_cache_key",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn compute_script_cache_key_passes_and_the_flags_edit_flips() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let src = std::fs::read_to_string(&path).expect("script/mod.rs");
        let body = fn_interior(&src, "compute_script_cache_key");
        let func = stitch(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(
                    body_translated,
                    "compute_script_cache_key must use the body"
                );
            }
            other => panic!("unpatched compute_script_cache_key must pass, got {other:?}"),
        }
        let boundary_src = body.replace("hasher.update(flags.to_le_bytes());", "");
        assert_ne!(boundary_src, body);
        let boundary = stitch(&boundary_src);
        let boundary_result = identity_query(&boundary, &clause);
        assert!(
            matches!(
                boundary_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "dropping the flags update must flip the identity, got {boundary_result:?}"
        );
    }
}

mod script_cache_hit_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn fn_interior(src: &str, name: &str) -> String {
        let marker = format!("fn {name}(");
        let at = src
            .find(&marker)
            .unwrap_or_else(|| panic!("missing {name}"));
        let rest = &src[at..];
        let brace = rest.find('{').expect("fn brace");
        let bytes = rest.as_bytes();
        let mut i = brace;
        let mut depth = 0i32;
        while i < bytes.len() {
            if bytes[i] == b'"' {
                i += 1;
                while i < bytes.len() {
                    if bytes[i] == b'\\' {
                        i += 2;
                        continue;
                    }
                    if bytes[i] == b'"' {
                        break;
                    }
                    i += 1;
                }
            } else if bytes[i] == b'{' {
                depth += 1;
            } else if bytes[i] == b'}' {
                depth -= 1;
                if depth == 0 {
                    return rest[brace + 1..i].to_string();
                }
            }
            i += 1;
        }
        panic!("unclosed {name}");
    }

    fn stitch(body: &str) -> syn::ItemFn {
        let src = format!("fn verify_script_cache_hit(script_sig: &[u8]) -> i64 {{\n{body}\n}}\n");
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse cache hit: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("cache hit fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "verify_script_cache_hit",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn verify_script_cache_hit_passes_and_dropping_the_return_flips() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let src = std::fs::read_to_string(&path).expect("script/mod.rs");
        let body = fn_interior(&src, "verify_script");
        let func = stitch(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "verify_script_cache_hit must use the body");
            }
            other => panic!("unpatched verify_script_cache_hit must pass, got {other:?}"),
        }
        let boundary_src = body.replace("return Ok(cached_result);", "");
        assert_ne!(boundary_src, body);
        let boundary = stitch(&boundary_src);
        let boundary_result = identity_query(&boundary, &clause);
        assert!(
            matches!(
                boundary_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "dropping the cached return must flip the identity, got {boundary_result:?}"
        );
    }
}

mod checksig_verifier_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn checksig_arm(src: &str) -> String {
        let at = src
            .find("script_bool_bytes(is_valid)")
            .expect("checksig push");
        let arm = src[..at].rfind("OP_CHECKSIG =>").expect("checksig arm");
        let rest = &src[arm..];
        let brace = rest.find('{').expect("arm brace");
        let bytes = rest.as_bytes();
        let mut i = brace;
        let mut depth = 0i32;
        while i < bytes.len() {
            if bytes[i] == b'"' {
                i += 1;
                while i < bytes.len() {
                    if bytes[i] == b'\\' {
                        i += 2;
                        continue;
                    }
                    if bytes[i] == b'"' {
                        break;
                    }
                    i += 1;
                }
            } else if bytes[i] == b'{' {
                depth += 1;
            } else if bytes[i] == b'}' {
                depth -= 1;
                if depth == 0 {
                    return rest[brace + 1..i].to_string();
                }
            }
            i += 1;
        }
        panic!("unclosed checksig arm");
    }

    fn stitch(body: &str) -> syn::ItemFn {
        let src = format!("fn op_checksig_verifier(stack: &[u8]) -> i64 {{\n{body}\n}}\n");
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse checksig: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("checksig fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_CHECKSIG_verifier",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_checksig_verifier_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let src = std::fs::read_to_string(&path).expect("script/mod.rs");
        let body = checksig_arm(&src);
        let func = stitch(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_CHECKSIG_verifier must use the body");
            }
            other => panic!("unpatched OP_CHECKSIG_verifier must pass, got {other:?}"),
        }
        let negated_src = body.replace(
            "script_bool_bytes(is_valid)",
            "script_bool_bytes(!is_valid)",
        );
        assert_ne!(negated_src, body);
        let negated = stitch(&negated_src);
        let negated_result = identity_query(&negated, &clause);
        assert!(
            matches!(
                negated_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "negating is_valid must flip the identity, got {negated_result:?}"
        );
        let forced_src = body.replace("script_bool_bytes(is_valid)", "script_bool_bytes(true)");
        assert_ne!(forced_src, body);
        let forced = stitch(&forced_src);
        let forced_result = identity_query(&forced, &clause);
        assert!(
            matches!(
                forced_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "forcing the checksig bit must flip the identity, got {forced_result:?}"
        );
    }
}

mod op_if_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn brace_body(rest: &str) -> String {
        let brace = rest.find('{').expect("brace");
        let bytes = rest.as_bytes();
        let mut i = brace;
        let mut depth = 0i32;
        while i < bytes.len() {
            if bytes[i] == b'"' {
                i += 1;
                while i < bytes.len() {
                    if bytes[i] == b'\\' {
                        i += 2;
                        continue;
                    }
                    if bytes[i] == b'"' {
                        break;
                    }
                    i += 1;
                }
            } else if bytes[i] == b'{' {
                depth += 1;
            } else if bytes[i] == b'}' {
                depth -= 1;
                if depth == 0 {
                    return rest[brace + 1..i].to_string();
                }
            }
            i += 1;
        }
        panic!("unclosed brace");
    }

    fn if_arm(src: &str) -> String {
        let mut from = 0;
        while let Some(rel) = src[from..].find("OP_IF =>") {
            let at = from + rel;
            let body = brace_body(&src[at..]);
            if body.contains("i += 1;") {
                return body;
            }
            from = at + "OP_IF =>".len();
        }
        panic!("OP_IF arm");
    }

    fn fn_body(src: &str, name: &str) -> String {
        let marker = format!("fn {name}(");
        let at = src.find(&marker).unwrap_or_else(|| panic!("{name}"));
        brace_body(&src[at..])
    }

    fn stitch(arm: &str, helper: &str) -> syn::ItemFn {
        let src = format!("fn op_if(stack: &[u8]) -> i64 {{\n{arm}\n;\n{helper}\n}}\n");
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse OP_IF: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("OP_IF fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/script/mod.rs"),
            "OP_IF",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn op_if_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/script/mod.rs");
        let src = std::fs::read_to_string(&path).expect("script/mod.rs");
        let arm = if_arm(&src);
        let helper = fn_body(&src, "pop_if_condition");
        let func = stitch(&arm, &helper);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "OP_IF must use the body");
            }
            other => panic!("unpatched OP_IF must pass, got {other:?}"),
        }
        let stepped = {
            let mut next = arm.clone();
            let at = next.find("i += 1;").expect("step");
            next.replace_range(at..at + "i += 1;".len(), "i += 2;");
            next
        };
        assert_ne!(stepped, arm);
        let stepped_result = identity_query(&stitch(&stepped, &helper), &clause);
        assert!(
            matches!(
                stepped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "i += 2 must flip the identity, got {stepped_result:?}"
        );
        let dropped = arm.replace("control_stack.push", "control_stack.len");
        assert_ne!(dropped, arm);
        let dropped_result = identity_query(&stitch(&dropped, &helper), &clause);
        assert!(
            matches!(
                dropped_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "dropping the control push must flip the identity, got {dropped_result:?}"
        );
    }
}

mod total_supply_identity {
    use super::{FailureKind, VerificationResult, make_function_to_verify, verify_function};
    use crate::parser::spec_expr::consensus_workspace_present;
    use std::path::PathBuf;

    fn fn_body(src: &str, name: &str) -> String {
        let marker = format!("fn {name}(");
        let at = src.find(&marker).unwrap_or_else(|| panic!("{name}"));
        let rest = &src[at..];
        let brace = rest.find('{').expect("brace");
        let bytes = rest.as_bytes();
        let mut i = brace;
        let mut depth = 0i32;
        while i < bytes.len() {
            if bytes[i] == b'"' {
                i += 1;
                while i < bytes.len() {
                    if bytes[i] == b'\\' {
                        i += 2;
                        continue;
                    }
                    if bytes[i] == b'"' {
                        break;
                    }
                    i += 1;
                }
            } else if bytes[i] == b'{' {
                depth += 1;
            } else if bytes[i] == b'}' {
                depth -= 1;
                if depth == 0 {
                    return rest[brace + 1..i].to_string();
                }
            }
            i += 1;
        }
        panic!("unclosed {name}");
    }

    fn stitch(body: &str) -> syn::ItemFn {
        let src = format!("fn total_supply(height: i64) -> i64 {{\n{body}\n}}\n");
        let file = syn::parse_file(&src).unwrap_or_else(|err| panic!("parse supply: {err}"));
        match &file.items[0] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("supply fn"),
        }
    }

    fn identity_query(func: &syn::ItemFn, clause: &str) -> VerificationResult {
        let mut function = make_function_to_verify(
            std::path::Path::new("src/economic.rs"),
            "total_supply",
            &func.attrs,
            func,
        );
        function.contracts = vec![super::Contract {
            contract_type: super::ContractType::Ensures,
            condition: clause.to_string(),
            expr: syn::parse_str(clause).ok(),
            is_spec_derived: true,
        }];
        verify_function(&function, 30, &[])
    }

    #[test]
    fn total_supply_passes_and_both_edits_flip() {
        if !consensus_workspace_present() {
            return;
        }
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src/economic.rs");
        let src = std::fs::read_to_string(&path).expect("economic.rs");
        let body = fn_body(&src, "total_supply");
        let func = stitch(&body);
        let block = func.block.clone();
        let clause = quote::quote!(#block).to_string();
        match identity_query(&func, &clause) {
            VerificationResult::Passed { body_translated } => {
                assert!(body_translated, "total_supply must use the body");
            }
            other => panic!("unpatched total_supply must pass, got {other:?}"),
        }
        let widened = body.replace("period_start > end", "period_start >= end");
        assert_ne!(widened, body);
        let widened_result = identity_query(&stitch(&widened), &clause);
        assert!(
            matches!(
                widened_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "period_start >= end must flip the identity, got {widened_result:?}"
        );
        let shifted = body.replace("INITIAL_SUBSIDY >> k", "INITIAL_SUBSIDY >> 0");
        assert_ne!(shifted, body);
        let shifted_result = identity_query(&stitch(&shifted), &clause);
        assert!(
            matches!(
                shifted_result,
                VerificationResult::Failed {
                    kind: FailureKind::Counterexample,
                    ..
                }
            ),
            "shifting by 0 must flip the identity, got {shifted_result:?}"
        );
    }
}
