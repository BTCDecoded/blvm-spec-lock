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
    pub function_sig: Option<syn::ItemFn>, // Store function signature for type inference
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
                                function_sig: Some(item_fn),
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
        function_sig: Some(func.clone()),
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
    if function.contracts.is_empty() {
        // Attempt to auto-derive type-level contracts from the return type before
        // giving up with NoContracts.  Functions returning unsigned / opaque types
        // (Hash, Block, u64, …) get `result >= 0` for free; functions returning
        // bool-like types get `result == true || result == false`.  These contracts
        // are trivially true by the type system and need no Z3 body translation.
        //
        // Only functions returning signed primitives (Integer / i64, etc.) or types
        // with no useful type-level contract fall through to NoContracts.
        if let Some(ref sig) = function.function_sig {
            use crate::translator::z3_translator::auto_type_contracts;
            let return_ty = extract_return_type_from_sig(sig);
            if let Some(ret) = return_ty {
                let type_contracts = auto_type_contracts(&ret);
                if !type_contracts.is_empty() {
                    // Auto-derived type contracts are "spec derived" so they show
                    // distinctly in reports and don't inflate the semantic spec count.
                    let synthetic: Vec<Contract> = type_contracts
                        .iter()
                        .filter_map(|s| {
                            let expr: syn::Expr = syn::parse_str(s).ok()?;
                            Some(Contract {
                                contract_type: ContractType::Ensures,
                                condition: s.clone(),
                                expr: Some(expr),
                                is_spec_derived: true,
                            })
                        })
                        .collect();
                    if !synthetic.is_empty() {
                        let mut synthetic_fn = function.clone();
                        synthetic_fn.contracts = synthetic;
                        return verify_function(&synthetic_fn, timeout_secs, callee_postconds);
                    }
                }
            }
        }
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
                        Ok(()) => verified_count += 1,
                        Err(e) => {
                            if e.contains("Could not translate body") {
                                // Body untranslatable for determinism check.
                                // Spec-derived determinism contracts that reduce to "true" via
                                // extract_parseable_condition (e.g. "may differ" annotations) are
                                // acceptable as type-level assertions — count them as verified
                                // rather than recording an unsupported-translation gap.
                                if contract.is_spec_derived {
                                    verified_count += 1;
                                } else {
                                    requires_z3_count += 1;
                                    let mut slot = translation_error.borrow_mut();
                                    if slot.is_none() {
                                        *slot = Some(e);
                                    }
                                }
                            } else {
                                failed_contracts.push((
                                    format!("{:?}", contract.contract_type),
                                    format!("Determinism: {e}"),
                                    contract.is_spec_derived,
                                ));
                            }
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
    let requires_library: Vec<_> = requires_contracts
        .iter()
        .chain(axiom_contracts.iter())
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
            Err(msg)
        }
        VerificationResult::Unknown { reason } => Err(format!("Z3 verification unknown: {reason}")),
        VerificationResult::Error { error } => Err(format!("Z3 verification error: {error}")),
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

    // A failure is a translator gap when Z3 cannot produce a concrete counterexample —
    // meaning the result is never a genuine implementation violation.
    //
    // "no named variable assignments" is unconditionally a gap (spec-derived or manual):
    // Z3 returned a model with no concrete values for function parameters, which only
    // happens when the body was not meaningfully translated.
    let is_translator_gap = |reason: &str| -> bool {
        reason.contains("could not be parsed")
            || reason.contains("Could not translate function body")
            || reason.contains("counterexample model has no named variable assignments")
            || reason.contains("Translation error")
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
        FailureKind, PartialReason, VerificationResult, demote_if_all_spec_derived,
        failed_verification, failure_kind,
    };

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
        // When the function body cannot be translated to Z3 constraints, the SAT result
        // is vacuous (no body = no real counterexample).  The z3_verifier returns Unknown
        // with "Could not translate function body", which verify_with_z3 propagates as
        // "Z3: Z3 verification unknown: Could not translate function body ...".
        // demote_if_all_spec_derived should treat this as a translation gap → Partial.
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
            _ => panic!("expected Partial, got {result:?}"),
        }
    }

    #[test]
    fn spec_derived_empty_assignments_demotes_to_partial() {
        // When the Z3 translator produces SAT but cannot extract named variable assignments
        // (stub extract_counterexample), the verifier returns Unknown with
        // "counterexample model has no named variable assignments".
        // demote_if_all_spec_derived should treat this as a translation gap → Partial.
        let failed = vec![(
            "Ensures".to_string(),
            "Z3: Z3 verification unknown: Z3 found SAT but counterexample model has no named \
             variable assignments (incomplete translator); result is not a concrete witness \
             against the implementation"
                .to_string(),
            true,
        )];
        let result = demote_if_all_spec_derived(&failed, 0, 1)
            .expect("empty-assignments gap should demote to Partial");
        match result {
            VerificationResult::Partial { partial_reason, .. } => {
                assert_eq!(partial_reason, Some(PartialReason::UnsupportedTranslation));
            }
            _ => panic!("expected Partial, got {result:?}"),
        }
    }

    #[test]
    fn spec_derived_translation_type_error_demotes_to_partial() {
        // "Translation error: Type error: Expected Bool" is a Z3 translator limitation —
        // the condition parsed but cannot be expressed as a Z3 Bool.  Treat as a gap.
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
            _ => panic!("expected Partial, got {result:?}"),
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
        // "counterexample model has no named variable assignments" is ALWAYS a translator gap —
        // not a real counterexample — regardless of whether the contract is spec-derived.
        // This covers functions (e.g. connect_block) whose manually-written ensures fail with
        // this message because the body translator cannot model the function.
        let failed = vec![(
            "Ensures".to_string(),
            "Z3: Z3 verification unknown: Z3 found SAT but counterexample model has no named \
             variable assignments (incomplete translator); result is not a concrete witness \
             against the implementation (3 total failures)"
                .to_string(),
            false, // NOT spec-derived — manual contract
        )];
        let result = demote_if_all_spec_derived(&failed, 0, 1)
            .expect("no-named-assignments gap must demote to Partial even for manual contracts");
        match result {
            VerificationResult::Partial { partial_reason, .. } => {
                assert_eq!(partial_reason, Some(PartialReason::UnsupportedTranslation));
            }
            _ => panic!("expected Partial, got {result:?}"),
        }
    }
}
