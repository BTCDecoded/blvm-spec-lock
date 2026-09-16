//! Implementation of the #[spec_locked] proc macro
//!
//! Links Rust functions to Orange Paper specifications.
//! Contracts are provided via manual #[requires] and #[ensures] attributes,
//! which will be verified by the BLVM Spec Lock verification tool.

use crate::parser::{
    Contract, ContractType, FunctionSpec, SpecParser, SpecSection,
    section_id_subsumes_formula_section,
};
use proc_macro2::{Span, TokenStream};
use quote::quote;
use regex::Regex;
use std::path::PathBuf;
use syn::{Ident, LitStr, Token, parse::Parse};

/// Resolve Orange Paper markdown paths for `#[spec_locked]`.
///
/// Order:
/// 1. `CARGO_MANIFEST_DIR/blvm-spec/` — vendored copy (matches what `cargo publish` unpacks).
/// 2. `CARGO_MANIFEST_DIR/../blvm-spec/` — monorepo / local sibling layout.
fn resolve_orange_paper_paths(manifest_dir: &str) -> Option<Vec<PathBuf>> {
    let manifest = PathBuf::from(manifest_dir);
    let candidates = [manifest.join("blvm-spec"), manifest.join("../blvm-spec")];
    // Prefer PROTOCOL.md + ARCHITECTURE.md from any candidate (canonical sections, e.g. 5.4, 11.4).
    // Otherwise an in-crate THE_ORANGE_PAPER-only tree would win and hide ../blvm-spec in monorepos.
    for spec_dir in &candidates {
        let protocol = spec_dir.join("PROTOCOL.md");
        let architecture = spec_dir.join("ARCHITECTURE.md");
        if protocol.exists() && architecture.exists() {
            return Some(vec![protocol, architecture]);
        }
    }
    for spec_dir in &candidates {
        let umbrella = spec_dir.join("THE_ORANGE_PAPER.md");
        if umbrella.exists() {
            return Some(vec![umbrella]);
        }
    }
    None
}

/// Arguments for #[spec_locked] attribute
///
/// Supports multiple elegant syntaxes:
/// - `#[spec_locked]` - Auto-infer section and theorem from function name (NEW!)
/// - `#[spec_locked("6.1")]` - Section only, function name inferred from Rust function
/// - `#[spec_locked("6.1.1")]` - Granular ID (theorem/subsection), function name inferred
/// - `#[spec_locked("6.1", "GetBlockSubsidy")]` - Simple positional
/// - `#[spec_locked(section = "6.1", function = "GetBlockSubsidy")]` - Named parameters
/// - `#[spec_locked("6.1::GetBlockSubsidy")]` - Single string with separator
struct SpecLockedArgs {
    section: Option<LitStr>,  // Optional - can be auto-inferred
    function: Option<LitStr>, // Optional - can be inferred from function name
    spec_path: Option<LitStr>,
}

impl Parse for SpecLockedArgs {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        // Try to parse as simple positional args first: "6.1", "GetBlockSubsidy" or just "6.1"
        if input.peek(LitStr) {
            let first: LitStr = input.parse()?;

            // Check if it's the combined format: "6.1::GetBlockSubsidy"
            let first_str = first.value();
            if first_str.contains("::") {
                let parts: Vec<&str> = first_str.split("::").collect();
                if parts.len() == 2 {
                    let section = LitStr::new(parts[0].trim(), first.span());
                    let function = LitStr::new(parts[1].trim(), first.span());

                    // Check for optional spec_path
                    let spec_path = if input.peek(Token![,]) {
                        input.parse::<Token![,]>()?;
                        if input.peek(Ident) {
                            let key: Ident = input.parse()?;
                            if key == "spec_path" {
                                input.parse::<Token![=]>()?;
                                Some(input.parse()?)
                            } else {
                                return Err(
                                    input.error("Expected 'spec_path' after section::function")
                                );
                            }
                        } else {
                            None
                        }
                    } else {
                        None
                    };

                    return Ok(SpecLockedArgs {
                        section: Some(section),
                        function: Some(function),
                        spec_path,
                    });
                }
            }

            // It's positional: first is section, second is optional function name
            let function = if input.peek(Token![,]) {
                input.parse::<Token![,]>()?;
                if input.peek(LitStr) {
                    Some(input.parse()?)
                } else {
                    None // Function name will be inferred
                }
            } else {
                None // Function name will be inferred
            };

            // Check for optional spec_path
            let spec_path = if input.peek(Token![,]) {
                input.parse::<Token![,]>()?;
                if input.peek(Ident) {
                    let key: Ident = input.parse()?;
                    if key == "spec_path" {
                        input.parse::<Token![=]>()?;
                        Some(input.parse()?)
                    } else {
                        return Err(input.error("Expected 'spec_path'"));
                    }
                } else {
                    None
                }
            } else {
                None
            };

            return Ok(SpecLockedArgs {
                section: Some(first),
                function,
                spec_path,
            });
        }

        // Parse as named parameters: section = "...", function = "..." (function optional)
        let mut section: Option<LitStr> = None;
        let mut function: Option<LitStr> = None;
        let mut spec_path: Option<LitStr> = None;

        while !input.is_empty() {
            let key: Ident = input.parse()?;
            input.parse::<Token![=]>()?;
            let value: LitStr = input.parse()?;

            if key == "section" {
                section = Some(value);
            } else if key == "function" {
                function = Some(value);
            } else if key == "spec_path" {
                spec_path = Some(value);
            } else {
                return Err(input.error(format!(
                    "Unknown parameter: {key}. Expected 'section', 'function', or 'spec_path'"
                )));
            }

            if !input.is_empty() {
                input.parse::<Token![,]>()?;
            }
        }

        Ok(SpecLockedArgs {
            section,  // Optional - can be auto-inferred if not provided
            function, // Optional - will be inferred if not provided
            spec_path,
        })
    }
}

/// Generate #[requires] preconditions
fn generate_requires(spec: &FunctionSpec, func: &syn::ItemFn) -> TokenStream {
    use proc_macro2::TokenStream as TokenStream2;
    let mut requires = Vec::<TokenStream2>::new();

    // Extract parameter names from function signature
    let param_names: Vec<String> = func
        .sig
        .inputs
        .iter()
        .filter_map(|input| {
            if let syn::FnArg::Typed(pat) = input {
                if let syn::Pat::Ident(ident) = &*pat.pat {
                    Some(ident.ident.to_string())
                } else {
                    None
                }
            } else {
                None
            }
        })
        .collect();

    // Generate basic preconditions from signature
    if let Some(sig) = &spec.signature {
        if let Some((inputs, _)) = SpecParser::parse_signature(sig) {
            // For Natural inputs, ensure non-negative (though Natural is u64, so always true)
            // For Integer inputs, we might want bounds checks
            for (i, input_type) in inputs.iter().enumerate() {
                if let Some(param_name) = param_names.get(i) {
                    let param_ident = syn::Ident::new(param_name, proc_macro2::Span::call_site());
                    match input_type.as_str() {
                        "Natural" => {
                            // Natural is u64, so always >= 0, but we can add explicit check
                            requires.push(quote! {
                                #[blvm_spec_lock::requires(#param_ident >= 0)]
                            });
                        }
                        "Integer" => {
                            // Could add bounds if needed
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    // Add conditions from spec
    for _condition in &spec.conditions {
        // Try to parse condition as Rust expression
        // For now, generate a comment - full parsing would require more sophisticated logic
        requires.push(quote! {
            // Precondition from spec: #condition
        });
    }

    if requires.is_empty() {
        TokenStream2::new()
    } else {
        quote! {
            #(#requires)*
        }
    }
}

/// Generate #[ensures] postconditions
///
/// Generates contracts from Orange Paper specifications only
fn generate_ensures(spec: &FunctionSpec, func: &syn::ItemFn) -> TokenStream {
    use proc_macro2::TokenStream as TokenStream2;
    let mut ensures = Vec::<TokenStream2>::new();

    // Check if function returns a tuple (which doesn't have View)
    let returns_tuple = if let syn::ReturnType::Type(_, return_type) = &func.sig.output {
        match return_type.as_ref() {
            syn::Type::Tuple(_) => true,
            syn::Type::Path(type_path) => {
                // Check for Result<Tuple, E>
                if let Some(segment) = type_path.path.segments.last() {
                    if segment.ident == "Result" {
                        // Check if Result contains a tuple
                        if let syn::PathArguments::AngleBracketed(args) = &segment.arguments {
                            if let Some(syn::GenericArgument::Type(inner_type)) = args.args.first()
                            {
                                matches!(inner_type, syn::Type::Tuple(_))
                            } else {
                                false
                            }
                        } else {
                            false
                        }
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
            _ => false,
        }
    } else {
        false
    };

    // First, try to generate contracts from Orange Paper mathematical properties
    if !spec.contracts.is_empty() && !returns_tuple {
        // Skip Orange Paper contracts for tuple return types - they need special handling
        for contract in &spec.contracts {
            match contract.contract_type {
                crate::parser::ContractType::Ensures
                | crate::parser::ContractType::Property
                | crate::parser::ContractType::EdgeCase => {
                    // Translate mathematical notation to Rust contract
                    let rust_expr =
                        translate_math_to_rust_contract(&contract.condition, &spec.name, func);

                    let comment_str = contract
                        .comment
                        .as_ref()
                        .map(|c| format!(" // {c}"))
                        .unwrap_or_else(String::new);
                    let comment_tokens: TokenStream = if comment_str.is_empty() {
                        TokenStream::new()
                    } else {
                        comment_str.parse().unwrap_or_default()
                    };

                    ensures.push(quote! {
                        #[blvm_spec_lock::ensures(#rust_expr)]#comment_tokens
                    });
                }
                crate::parser::ContractType::Requires => {
                    // Requires are handled in generate_requires
                }
            }
        }

        // If we found contracts from Orange Paper, use them
        if !ensures.is_empty() {
            return quote! {
                #(#ensures)*
            };
        }
    }

    // No contracts found in contracts array - try extracting from properties
    if !spec.properties.is_empty() && !returns_tuple {
        for property in &spec.properties {
            if matches!(
                property.property_type,
                crate::parser::PropertyType::Ensures | crate::parser::PropertyType::Invariant
            ) {
                // Translate mathematical notation to Rust contract
                let rust_expr =
                    translate_math_to_rust_contract(&property.statement, &spec.name, func);

                let name = &property.name;
                let comment_str = format!(" // {name}");
                let comment_tokens: TokenStream = comment_str.parse().unwrap_or_default();

                ensures.push(quote! {
                    #[blvm_spec_lock::ensures(#rust_expr)]#comment_tokens
                });
            }
        }

        // If we found contracts from properties, use them
        if !ensures.is_empty() {
            return quote! {
                #(#ensures)*
            };
        }
    }

    // Try extracting from theorems
    for theorem in &spec.theorems {
        // Translate theorem statement to Rust contract
        let rust_expr = translate_math_to_rust_contract(&theorem.statement, &spec.name, func);

        let comment_str = format!(
            " // Theorem {n}: {name}",
            n = theorem.number.as_str(),
            name = theorem.name.as_str()
        );
        let comment_tokens: TokenStream = comment_str.parse().unwrap_or_default();

        ensures.push(quote! {
            #[blvm_spec_lock::ensures(#rust_expr)]#comment_tokens
        });
    }

    // Try extracting from formula
    if let Some(formula) = &spec.formula {
        let rust_expr = translate_math_to_rust_contract(formula, &spec.name, func);
        ensures.push(quote! {
            #[blvm_spec_lock::ensures(#rust_expr)] // From formula
        });
    }

    if ensures.is_empty() {
        TokenStream2::new()
    } else {
        quote! {
            #(#ensures)*
        }
    }
}

/// Convert Rust function name (snake_case) to Orange Paper function name (PascalCase)
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

/// Generate name variations for improved matching
/// e.g., "check_bip30" -> ["CheckBip30", "BIP30", "CheckBIP30", "Bip30"]
fn generate_name_variations(func_name: &str) -> Vec<String> {
    let mut variations = Vec::new();

    // Original PascalCase
    variations.push(rust_to_pascal_case(func_name));

    // Remove common prefixes
    let without_check = func_name.strip_prefix("check_").unwrap_or(func_name);
    let without_verify = without_check
        .strip_prefix("verify_")
        .unwrap_or(without_check);
    let without_calculate = without_verify
        .strip_prefix("calculate_")
        .unwrap_or(without_verify);
    let without_get = without_calculate
        .strip_prefix("get_")
        .unwrap_or(without_calculate);

    if without_check != func_name {
        variations.push(rust_to_pascal_case(without_check));
    }
    if without_verify != without_check {
        variations.push(rust_to_pascal_case(without_verify));
    }
    if without_calculate != without_verify {
        variations.push(rust_to_pascal_case(without_calculate));
    }
    if without_get != without_calculate {
        variations.push(rust_to_pascal_case(without_get));
    }

    // Handle BIP/script variations
    if func_name.contains("bip") {
        let bip_upper = func_name.replace("bip", "BIP").replace("_", "");
        variations.push(bip_upper);
        let bip_pascal = rust_to_pascal_case(func_name).replace("Bip", "BIP");
        variations.push(bip_pascal);
    }

    // Remove "With" suffixes
    if func_name.contains("_with_") {
        let without_with: Vec<&str> = func_name.split("_with_").collect();
        if !without_with.is_empty() {
            variations.push(rust_to_pascal_case(without_with[0]));
        }
    }

    variations
}

/// Process #[spec_locked] attribute
pub fn process_spec_locked(
    args: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    use syn::{ItemFn, parse_macro_input};

    // Parse so attribute placement / trailing attrs stay attached to the item.
    let func = parse_macro_input!(input as ItemFn);
    let _args = parse_macro_input!(args as SpecLockedArgs);

    // Compile-time pass-through: do not synthesize #[requires]/#[ensures] from Orange
    // Paper. Generated ensures from prose (EvalScript §5.2) escaped attribute brackets
    // via newline-bearing `//` comment TokenStream parses → "expected item after
    // attributes" on rustc 1.88 / edition 2024. Per-attribute Orange Paper parse was
    // also too slow for cargo check/test. `cargo-spec-lock verify` still reads source
    // #[spec_locked] markers. Runtime consensus is unchanged.
    proc_macro::TokenStream::from(quote! { #func })
}

/// Translate mathematical notation from Orange Paper to Rust contract syntax
///
/// Converts LaTeX math expressions like:
/// - `$\text{GetBlockSubsidy}(h) \geq 0$` → `*result >= 0`
/// - `$h = 0 \implies \text{GetBlockSubsidy}(h) = 50 \times C$` → `*height == 0 ==> *result == INITIAL_SUBSIDY`
fn translate_math_to_rust_contract(
    math_expr: &str,
    func_name: &str,
    func: &syn::ItemFn,
) -> TokenStream {
    let mut translated = math_expr.to_string();

    // Get parameter names from function signature
    let param_names: Vec<String> = func
        .sig
        .inputs
        .iter()
        .filter_map(|input| {
            if let syn::FnArg::Typed(pat) = input {
                if let syn::Pat::Ident(ident) = &*pat.pat {
                    Some(ident.ident.to_string())
                } else {
                    None
                }
            } else {
                None
            }
        })
        .collect();

    // Translate LaTeX operators to Rust contract syntax
    translated = translated.replace(r"\geq", ">=");
    translated = translated.replace(r"\leq", "<=");
    translated = translated.replace(r"\implies", "==>");
    translated = translated.replace(r"\iff", "==");
    translated = translated.replace(r"\land", "&&");
    translated = translated.replace(r"\lor", "||");
    translated = translated.replace(r"\times", "*");
    translated = translated.replace(r"\text{", "");
    translated = translated.replace("}", "");

    // Replace function calls with *result
    // Pattern: FunctionName(args) → *result
    // BUT: Skip this for tuple return types (they don't support dereferencing)
    let func_name_pattern = Regex::new(&format!(r"\b{}", regex::escape(func_name))).unwrap();
    // Check if function returns a tuple - if so, don't replace with *result
    let returns_tuple = if let syn::ReturnType::Type(_, return_type) = &func.sig.output {
        match return_type.as_ref() {
            syn::Type::Tuple(_) => true,
            syn::Type::Path(type_path) => {
                if let Some(segment) = type_path.path.segments.last() {
                    if segment.ident == "Result" {
                        if let syn::PathArguments::AngleBracketed(args) = &segment.arguments {
                            if let Some(syn::GenericArgument::Type(inner_type)) = args.args.first()
                            {
                                matches!(inner_type, syn::Type::Tuple(_))
                            } else {
                                false
                            }
                        } else {
                            false
                        }
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
            _ => false,
        }
    } else {
        false
    };

    if !returns_tuple {
        translated = func_name_pattern
            .replace_all(&translated, "*result")
            .to_string();
    } else {
        // For tuple return types, replace with match expression instead
        translated = func_name_pattern
            .replace_all(
                &translated,
                "match result { Ok(_) => true, Err(_) => true }",
            )
            .to_string();
    }

    // Replace common variable names with parameter names + *
    // Common patterns: h → *height, tx → *tx, etc.
    if param_names.len() == 1 {
        let param_name = &param_names[0];
        // Simple heuristic: if math uses single letter, map to first parameter
        translated = translated.replace("h", &format!("*{param_name}"));
    } else {
        // Multi-parameter: try to match common patterns
        translated = translated.replace("h", "*height");
        translated = translated.replace("tx", "*tx");
        translated = translated.replace("us", "*utxo_set");
    }

    // Replace mathematical constants
    translated = translated.replace("50 \\times C", "INITIAL_SUBSIDY");
    translated = translated.replace("25 \\times C", "INITIAL_SUBSIDY / 2");
    translated = translated.replace("12.5 \\times C", "INITIAL_SUBSIDY / 4");
    translated = translated.replace("MAX\\_MONEY", "MAX_MONEY");
    translated = translated.replace("H", "HALVING_INTERVAL");

    // Replace set notation
    translated = translated.replace(r"\mathbb{N}", "Natural");
    translated = translated.replace(r"\mathbb{Z}", "Integer");

    // Replace array/list access notation
    translated = translated.replace(r"\[", "[");
    translated = translated.replace(r"\]", "]");

    // Replace cardinality notation |x| with .len()
    let cardinality_pattern = Regex::new(r"\|([^|]+)\|").unwrap();
    translated = cardinality_pattern
        .replace_all(&translated, "$1.len()")
        .to_string();

    // Replace superscript notation (e.g., 0^{32} → [0u8; 32])
    translated = translated.replace("0^{32}", "[0u8; 32]");
    translated = translated.replace("2^{32} - 1", "0xffffffff");

    // Clean up: remove $ delimiters
    translated = translated.replace("$", "");

    // Replace @ syntax with * for result dereference
    translated = translated.replace("@", "*");

    // Replace seq@.len() with seq.len() (direct access for slices/vecs)
    let seq_len_pattern = Regex::new(r"(\w+)@\.len\(\)").unwrap();
    translated = seq_len_pattern
        .replace_all(&translated, "$1.len()")
        .to_string();

    // Replace old(value@) with old(*value) in postconditions
    let old_pattern = Regex::new(r"old\((\w+)@\)").unwrap();
    translated = old_pattern.replace_all(&translated, "old(*$1)").to_string();

    // Try to parse as valid Rust contract expression
    translated.parse().unwrap_or_else(|_| {
        // If parsing fails, create a comment with the original math
        quote! { /* Math translation failed: #math_expr -> #translated */ }
    })
}
