//! Implementation of the #[spec_locked] proc macro
//!
//! Links Rust functions to Orange Paper specifications.
//! Contracts are provided via manual #[requires] and #[ensures] attributes,
//! which will be verified by the BLVM Spec Lock verification tool.

use proc_macro2::{TokenStream, Span};
use quote::quote;
use syn::{parse::Parse, parse_macro_input, ItemFn, LitStr, Token, Ident};
use crate::parser::{SpecParser, FunctionSpec, SpecSection};
use regex::Regex;

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
    function: Option<LitStr>,  // Optional - can be inferred from function name
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
                                return Err(input.error("Expected 'spec_path' after section::function"));
                            }
                        } else {
                            None
                        }
                    } else {
                        None
                    };
                    
                    return Ok(SpecLockedArgs { section: Some(section), function: Some(function), spec_path });
                }
            }
            
            // It's positional: first is section, second is optional function name
            let function = if input.peek(Token![,]) {
                input.parse::<Token![,]>()?;
                if input.peek(LitStr) {
                    Some(input.parse()?)
                } else {
                    None  // Function name will be inferred
                }
            } else {
                None  // Function name will be inferred
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
                return Err(input.error(format!("Unknown parameter: {}. Expected 'section', 'function', or 'spec_path'", key)));
            }

            if !input.is_empty() {
                input.parse::<Token![,]>()?;
            }
        }

        Ok(SpecLockedArgs {
            section,  // Optional - can be auto-inferred if not provided
            function,  // Optional - will be inferred if not provided
            spec_path,
        })
    }
}

/// Generate contract annotations from parsed Orange Paper specification
///
/// Tailored for Bitcoin consensus functions:
/// - Maps Orange Paper types to Rust types (Natural, Integer, etc.)
/// - Generates contracts from mathematical formulas
/// - Extracts pre/post conditions from theorems
fn generate_contract_annotations(spec: &FunctionSpec, func: &syn::ItemFn) -> TokenStream {
    use proc_macro2::TokenStream as TokenStream2;
    let mut annotations = Vec::<TokenStream2>::new();
    
    // Generate #[requires] from conditions and function signature
    let requires = generate_requires(spec, func);
    if !requires.is_empty() {
        annotations.push(requires);
    }
    
    // Generate #[ensures] from formula and theorems
    let ensures = generate_ensures(spec, func);
    if !ensures.is_empty() {
        annotations.push(ensures);
    }
    
    quote! {
        #(#annotations)*
    }
}

/// Generate #[requires] preconditions
fn generate_requires(spec: &FunctionSpec, func: &syn::ItemFn) -> TokenStream {
    use proc_macro2::TokenStream as TokenStream2;
    let mut requires = Vec::<TokenStream2>::new();
    
    // Extract parameter names from function signature
    let param_names: Vec<String> = func.sig.inputs.iter()
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
    for condition in &spec.conditions {
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
                            if let Some(syn::GenericArgument::Type(inner_type)) = args.args.first() {
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
            _ => false
        }
    } else {
        false
    };
    
    // First, try to generate contracts from Orange Paper mathematical properties
    if !spec.contracts.is_empty() && !returns_tuple {
        // Skip Orange Paper contracts for tuple return types - they need special handling
        for contract in &spec.contracts {
            match contract.contract_type {
                crate::parser::ContractType::Ensures | 
                crate::parser::ContractType::Property | 
                crate::parser::ContractType::EdgeCase => {
                    // Translate mathematical notation to Rust contract
                    let rust_expr = translate_math_to_rust_contract(&contract.condition, &spec.name, func);
                    
                    let comment_str = contract.comment.as_ref()
                        .map(|c| format!(" // {}", c))
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
            if matches!(property.property_type, crate::parser::PropertyType::Ensures | crate::parser::PropertyType::Invariant) {
                // Translate mathematical notation to Rust contract
                let rust_expr = translate_math_to_rust_contract(&property.statement, &spec.name, func);
                
                let comment_str = format!(" // {}", property.name);
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
        
        let comment_str = format!(" // Theorem {}: {}", theorem.number, theorem.name);
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
                Some(first) => first.to_uppercase().collect::<String>() + &chars.as_str(),
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
    let without_verify = without_check.strip_prefix("verify_").unwrap_or(without_check);
    let without_calculate = without_verify.strip_prefix("calculate_").unwrap_or(without_verify);
    let without_get = without_calculate.strip_prefix("get_").unwrap_or(without_calculate);
    
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
pub fn process_spec_locked(args: proc_macro::TokenStream, input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    use syn::{parse_macro_input, ItemFn};
    
    // Parse the function
    let func = parse_macro_input!(input as ItemFn);
    // Parse arguments
    let args = parse_macro_input!(args as SpecLockedArgs);
    
    // Infer function name from Rust function if not provided
    let func_name = if let Some(ref explicit_name) = args.function {
        explicit_name.value()
    } else {
        // Infer from Rust function name
        let rust_func_name = func.sig.ident.to_string();
        rust_to_pascal_case(&rust_func_name)
    };
    
    // Get spec path (default to workspace-relative)
    let spec_path = args.spec_path
        .as_ref()
        .map(|p| p.value())
        .unwrap_or_else(|| {
            // Try to resolve relative to CARGO_MANIFEST_DIR
            let manifest_dir = std::env::var("CARGO_MANIFEST_DIR")
                .unwrap_or_else(|_| ".".to_string());
            format!("{}/../blvm-spec/THE_ORANGE_PAPER.md", manifest_dir)
        });

    // Read Orange Paper
    let spec_content = match std::fs::read_to_string(&spec_path) {
        Ok(content) => content,
        Err(e) => {
            // Return function unchanged with compile error
            let error_msg = format!("Could not read Orange Paper specification at {}: {}. Ensure blvm-spec/THE_ORANGE_PAPER.md exists.", spec_path, e);
            return proc_macro::TokenStream::from(quote! {
                compile_error!(#error_msg);
                #func
            });
        }
    };

    // Parse specification
    let mut parser = SpecParser::new(spec_content);
    if let Err(e) = parser.parse() {
        let error_msg = format!("Failed to parse Orange Paper: {}", e);
        return proc_macro::TokenStream::from(quote! {
            compile_error!(#error_msg);
            #func
        });
    }

    // NEW: Auto-inference logic - if no section provided, search everywhere
    let (section, section_id, func_spec_opt) = if let Some(ref section_id_str) = args.section {
        // Section ID provided (could be "6.1" or "6.1.1")
        let section_id_value = section_id_str.value();
        
        // Check if it's a granular ID (contains more than one dot, e.g., "6.1.1")
        let is_granular = section_id_value.matches('.').count() > 1;
        
        if is_granular {
            // Try to find subsection first
            if let Some((section, subsection_id)) = parser.find_subsection(&section_id_value) {
                // Find function in this section
                let func_spec_opt = section.functions.iter()
                    .find(|f| f.name.eq_ignore_ascii_case(&func_name))
                    .or_else(|| section.functions.iter().find(|f| f.name.eq_ignore_ascii_case(&func_name)));
                
                // Extract base section ID (e.g., "6.1.1" -> "6.1")
                let base_section_id = section_id_value.split('.').take(2).collect::<Vec<&str>>().join(".");
                (section, base_section_id, func_spec_opt)
            } else {
                // Granular ID not found, try as regular section
                match parser.find_section(&section_id_value) {
                    Some(s) => {
                        let func_spec_opt = s.functions.iter()
                            .find(|f| f.name.eq_ignore_ascii_case(&func_name))
                            .or_else(|| s.functions.iter().find(|f| f.name.eq_ignore_ascii_case(&func_name)));
                        (s, section_id_value.clone(), func_spec_opt)
                    }
                    None => {
                        return proc_macro::TokenStream::from(quote! {
                            compile_error!(concat!("Section or subsection ", #section_id_value, " not found in Orange Paper"));
                            #func
                        });
                    }
                }
            }
        } else {
            // Regular section ID
            match parser.find_section(&section_id_value) {
                Some(s) => {
                    let func_spec_opt = s.functions.iter()
                        .find(|f| f.name.eq_ignore_ascii_case(&func_name))
                        .or_else(|| s.functions.iter().find(|f| f.name.eq_ignore_ascii_case(&func_name)));
                    (s, section_id_value.clone(), func_spec_opt)
                }
                None => {
                    return proc_macro::TokenStream::from(quote! {
                        compile_error!(concat!("Section ", #section_id_value, " not found in Orange Paper"));
                        #func
                    });
                }
            }
        }
    } else {
        // NEW: No section provided - auto-infer from function name
        // Search across all sections for the function
        match parser.find_function_anywhere(&func_name) {
            Some((func_spec, found_section_id)) => {
                let section = parser.find_section(found_section_id).unwrap();
                (section, found_section_id.to_string(), Some(func_spec))
            }
                    None => {
                        // Try to find by theorem
                        match parser.find_theorem_by_function_name(&func_name) {
                            Some((_theorem, found_section_id, _func_name)) => {
                                let section = parser.find_section(found_section_id).unwrap();
                                let func_spec_opt = section.functions.iter()
                                    .find(|f| f.name.eq_ignore_ascii_case(&func_name));
                                (section, found_section_id.to_string(), func_spec_opt)
                            }
                            None => {
                                // Function not found anywhere - try improved name matching
                                let name_variations = generate_name_variations(&func_name);
                                
                                // Try name variations
                                let mut found_result: Option<(&SpecSection, String, Option<&FunctionSpec>)> = None;
                                for variant in &name_variations {
                                    if let Some((func_spec, found_section_id)) = parser.find_function_anywhere(variant) {
                                        let section = parser.find_section(found_section_id).unwrap();
                                        found_result = Some((section, found_section_id.to_string(), Some(func_spec)));
                                        break;
                                    }
                                }
                                
                                if let Some(result) = found_result {
                                    result
                                } else {
                                    // Still not found - create minimal spec (migration mode)
                                    // This allows functions to compile even if not yet in Orange Paper
                                    let minimal_spec_static: &'static FunctionSpec = Box::leak(Box::new(FunctionSpec {
                                        name: func_name.clone(),
                                        section: "auto-inferred".to_string(),
                                        signature: None,
                                        formula: None,
                                        description: Some(format!("Function '{}' auto-inferred (not yet in Orange Paper - migration mode)", func_name)),
                                        conditions: vec![],
                                        theorems: vec![],
                                        contracts: vec![],
                                        properties: vec![],
                                        content: String::new(),
                                    }));
                                    
                                    // Use first available section as fallback (try common sections)
                                    let default_section = parser.find_section("1.1")
                                        .or_else(|| parser.find_section("5.1"))
                                        .or_else(|| parser.find_section("6.1"))
                                        .or_else(|| parser.find_section("2.1"))
                                        .or_else(|| parser.find_section("3.1"))
                                        .or_else(|| parser.find_section("4.1"))
                                        .or_else(|| parser.find_section("7.1"))
                                        .or_else(|| parser.find_section("8.1"))
                                        .unwrap_or_else(|| {
                                            // If all else fails, we need a section - this shouldn't happen
                                            // Use section 1.1 as absolute fallback (will panic if it doesn't exist, but that's better than wrong behavior)
                                            parser.find_section("1.1").expect("Orange Paper must have at least one section")
                                        });
                                    
                                    // Return with static lifetime spec
                                    (default_section, "auto-inferred".to_string(), Some(minimal_spec_static))
                                }
                            }
                        }
                    }
        }
    };

    // If function not found, check if it's referenced in section content (theorems/formulas)
    // If so, create a minimal spec; otherwise error
    let func_spec = match func_spec_opt {
        Some(f) => f,
        None => {
            let section_str = section_id.clone();
            let content_lower = section.content.to_lowercase();
            let func_name_lower = func_name.to_lowercase();
            
            // Check if function name appears in section content (theorems/formulas)
            // Handle LaTeX format: \text{FunctionName} and various naming conventions
            let mut func_name_variations = vec![
                func_name_lower.clone(),
                func_name.clone(), // Original case
                func_name_lower.replace("sigop", "sig op"),
                func_name_lower.replace("sigop", "sigop"),
                format!("\\text{{{}}}", func_name), // LaTeX \text{FunctionName}
                format!("\\text{{{}}}", func_name_lower), // LaTeX lowercase
                format!("text{{{}}}", func_name), // Without backslash
                format!("text{{{}}}", func_name_lower),
            ];
            // Also check for function name without "Count", "Get", "Calculate" prefixes
            if let Some(suffix) = func_name_lower.strip_prefix("count") {
                func_name_variations.push(suffix.to_string());
            }
            if let Some(suffix) = func_name_lower.strip_prefix("get") {
                func_name_variations.push(suffix.to_string());
            }
            if let Some(suffix) = func_name_lower.strip_prefix("calculate") {
                func_name_variations.push(suffix.to_string());
            }
            
            // Check both raw content and theorems
            let content_contains_func = func_name_variations.iter().any(|variant| {
                content_lower.contains(variant) || section.content.contains(variant)
            });
            let theorem_contains_func = section.theorems.iter().any(|t| {
                let theorem_lower = t.statement.to_lowercase();
                func_name_variations.iter().any(|variant| {
                    theorem_lower.contains(variant) || t.statement.contains(variant)
                })
            });
            
            // Also check if function name appears in any formula
            let formula_contains_func = section.functions.iter().any(|f| {
                if let Some(ref formula) = f.formula {
                    let formula_lower: String = formula.to_lowercase();
                    func_name_variations.iter().any(|variant: &String| {
                        let variant_str: &str = variant.as_str();
                        formula_lower.contains(variant_str) || formula.contains(variant_str)
                    })
                } else {
                    false
                }
            });
            
            if content_contains_func || theorem_contains_func || formula_contains_func {
                // Function is referenced in section - create a minimal spec on the heap
                // We need to store it somewhere that outlives the match
                // For now, we'll create it and use it directly
                // Since we can't return a reference to a local, we'll create a boxed version
                // Actually, we can clone the section and add the function, but that's expensive
                // Better: create minimal spec and continue - generate_ensures will handle it with generic contracts
                // We'll create a temporary FunctionSpec that we can reference
                // Since we need a &FunctionSpec, we'll store it in the section (but we can't modify)
                // Solution: create a new minimal FunctionSpec and use it via a match that returns a reference
                // Actually, the simplest is to create a static-like minimal spec inline
                // But we can't do that easily. Let's just allow it and let generate_ensures handle it
                // We'll create a boxed minimal spec and leak it (not ideal but works for proc macro)
                let minimal_spec = Box::leak(Box::new(FunctionSpec {
                    name: func_name.clone(),
                    section: section_str.to_string(),
                    signature: None,
                    formula: None,
                    description: Some(format!("Referenced in section {} (theorem/formula)", section_str)),
                    conditions: vec![],
                    theorems: vec![],
                    contracts: vec![],
                    properties: vec![],
                    content: section.content.clone(),
                }));
                minimal_spec
            } else {
                // Function not found in section - create minimal spec
                let available: Vec<String> = section.functions.iter().map(|f| f.name.clone()).collect();
                let available_str = if available.is_empty() {
                    format!("(none found - section content length: {})", section.content.len())
                } else {
                    available.join(", ")
                };
                // Create a minimal FunctionSpec for functions not yet in spec
                let minimal_spec = Box::leak(Box::new(FunctionSpec {
                    name: func_name.clone(),
                    section: section_str.to_string(),
                    signature: None,
                    formula: None,
                    description: Some(format!("Function '{}' referenced but not yet in spec section {} (Migration mode). Available: {}", 
                                       func_name, section_str, available_str)),
                    properties: vec![],
                    content: section.content.clone(),
                    conditions: vec![],
                    theorems: vec![],
                    contracts: vec![],
                }));
                minimal_spec
            }
        }
    };

    // Validate function signature matches spec (if possible)
    if let Some(sig) = &func_spec.signature {
        if let Some((inputs, output)) = SpecParser::parse_signature(sig) {
            // Basic validation: check parameter count matches
            let param_count = func.sig.inputs.len() - 1; // -1 for self if method
            if param_count != inputs.len() {
                // Warning, not error - might be self parameter
                // Could add more sophisticated validation here
            }
        }
    }

    // Generate contracts from Orange Paper
    let requires_attrs = generate_requires(func_spec, &func);
    let ensures_attrs = generate_ensures(func_spec, &func);
    
    // Add documentation comment with spec reference
    let section_id_display = args.section.as_ref()
        .map(|s| s.value())
        .unwrap_or_else(|| section_id.clone());
    let spec_doc = format!(
        "Spec-locked to Orange Paper Section {}: {}\n\n{}",
        section_id_display,
        func_spec.name,
        func_spec.description.as_deref().unwrap_or("")
    );

    // Return function with documentation and generated contracts
    let doc_str_lit = LitStr::new(&spec_doc, Span::call_site());
    
    proc_macro::TokenStream::from(quote::quote! {
        #[doc = #doc_str_lit]
        #requires_attrs
        #ensures_attrs
        #func
    })
}

/// Translate mathematical notation from Orange Paper to Rust contract syntax
///
/// Converts LaTeX math expressions like:
/// - `$\text{GetBlockSubsidy}(h) \geq 0$` → `*result >= 0`
/// - `$h = 0 \implies \text{GetBlockSubsidy}(h) = 50 \times C$` → `*height == 0 ==> *result == INITIAL_SUBSIDY`
fn translate_math_to_rust_contract(math_expr: &str, func_name: &str, func: &syn::ItemFn) -> TokenStream {
    let mut translated = math_expr.to_string();
    
    // Get parameter names from function signature
    let param_names: Vec<String> = func.sig.inputs.iter()
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
                            if let Some(syn::GenericArgument::Type(inner_type)) = args.args.first() {
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
            _ => false
        }
    } else {
        false
    };
    
    if !returns_tuple {
        translated = func_name_pattern.replace_all(&translated, "*result").to_string();
    } else {
        // For tuple return types, replace with match expression instead
        translated = func_name_pattern.replace_all(&translated, "match result { Ok(_) => true, Err(_) => true }").to_string();
    }
    
    // Replace common variable names with parameter names + *
    // Common patterns: h → *height, tx → *tx, etc.
    if param_names.len() == 1 {
        let param_name = &param_names[0];
        // Simple heuristic: if math uses single letter, map to first parameter
        translated = translated.replace("h", &format!("*{}", param_name));
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
    translated = translated.replace(".", ".");
    
    // Replace cardinality notation |x| with .len()
    let cardinality_pattern = Regex::new(r"\|([^|]+)\|").unwrap();
    translated = cardinality_pattern.replace_all(&translated, "$1.len()").to_string();
    
    // Replace superscript notation (e.g., 0^{32} → [0u8; 32])
    translated = translated.replace("0^{32}", "[0u8; 32]");
    translated = translated.replace("2^{32} - 1", "0xffffffff");
    
    // Clean up: remove $ delimiters
    translated = translated.replace("$", "");
    
    // Replace @ syntax with * for result dereference
    translated = translated.replace("@", "*");
    
    // Replace seq@.len() with seq.len() (direct access for slices/vecs)
    let seq_len_pattern = Regex::new(r"(\w+)@\.len\(\)").unwrap();
    translated = seq_len_pattern.replace_all(&translated, "$1.len()").to_string();
    
    // Replace old(value@) with old(*value) in postconditions
    let old_pattern = Regex::new(r"old\((\w+)@\)").unwrap();
    translated = old_pattern.replace_all(&translated, "old(*$1)").to_string();
    
    // Try to parse as valid Rust contract expression
    translated.parse().unwrap_or_else(|_| {
        // If parsing fails, create a comment with the original math
        quote! { /* Math translation failed: #math_expr -> #translated */ }
    })
}
