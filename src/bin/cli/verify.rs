//! Verification orchestration
//!
//! Discovers functions, extracts contracts, and runs verification

use std::path::PathBuf;
use walkdir::WalkDir;
use syn::{File, ItemFn, Attribute};
use quote::quote;

/// Simplified contract structure for CLI
#[derive(Debug, Clone)]
pub struct Contract {
    pub contract_type: ContractType,
    pub condition: String,
    pub expr: Option<syn::Expr>, // Parsed expression for static checker
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ContractType {
    Requires,
    Ensures,
}

/// Extract contracts from a function
fn extract_contracts(func: &ItemFn) -> Vec<Contract> {
    let mut contracts = Vec::new();
    
    for attr in &func.attrs {
        let path = attr.path();
        
        // Check for #[requires(...)] or #[ensures(...)]
        let is_requires = path.is_ident("requires") ||
            (path.segments.len() == 2 &&
             path.segments[0].ident == "blvm_spec_lock" &&
             path.segments[1].ident == "requires");
        
        let is_ensures = path.is_ident("ensures") ||
            (path.segments.len() == 2 &&
             path.segments[0].ident == "blvm_spec_lock" &&
             path.segments[1].ident == "ensures");
        
        if is_requires || is_ensures {
            // Parse the condition expression from the attribute
            // The attribute format is: #[requires(condition)] or #[ensures(condition)]
            if let Ok(expr) = attr.parse_args::<syn::Expr>() {
                // Convert expression to string for storage
                let condition_str = quote::quote!(#expr).to_string();
                
                contracts.push(Contract {
                    contract_type: if is_requires {
                        ContractType::Requires
                    } else {
                        ContractType::Ensures
                    },
                    condition: condition_str,
                    expr: Some(expr), // Store parsed expression for static checker
                });
            } else {
                // If parsing fails, store as string only
                let condition_str = quote::quote!(#attr).to_string();
                contracts.push(Contract {
                    contract_type: if is_requires {
                        ContractType::Requires
                    } else {
                        ContractType::Ensures
                    },
                    condition: condition_str,
                    expr: None,
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
    pub function_sig: Option<syn::ItemFn>, // Store function signature for type inference
}

/// Discover all functions with #[spec_locked] attributes
pub fn discover_functions(workspace_root: &PathBuf) -> Result<Vec<FunctionToVerify>, String> {
    let mut functions = Vec::new();
    let mut errors = Vec::new();
    
    // Walk through Rust source files
    for entry in WalkDir::new(workspace_root)
        .into_iter()
        .filter_entry(|e| {
            let path = e.path();
            // Skip target directory and other build artifacts
            !path.to_string_lossy().contains("/target/") &&
            !path.to_string_lossy().contains("/.git/") &&
            !path.to_string_lossy().contains("/.cargo/")
        })
        .filter_map(|e| e.ok())
    {
        let path = entry.path();
        
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
        Err(format!("Failed to discover functions:\n{}", errors.join("\n")))
    }
}

/// Parse a Rust file for functions with #[spec_locked]
fn parse_file_for_functions(file_path: &std::path::Path) -> Result<Vec<FunctionToVerify>, String> {
    let content = std::fs::read_to_string(file_path)
        .map_err(|e| format!("Failed to read {}: {}", file_path.display(), e))?;
    
    let ast: File = syn::parse_file(&content)
        .map_err(|e| format!("Failed to parse {}: {}", file_path.display(), e))?;
    
    let mut functions = Vec::new();
    
    // Find all functions
    for item in ast.items {
        if let syn::Item::Fn(func) = item {
            // Check if function has #[spec_locked] attribute
            if has_spec_locked(&func.attrs) {
                let contracts = extract_contracts(&func);
                let section = extract_section(&func.attrs);
                
                functions.push(FunctionToVerify {
                    file_path: file_path.to_path_buf(),
                    function_name: func.sig.ident.to_string(),
                    contracts,
                    section,
                    function_sig: Some(func.clone()),
                });
            }
        }
    }
    
    Ok(functions)
}

/// Check if function has #[spec_locked] attribute
fn has_spec_locked(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|attr| {
        let path = attr.path();
        path.is_ident("spec_locked") ||
        (path.segments.len() == 2 &&
         path.segments[0].ident == "blvm_spec_lock" &&
         path.segments[1].ident == "spec_locked")
    })
}

/// Extract Orange Paper section from #[spec_locked] attribute
fn extract_section(attrs: &[Attribute]) -> Option<String> {
    for attr in attrs {
        let path = attr.path();
        let is_spec_locked = path.is_ident("spec_locked") ||
            (path.segments.len() == 2 &&
             path.segments[0].ident == "blvm_spec_lock" &&
             path.segments[1].ident == "spec_locked");
        
        if is_spec_locked {
            // Try to parse the section from the attribute tokens
            // The attribute format is: #[spec_locked("6.1")] or #[spec_locked("6.1", "FunctionName")]
            let tokens = quote::quote!(#attr).to_string();
            
            // Simple regex-like extraction: look for quoted strings
            // This is a simplified parser - full implementation would use syn::parse
            if let Some(start) = tokens.find('"') {
                if let Some(end) = tokens[start+1..].find('"') {
                    let section = &tokens[start+1..start+1+end];
                    // Check if it looks like a section number (e.g., "6.1", "5.2.3")
                    if section.chars().any(|c| c.is_ascii_digit()) {
                        return Some(section.to_string());
                    }
                }
            }
        }
    }
    None
}

/// Verify a single function
pub fn verify_function(function: &FunctionToVerify) -> VerificationResult {
    if function.contracts.is_empty() {
        // No contracts to verify - this is valid (function might only have #[spec_locked])
        return VerificationResult::Passed;
    }
    
    // Verification flow:
    // 1. Try static checks first (fast, no Z3 needed)
    // 2. If static checks can't verify, use Z3 (if available)
    // 3. Return appropriate result
    
    let mut verified_count = 0;
    let mut failed_contracts = Vec::new();
    let mut requires_z3_count = 0;
    
    // Separate requires and ensures contracts
    let requires_contracts: Vec<_> = function.contracts.iter()
        .filter(|c| c.contract_type == ContractType::Requires)
        .collect();
    let ensures_contracts: Vec<_> = function.contracts.iter()
        .filter(|c| c.contract_type == ContractType::Ensures)
        .collect();
    
    // Verify requires contracts first
    for contract in &requires_contracts {
        // Basic validation: check if contract condition is non-empty
        if contract.condition.trim().is_empty() {
            failed_contracts.push((
                format!("{:?}", contract.contract_type),
                "Empty contract condition".to_string(),
            ));
            continue;
        }
        
        // Try static checking if we have a parsed expression
        if let Some(ref expr) = contract.expr {
            match check_contract_statically(expr, contract.contract_type) {
                StaticCheck::Passed => {
                    verified_count += 1;
                }
                StaticCheck::Failed(reason) => {
                    failed_contracts.push((
                        format!("{:?}", contract.contract_type),
                        reason,
                    ));
                }
                StaticCheck::RequiresZ3 => {
                    requires_z3_count += 1;
                    // Try Z3 if available
                    #[cfg(feature = "z3")]
                    {
                        if let Err(e) = verify_with_z3(contract, function.function_sig.as_ref(), &[]) {
                            failed_contracts.push((
                                format!("{:?}", contract.contract_type),
                                format!("Z3 verification failed: {}", e),
                            ));
                        } else {
                            verified_count += 1;
                        }
                    }
                    #[cfg(not(feature = "z3"))]
                    {
                        // Z3 not available - cannot verify complex contracts
                        // For now, we'll mark as requiring Z3 but not fail
                        // This allows the tool to run without Z3 and report what needs verification
                        // In production, you'd want to fail here or have a flag to allow partial verification
                        requires_z3_count += 1;
                        // Don't add to failed_contracts - mark as partial verification needed
                    }
                }
            }
        } else {
            // No parsed expression - can't do static check
            // Mark as requiring Z3 or manual verification
            requires_z3_count += 1;
            // Don't count as verified - we can't verify without a parsed expression
            failed_contracts.push((
                format!("{:?}", contract.contract_type),
                "Cannot verify: contract condition could not be parsed as expression".to_string(),
            ));
        }
    }
    
    // Early return if requires contracts failed
    if !failed_contracts.is_empty() {
        let (contract_type, reason) = &failed_contracts[0];
        return VerificationResult::Failed {
            contract: contract_type.clone(),
            reason: format!("{} ({} total failures)", reason, failed_contracts.len()),
        };
    }
    
    // Now verify ensures contracts with the requires as context
    // This is the KEY to Orange Paper verification:
    // We prove: requires && implementation => ensures
    for contract in &ensures_contracts {
        if contract.condition.trim().is_empty() {
            failed_contracts.push((
                format!("{:?}", contract.contract_type),
                "Empty contract condition".to_string(),
            ));
            continue;
        }
        
        if let Some(ref expr) = contract.expr {
            match check_contract_statically(expr, contract.contract_type) {
                StaticCheck::Passed => {
                    verified_count += 1;
                }
                StaticCheck::Failed(reason) => {
                    failed_contracts.push((
                        format!("{:?}", contract.contract_type),
                        reason,
                    ));
                }
                StaticCheck::RequiresZ3 => {
                    requires_z3_count += 1;
                    #[cfg(feature = "z3")]
                    {
                        // For ensures, pass the requires contracts as context
                        // This allows verifier to prove: requires && impl => ensures
                        if let Err(e) = verify_with_z3(contract, function.function_sig.as_ref(), &requires_contracts) {
                            failed_contracts.push((
                                format!("{:?}", contract.contract_type),
                                format!("Z3: {}", e),
                            ));
                        } else {
                            verified_count += 1;
                        }
                    }
                    #[cfg(not(feature = "z3"))]
                    {
                        requires_z3_count += 1;
                    }
                }
            }
        } else {
            requires_z3_count += 1;
            failed_contracts.push((
                format!("{:?}", contract.contract_type),
                "Cannot verify: contract condition could not be parsed".to_string(),
            ));
        }
    }
    
    // Report results
    if !failed_contracts.is_empty() {
        let (contract_type, reason) = &failed_contracts[0];
        return VerificationResult::Failed {
            contract: contract_type.clone(),
            reason: format!("{} ({} total failures)", reason, failed_contracts.len()),
        };
    }
    
    if verified_count == function.contracts.len() {
        VerificationResult::Passed
    } else if requires_z3_count > 0 {
        VerificationResult::Partial {
            verified: verified_count,
            total: function.contracts.len(),
        }
    } else {
        VerificationResult::Passed
    }
}

/// Result of static checking
enum StaticCheck {
    Passed,
    Failed(String),
    RequiresZ3,
}

/// Check a contract statically (simplified version for CLI)
fn check_contract_statically(expr: &syn::Expr, contract_type: ContractType) -> StaticCheck {
    // Simple pattern matching for common cases
    match expr {
        // Non-negative checks: x >= 0 or 0 <= x
        syn::Expr::Binary(bin) if matches!(bin.op, syn::BinOp::Ge(_)) => {
            if is_zero_literal(&bin.right) || is_zero_literal(&bin.left) {
                // x >= 0 or 0 <= x - this is a valid check pattern
                // Can't verify statically without type info, but syntax is valid
                return StaticCheck::RequiresZ3;
            }
        }
        // Equality checks: x == CONSTANT
        syn::Expr::Binary(bin) if matches!(bin.op, syn::BinOp::Eq(_)) => {
            if is_literal(&bin.left) || is_literal(&bin.right) {
                // Constant equality - requires Z3 for actual verification
                return StaticCheck::RequiresZ3;
            }
        }
        // Comparison checks: x < y, x > y, etc.
        syn::Expr::Binary(bin) if matches!(
            bin.op,
            syn::BinOp::Lt(_) | syn::BinOp::Le(_) | syn::BinOp::Gt(_) | syn::BinOp::Ge(_)
        ) => {
            // Comparison - requires Z3
            return StaticCheck::RequiresZ3;
        }
        // Boolean operations: x && y, x || y
        syn::Expr::Binary(bin) if matches!(bin.op, syn::BinOp::And(_) | syn::BinOp::Or(_)) => {
            // Boolean logic - requires Z3
            return StaticCheck::RequiresZ3;
        }
        _ => {
            // Unknown pattern - requires Z3
            return StaticCheck::RequiresZ3;
        }
    }
    
    StaticCheck::RequiresZ3
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

/// Verify contract with Z3 (if feature enabled)
#[cfg(feature = "z3")]
fn verify_with_z3(contract: &Contract, func_sig: Option<&syn::ItemFn>, requires_contracts: &[&Contract]) -> Result<(), String> {
    use crate::parser::contracts::{Contract as LibraryContract, ContractType as LibraryContractType};
    use crate::translator::z3_verifier::{Z3Verifier, VerificationResult};
    
    // Convert CLI Contract to library Contract
    let expr = contract.expr.as_ref().ok_or_else(|| {
        "Cannot verify: missing parsed expression".to_string()
    })?;
    
    let library_contract = LibraryContract {
        contract_type: match contract.contract_type {
            ContractType::Requires => LibraryContractType::Requires,
            ContractType::Ensures => LibraryContractType::Ensures,
        },
        condition: expr.clone(),
        comment: None,
    };
    
    // Use Z3 verifier with function signature and requires contracts for context
    let mut verifier = Z3Verifier::new();
    
    // Convert requires contracts to library format
    let requires_library: Vec<_> = requires_contracts.iter()
        .filter_map(|c| {
            c.expr.as_ref().map(|expr| {
                LibraryContract {
                    contract_type: LibraryContractType::Requires,
                    condition: expr.clone(),
                    comment: None,
                }
            })
        })
        .collect();
    
    match verifier.verify_contract_with_context(&library_contract, func_sig, &requires_library) {
        VerificationResult::Verified => {
            Ok(())
        }
        VerificationResult::Failed { counterexample } => {
            let msg = if let Some(ce) = counterexample {
                format!("Contract violated. Counterexample: {:?}", ce.assignments)
            } else {
                "Contract violated (no counterexample available)".to_string()
            };
            Err(msg)
        }
        VerificationResult::Unknown { reason } => {
            Err(format!("Z3 verification unknown: {}", reason))
        }
        VerificationResult::Error { error } => {
            Err(format!("Z3 verification error: {}", error))
        }
    }
}

#[cfg(not(feature = "z3"))]
fn verify_with_z3(_contract: &Contract, _func_sig: Option<&syn::ItemFn>, _requires: &[&Contract]) -> Result<(), String> {
    Err("Z3 feature not enabled. Build with --features z3 to enable Z3 verification.".to_string())
}

/// Result of function verification
#[derive(Debug, Clone)]
pub enum VerificationResult {
    Passed,
    Failed {
        contract: String,
        reason: String,
    },
    Partial {
        verified: usize,
        total: usize,
    },
    NotImplemented,
}

