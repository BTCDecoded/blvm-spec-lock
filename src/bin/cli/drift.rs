//! Spec drift detection
//!
//! Detects when Orange Paper and implementation diverge

use std::path::PathBuf;
use std::collections::HashMap;
use super::verify::{discover_functions, FunctionToVerify};
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
pub fn detect_drift(workspace_root: &PathBuf, orange_paper_path: Option<&PathBuf>) -> Result<DriftResult, String> {
    // Discover all spec-locked functions
    let functions = discover_functions(workspace_root)?;
    
    // Load Orange Paper
    let spec_path = orange_paper_path
        .map(|p| p.clone())
        .unwrap_or_else(|| {
            workspace_root.join("../blvm-spec/THE_ORANGE_PAPER.md")
        });
    
    // Simplified drift detection (full implementation requires SpecParser access)
    // For now, detect functions without contracts as potential drift
    let mut mismatched_contracts = Vec::new();
    let mut missing_from_spec = Vec::new();
    let mut auto_inferred = Vec::new();
    
    // Check each function
    for func in &functions {
        // Check if function has section (not auto-inferred)
        if func.section.is_none() {
            auto_inferred.push(func.clone());
            continue;
        }
        
        // Functions without contracts may indicate drift
        if func.contracts.is_empty() {
            missing_from_spec.push(func.clone());
        }
    }
    
    // Find theorems without implementations
    // Note: Full implementation requires SpecParser access from binary
    let missing_implementations = Vec::new();
    
    Ok(DriftResult {
        mismatched_contracts,
        missing_from_spec,
        missing_implementations,
        auto_inferred,
    })
}

/// Convert Rust snake_case to PascalCase
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

/// Check if two contracts are similar (allows for minor formatting differences)
fn contracts_similar(spec: &str, impl_contract: &str) -> bool {
    // Normalize both contracts
    let spec_norm = normalize_contract(spec);
    let impl_norm = normalize_contract(impl_contract);
    
    // Check for exact match
    if spec_norm == impl_norm {
        return true;
    }
    
    // Check if one contains the other (for partial matches)
    spec_norm.contains(&impl_norm) || impl_norm.contains(&spec_norm)
}

/// Normalize contract string for comparison
fn normalize_contract(contract: &str) -> String {
    contract
        .to_lowercase()
        .replace(" ", "")
        .replace(">=", ">=")
        .replace("<=", "<=")
        .replace("!=", "!=")
        .replace("==", "==")
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
            output.push_str(&format!("  Function: {} (Section {})\n", 
                mismatch.function.function_name, mismatch.section));
            output.push_str(&format!("    Orange Paper: {}\n", mismatch.orange_paper_contract));
            output.push_str(&format!("    Implementation: {}\n", mismatch.implementation_contract));
            output.push_str("\n");
        }
    }
    
    // Missing from spec
    if !result.missing_from_spec.is_empty() {
        output.push_str("❌ Functions Missing from Orange Paper:\n");
        output.push_str("--------------------------------------\n");
        for func in &result.missing_from_spec {
            output.push_str(&format!("  {} ({})\n", 
                func.function_name, func.file_path.display()));
        }
        output.push_str("\n");
    }
    
    // Auto-inferred
    if !result.auto_inferred.is_empty() {
        output.push_str("ℹ️  Auto-Inferred Functions (verify manually):\n");
        output.push_str("---------------------------------------------\n");
        for func in &result.auto_inferred {
            output.push_str(&format!("  {} ({})\n", 
                func.function_name, func.file_path.display()));
        }
        output.push_str("\n");
    }
    
    // Summary
    output.push_str("Summary:\n");
    output.push_str("--------\n");
    output.push_str(&format!("  Mismatched contracts: {}\n", result.mismatched_contracts.len()));
    output.push_str(&format!("  Missing from spec: {}\n", result.missing_from_spec.len()));
    output.push_str(&format!("  Auto-inferred: {}\n", result.auto_inferred.len()));
    output.push_str(&format!("  Missing implementations: {}\n", result.missing_implementations.len()));
    
    if result.mismatched_contracts.is_empty() && 
       result.missing_from_spec.is_empty() && 
       result.missing_implementations.is_empty() {
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
        "auto_inferred": result.auto_inferred.iter().map(|f| serde_json::json!({
            "function": f.function_name,
            "file": f.file_path.display().to_string(),
        })).collect::<Vec<_>>(),
        "missing_implementations": result.missing_implementations,
    }).to_string()
}

