//! Coverage reporting for spec-locked functions
//!
//! Reports which functions are spec-locked, coverage by section, missing functions, etc.

use std::path::PathBuf;
use std::collections::HashMap;
use crate::cli::verify::{discover_functions, FunctionToVerify};

/// Coverage statistics
#[derive(Debug, Clone)]
pub struct CoverageStats {
    /// Total number of spec-locked functions
    pub total_spec_locked: usize,
    /// Functions grouped by section
    pub by_section: HashMap<String, Vec<FunctionToVerify>>,
    /// Functions without section (auto-inferred)
    pub without_section: Vec<FunctionToVerify>,
    /// Functions with contracts
    pub with_contracts: usize,
    /// Functions without contracts
    pub without_contracts: usize,
}

/// Generate coverage report
pub fn generate_coverage(workspace_root: &PathBuf) -> Result<CoverageStats, String> {
    let functions = discover_functions(workspace_root)?;
    
    let mut by_section: HashMap<String, Vec<FunctionToVerify>> = HashMap::new();
    let mut without_section = Vec::new();
    let mut with_contracts = 0;
    let mut without_contracts = 0;
    
    for func in functions {
        if func.contracts.is_empty() {
            without_contracts += 1;
        } else {
            with_contracts += 1;
        }
        
        if let Some(section) = &func.section {
            by_section.entry(section.clone())
                .or_insert_with(Vec::new)
                .push(func);
        } else {
            without_section.push(func);
        }
    }
    
    Ok(CoverageStats {
        total_spec_locked: with_contracts + without_contracts,
        by_section,
        without_section,
        with_contracts,
        without_contracts,
    })
}

/// Format coverage report as human-readable text
pub fn format_coverage_human(stats: &CoverageStats) -> String {
    let mut output = String::new();
    
    output.push_str("=== Spec Lock Coverage Report ===\n\n");
    
    // Overall statistics
    output.push_str(&format!("Total spec-locked functions: {}\n", stats.total_spec_locked));
    output.push_str(&format!("  - With contracts: {}\n", stats.with_contracts));
    output.push_str(&format!("  - Without contracts: {}\n", stats.without_contracts));
    
    if stats.total_spec_locked > 0 {
        let contract_coverage = (stats.with_contracts as f64 / stats.total_spec_locked as f64) * 100.0;
        output.push_str(&format!("Contract coverage: {:.1}%\n", contract_coverage));
    }
    
    output.push_str("\n");
    
    // By section
    if !stats.by_section.is_empty() {
        output.push_str("Coverage by Orange Paper Section:\n");
        output.push_str("--------------------------------\n");
        
        let mut sections: Vec<(&String, &Vec<FunctionToVerify>)> = stats.by_section.iter().collect();
        sections.sort_by_key(|(section, _)| {
            // Sort by section number (e.g., "5.1" < "5.2" < "6.1")
            let parts: Vec<&str> = section.split('.').collect();
            let major: u32 = parts.get(0).and_then(|s| s.parse().ok()).unwrap_or(0);
            let minor: u32 = parts.get(1).and_then(|s| s.parse().ok()).unwrap_or(0);
            let sub: u32 = parts.get(2).and_then(|s| s.parse().ok()).unwrap_or(0);
            (major, minor, sub)
        });
        
        for (section, funcs) in sections {
            output.push_str(&format!("  Section {}: {} functions\n", section, funcs.len()));
            for func in funcs {
                let contract_status = if func.contracts.is_empty() {
                    "⚠️  no contracts"
                } else {
                    "✅"
                };
                output.push_str(&format!("    - {} {} ({})\n", 
                    contract_status,
                    func.function_name,
                    func.file_path.display()
                ));
            }
        }
        output.push_str("\n");
    }
    
    // Functions without section (auto-inferred)
    if !stats.without_section.is_empty() {
        output.push_str("Functions with auto-inferred sections:\n");
        output.push_str("--------------------------------------\n");
        for func in &stats.without_section {
            let contract_status = if func.contracts.is_empty() {
                "⚠️  no contracts"
            } else {
                "✅"
            };
            output.push_str(&format!("  {} {} ({})\n", 
                contract_status,
                func.function_name,
                func.file_path.display()
            ));
        }
        output.push_str("\n");
    }
    
    // Summary
    output.push_str("Summary:\n");
    output.push_str("--------\n");
    output.push_str(&format!("  Total sections covered: {}\n", stats.by_section.len()));
    output.push_str(&format!("  Functions with contracts: {}\n", stats.with_contracts));
    output.push_str(&format!("  Functions without contracts: {}\n", stats.without_contracts));
    
    if stats.total_spec_locked > 0 {
        let contract_coverage = (stats.with_contracts as f64 / stats.total_spec_locked as f64) * 100.0;
        output.push_str(&format!("  Contract coverage: {:.1}%\n", contract_coverage));
    }
    
    output
}

/// Format coverage report as JSON
pub fn format_coverage_json(stats: &CoverageStats) -> String {
    use std::collections::HashMap;
    
    let mut json = serde_json::json!({
        "total_spec_locked": stats.total_spec_locked,
        "with_contracts": stats.with_contracts,
        "without_contracts": stats.without_contracts,
        "contract_coverage_percent": if stats.total_spec_locked > 0 {
            (stats.with_contracts as f64 / stats.total_spec_locked as f64) * 100.0
        } else {
            0.0
        },
        "by_section": {},
        "without_section": []
    });
    
    // Add by_section
    let by_section_obj = json["by_section"].as_object_mut().unwrap();
    for (section, funcs) in &stats.by_section {
        by_section_obj.insert(section.clone(), serde_json::json!({
            "count": funcs.len(),
            "functions": funcs.iter().map(|f| serde_json::json!({
                "name": f.function_name,
                "file": f.file_path.display().to_string(),
                "has_contracts": !f.contracts.is_empty(),
                "contract_count": f.contracts.len()
            })).collect::<Vec<_>>()
        }));
    }
    
    // Add without_section
    let without_section_arr = json["without_section"].as_array_mut().unwrap();
    for func in &stats.without_section {
        without_section_arr.push(serde_json::json!({
            "name": func.function_name,
            "file": func.file_path.display().to_string(),
            "has_contracts": !func.contracts.is_empty(),
            "contract_count": func.contracts.len()
        }));
    }
    
    serde_json::to_string_pretty(&json).unwrap_or_else(|_| "{}".to_string())
}

/// Format coverage report as Markdown
pub fn format_coverage_markdown(stats: &CoverageStats) -> String {
    let mut output = String::new();
    
    output.push_str("# Spec Lock Coverage Report\n\n");
    
    // Overall statistics
    output.push_str("## Overall Statistics\n\n");
    output.push_str(&format!("- **Total spec-locked functions**: {}\n", stats.total_spec_locked));
    output.push_str(&format!("- **With contracts**: {}\n", stats.with_contracts));
    output.push_str(&format!("- **Without contracts**: {}\n", stats.without_contracts));
    
    if stats.total_spec_locked > 0 {
        let contract_coverage = (stats.with_contracts as f64 / stats.total_spec_locked as f64) * 100.0;
        output.push_str(&format!("- **Contract coverage**: {:.1}%\n", contract_coverage));
    }
    
    output.push_str("\n");
    
    // By section
    if !stats.by_section.is_empty() {
        output.push_str("## Coverage by Orange Paper Section\n\n");
        output.push_str("| Section | Functions | Status |\n");
        output.push_str("|---------|-----------|--------|\n");
        
        let mut sections: Vec<(&String, &Vec<FunctionToVerify>)> = stats.by_section.iter().collect();
        sections.sort_by_key(|(section, _)| {
            let parts: Vec<&str> = section.split('.').collect();
            let major: u32 = parts.get(0).and_then(|s| s.parse().ok()).unwrap_or(0);
            let minor: u32 = parts.get(1).and_then(|s| s.parse().ok()).unwrap_or(0);
            let sub: u32 = parts.get(2).and_then(|s| s.parse().ok()).unwrap_or(0);
            (major, minor, sub)
        });
        
        for (section, funcs) in sections {
            let with_contracts = funcs.iter().filter(|f| !f.contracts.is_empty()).count();
            let status = if with_contracts == funcs.len() {
                "✅ Complete"
            } else if with_contracts > 0 {
                "⚠️  Partial"
            } else {
                "❌ No contracts"
            };
            output.push_str(&format!("| {} | {} | {} |\n", section, funcs.len(), status));
        }
        output.push_str("\n");
    }
    
    output
}




