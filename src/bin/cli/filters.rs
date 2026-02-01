//! Filtering logic for verification
//!
//! Filters functions by subsystem, name, section, etc.

use crate::cli::verify::FunctionToVerify;

/// Filter functions based on criteria
pub fn filter_functions(
    functions: Vec<FunctionToVerify>,
    subsystem: Option<&str>,
    name: Option<&str>,
    sections: &[String],
) -> Vec<FunctionToVerify> {
    functions
        .into_iter()
        .filter(|f| {
            // Filter by subsystem (if specified)
            if let Some(subsys) = subsystem {
                if !matches_subsystem(&f.file_path, subsys) {
                    return false;
                }
            }
            
            // Filter by name (if specified)
            if let Some(name_pattern) = name {
                if !matches_name(&f.function_name, name_pattern) {
                    return false;
                }
            }
            
            // Filter by section (if specified)
            if !sections.is_empty() {
                if let Some(ref section) = f.section {
                    if !sections.contains(section) {
                        return false;
                    }
                } else {
                    return false; // No section specified, exclude
                }
            }
            
            true
        })
        .collect()
}

/// Check if file path matches subsystem
fn matches_subsystem(file_path: &std::path::Path, subsystem: &str) -> bool {
    let path_str = file_path.to_string_lossy();
    // Simple heuristic: check if subsystem name appears in path
    path_str.contains(subsystem)
}

/// Check if function name matches pattern
fn matches_name(function_name: &str, pattern: &str) -> bool {
    // Simple pattern matching (support * wildcard)
    if pattern.contains('*') {
        let regex_pattern = pattern.replace('*', ".*");
        // For now, simple contains check
        function_name.contains(&pattern.replace('*', ""))
    } else {
        function_name == pattern
    }
}

