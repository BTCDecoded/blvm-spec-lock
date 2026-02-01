//! Orange Paper parser
//!
//! Parses Orange Paper markdown to extract function specifications, theorems, and properties
//! and links them to Rust implementations.

use regex::Regex;
use std::collections::HashMap;

/// A function specification from the Orange Paper
#[derive(Debug, Clone)]
pub struct FunctionSpec {
    /// Function name (e.g., "GetBlockSubsidy")
    pub name: String,
    /// Section ID (e.g., "6.1")
    pub section: String,
    /// Function signature (e.g., "ℕ → ℤ")
    pub signature: Option<String>,
    /// Properties extracted from the Orange Paper
    pub properties: Vec<Property>,
    /// Theorems related to this function
    pub theorems: Vec<Theorem>,
    /// Contracts extracted from properties
    pub contracts: Vec<Contract>,
    /// Raw markdown content for this section
    pub content: String,
    /// Conditions (for backward compatibility with macro_impl)
    pub conditions: Vec<String>,
    /// Mathematical formula
    pub formula: Option<String>,
    /// Description
    pub description: Option<String>,
}

/// A property from the Orange Paper
#[derive(Debug, Clone)]
pub struct Property {
    /// Property name (e.g., "Non-negative")
    pub name: String,
    /// Mathematical statement
    pub statement: String,
    /// Type of property (precondition, postcondition, invariant)
    pub property_type: PropertyType,
}

/// Type of property
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PropertyType {
    Requires,  // Precondition
    Ensures,   // Postcondition
    Invariant, // Invariant
}

/// A theorem from the Orange Paper
#[derive(Debug, Clone)]
pub struct Theorem {
    /// Theorem number (e.g., "6.1.1")
    pub number: String,
    /// Theorem name
    pub name: String,
    /// Mathematical statement
    pub statement: String,
    /// Proof reference (e.g., formal proof name)
    pub proof_reference: Option<String>,
}

/// A contract extracted from Orange Paper
#[derive(Debug, Clone)]
pub struct Contract {
    /// Contract type
    pub contract_type: ContractType,
    /// Condition (mathematical expression, to be translated to Rust)
    pub condition: String,
    /// Comment/description
    pub comment: Option<String>,
}

/// Contract type
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ContractType {
    Requires,
    Ensures,
    Property,
    EdgeCase,
}

/// Orange Paper parser
pub struct SpecParser {
    content: String,
    sections: HashMap<String, SpecSection>,
}

/// A section from the Orange Paper
#[derive(Debug, Clone)]
pub struct SpecSection {
    /// Section ID (e.g., "6.1")
    pub id: String,
    /// Section title
    pub title: String,
    /// Functions in this section
    pub functions: Vec<FunctionSpec>,
    /// Theorems in this section
    pub theorems: Vec<Theorem>,
    /// Raw content
    pub content: String,
}

impl SpecParser {
    /// Create a new parser from Orange Paper content
    pub fn new(content: String) -> Self {
        SpecParser {
            content,
            sections: HashMap::new(),
        }
    }

    /// Parse the entire Orange Paper (must be called before using other methods)
    pub fn parse(&mut self) -> Result<(), String> {
        // Initialize sections map if not already done
        if self.sections.is_empty() {
            // Parse will populate sections
        }
        // Split into sections by headers (both ### and ##)
        // Match sections like "6.1", "5.2.1", etc.
        let section_re = Regex::new(r"^##+?\s+(\d+(?:\.\d+)*)\s+(.+)$").map_err(|e| format!("Regex error: {}", e))?;
        
        // Clone content to avoid borrow checker issues
        let content = self.content.clone();
        let lines: Vec<&str> = content.lines().collect();
        let mut current_section: Option<String> = None;
        let mut current_content = Vec::new();
        
        for line in &lines {
            if let Some(caps) = section_re.captures(line) {
                // Save previous section
                if let Some(ref section_id) = current_section {
                    self.parse_section(section_id, &current_content.join("\n"))?;
                }
                
                // Start new section
                let section_id = caps.get(1).unwrap().as_str().to_string();
                let title = caps.get(2).unwrap().as_str().to_string();
                current_section = Some(section_id.clone());
                current_content = vec![line.to_string()];
                
                // Initialize section
                self.sections.insert(section_id.clone(), SpecSection {
                    id: section_id,
                    title,
                    functions: Vec::new(),
                    theorems: Vec::new(),
                    content: String::new(),
                });
            } else if current_section.is_some() {
                current_content.push(line.to_string());
            }
        }
        
        // Parse last section
        if let Some(ref section_id) = current_section {
            self.parse_section(section_id, &current_content.join("\n"))?;
        }
        
        Ok(())
    }

    /// Parse a specific section
    fn parse_section(&mut self, section_id: &str, content: &str) -> Result<(), String> {
        // Get section content first
        let section_content = content.to_string();
        
        // Extract functions
        let function_re = Regex::new(r"\*\*(\w+)\*\*:\s*\$?([^\$]+)\$?").map_err(|e| format!("Regex error: {}", e))?;
        
        let mut functions = Vec::new();
        
        for cap in function_re.captures_iter(content) {
            let name = cap.get(1).unwrap().as_str().to_string();
            let signature = cap.get(2).map(|m| m.as_str().to_string());
            
            let mut func_spec = FunctionSpec {
                name: name.clone(),
                section: section_id.to_string(),
                signature: signature.clone(),
                properties: Vec::new(),
                theorems: Vec::new(),
                contracts: Vec::new(),
                content: String::new(),
                conditions: Vec::new(),
                formula: None,
                description: None,
            };
            
            // Extract properties for this function
            self.extract_properties(&mut func_spec, content, &name)?;
            
            // Extract theorems
            self.extract_theorems(&mut func_spec, content)?;
            
            // Extract formula
            self.extract_formula(&mut func_spec, content, &name)?;
            
            // Generate contracts from properties
            self.generate_contracts(&mut func_spec)?;
            
            // NEW: Generate contracts from theorems
            self.generate_contracts_from_theorems(&mut func_spec)?;
            
            // Populate conditions from contracts
            func_spec.conditions = func_spec.contracts.iter()
                .map(|c| c.condition.clone())
                .collect();
            
            functions.push(func_spec);
        }
        
        // Update section with parsed functions
        if let Some(section) = self.sections.get_mut(section_id) {
            section.content = section_content;
            section.functions = functions;
        }
        
        Ok(())
    }

    /// Extract properties for a function
    fn extract_properties(&self, func: &mut FunctionSpec, content: &str, func_name: &str) -> Result<(), String> {
        // Look for properties list - match lines starting with "- **PropertyName**:"
        // Use multiline mode to match across lines
        // Simple pattern without look-ahead
        let property_re = Regex::new(r"(?m)^\s*-\s*\*\*([^:]+)\*\*:\s*(.+)$").map_err(|e| format!("Regex error: {}", e))?;
        
        // Find the Properties section for this function using string search (avoid regex issues)
        // Look for function name in bold: **FunctionName**
        let func_marker = format!("**{}**", func_name);
        
        if let Some(func_pos) = content.find(&func_marker) {
            // Extract properties from the section content after the function name
            let start_pos = func_pos + func_marker.len();
            let remaining = &content[start_pos..];
            
            // Find the end of this function's section (next function or section header)
            let next_func = remaining.find("**").unwrap_or(remaining.len());
            let next_section = remaining.find("\n###").unwrap_or(remaining.len());
            let block_end = next_func.min(next_section);
            let block_content = &remaining[..block_end];
            
            // Look for "**Properties**:" header and extract properties after it
            if let Some(props_start) = block_content.find("**Properties**:") {
                let props_section = &block_content[props_start..];
                // Extract properties from this block
                for cap in property_re.captures_iter(props_section) {
                    let name = cap.get(1).unwrap().as_str().trim().to_string();
                    let statement = cap.get(2).unwrap().as_str().trim().to_string();
                    
                    // Determine property type
                    let property_type = if statement.contains("≥") || statement.contains(">=") || 
                                         statement.contains("≤") || statement.contains("<=") ||
                                         statement.contains("=") {
                        // Usually a postcondition or invariant
                        if statement.contains("result") || statement.contains("return") {
                            PropertyType::Ensures
                        } else {
                            PropertyType::Invariant
                        }
                    } else if statement.contains("implies") || statement.contains("⟹") {
                        PropertyType::Requires
                    } else {
                        PropertyType::Ensures
                    };
                    
                    func.properties.push(Property {
                        name,
                        statement,
                        property_type,
                    });
                }
            }
        }
        
        Ok(())
    }

    /// Extract theorems
    fn extract_theorems(&self, func: &mut FunctionSpec, content: &str) -> Result<(), String> {
        // Match: **Theorem X.Y.Z** (Name)
        // Use simple, reliable regex
        let theorem_re = Regex::new(r"\*\*Theorem\s+([\d.]+)\*\*[^(]*\(([^)]+)\)").map_err(|e| format!("Regex error: {}", e))?;
        
        for cap in theorem_re.captures_iter(content) {
            let number = cap.get(1).unwrap().as_str().to_string();
            let name = cap.get(2).unwrap().as_str().to_string();
            
            // Extract statement - look for LaTeX math blocks or inline math after theorem
            let mut statement = String::new();
            
            // Find position of this theorem in content
            let theorem_pos = cap.get(0).unwrap().end();
            let content_after = &content[theorem_pos..];
            
            // Look for LaTeX math blocks ($$...$$)
            let latex_block_re = Regex::new(r"\$\$([^$]+)\$\$").map_err(|e| format!("Regex error: {}", e))?;
            if let Some(latex_cap) = latex_block_re.captures(content_after) {
                if let Some(latex_content) = latex_cap.get(1) {
                    statement = latex_content.as_str().to_string();
                }
            }
            
            // If no LaTeX block, look for inline math
            if statement.is_empty() {
                let inline_math_re = Regex::new(r"\$([^$]+)\$").map_err(|e| format!("Regex error: {}", e))?;
                if let Some(math_cap) = inline_math_re.captures(content_after) {
                    if let Some(math_content) = math_cap.get(1) {
                        statement = math_content.as_str().to_string();
                    }
                }
            }
            
            // If still empty, try to extract from next few lines
            if statement.is_empty() {
                let lines: Vec<&str> = content_after.lines().take(5).collect();
                let potential_statement: String = lines.join(" ").trim().to_string();
                // Only use if it looks like a mathematical statement
                if potential_statement.contains("∀") || 
                   potential_statement.contains("∈") ||
                   potential_statement.contains("≥") ||
                   potential_statement.contains("≤") ||
                   potential_statement.contains("=") ||
                   potential_statement.contains(&func.name) {
                    statement = potential_statement;
                }
            }
            
            // Fallback if still empty
            if statement.is_empty() {
                statement = format!("See Orange Paper Theorem {} for full statement", number);
            }
            
            // Look for proof reference
            let proof_ref = if content_after.contains("proof") || content_after.contains("verification") {
                Some("Formal verification".to_string())
            } else {
                None
            };
            
            func.theorems.push(Theorem {
                number,
                name,
                statement,
                proof_reference: proof_ref,
            });
        }
        
        Ok(())
    }

    /// Extract mathematical formula
    fn extract_formula(&self, func: &mut FunctionSpec, content: &str, func_name: &str) -> Result<(), String> {
        // Look for LaTeX formula: $$\text{FunctionName}(...) = ...$$
        // Use string search instead of regex to avoid escape issues
        let latex_func = format!(r"\text{{{}}}", func_name);
        
        // Find formula blocks (between $$)
        let mut in_formula = false;
        let mut formula_start = 0;
        let mut formula_content = String::new();
        
        for (i, line) in content.lines().enumerate() {
            if line.contains("$$") {
                if !in_formula {
                    // Start of formula
                    in_formula = true;
                    formula_start = i;
                    formula_content = line.to_string();
                } else {
                    // End of formula
                    formula_content.push_str("\n");
                    formula_content.push_str(line);
                    if formula_content.contains(&latex_func) {
                        func.formula = Some(formula_content.clone());
                        break;
                    }
                    in_formula = false;
                    formula_content.clear();
                }
            } else if in_formula {
                formula_content.push_str("\n");
                formula_content.push_str(line);
            }
        }
        
        Ok(())
    }

    /// Generate contracts from properties
    fn generate_contracts(&self, func: &mut FunctionSpec) -> Result<(), String> {
        for property in &func.properties {
            // Translate mathematical notation to Rust-like expression
            let condition = self.translate_property_to_rust(&property.statement, &func.name)?;
            
            let contract_type = match property.property_type {
                PropertyType::Requires => ContractType::Requires,
                PropertyType::Ensures | PropertyType::Invariant => ContractType::Ensures,
            };
            
            func.contracts.push(Contract {
                contract_type,
                condition,
                comment: Some(property.name.clone()),
            });
        }
        
        Ok(())
    }

    /// Generate contracts from theorems
    /// Extracts properties directly from theorem statements
    fn generate_contracts_from_theorems(&self, func: &mut FunctionSpec) -> Result<(), String> {
        for theorem in &func.theorems {
            // Parse theorem statement to extract properties
            // Theorem format: "∀h ∈ ℕ: get_block_subsidy(h) ≥ 0 ∧ get_block_subsidy(h) ≤ INITIAL_SUBSIDY"
            let statement = &theorem.statement;
            
            // Split by logical operators (∧, ∨, ⟹, etc.)
            // For now, handle simple conjunctions (∧)
            let parts: Vec<&str> = statement.split('∧').collect();
            
            for part in parts {
                let part = part.trim();
                
                // Check if this part mentions the function
                let func_name_lower = func.name.to_lowercase();
                if part.to_lowercase().contains(&func_name_lower) || 
                   part.contains(&format!(r"\text{{{}}}", func.name)) {
                    
                    // Translate to Rust contract
                    let condition = self.translate_theorem_statement_to_rust(part, &func.name)?;
                    
                    // Determine contract type based on statement
                    let contract_type = if part.contains("≥") || part.contains("≤") || 
                                         part.contains(">") || part.contains("<") ||
                                         part.contains("=") {
                        ContractType::Ensures
                    } else {
                        ContractType::Ensures  // Default to ensures for theorems
                    };
                    
                    func.contracts.push(Contract {
                        contract_type,
                        condition,
                        comment: Some(format!("From Theorem {}", theorem.number)),
                    });
                }
            }
        }
        
        Ok(())
    }

    /// Translate theorem statement to Rust-like expression
    fn translate_theorem_statement_to_rust(&self, statement: &str, func_name: &str) -> Result<String, String> {
        // Use the same translation logic as properties
        self.translate_property_to_rust(statement, func_name)
    }

    /// Translate mathematical property to Rust-like expression
    fn translate_property_to_rust(&self, statement: &str, func_name: &str) -> Result<String, String> {
        // Simple translation - replace common patterns
        let mut rust_expr = statement.to_string();
        
        // Replace LaTeX function calls - handle escaped backslashes properly
        // First replace LaTeX \text{FunctionName} format (literal backslash + text)
        let latex_pattern = format!(r"\text{{{}}}", func_name);
        rust_expr = rust_expr.replace(&latex_pattern, "result");
        // Also handle escaped version
        let latex_pattern_escaped = format!(r"\\text{{{}}}", func_name);
        rust_expr = rust_expr.replace(&latex_pattern_escaped, "result");
        // Then replace plain function name (but not if it's part of a larger word)
        rust_expr = rust_expr.replace(&format!("{}", func_name), "result");
        
        // Replace mathematical operators
        rust_expr = rust_expr.replace("≥", ">=");
        rust_expr = rust_expr.replace("≤", "<=");
        rust_expr = rust_expr.replace("≠", "!=");
        rust_expr = rust_expr.replace("⟹", "=>");
        
        // Replace common variables (be careful not to replace in the middle of words)
        rust_expr = rust_expr.replace(" h ", " height ");
        rust_expr = rust_expr.replace("(h)", "(height)");
        rust_expr = rust_expr.replace(" h,", " height,");
        rust_expr = rust_expr.replace(" h)", " height)");
        rust_expr = rust_expr.replace(" H ", " HALVING_INTERVAL ");
        rust_expr = rust_expr.replace("(H)", "(HALVING_INTERVAL)");
        rust_expr = rust_expr.replace(" C ", " SATOSHIS_PER_BTC ");
        rust_expr = rust_expr.replace("(C)", "(SATOSHIS_PER_BTC)");
        
        // Remove LaTeX formatting (do this last)
        rust_expr = rust_expr.replace("$", "");
        rust_expr = rust_expr.replace(r"\text{", "");
        rust_expr = rust_expr.replace(r"\{", "{");
        rust_expr = rust_expr.replace(r"\}", "}");
        
        Ok(rust_expr)
    }

    /// Find a section by ID
    pub fn find_section(&self, section_id: &str) -> Option<&SpecSection> {
        self.sections.get(section_id)
    }

    /// Find a function specification by section and name
    pub fn find_function(&self, section: &str, name: Option<&str>) -> Option<&FunctionSpec> {
        if let Some(spec_section) = self.sections.get(section) {
            if let Some(func_name) = name {
                spec_section.functions.iter()
                    .find(|f| f.name.eq_ignore_ascii_case(func_name))
            } else {
                spec_section.functions.first()
            }
        } else {
            None
        }
    }

    /// Get all functions in a section
    pub fn get_section_functions(&self, section: &str) -> Vec<&FunctionSpec> {
        self.sections.get(section)
            .map(|s| s.functions.iter().collect())
            .unwrap_or_default()
    }

    /// Parse function signature
    pub fn parse_signature(sig: &str) -> Option<(Vec<String>, String)> {
        // Simple signature parser: "ℕ → ℤ" or "Natural → Integer"
        if sig.contains("→") || sig.contains("->") {
            let parts: Vec<&str> = sig.split("→").collect();
            if parts.len() == 2 {
                let input = parts[0].trim().to_string();
                let output = parts[1].trim().to_string();
                return Some((vec![input], output));
            }
        }
        None
    }

    /// Find a function specification by name across all sections
    /// Returns the function spec and its section ID
    pub fn find_function_anywhere(&self, func_name: &str) -> Option<(&FunctionSpec, &str)> {
        for (section_id, section) in &self.sections {
            if let Some(func_spec) = section.functions.iter()
                .find(|f| f.name.eq_ignore_ascii_case(func_name)) {
                return Some((func_spec, section_id));
            }
        }
        None
    }

    /// Find a theorem by function name across all sections
    /// Searches theorem statements for function name mentions
    pub fn find_theorem_by_function_name(&self, func_name: &str) -> Option<(&Theorem, &str, &str)> {
        let func_name_lower = func_name.to_lowercase();
        let func_name_variations = vec![
            func_name_lower.clone(),
            func_name.to_string(),
            format!("\\text{{{}}}", func_name),
            format!("\\text{{{}}}", func_name_lower),
        ];

        for (section_id, section) in &self.sections {
            for theorem in &section.theorems {
                // Check if theorem statement contains function name
                let theorem_lower = theorem.statement.to_lowercase();
                if func_name_variations.iter().any(|variant| {
                    theorem_lower.contains(variant) || theorem.statement.contains(variant)
                }) {
                    // Find the function in this section
                    if let Some(func_spec) = section.functions.iter()
                        .find(|f| f.name.eq_ignore_ascii_case(func_name)) {
                        return Some((theorem, section_id, &func_spec.name));
                    }
                }
            }
        }
        None
    }

    /// Find subsection by granular ID (e.g., "5.1.1")
    /// Returns the section and subsection ID
    pub fn find_subsection(&self, granular_id: &str) -> Option<(&SpecSection, String)> {
        // Parse granular ID: "5.1.1" -> section "5.1", subsection "5.1.1"
        let parts: Vec<&str> = granular_id.split('.').collect();
        if parts.len() >= 2 {
            let section_id = parts[0..parts.len()-1].join(".");
            if let Some(section) = self.sections.get(&section_id) {
                // Check if granular_id matches a subsection pattern
                // For now, check if it's mentioned in section content or theorems
                if section.content.contains(granular_id) || 
                   section.theorems.iter().any(|t| t.number == granular_id) {
                    return Some((section, granular_id.to_string()));
                }
            }
        }
        None
    }

    /// Get all theorems in a section
    pub fn get_section_theorems(&self, section_id: &str) -> Vec<&Theorem> {
        self.sections.get(section_id)
            .map(|s| s.theorems.iter().collect())
            .unwrap_or_default()
    }
}
