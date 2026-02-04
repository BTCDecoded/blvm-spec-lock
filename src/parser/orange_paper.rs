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
    /// Constants in this section
    pub constants: Vec<ExtractedConstant>,
    /// Raw content
    pub content: String,
}

/// Extracted constant from Orange Paper
#[derive(Debug, Clone)]
pub struct ExtractedConstant {
    /// Constant name (e.g., "H", "C", "MAX_MONEY")
    pub name: String,
    /// Section ID (e.g., "4.1")
    pub section: String,
    /// Mathematical value (e.g., "210000", "10^8")
    pub value: String,
    /// Rust type (e.g., "u64", "i64")
    pub rust_type: String,
    /// Rust expression (e.g., "210_000", "100_000_000")
    pub rust_expr: String,
    /// Description from Orange Paper
    pub description: String,
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
                    constants: Vec::new(),
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
        
        // Extract constants for Section 4 (Consensus Constants)
        let mut constants = Vec::new();
        if section_id.starts_with("4.") {
            constants = self.extract_constants_from_section(section_id, content)?;
        }
        
        // Update section with parsed functions and constants
        if let Some(section) = self.sections.get_mut(section_id) {
            section.content = section_content;
            section.functions = functions;
            section.constants = constants;
        }
        
        Ok(())
    }
    
    /// Extract constants from Section 4 (Consensus Constants)
    fn extract_constants_from_section(&self, section_id: &str, content: &str) -> Result<Vec<ExtractedConstant>, String> {
        let mut constants = Vec::new();
        
        // Pattern: $CONSTANT_NAME = value$ (description)
        // Examples:
        // $C = 10^8$ (satoshis per BTC, ...)
        // $H = 210,000$ (halving interval, ...)
        // $M_{max} = 21 \times 10^6 \times C$ (maximum money supply, ...)
        let constant_re = Regex::new(r"\$([A-Za-z_]+(?:\{[^}]+\})?)\s*=\s*([^$]+)\$\s*(?:\(([^)]+)\))?")
            .map_err(|e| format!("Regex error: {}", e))?;
        
        // Also match lines that might have constants without parentheses
        let constant_re_alt = Regex::new(r"\$([A-Za-z_]+(?:\{[^}]+\})?)\s*=\s*([^$]+)\$")
            .map_err(|e| format!("Regex error: {}", e))?;
        
        for cap in constant_re.captures_iter(content) {
            let name_raw = cap.get(1).unwrap().as_str();
            let value_raw = cap.get(2).unwrap().as_str().trim();
            // Extract description - handle cases where it might be cut off
            let description = cap.get(3)
                .map(|m| {
                    let desc = m.as_str().to_string();
                    // Fix common issues: add closing paren if missing, clean up
                    if !desc.ends_with(')') && !desc.contains(')') {
                        format!("{})", desc)
                    } else {
                        desc
                    }
                })
                .unwrap_or_else(|| {
                    // Try to find description in next line
                    String::new()
                });
            
            // Clean up constant name (remove LaTeX formatting)
            // Handle subscripts like M_{max} -> M_MAX
            let name = if name_raw.contains('{') {
                // Extract base and subscript
                let parts: Vec<&str> = name_raw.split('{').collect();
                if parts.len() == 2 {
                    let base = parts[0];
                    let subscript = parts[1].trim_end_matches('}');
                    format!("{}_{}", base.to_uppercase(), subscript.to_uppercase())
                } else {
                    name_raw.to_uppercase()
                }
            } else {
                name_raw.to_uppercase()
            };
            
            // Remove double underscores
            let name = name.replace("__", "_");
            
            // Parse value and convert to Rust expression
            let (rust_type, rust_expr) = self.parse_constant_value(value_raw)?;
            
            constants.push(ExtractedConstant {
                name,
                section: section_id.to_string(),
                value: value_raw.to_string(),
                rust_type,
                rust_expr,
                description,
            });
        }
        
        Ok(constants)
    }
    
    /// Parse constant value from mathematical notation to Rust expression
    fn parse_constant_value(&self, value: &str) -> Result<(String, String), String> {
        let value = value.trim();
        
        // Handle different formats:
        // - "10^8" -> 100_000_000 (u64)
        // - "210,000" -> 210_000 (u64)
        // - "21 \times 10^6 \times C" -> 21_000_000 * C (i64, needs C constant)
        // - "4 \times 10^6" -> 4_000_000 (usize)
        
        // Remove LaTeX formatting and normalize (keep commas for now, remove later)
        let cleaned = value
            .replace("\\times", "*")
            .replace("×", "*")
            .replace(" ", "")
            .trim()
            .to_string();
        
        // IMPORTANT: Check most specific patterns FIRST (with anchors ^ and $)
        // This prevents partial matches (e.g., "10^6" matching inside "21*10^6*C")
        
        // 1. Handle N * 10^M * C format (e.g., "21*10^6*C") - MOST SPECIFIC
        let mult_exp_c_re = Regex::new(r"^(\d+)\*10\^(\d+)\*C$").map_err(|e| format!("Regex error: {}", e))?;
        if let Some(captures) = mult_exp_c_re.captures(&cleaned) {
            let base: u64 = captures.get(1).unwrap().as_str().parse()
                .map_err(|_| format!("Invalid base: {}", value))?;
            let exponent: u32 = captures.get(2).unwrap().as_str().parse()
                .map_err(|_| format!("Invalid exponent: {}", value))?;
            let multiplier = base * 10u64.pow(exponent);
            let formatted = self.format_number_with_underscores(multiplier);
            // C is u64, so we need to cast for i64 result
            return Ok(("i64".to_string(), format!("({} * C) as i64", formatted)));
        }
        
        // 2. Handle N * 10^M format (without C) - SECOND MOST SPECIFIC
        let mult_exp_re = Regex::new(r"^(\d+)\*10\^(\d+)$").map_err(|e| format!("Regex error: {}", e))?;
        if let Some(captures) = mult_exp_re.captures(&cleaned) {
            let base: u64 = captures.get(1).unwrap().as_str().parse()
                .map_err(|_| format!("Invalid base: {}", value))?;
            let exponent: u32 = captures.get(2).unwrap().as_str().parse()
                .map_err(|_| format!("Invalid exponent: {}", value))?;
            let result = base * 10u64.pow(exponent);
            let formatted = self.format_number_with_underscores(result);
            return Ok(("u64".to_string(), formatted));
        }
        
        // 3. Handle 10^N format - THIRD
        let exp_re = Regex::new(r"^10\^(\d+)$").map_err(|e| format!("Regex error: {}", e))?;
        if let Some(captures) = exp_re.captures(&cleaned) {
            let exponent: u32 = captures.get(1).unwrap().as_str().parse()
                .map_err(|_| format!("Invalid exponent: {}", value))?;
            let result = 10u64.pow(exponent);
            let formatted = self.format_number_with_underscores(result);
            return Ok(("u64".to_string(), formatted));
        }
        
        // 4. Try to parse as number (handle commas) - LEAST SPECIFIC
        let num_str = cleaned.replace(",", "").replace("_", "");
        if let Ok(num) = num_str.parse::<u64>() {
            // Format with underscores for readability
            let formatted = self.format_number_with_underscores(num);
            return Ok(("u64".to_string(), formatted));
        }
        
        Err(format!("Could not parse constant value: {}", value))
    }
    
    /// Format number with underscores for readability (e.g., 210000 -> 210_000)
    fn format_number_with_underscores(&self, num: u64) -> String {
        let s = num.to_string();
        let mut result = String::new();
        let chars: Vec<char> = s.chars().rev().collect();
        
        for (i, ch) in chars.iter().enumerate() {
            if i > 0 && i % 3 == 0 {
                result.push('_');
            }
            result.push(*ch);
        }
        
        result.chars().rev().collect()
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
        let latex_func_alt = format!(r"{}", func_name);  // Also match without \text{}
        
        // Find formula blocks (between $$)
        let mut in_formula = false;
        let mut formula_content = String::new();
        let mut lines_in_formula = 0;
        const MAX_FORMULA_LINES: usize = 10;  // Limit formula extraction to prevent grabbing too much
        
        for line in content.lines() {
            if line.contains("$$") {
                if !in_formula {
                    // Start of formula
                    in_formula = true;
                    formula_content = line.to_string();
                    lines_in_formula = 1;
                } else {
                    // End of formula
                    formula_content.push_str("\n");
                    formula_content.push_str(line);
                    lines_in_formula += 1;
                    
                    // Check if this formula matches our function
                    if formula_content.contains(&latex_func) || 
                       formula_content.contains(&latex_func_alt) ||
                       (formula_content.contains("GetBlockSubsidy") && func_name.contains("Subsidy")) ||
                       (formula_content.contains("TotalSupply") && func_name.contains("Supply")) {
                        // Clean up formula - remove extra content after closing $$
                        let cleaned = self.clean_formula(&formula_content);
                        func.formula = Some(cleaned);
                        break;
                    }
                    in_formula = false;
                    formula_content.clear();
                    lines_in_formula = 0;
                }
            } else if in_formula {
                if lines_in_formula < MAX_FORMULA_LINES {
                    formula_content.push_str("\n");
                    formula_content.push_str(line);
                    lines_in_formula += 1;
                } else {
                    // Formula too long, stop extracting
                    in_formula = false;
                    formula_content.clear();
                    lines_in_formula = 0;
                }
            }
        }
        
        Ok(())
    }
    
    /// Clean up extracted formula to remove extra content
    fn clean_formula(&self, formula: &str) -> String {
        // Extract just the formula between $$ markers
        let parts: Vec<&str> = formula.split("$$").collect();
        if parts.len() >= 2 {
            // Take content between first and last $$
            let mut cleaned = String::new();
            for (i, part) in parts.iter().enumerate() {
                if i % 2 == 1 {  // Odd indices are between $$ markers
                    if !cleaned.is_empty() {
                        cleaned.push('\n');
                    }
                    cleaned.push_str(part);
                }
            }
            cleaned.trim().to_string()
        } else {
            formula.trim().to_string()
        }
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
    
    /// Extract all constants from Section 4 (Consensus Constants)
    pub fn extract_constants(&self) -> Vec<&ExtractedConstant> {
        let mut constants = Vec::new();
        
        // Extract from Section 4.1, 4.2, 4.3
        for section_id in &["4.1", "4.2", "4.3"] {
            if let Some(section) = self.sections.get(*section_id) {
                constants.extend(section.constants.iter());
            }
        }
        
        constants
    }
    
    /// Get constants from a specific section
    pub fn get_section_constants(&self, section_id: &str) -> Vec<&ExtractedConstant> {
        self.sections.get(section_id)
            .map(|s| s.constants.iter().collect())
            .unwrap_or_default()
    }
    
    /// Extract all functions with formulas from Orange Paper
    pub fn extract_functions_with_formulas(&self) -> Vec<&FunctionSpec> {
        let mut functions = Vec::new();
        
        for section in self.sections.values() {
            for func in &section.functions {
                if func.formula.is_some() {
                    functions.push(func);
                }
            }
        }
        
        functions
    }
    
    /// Get function by name
    pub fn get_function(&self, name: &str) -> Option<&FunctionSpec> {
        for section in self.sections.values() {
            for func in &section.functions {
                if func.name == name {
                    return Some(func);
                }
            }
        }
        None
    }
}
