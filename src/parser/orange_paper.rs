//! Orange Paper parser
//!
//! Parses Orange Paper markdown to extract function specifications, theorems, and properties
//! and links them to Rust implementations.

use regex::Regex;
use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

/// Parse round-trip formula: \text{Outer}(\text{Inner}(x)) = x or (tx, w)
/// Returns (property_type, outer_func, inner_func, constraint)
fn parse_round_trip_formula(
    formula: &str,
) -> (
    StandalonePropertyType,
    Option<String>,
    Option<String>,
    Option<String>,
) {
    // Match \text{FunctionName} - capture names (filter out common non-functions like "inputs", "valid")
    let text_func_re = Regex::new(r"\\text\{([^}]+)\}").ok().unwrap();
    let non_functions = ["inputs", "outputs", "valid", "invalid", "value"];
    let func_names: Vec<String> = text_func_re
        .captures_iter(formula)
        .map(|c| c.get(1).unwrap().as_str().to_string())
        .filter(|s| !non_functions.contains(&s.as_str()))
        .collect();

    // Round-trip: Outer(Inner(x)) = x → outer is first \text{} (wraps the rest), inner is second
    if func_names.len() >= 2 {
        let outer = func_names.first().cloned();
        let inner = func_names.get(1).cloned();
        if outer.is_some() && inner.is_some() {
            // Check for constraint: |w| = |tx.inputs| or similar
            let constraint = if formula.contains("|w|") && formula.contains("|tx") {
                Some("|w| = |tx.inputs|".to_string())
            } else if formula.contains("implies") || formula.contains("⟹") {
                formula
                    .split("implies")
                    .next()
                    .or_else(|| formula.split("⟹").next())
                    .map(|s| s.trim().to_string())
            } else {
                None
            };
            return (StandalonePropertyType::RoundTrip, outer, inner, constraint);
        }
    }

    // Idempotent: F(F(x)) = F(x) - same func name appears twice in nesting
    if !func_names.is_empty() {
        let first = &func_names[0];
        if formula.matches(first).count() >= 2 {
            return (
                StandalonePropertyType::Idempotent,
                func_names.first().cloned(),
                func_names.first().cloned(),
                None,
            );
        }
    }

    (StandalonePropertyType::Other, None, None, None)
}

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

/// Named formula **`F_*`** from the Orange Paper (**`SpecParser::formulas()`** **v1**).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FormulaSpec {
    /// Stable id (`F_SubsidyHalf` — validate `^F_[A-Za-z0-9_]+$` at extraction).
    pub id: String,
    /// Section heading id where the **`Formula`** block appeared (e.g. `"6.1"`).
    pub section: String,
    /// Inner LaTeX from the first `$$ … $$` after the **`Formula`** header.
    pub latex_body: String,
    /// Bold **`F_*`** / **`C_*`** ids from **`**Depends on:**`** prose after the **`$$`** block (empty if absent).
    pub depends_on: Vec<String>,
    /// Raw markdown spanning header through closing **`$$`** (drift diagnostics).
    pub raw_markdown: String,
}

/// True when **`#[spec_locked]`** § (**`lock_section`**) equals or strictly prefixes **`formula_section`**
/// (formula is defined under the same § or a deeper subsection — same rule as **`spec_enrich`** / verify).
///
/// Examples: **`6.1`** covers **`6.1.3`**; **`6.1`** does **not** cover **`7.1`**.
pub fn section_id_subsumes_formula_section(lock_section: &str, formula_section: &str) -> bool {
    if lock_section.is_empty() {
        return false;
    }
    if lock_section == formula_section {
        return true;
    }
    formula_section
        .strip_prefix(lock_section)
        .map(|rest| rest.starts_with('.'))
        .unwrap_or(false)
}

/// When **`false`**, **`ingest_formula_blocks`** is skipped for this process (**`SpecParser::formulas()`** stays empty).
///
/// **Unset** or any other value: formulas **enabled** (default).
///
/// Recognized “off” values (trimmed, ASCII-lowercased): **`0`**, **`false`**, **`no`**, **`off`**.
fn formula_block_ingestion_enabled() -> bool {
    match std::env::var("SPEC_LOCK_FORMULAS") {
        Err(_) => true,
        Ok(v) => {
            let x = v.trim().to_ascii_lowercase();
            !matches!(x.as_str(), "0" | "false" | "no" | "off")
        }
    }
}

/// Orange Paper parser
pub struct SpecParser {
    content: String,
    sections: HashMap<String, SpecSection>,
    /// Global **`F_*`** registry (filled during **`parse()`**; duplicates are errors).
    formulas: HashMap<String, FormulaSpec>,
}

/// Standalone property block (e.g. **Property** (Name): ... $$...$$)
#[derive(Debug, Clone)]
pub struct StandaloneProperty {
    /// Property name (e.g. "SegWit Transaction Serialization Round-Trip")
    pub name: String,
    /// Section ID (e.g., "8.2.2")
    pub section_id: String,
    /// Raw LaTeX formula from $$...$$
    pub formula_raw: String,
    /// Parsed property type
    pub property_type: StandalonePropertyType,
    /// For round-trip: outer function (e.g. DeserializeTransactionWithWitness)
    pub outer_func: Option<String>,
    /// For round-trip: inner function (e.g. SerializeTransactionWithWitness)
    pub inner_func: Option<String>,
    /// Constraint from formula (e.g. |w| = |tx.inputs|)
    pub constraint: Option<String>,
}

/// Type of standalone property
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StandalonePropertyType {
    RoundTrip,
    Idempotent,
    Ordering,
    Other,
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
    /// Standalone properties (e.g. **Property** (Name): ... $$...$$)
    pub standalone_properties: Vec<StandaloneProperty>,
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
            formulas: HashMap::new(),
        }
    }

    /// Merge sections and named **`F_*`** formulas from another parser. Errors on duplicate section IDs or formula ids across inputs.
    pub fn merge(&mut self, other: SpecParser) -> Result<(), String> {
        for (id, formula) in other.formulas {
            if self.formulas.contains_key(&id) {
                return Err(format!("Duplicate formula id across merged specs: {id}"));
            }
            self.formulas.insert(id, formula);
        }
        for (id, section) in other.sections {
            if self.sections.contains_key(&id) {
                return Err(format!("Duplicate section ID: {id}"));
            }
            self.sections.insert(id, section);
        }
        Ok(())
    }

    /// Parsed **`F_*`** registry (**v1** grammar).
    pub fn formulas(&self) -> &HashMap<String, FormulaSpec> {
        &self.formulas
    }

    /// **`Depends on`** entries **`F_*`** that are **missing** from the merged formula registry.
    ///
    /// Intended for diagnostics (**`list-formulas`**, workspace docs): cross-file refs must be merged
    /// (**`SpecParser::merge`**) before every expected **`F_*`** id is visible.
    pub fn unresolved_formula_dependencies(&self) -> Vec<(String, String)> {
        let ids: std::collections::HashSet<_> = self.formulas.keys().cloned().collect();
        let mut out = Vec::new();
        for (id, f) in &self.formulas {
            for dep in &f.depends_on {
                if dep.starts_with("F_") && !ids.contains(dep.as_str()) {
                    out.push((id.clone(), dep.clone()));
                }
            }
        }
        out.sort();
        out
    }

    /// Stable **`C_*`** ids (**`ExtractedConstant.name`**) extracted from merged sections whose id starts **`4.`**.
    ///
    /// Used for **`Depends on`** **`C_*`** diagnostics (formula blocks may cite constants not present in merged §**4** excerpts).
    pub fn merged_consensus_constant_ids(&self) -> std::collections::HashSet<String> {
        let mut s = std::collections::HashSet::new();
        for sec in self.sections.values() {
            for c in &sec.constants {
                s.insert(format!("C_{}", c.name));
            }
        }
        s
    }

    /// **`Depends on`** entries **`C_*`** that are **missing** from **`merged_consensus_constant_ids`**.
    ///
    /// Cross-file merges must bring in every **`4.*`** excerpt that defines cited constants (**`constants_stable_id_map`** aligns).
    pub fn unresolved_constant_dependencies(&self) -> Vec<(String, String)> {
        let c_ids = self.merged_consensus_constant_ids();
        let mut out = Vec::new();
        for (id, f) in &self.formulas {
            for dep in &f.depends_on {
                if dep.starts_with("C_") && !c_ids.contains(dep.as_str()) {
                    out.push((id.clone(), dep.clone()));
                }
            }
        }
        out.sort();
        out
    }

    /// **`C_<NAME>`** keys (**`ExtractedConstant.name`**) → consensus constant (**§4**, **`extract_constants_from_section`**).
    ///
    /// Duplicate stable ids conflict unless **`rust_expr`** and **`section`** match.
    pub fn constants_stable_id_map(&self) -> Result<HashMap<String, ExtractedConstant>, String> {
        use std::collections::hash_map::Entry;
        let mut m = HashMap::new();
        for s in self.sections.values() {
            for c in &s.constants {
                let sid = format!("C_{}", c.name);
                match m.entry(sid.clone()) {
                    Entry::Vacant(e) => {
                        e.insert(c.clone());
                    }
                    Entry::Occupied(o) => {
                        let prev = o.get();
                        if prev.rust_expr != c.rust_expr || prev.section != c.section {
                            return Err(format!(
                                "Merged spec: duplicate `{sid}` stable id (sections §{} vs §{})",
                                prev.section, c.section
                            ));
                        }
                    }
                }
            }
        }
        Ok(m)
    }

    fn ingest_formula_blocks(&mut self, section_id: &str, content: &str) -> Result<(), String> {
        let extracted = Self::extract_formulas_for_section(section_id, content)?;
        for spec in extracted {
            let id = spec.id.clone();
            match self.formulas.entry(id) {
                std::collections::hash_map::Entry::Vacant(e) => {
                    e.insert(spec);
                }
                std::collections::hash_map::Entry::Occupied(o) => {
                    return Err(format!(
                        "Duplicate named formula `{}` (already defined under section `{}`)",
                        o.key(),
                        o.get().section
                    ));
                }
            }
        }
        Ok(())
    }

    fn extract_formulas_for_section(
        section_id: &str,
        content: &str,
    ) -> Result<Vec<FormulaSpec>, String> {
        let header_re = Regex::new(r"\*\*Formula\*\*\s*\(\*\*(F_[A-Za-z0-9_]+)\*\*\)\s*:")
            .map_err(|e| format!("Regex error: {e}"))?;
        let mut out = Vec::new();
        let mut seen_section: HashSet<String> = HashSet::new();

        for cap in header_re.captures_iter(content) {
            let id = cap.get(1).unwrap().as_str().to_string();
            if !seen_section.insert(id.clone()) {
                return Err(format!(
                    "Duplicate **Formula** id `{id}` in section `{section_id}`"
                ));
            }
            let header = cap.get(0).unwrap();
            let header_start = header.start();
            let header_end = header.end();
            let tail = &content[header_end..];
            let (latex_body, consumed) = Self::first_display_math_block(tail).map_err(|e| {
                format!("Section `{section_id}` formula `{id}` — display math extraction: {e}")
            })?;
            let raw_markdown = content[header_start..header_end + consumed].to_string();
            let after_formula_abs = header_end + consumed;
            let rest = &content[after_formula_abs..];
            let window_end = header_re
                .find(rest)
                .map(|m| m.start())
                .unwrap_or_else(|| rest.len());
            let depends_on = Self::parse_depends_on_ids(&rest[..window_end]);
            out.push(FormulaSpec {
                id,
                section: section_id.to_string(),
                latex_body,
                depends_on,
                raw_markdown,
            });
        }
        Ok(out)
    }

    /// First balanced `$$ … $$` in `tail` (bytes consumed measured from **`tail`**).
    fn first_display_math_block(tail: &str) -> Result<(String, usize), String> {
        let open = tail
            .find("$$")
            .ok_or_else(|| "missing opening `$$` after **Formula** header".to_string())?;
        let after_open = &tail[open + 2..];
        let inner_end_rel = after_open
            .find("$$")
            .ok_or_else(|| "missing closing `$$` for display math formula".to_string())?;
        let latex_body = after_open[..inner_end_rel].trim().to_string();
        if latex_body.is_empty() {
            return Err("display math `$$ $$` formula is empty".to_string());
        }
        let consumed = open + 2 + inner_end_rel + 2;
        Ok((latex_body, consumed))
    }

    /// **`**Depends on:**`** excerpt after **`$$`**; **`F_*`** / **`C_*`** as **`**…**`** prose (optional inline backticks **` `…` ` **` inside bold).
    fn parse_depends_on_ids(after_formula_excerpt: &str) -> Vec<String> {
        static DEPENDS_ON_BOLD_ID_RE: OnceLock<Regex> = OnceLock::new();
        // Allow optional inline-code backticks inside bold: **`F_x`** common in prose lists.
        let id_re = DEPENDS_ON_BOLD_ID_RE.get_or_init(|| {
            Regex::new(r"\*\*`?((?:F_|C_)[A-Za-z0-9_]+)`?\*\*").expect("depends id regex")
        });
        let Some((idx, hdr_len)) = after_formula_excerpt
            .find("**Depends on**:")
            .map(|i| (i, "**Depends on**:".len()))
            .or_else(|| {
                after_formula_excerpt
                    .find("**Depends on:**")
                    .map(|i| (i, "**Depends on:**".len()))
            })
        else {
            return Vec::new();
        };
        let after = &after_formula_excerpt[idx + hdr_len..];
        let mut out = Vec::new();
        let mut saw_dependency_line = false;
        for line in after.lines() {
            let t = line.trim();
            if t.is_empty() {
                if saw_dependency_line {
                    break;
                }
                continue;
            }
            if t.starts_with("**Formula**") {
                break;
            }
            if t.starts_with('|') || t.starts_with("```") {
                break;
            }
            saw_dependency_line = true;
            for cap in id_re.captures_iter(line) {
                let id = cap.get(1).unwrap().as_str().to_string();
                if id.starts_with("F_") || id.starts_with("C_") {
                    out.push(id);
                }
            }
        }
        out.sort_unstable();
        out.dedup();
        out
    }

    /// Create a parser from one or more spec files. Reads each file, parses, and merges sections.
    /// Errors on duplicate section IDs across files.
    pub fn from_paths<P: AsRef<Path>>(paths: &[P]) -> Result<SpecParser, String> {
        if paths.is_empty() {
            return Err("At least one spec path required".to_string());
        }
        // Proc-macros run with an unreliable cwd; prefer CARGO_MANIFEST_DIR for relative paths.
        // Canonicalize when possible so `manifest/../blvm-spec/PROTOCOL.md` resolves correctly.
        let resolve = |p: &Path| -> Result<PathBuf, String> {
            if p.is_absolute() {
                return std::fs::canonicalize(p).or(Ok(p.to_path_buf()));
            }
            if let Ok(manifest) = std::env::var("CARGO_MANIFEST_DIR") {
                let candidate = PathBuf::from(manifest).join(p);
                if let Ok(c) = std::fs::canonicalize(&candidate) {
                    return Ok(c);
                }
                if candidate.exists() {
                    return Ok(candidate);
                }
            }
            let cwd = std::env::current_dir().map_err(|e| format!("Failed to get cwd: {e}"))?;
            let candidate = cwd.join(p);
            std::fs::canonicalize(&candidate).or(Ok(candidate))
        };
        let p0 = resolve(paths[0].as_ref())?;
        let content = std::fs::read_to_string(&p0)
            .map_err(|e| format!("Failed to read spec {}: {}", p0.display(), e))?;
        let mut parser = SpecParser::new(content);
        parser
            .parse()
            .map_err(|e| format!("Failed to parse spec: {e}"))?;

        for path in paths.iter().skip(1) {
            let p = resolve(path.as_ref())?;
            let content = std::fs::read_to_string(&p)
                .map_err(|e| format!("Failed to read spec {}: {}", p.display(), e))?;
            let mut other = SpecParser::new(content);
            other
                .parse()
                .map_err(|e| format!("Failed to parse spec {}: {}", p.display(), e))?;
            parser.merge(other)?;
        }
        Ok(parser)
    }

    /// Parse the entire Orange Paper (must be called before using other methods)
    pub fn parse(&mut self) -> Result<(), String> {
        // Initialize sections map if not already done
        if self.sections.is_empty() {
            // Parse will populate sections
        }
        // Split into sections by headers (both ### and ##)
        // Match sections like "6.1", "5.2.1", etc.
        let section_re = Regex::new(r"^##+?\s+(\d+(?:\.\d+)*)\s+(.+)$")
            .map_err(|e| format!("Regex error: {e}"))?;

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
                self.sections.insert(
                    section_id.clone(),
                    SpecSection {
                        id: section_id,
                        title,
                        functions: Vec::new(),
                        theorems: Vec::new(),
                        constants: Vec::new(),
                        standalone_properties: Vec::new(),
                        content: String::new(),
                    },
                );
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
        let function_re = Regex::new(r"\*\*(\w+)\*\*:\s*\$?([^\$]+)\$?")
            .map_err(|e| format!("Regex error: {e}"))?;

        let mut functions = Vec::new();

        for cap in function_re.captures_iter(content) {
            let name = cap.get(1).unwrap().as_str().to_string();
            // Skip section headers that look like functions
            if matches!(name.as_str(), "Properties" | "Theorem" | "Formula") {
                continue;
            }
            // Single-word `**…**:` prose/metadata (not operable function specs)
            if matches!(
                name.as_str(),
                "Inputs" | "Activation" | "Deactivation" | "References" | "Mainnet" | "Regtest"
            ) {
                continue;
            }
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

            // Compute this function's block (from after signature to next function).
            // Use "**Name**:" (with colon) to anchor to the real function heading and avoid
            // matching inline bold references like `see **FunctionName** below`.
            let func_marker_colon = format!("**{name}**:");
            let func_marker_plain = format!("**{name}**");
            let block_content: &str = if let Some(func_pos) = content
                .find(&func_marker_colon)
                .or_else(|| content.find(&func_marker_plain))
            {
                // Advance past the marker (use the colon form if found, plain otherwise).
                let marker_len = if content[func_pos..].starts_with(&func_marker_colon) {
                    func_marker_colon.len()
                } else {
                    func_marker_plain.len()
                };
                let start = func_pos + marker_len;
                let remaining = &content[start..];
                let block_end = Self::find_next_function_boundary(remaining);
                &remaining[..block_end]
            } else {
                ""
            };

            // Extract properties and theorems from this function's block only
            self.extract_properties_from_block(&mut func_spec, block_content, &name)?;
            self.extract_theorems(&mut func_spec, block_content)?;

            // Extract formula
            self.extract_formula(&mut func_spec, content, &name)?;

            // Generate contracts from properties
            self.generate_contracts(&mut func_spec)?;

            // NEW: Generate contracts from theorems
            self.generate_contracts_from_theorems(&mut func_spec)?;

            // Populate conditions from contracts
            func_spec.conditions = func_spec
                .contracts
                .iter()
                .map(|c| c.condition.clone())
                .collect();

            functions.push(func_spec);
        }

        // Extract constants for Section 4 (Consensus Constants)
        let mut constants = Vec::new();
        if section_id.starts_with("4.") {
            constants = self.extract_constants_from_section(section_id, content)?;
        }

        // Extract standalone **Property** (Name): ... $$...$$ blocks
        let standalone_properties = self.extract_standalone_properties(section_id, content)?;

        // Extract **`F_*`** formula blocks (**v1**: `**Formula** (**F_Id**):` + first `$$…$$`).
        if formula_block_ingestion_enabled() {
            self.ingest_formula_blocks(section_id, content)?;
        }

        // Sections with Implementation Invariants: add synthetic "*" function so any
        // spec_locked function in this section gets those contracts (e.g. 10.6 Dandelion)
        if let Some(invariant_func) = self.extract_implementation_invariants(section_id, content)? {
            functions.push(invariant_func);
        }

        // Update section with parsed functions, constants, and standalone properties
        if let Some(section) = self.sections.get_mut(section_id) {
            section.content = section_content;
            section.functions = functions;
            section.constants = constants;
            section.standalone_properties = standalone_properties;
        }

        Ok(())
    }

    /// Extract Implementation Invariants block (e.g. 10.6 Dandelion)
    fn extract_implementation_invariants(
        &self,
        section_id: &str,
        content: &str,
    ) -> Result<Option<FunctionSpec>, String> {
        let marker = "**Implementation Invariants**";
        let inv_pos = content
            .find(marker)
            .or_else(|| {
                content.find("**Implementation Invariants (BLVM Specification Lock Verified)**")
            })
            .or_else(|| content.find("**Invariants**"));
        let Some(inv_pos) = inv_pos else {
            return Ok(None);
        };
        let block = &content[inv_pos..];
        let inv_re = Regex::new(r"(?m)^\d+\.\s*\*\*([^*]+)\*\*:\s*\$([^$]+)\$")
            .map_err(|e| format!("Regex error: {e}"))?;
        let mut properties = Vec::new();
        for cap in inv_re.captures_iter(block) {
            properties.push(Property {
                name: cap.get(1).unwrap().as_str().trim().to_string(),
                statement: cap.get(2).unwrap().as_str().trim().to_string(),
                property_type: PropertyType::Invariant,
            });
        }
        if properties.is_empty() {
            return Ok(None);
        }
        let mut func_spec = FunctionSpec {
            name: "*".to_string(),
            section: section_id.to_string(),
            signature: None,
            properties: properties.clone(),
            theorems: Vec::new(),
            contracts: Vec::new(),
            content: String::new(),
            conditions: Vec::new(),
            formula: None,
            description: None,
        };
        self.generate_contracts(&mut func_spec)?;
        Ok(Some(func_spec))
    }

    /// Extract constants from Section 4 (Consensus Constants)
    fn extract_constants_from_section(
        &self,
        section_id: &str,
        content: &str,
    ) -> Result<Vec<ExtractedConstant>, String> {
        let mut constants = Vec::new();

        // Pattern: $CONSTANT_NAME = value$ (description)
        // Examples:
        // $C = 10^8$ (satoshis per BTC, ...)
        // $H = 210,000$ (halving interval, ...)
        // $M_{max} = 21 \times 10^6 \times C$ (maximum money supply, ...)
        let constant_re =
            Regex::new(r"\$([A-Za-z_]+(?:\{[^}]+\})?)\s*=\s*([^$]+)\$\s*(?:\(([^)]+)\))?")
                .map_err(|e| format!("Regex error: {e}"))?;

        // Also match lines that might have constants without parentheses
        let _constant_re_alt = Regex::new(r"\$([A-Za-z_]+(?:\{[^}]+\})?)\s*=\s*([^$]+)\$")
            .map_err(|e| format!("Regex error: {e}"))?;

        for cap in constant_re.captures_iter(content) {
            let name_raw = cap.get(1).unwrap().as_str();
            let value_raw = cap.get(2).unwrap().as_str().trim();
            // Extract description - handle cases where it might be cut off
            let description = cap
                .get(3)
                .map(|m| {
                    let desc = m.as_str().to_string();
                    // Fix common issues: add closing paren if missing, clean up
                    if !desc.ends_with(')') && !desc.contains(')') {
                        format!("{desc})")
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

    /// Extract standalone **Property** (Name): ... $$...$$ blocks
    fn extract_standalone_properties(
        &self,
        section_id: &str,
        content: &str,
    ) -> Result<Vec<StandaloneProperty>, String> {
        let mut properties = Vec::new();
        // Match **Property** (Name): - capture property name
        let property_re = Regex::new(r"\*\*Property\*\*\s*\(([^)]+)\):")
            .map_err(|e| format!("Regex error: {e}"))?;
        let formula_re = Regex::new(r"\$\$([^$]+)\$\$").map_err(|e| format!("Regex error: {e}"))?;

        for cap in property_re.captures_iter(content) {
            let name = cap.get(1).unwrap().as_str().trim().to_string();
            // Find position of this property in content
            let match_start = cap.get(0).unwrap().start();
            // Look for $$...$$ after this property (formula typically on next line)
            let after_prop = &content[match_start..];
            let formula_raw = formula_re
                .captures(after_prop)
                .and_then(|c| c.get(1))
                .map(|m| m.as_str().trim().to_string())
                .unwrap_or_default();

            if formula_raw.is_empty() {
                continue;
            }

            // Parse round-trip: \text{Outer}(\text{Inner}(x)) = x or (tx, w)
            let (property_type, outer_func, inner_func, constraint) =
                parse_round_trip_formula(&formula_raw);

            properties.push(StandaloneProperty {
                name,
                section_id: section_id.to_string(),
                formula_raw: formula_raw.clone(),
                property_type,
                outer_func,
                inner_func,
                constraint,
            });
        }

        Ok(properties)
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
        let mult_exp_c_re =
            Regex::new(r"^(\d+)\*10\^(\d+)\*C$").map_err(|e| format!("Regex error: {e}"))?;
        if let Some(captures) = mult_exp_c_re.captures(&cleaned) {
            let base: u64 = captures
                .get(1)
                .unwrap()
                .as_str()
                .parse()
                .map_err(|_| format!("Invalid base: {value}"))?;
            let exponent: u32 = captures
                .get(2)
                .unwrap()
                .as_str()
                .parse()
                .map_err(|_| format!("Invalid exponent: {value}"))?;
            let multiplier = base * 10u64.pow(exponent);
            let formatted = self.format_number_with_underscores(multiplier);
            // C is u64, so we need to cast for i64 result
            return Ok(("i64".to_string(), format!("({formatted} * C) as i64")));
        }

        // 2. Handle N * 10^M format (without C) - SECOND MOST SPECIFIC
        let mult_exp_re =
            Regex::new(r"^(\d+)\*10\^(\d+)$").map_err(|e| format!("Regex error: {e}"))?;
        if let Some(captures) = mult_exp_re.captures(&cleaned) {
            let base: u64 = captures
                .get(1)
                .unwrap()
                .as_str()
                .parse()
                .map_err(|_| format!("Invalid base: {value}"))?;
            let exponent: u32 = captures
                .get(2)
                .unwrap()
                .as_str()
                .parse()
                .map_err(|_| format!("Invalid exponent: {value}"))?;
            let result = base * 10u64.pow(exponent);
            let formatted = self.format_number_with_underscores(result);
            return Ok(("u64".to_string(), formatted));
        }

        // 3. Handle 10^N format - THIRD
        let exp_re = Regex::new(r"^10\^(\d+)$").map_err(|e| format!("Regex error: {e}"))?;
        if let Some(captures) = exp_re.captures(&cleaned) {
            let exponent: u32 = captures
                .get(1)
                .unwrap()
                .as_str()
                .parse()
                .map_err(|_| format!("Invalid exponent: {value}"))?;
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

        Err(format!("Could not parse constant value: {value}"))
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

    /// `**Word**:` lines that are not Orange Paper function signatures (metadata / prose).
    /// Must not end the previous `**Func**:` block, or enrichment loses **Properties**.
    fn skip_metadata_bold_header_len(after_open_bold: &str) -> Option<usize> {
        let metadata = after_open_bold.starts_with("Properties**")
            || after_open_bold.starts_with("Inputs**")
            || after_open_bold.starts_with("Activation**")
            || after_open_bold.starts_with("Deactivation**")
            || after_open_bold.starts_with("References**")
            || after_open_bold.starts_with("Mainnet**")
            || after_open_bold.starts_with("Regtest**");
        if metadata {
            after_open_bold
                .find(':')
                .map(|colon| colon.saturating_add(1))
        } else {
            None
        }
    }

    /// Find the position where the next function block starts (not **Properties** or **Theorem**)
    fn find_next_function_boundary(content: &str) -> usize {
        let mut search_start = 0;
        while let Some(pos) = content[search_start..].find("**") {
            let abs_pos = search_start + pos;
            let after = &content[abs_pos + 2..];
            if let Some(advance) = Self::skip_metadata_bold_header_len(after) {
                search_start = abs_pos + 2 + advance;
                continue;
            }
            if after.starts_with("Theorem") && !after.starts_with("Theorem** (") {
                // Skip past "Theorem X.Y**" - find the closing **
                if let Some(close) = after.find("**") {
                    search_start = abs_pos + 2 + close + 2;
                } else {
                    search_start = abs_pos + 2;
                }
                continue;
            }
            // Skip inline bold markers (e.g. **BIP 342**, **not**, **important**).
            // A real function spec has its closing ** immediately followed by ':'.
            // Inline bold has its closing ** followed by anything other than ':'.
            match after.find("**") {
                Some(close_pos) => {
                    let after_close = after[close_pos + 2..].trim_start_matches(' ');
                    if !after_close.starts_with(':') {
                        // **Name** (Qualifier): signature — e.g. **SighashScriptCode** (Updated):
                        if after_close.starts_with('(') {
                            if let Some(i) = after_close.find(')') {
                                let rest = after_close[i + 1..].trim_start();
                                if let Some(tail) = rest.strip_prefix(':') {
                                    let tail = tail.trim_start();
                                    // Prose after "(Qualifier):" (e.g. **Definition** (BIP141 …): For each…)
                                    // is not a function boundary; real specs put a single-dollar inline
                                    // type annotation immediately after ':' (e.g. $T_1 \times T_2 \to T_3$).
                                    // Block math formulas ($$...$$) or prose are NOT function type signatures.
                                    let is_inline_math =
                                        tail.starts_with('$') && !tail.starts_with("$$");
                                    if is_inline_math || tail.starts_with('\\') {
                                        return abs_pos;
                                    }
                                }
                            }
                        }
                        // Inline bold — skip past closing **
                        search_start = abs_pos + 2 + close_pos + 2;
                        continue;
                    }
                    // Closing ** is followed by ':' — function spec unless it's a known non-function header
                    let bold = &after[..close_pos];
                    if matches!(
                        bold,
                        "Definition"
                            | "Properties"
                            | "Note"
                            | "Theorem"
                            | "Formula"
                            | "Halving Schedule"
                            | "Required Methods"
                            | "Consensus Requirements"
                            | "Validation Rules"
                            | "Structure"
                    ) {
                        search_start = abs_pos + 2 + close_pos + 2;
                        continue;
                    }
                    // A real function-spec header has a math type annotation immediately after
                    // the colon (e.g. `**Name**: $T_1 \times T_2 \to T_3$`).  Descriptive
                    // subsection headers like `**Precomputed hashes**:` or
                    // `**Sighash type handling**:` are followed by a newline or prose — not
                    // `$`.  Skipping them prevents premature block truncation that would cut
                    // off the `**Properties**:` section for the current function.
                    let type_annotation = after_close[1..].trim_start(); // skip ':'
                    if !type_annotation.starts_with('$') && !type_annotation.starts_with('\\') {
                        search_start = abs_pos + 2 + close_pos + 2;
                        continue;
                    }
                }
                None => {
                    // Unclosed ** marker — skip past it
                    search_start = abs_pos + 2;
                    continue;
                }
            }
            return abs_pos;
        }
        content.len()
    }

    /// Extract properties for a function from its block content (already scoped to this function)
    fn extract_properties_from_block(
        &self,
        func: &mut FunctionSpec,
        block_content: &str,
        _func_name: &str,
    ) -> Result<(), String> {
        // Look for properties list - match "- PropertyName:" or "- **PropertyName**:"
        let property_re = Regex::new(r"(?m)^\s*-\s*(?:\*\*)?([^:*]+)(?:\*\*)?:\s*(.+)$")
            .map_err(|e| format!("Regex error: {e}"))?;

        // Look for "**Properties**:" header (exact - not **Properties** (Updated):)
        // Also try "**Properties**:" with optional space before colon (spec format variation)
        let props_start = block_content
            .find("**Properties**:")
            .or_else(|| block_content.find("**Properties** :"))
            .or_else(|| block_content.find("**Properties** (Updated):"))
            .or_else(|| block_content.find("**Properties** (Updated) :"));
        if std::env::var("SPEC_LOCK_DEBUG_PROPS").is_ok() && func.name == "CalculateTransactionSize"
        {
            eprintln!(
                "PROPS_DEBUG[{}]: props_start={:?} block_content={:?}",
                func.name,
                props_start,
                &block_content[..block_content.len().min(600)]
            );
        }
        if let Some(props_start) = props_start {
            let props_raw = &block_content[props_start..];
            // Stop at the next bold section header (e.g. **Note**:, **Required Methods**:,
            // **Extension field** (BIP 342):, etc.) to avoid capturing non-property bullets
            // from adjacent sections.  The optional `(?:\([^)]*\)\s*)?` handles qualified
            // headers like `**Extension field** (BIP 342):`.
            let section_header_re = Regex::new(r"\*\*[A-Z][^*]+\*\*\s*(?:\([^)]*\)\s*)?:")
                .map_err(|e| format!("Regex error: {e}"))?;
            let props_end = section_header_re
                .find_at(props_raw, 2) // skip the opening **Properties**: itself
                .map(|m| m.start())
                .unwrap_or(props_raw.len());
            let props_section = &props_raw[..props_end];
            if std::env::var("SPEC_LOCK_DEBUG_PROPS").is_ok()
                && func.name == "CalculateTransactionSize"
            {
                eprintln!(
                    "PROPS_DEBUG[{}]: props_end={} props_section={:?}",
                    func.name,
                    props_end,
                    &props_section[..props_section.len().min(200)]
                );
            }
            for cap in property_re.captures_iter(props_section) {
                let name = cap.get(1).unwrap().as_str().trim().to_string();
                let statement = cap.get(2).unwrap().as_str().trim().to_string();

                // Determine property type
                let property_type = if statement.contains("≥")
                    || statement.contains(">=")
                    || statement.contains("≤")
                    || statement.contains("<=")
                    || statement.contains("=")
                {
                    // Usually a postcondition or invariant
                    if statement.contains("result") || statement.contains("return") {
                        PropertyType::Ensures
                    } else {
                        PropertyType::Invariant
                    }
                } else if statement.contains("implies") || statement.contains("⟹") {
                    // A => B: conclusion B is postcondition (ensures when precondition A holds)
                    PropertyType::Ensures
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

        Ok(())
    }

    /// Extract theorems
    fn extract_theorems(&self, func: &mut FunctionSpec, content: &str) -> Result<(), String> {
        // Match: **Theorem X.Y.Z** (Name)
        // Use simple, reliable regex
        let theorem_re = Regex::new(r"\*\*Theorem\s+([\d.]+)\*\*[^(]*\(([^)]+)\)")
            .map_err(|e| format!("Regex error: {e}"))?;
        let latex_block_re =
            Regex::new(r"\$\$([^$]+)\$\$").map_err(|e| format!("Regex error: {e}"))?;
        let inline_math_re = Regex::new(r"\$([^$]+)\$").map_err(|e| format!("Regex error: {e}"))?;

        for cap in theorem_re.captures_iter(content) {
            let number = cap.get(1).unwrap().as_str().to_string();
            let name = cap.get(2).unwrap().as_str().to_string();

            // Extract statement - look for LaTeX math blocks or inline math after theorem
            let mut statement = String::new();

            // Find position of this theorem in content
            let theorem_pos = cap.get(0).unwrap().end();
            let content_after = &content[theorem_pos..];

            // Look for LaTeX math blocks ($$...$$)
            if let Some(latex_cap) = latex_block_re.captures(content_after) {
                if let Some(latex_content) = latex_cap.get(1) {
                    statement = latex_content.as_str().to_string();
                }
            }

            // If no LaTeX block, look for inline math
            if statement.is_empty() {
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
                if potential_statement.contains("∀")
                    || potential_statement.contains("∈")
                    || potential_statement.contains("≥")
                    || potential_statement.contains("≤")
                    || potential_statement.contains("=")
                    || potential_statement.contains(&func.name)
                {
                    statement = potential_statement;
                }
            }

            // Fallback if still empty
            if statement.is_empty() {
                statement = format!("See Orange Paper Theorem {number} for full statement");
            }

            // Look for proof reference
            let proof_ref =
                if content_after.contains("proof") || content_after.contains("verification") {
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
    fn extract_formula(
        &self,
        func: &mut FunctionSpec,
        content: &str,
        func_name: &str,
    ) -> Result<(), String> {
        // Look for LaTeX formula: $$\text{FunctionName}(...) = ...$$
        // Use string search instead of regex to avoid escape issues
        let latex_func = format!(r"\text{{{func_name}}}");
        let latex_func_alt = func_name.to_string(); // Also match without \text{}

        // Find formula blocks (between $$)
        let mut in_formula = false;
        let mut formula_content = String::new();
        let mut lines_in_formula = 0;
        const MAX_FORMULA_LINES: usize = 10; // Limit formula extraction to prevent grabbing too much

        for line in content.lines() {
            if line.contains("$$") {
                if !in_formula {
                    // Start of formula
                    in_formula = true;
                    formula_content = line.to_string();
                    lines_in_formula = 1;
                } else {
                    // End of formula
                    formula_content.push('\n');
                    formula_content.push_str(line);

                    // Check if this formula matches our function
                    if formula_content.contains(&latex_func)
                        || formula_content.contains(&latex_func_alt)
                        || (formula_content.contains("GetBlockSubsidy")
                            && func_name.contains("Subsidy"))
                        || (formula_content.contains("TotalSupply") && func_name.contains("Supply"))
                    {
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
                    formula_content.push('\n');
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
                if i % 2 == 1 {
                    // Odd indices are between $$ markers
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
                if part.to_lowercase().contains(&func_name_lower)
                    || part.contains(&format!(r"\text{{{}}}", func.name))
                {
                    // Translate to Rust contract
                    let condition = self.translate_theorem_statement_to_rust(part, &func.name)?;

                    // Determine contract type based on statement (theorems → ensures)
                    let contract_type = ContractType::Ensures;

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
    fn translate_theorem_statement_to_rust(
        &self,
        statement: &str,
        func_name: &str,
    ) -> Result<String, String> {
        // Use the same translation logic as properties
        self.translate_property_to_rust(statement, func_name)
    }

    /// Translate mathematical property to Rust-like expression
    fn translate_property_to_rust(
        &self,
        statement: &str,
        func_name: &str,
    ) -> Result<String, String> {
        // Simple translation - replace common patterns
        let mut rust_expr = statement.to_string();

        // Replace LaTeX function calls - handle escaped backslashes properly
        // First replace LaTeX \text{FunctionName} format (literal backslash + text)
        let latex_pattern = format!(r"\text{{{func_name}}}");
        rust_expr = rust_expr.replace(&latex_pattern, "result");
        // Also handle escaped version
        let latex_pattern_escaped = format!(r"\\text{{{func_name}}}");
        rust_expr = rust_expr.replace(&latex_pattern_escaped, "result");
        // Then replace plain function name (but not if it's part of a larger word)
        rust_expr = rust_expr.replace(func_name, "result");

        // §5.1.1 heading **SighashScriptCodeWithSigVersion** but properties still spell the 5-arg overload `\text{SighashScriptCode}(...)`.
        if func_name == "SighashScriptCodeWithSigVersion" {
            rust_expr = rust_expr.replace("SighashScriptCode", "result");
        }

        // Replace mathematical operators
        rust_expr = rust_expr.replace("≥", ">=");
        rust_expr = rust_expr.replace("≤", "<=");
        rust_expr = rust_expr.replace("≠", "!=");
        rust_expr = rust_expr.replace("⟹", "=>");
        // LaTeX \land in bitwise context (e.g. seq \land 0x00400000) → Rust &
        rust_expr = rust_expr.replace(r"\land", " & ");

        // For "A => B" (implication), use conclusion B for ensures
        if let Some(arrow) = rust_expr.find("=>") {
            let after = rust_expr[arrow + 2..].trim();
            if !after.is_empty() && !after.contains("=>") {
                rust_expr = after.to_string();
            }
        }

        // Math "=" in comparisons → Rust "==" (equality)
        // Be careful: only in comparison context, not assignment. Replace standalone = between identifiers/numbers
        rust_expr = rust_expr.replace(" = ", " == ");
        if rust_expr.starts_with("= ") {
            rust_expr = rust_expr.replacen("= ", "== ", 1);
        }
        if rust_expr.ends_with(" =") {
            let len = rust_expr.len();
            rust_expr = rust_expr[..len - 2].to_string() + " ==";
        }

        // |result| or |result(args)| (spec cardinality after func rename) → result.len()
        // e.g. §10.1.1 CalculateChecksum: |CalculateChecksum(payload)| = 4 → result.len() == 4
        if let Ok(re) = Regex::new(r"\|result(?:\([^)]*\))?\|\s*==\s*(\d+)") {
            rust_expr = re.replace_all(&rust_expr, "result.len() == $1").to_string();
        }

        // |x| (cardinality) → x.len()
        let cardinality_re = Regex::new(r"\|([a-zA-Z_][a-zA-Z0-9_]*)\|").ok();
        if let Some(re) = cardinality_re {
            rust_expr = re.replace_all(&rust_expr, "${1}.len()").to_string();
        }

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
        // Expand `\text{Name}` to `Name` as a unit. Stripping only `\text{` leaves a stray `}`
        // before `(` (e.g. `\text{SighashScriptCode}(tx,...)` → `SighashScriptCode}(tx,...)`),
        // which breaks drift / lexer parsing for contracts under a differently named heading.
        if let Ok(re) = Regex::new(r"\\text\{([^}]*)\}") {
            rust_expr = re.replace_all(&rust_expr, "$1").to_string();
        }
        rust_expr = rust_expr.replace(r"\{", "{");
        rust_expr = rust_expr.replace(r"\}", "}");

        Ok(rust_expr)
    }

    /// Iterate over all sections (for coverage reports)
    pub fn iter_sections(&self) -> impl Iterator<Item = (&String, &SpecSection)> {
        self.sections.iter()
    }

    /// Find a section by ID
    pub fn find_section(&self, section_id: &str) -> Option<&SpecSection> {
        self.sections.get(section_id)
    }

    /// Find a function specification by section and name
    pub fn find_function(&self, section: &str, name: Option<&str>) -> Option<&FunctionSpec> {
        if let Some(spec_section) = self.sections.get(section) {
            if let Some(func_name) = name {
                spec_section
                    .functions
                    .iter()
                    .find(|f| f.name.eq_ignore_ascii_case(func_name))
                    .or_else(|| {
                        // Fallback: section with Implementation Invariants ("*") applies to any function
                        spec_section.functions.iter().find(|f| f.name == "*")
                    })
            } else {
                spec_section.functions.first()
            }
        } else {
            None
        }
    }

    /// Get all functions in a section
    pub fn get_section_functions(&self, section: &str) -> Vec<&FunctionSpec> {
        self.sections
            .get(section)
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
            if let Some(func_spec) = section
                .functions
                .iter()
                .find(|f| f.name.eq_ignore_ascii_case(func_name))
            {
                return Some((func_spec, section_id));
            }
        }
        None
    }

    /// Find a theorem by function name across all sections
    /// Searches theorem statements for function name mentions
    pub fn find_theorem_by_function_name(&self, func_name: &str) -> Option<(&Theorem, &str, &str)> {
        let func_name_lower = func_name.to_lowercase();
        let func_name_variations = [
            func_name_lower.clone(),
            func_name.to_string(),
            format!("\\text{{{func_name}}}"),
            format!("\\text{{{func_name_lower}}}"),
        ];

        for (section_id, section) in &self.sections {
            for theorem in &section.theorems {
                // Check if theorem statement contains function name
                let theorem_lower = theorem.statement.to_lowercase();
                if func_name_variations.iter().any(|variant| {
                    theorem_lower.contains(variant) || theorem.statement.contains(variant)
                }) {
                    // Find the function in this section
                    if let Some(func_spec) = section
                        .functions
                        .iter()
                        .find(|f| f.name.eq_ignore_ascii_case(func_name))
                    {
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
        // `#### 10.1.1` creates a top-level section key "10.1.1" (not nested under 10.1 content).
        if let Some(section) = self.sections.get(granular_id) {
            return Some((section, granular_id.to_string()));
        }
        // Parse granular ID: "5.1.1" -> section "5.1", subsection "5.1.1"
        let parts: Vec<&str> = granular_id.split('.').collect();
        if parts.len() >= 2 {
            let section_id = parts[0..parts.len() - 1].join(".");
            if let Some(section) = self.sections.get(&section_id) {
                // Check if granular_id matches a subsection pattern
                // For now, check if it's mentioned in section content or theorems
                if section.content.contains(granular_id)
                    || section.theorems.iter().any(|t| t.number == granular_id)
                {
                    return Some((section, granular_id.to_string()));
                }
            }
        }
        None
    }

    /// Get all theorems in a section
    pub fn get_section_theorems(&self, section_id: &str) -> Vec<&Theorem> {
        self.sections
            .get(section_id)
            .map(|s| s.theorems.iter().collect())
            .unwrap_or_default()
    }

    /// Extract all constants from Section 4 (Consensus Constants)
    pub fn extract_constants(&self) -> Vec<&ExtractedConstant> {
        let mut constants = Vec::new();

        // Extract from Section 4.1, 4.2, 4.3, 4.4
        for section_id in &["4.1", "4.2", "4.3", "4.4"] {
            if let Some(section) = self.sections.get(*section_id) {
                constants.extend(section.constants.iter());
            }
        }

        constants
    }

    /// Get constants from a specific section
    pub fn get_section_constants(&self, section_id: &str) -> Vec<&ExtractedConstant> {
        self.sections
            .get(section_id)
            .map(|s| s.constants.iter().collect())
            .unwrap_or_default()
    }

    /// Get all standalone properties (round-trip, etc.) from all sections
    pub fn get_all_standalone_properties(&self) -> Vec<&StandaloneProperty> {
        let mut props = Vec::new();
        for section in self.sections.values() {
            props.extend(section.standalone_properties.iter());
        }
        props
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

#[cfg(test)]
mod formula_extraction_tests {
    use super::{SpecParser, section_id_subsumes_formula_section};
    use std::sync::Mutex;

    /// Serializes env + parser tests (**`SPEC_LOCK_FORMULAS`** affects process-global state).
    static FORMULA_TESTS_MUTEX: Mutex<()> = Mutex::new(());

    struct ScopedSpecLockFormulas {
        prev: Option<String>,
    }

    impl ScopedSpecLockFormulas {
        fn set(value: Option<&str>) -> Self {
            let prev = std::env::var("SPEC_LOCK_FORMULAS").ok();
            match value {
                Some(v) => unsafe { std::env::set_var("SPEC_LOCK_FORMULAS", v) },
                None => unsafe { std::env::remove_var("SPEC_LOCK_FORMULAS") },
            }
            Self { prev }
        }
    }

    impl Drop for ScopedSpecLockFormulas {
        fn drop(&mut self) {
            match self.prev.take() {
                Some(p) => unsafe { std::env::set_var("SPEC_LOCK_FORMULAS", p) },
                None => unsafe { std::env::remove_var("SPEC_LOCK_FORMULAS") },
            }
        }
    }

    #[test]
    fn section_subsumption_for_formula_locks_matches_verify_enrich() {
        assert!(section_id_subsumes_formula_section("6.1", "6.1"));
        assert!(section_id_subsumes_formula_section("6.1", "6.1.3"));
        assert!(!section_id_subsumes_formula_section("6.1", "7.1"));
        assert!(!section_id_subsumes_formula_section("6.1", "61"));
        assert!(!section_id_subsumes_formula_section("", "6.1"));
    }

    fn parse_unsync(md: &str) -> Result<SpecParser, String> {
        let mut p = SpecParser::new(md.to_string());
        p.parse()?;
        Ok(p)
    }

    fn parse(md: &str) -> Result<SpecParser, String> {
        let _guard = FORMULA_TESTS_MUTEX
            .lock()
            .expect("formula tests mutex poisoned");
        parse_unsync(md)
    }

    #[test]
    fn spec_lock_formulas_env_zero_skips_formula_registry() {
        let _guard = FORMULA_TESTS_MUTEX
            .lock()
            .expect("formula tests mutex poisoned");
        let _scoped = ScopedSpecLockFormulas::set(Some("0"));
        let md = r"## 42.99 Toggle

**Formula** (**F_Toggled**):

$$1$$
";
        let p = parse_unsync(md).expect("parse");
        assert!(
            !p.formulas().contains_key("F_Toggled"),
            "SPEC_LOCK_FORMULAS=0 must skip ingestion"
        );
    }

    #[test]
    fn v1_formula_block_populates_registry() {
        let md = r"## 42.42 Test formulas

**Formula** (**F_Hello**):

$$x \leq y$$
";
        let p = parse(md).expect("parse");
        let f = p.formulas().get("F_Hello").expect("F_Hello");
        assert_eq!(f.section, "42.42");
        assert_eq!(f.latex_body, r"x \leq y");
        assert!(f.raw_markdown.contains("**Formula**"));
        assert!(f.raw_markdown.contains("$$"));
    }

    #[test]
    fn formula_depends_on_parses_bold_f_or_c_ids() {
        let md = r"## 42.48 Deps

**Formula** (**F_Dep**):

$$true$$

**Depends on:**
- **`F_Other`** references **`C_SAT`**
";

        let p = parse(md).expect("parse");
        let f = p.formulas().get("F_Dep").expect("F_Dep");
        assert_eq!(
            f.depends_on,
            vec!["C_SAT".to_string(), "F_Other".to_string()]
        );
    }

    #[test]
    fn unresolved_formula_dependencies_lists_missing_f_refs() {
        let md = r"## 42.49 Missing F_

**Formula** (**F_HasHole**):

$$true$$

**Depends on:**
- **`F_NotInRegistry`**
";

        let p = parse(md).expect("parse");
        assert_eq!(
            p.unresolved_formula_dependencies(),
            vec![("F_HasHole".to_string(), "F_NotInRegistry".to_string())]
        );
    }

    #[test]
    fn unresolved_constant_dependencies_lists_missing_c_refs() {
        let md = r"## 42.51 Missing C_

**Formula** (**F_NoC**):

$$true$$

**Depends on:**
- **`C_AbsentConstant`**
";
        let p = parse(md).expect("parse");
        assert!(p.unresolved_formula_dependencies().is_empty());
        assert_eq!(
            p.unresolved_constant_dependencies(),
            vec![("F_NoC".to_string(), "C_AbsentConstant".to_string())]
        );
    }

    #[test]
    fn unresolved_constant_dependencies_resolved_when_section_4_defines_constant() {
        let md = r"## 4.92 Test consensus

$WIT = 1$ (witness).

## 42.52 Refs C_

**Formula** (**F_RefsC**):

$$true$$

**Depends on:**
- **`C_WIT`**
";
        let p = parse(md).expect("parse");
        assert!(p.unresolved_constant_dependencies().is_empty());
        assert!(p.unresolved_formula_dependencies().is_empty());
        assert!(
            p.merged_consensus_constant_ids().contains("C_WIT"),
            "{:?}",
            p.merged_consensus_constant_ids()
        );
    }

    #[test]
    fn duplicate_formula_in_same_section_is_error() {
        let md = r"## 42.43 Test formulas

**Formula** (**F_A**):

$$1$$

**Formula** (**F_A**):

$$2$$
";
        let Err(e) = parse(md) else {
            panic!("expected parse failure for duplicate F_* in one section");
        };
        assert!(
            e.contains("Duplicate **Formula**") || e.contains("F_A"),
            "{e}"
        );
    }

    #[test]
    fn duplicate_formula_across_sections_is_error() {
        let md = r"## 42.44 A section

**Formula** (**F_Same**):

$$1$$

## 42.45 B section

**Formula** (**F_Same**):

$$2$$
";
        assert!(parse(md).is_err());
    }

    #[test]
    fn merge_reports_duplicate_formula_id() {
        let _guard = FORMULA_TESTS_MUTEX
            .lock()
            .expect("formula tests mutex poisoned");
        let a = r"## 1.1 Only

**Formula** (**F_Merge**):

$$a$$
";
        let b = r"## 2.1 Only

**Formula** (**F_Merge**):

$$b$$
";
        let mut p1 = SpecParser::new(a.to_string());
        p1.parse().unwrap();
        let mut p2 = SpecParser::new(b.to_string());
        p2.parse().unwrap();
        let err = p1.merge(p2).unwrap_err();
        assert!(err.contains("Duplicate formula id"), "unexpected: {err}");
    }

    #[test]
    fn formula_without_display_math_is_error() {
        let md = r"## 42.46 Test formulas

**Formula** (**F_NoMath**):

No dollars here.
";
        assert!(parse(md).is_err());
    }

    #[test]
    fn formula_heading_not_parsed_as_function_spec() {
        let md = r"## 42.47 Test formulas

**Formula** (**F_Only**):

$$1$$
";
        let p = parse(md).expect("parse");
        assert!(
            !p.get_section_functions("42.47")
                .iter()
                .any(|f| f.name == "Formula"),
            "Formula must not appear as bogus FunctionSpec"
        );
        assert!(p.formulas().contains_key("F_Only"));
    }

    #[test]
    fn translate_checksum_cardinality_property() {
        let parser = SpecParser::new(String::new());
        let rust = parser
            .translate_property_to_rust(
                r"|\text{CalculateChecksum}(payload)| = 4",
                "CalculateChecksum",
            )
            .expect("translate");
        assert_eq!(rust, "result.len() == 4");
        let parsed =
            crate::parser::condition::extract_parseable_condition(&rust).expect("parseable");
        assert!(
            parsed.contains("result") && parsed.contains("len") && parsed.contains("4"),
            "parsed: {parsed}"
        );
    }

    #[test]
    fn translate_checksum_cardinality_property_dollar_wrapped() {
        let parser = SpecParser::new(String::new());
        let rust = parser
            .translate_property_to_rust(
                r"$|\text{CalculateChecksum}(payload)| = 4$",
                "CalculateChecksum",
            )
            .expect("translate");
        assert_eq!(
            rust, "result.len() == 4",
            "dollar-wrapped spec property must not leave |result(payload)|"
        );
    }
}

#[cfg(test)]
mod depends_on_regex_tests {
    use super::SpecParser;

    #[test]
    fn parse_depends_on_ids_accepts_bold_with_inner_backticks() {
        let s = "\n\n**Depends on:**\n- **`F_Other`** references **`C_SAT`**\n";
        let ids = SpecParser::parse_depends_on_ids(s);
        assert_eq!(ids, vec!["C_SAT".to_string(), "F_Other".to_string()]);
    }
}
