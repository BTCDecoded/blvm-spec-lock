//! Lean gate for a pinned btc-lean checkout.
//!
//! An anchor is Lean-covered only when the pin matches, the static gates pass,
//! the cited module builds, the cited source has no `sorry` or `admit`, the
//! cited declaration's axioms stay inside the allowlist, and a `lean_formula`
//! link is definitionally the emitted formula. A missing checkout does not
//! mark anything covered.

use super::lean_census::{self, CensusRow, RowClass};
use super::lean_evidence::{AnchorLean, EvidenceOverlay, LeanStatus};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

pub const PIN: &str = include_str!("../../../docs/btc-lean/PIN");
pub const ALLOWLIST: &str = include_str!("../../../docs/btc-lean/axiom-allowlist.txt");

#[derive(Clone, Debug)]
pub struct AnchorLink {
    pub function: String,
    pub row_id: String,
    pub declaration: String,
    pub module: String,
    pub classification: String,
    pub statement_expr: Option<String>,
    pub definition: Option<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Defeq {
    Equal,
    Different,
    Unavailable,
}

pub fn pin_matches(actual: &str, expected: &str) -> Result<(), String> {
    let actual = actual.trim();
    let expected = expected.trim();
    if actual == expected {
        Ok(())
    } else {
        Err(format!("btc-lean pin is {actual}, expected {expected}"))
    }
}

pub fn allowlist() -> Vec<&'static str> {
    ALLOWLIST
        .lines()
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .collect()
}

/// Words `sorry` and `admit` outside a `--` comment.
pub fn sorry_or_admit(src: &str) -> Option<&'static str> {
    for line in src.lines() {
        let code = line.split("--").next().unwrap_or(line);
        if code
            .split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
            .any(|w| w == "sorry")
        {
            return Some("sorry");
        }
        if code
            .split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
            .any(|w| w == "admit")
        {
            return Some("admit");
        }
    }
    None
}

pub fn axioms_outside<'a>(found: impl IntoIterator<Item = &'a str>, allow: &[&str]) -> Vec<String> {
    found
        .into_iter()
        .map(str::trim)
        .filter(|name| !name.is_empty() && !allow.contains(name))
        .map(str::to_string)
        .collect()
}

pub fn parse_print_axioms(text: &str) -> Vec<String> {
    let mut names = Vec::new();
    if let Some(start) = text.find('[') {
        if let Some(end) = text[start..].find(']') {
            let inner = &text[start + 1..start + end];
            for part in inner.split(',') {
                let name = part.trim().trim_matches('\'');
                if !name.is_empty() {
                    names.push(name.to_string());
                }
            }
        }
    }
    names
}

pub fn module_built(exit: i32) -> Result<(), String> {
    if exit == 0 {
        Ok(())
    } else {
        Err(format!("cited module build exited {exit}"))
    }
}

pub fn formula_defeq(outcome: Defeq) -> Result<(), String> {
    match outcome {
        Defeq::Equal => Ok(()),
        Defeq::Different => {
            Err("theorem type is not definitionally equal to the emitted formula".to_string())
        }
        Defeq::Unavailable => Err(
            "Lean elaborator is not available; a lean_formula anchor stays uncovered".to_string(),
        ),
    }
}

/// Outcome of starting `lake env lean` on a probe that is not stored in the checkout.
#[derive(Clone, Debug)]
pub enum ProbeStart {
    Missing,
    Ran {
        code: i32,
        stdout: String,
        stderr: String,
    },
}

pub fn axiom_probe_source(module: &str, declaration: &str) -> Result<String, String> {
    lean_name(module)?;
    lean_name(declaration)?;
    Ok(format!("import {module}\n#print axioms {declaration}\n"))
}

pub fn defeq_probe_source(
    module: &str,
    declaration: &str,
    emitted: &str,
) -> Result<String, String> {
    lean_name(module)?;
    lean_name(declaration)?;
    emitted_is_probe_safe(emitted)?;
    Ok(format!(
        "import {module}\nexample : ({emitted}) := {declaration}\n"
    ))
}

pub fn defeq_from_probe(start: ProbeStart) -> Result<Defeq, String> {
    match start {
        ProbeStart::Missing => Ok(Defeq::Unavailable),
        ProbeStart::Ran { code: 0, .. } => Ok(Defeq::Equal),
        ProbeStart::Ran { stderr, .. } if stderr.to_lowercase().contains("type mismatch") => {
            Ok(Defeq::Different)
        }
        ProbeStart::Ran { .. } => {
            Err("elaborator could not check the cited declaration".to_string())
        }
    }
}

pub fn axioms_from_probe(start: ProbeStart, declaration: &str) -> Result<Vec<String>, String> {
    match start {
        ProbeStart::Missing => Err(
            "Lean elaborator is not available; the cited declaration stays uncovered".to_string(),
        ),
        ProbeStart::Ran {
            code: 0, stdout, ..
        } => axiom_line(&stdout, declaration),
        ProbeStart::Ran { .. } => Err("elaborator could not print axioms".to_string()),
    }
}

pub fn axiom_line(text: &str, declaration: &str) -> Result<Vec<String>, String> {
    let Some(line) = text.lines().find(|line| {
        line.contains(&format!("'{declaration}'"))
            && (line.contains("depends on axioms")
                || line.contains("does not depend on any axioms"))
    }) else {
        return Err(format!("{declaration} has no #print axioms line"));
    };
    if line.contains("does not depend on any axioms") {
        return Ok(Vec::new());
    }
    let names = parse_print_axioms(line);
    if names.is_empty() {
        return Err(format!("{declaration} axiom line has no names"));
    }
    Ok(names)
}

pub fn same_axioms(live: &[String], manifest: &[String]) -> bool {
    let mut live = live.to_vec();
    let mut manifest = manifest.to_vec();
    live.sort();
    manifest.sort();
    live == manifest
}

fn lean_name(value: &str) -> Result<(), String> {
    if value.is_empty() {
        return Err("lean name is empty".to_string());
    }
    for part in value.split('.') {
        let mut chars = part.chars();
        let Some(first) = chars.next() else {
            return Err("lean name is not an identifier".to_string());
        };
        if !first.is_ascii_alphabetic() && first != '_' {
            return Err("lean name is not an identifier".to_string());
        }
        if !chars.all(|c| c.is_ascii_alphanumeric() || c == '_') {
            return Err("lean name is not an identifier".to_string());
        }
    }
    Ok(())
}

fn emitted_is_probe_safe(emitted: &str) -> Result<(), String> {
    if emitted.is_empty()
        || emitted.contains('\n')
        || emitted.contains('\r')
        || emitted.contains("--")
        || emitted.contains("/-")
        || emitted.contains("sorry")
        || emitted.contains("admit")
        || emitted.contains("import")
        || emitted.contains('#')
        || emitted.contains(':')
        || emitted.contains(';')
    {
        return Err("emitted formula is not a single proposition".to_string());
    }
    Ok(())
}

pub fn declaration_present(source: &str, declaration: &str) -> Result<(), String> {
    let name = declaration.rsplit('.').next().unwrap_or(declaration);
    if source.contains(&format!("theorem {name}")) || source.contains(&format!("lemma {name}")) {
        Ok(())
    } else {
        Err(format!(
            "declaration {declaration} is not in the cited source"
        ))
    }
}

/// `lean_formula` is the emitted proposition. Any other class is not that proposition.
pub fn same_proposition(classification: &str) -> bool {
    classification == "lean_formula"
}

pub fn locate_checkout() -> Result<Option<PathBuf>, String> {
    if let Ok(raw) = std::env::var("BTC_LEAN_ROOT") {
        let path = PathBuf::from(&raw);
        if path.join("spec/db/rules.yaml").is_file() {
            Ok(Some(path))
        } else {
            Err("BTC_LEAN_ROOT is set but spec/db/rules.yaml is not there".to_string())
        }
    } else {
        let sibling = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../btc-lean");
        if sibling.join("spec/db/rules.yaml").is_file() {
            Ok(Some(sibling))
        } else {
            Ok(None)
        }
    }
}

pub fn read_pin_head(root: &Path) -> Result<String, String> {
    let output = Command::new("git")
        .arg("-C")
        .arg(root)
        .args(["rev-parse", "HEAD"])
        .output()
        .map_err(|err| format!("git rev-parse failed: {err}"))?;
    if !output.status.success() {
        return Err("git rev-parse failed".to_string());
    }
    Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
}

pub fn run_static_gates(root: &Path) -> Result<(), String> {
    let status = Command::new("make")
        .arg("gates")
        .current_dir(root)
        .status()
        .map_err(|err| format!("make gates failed to start: {err}"))?;
    if status.success() {
        Ok(())
    } else {
        Err("btc-lean static gates failed".to_string())
    }
}

pub fn load_links(text: &str) -> Result<Vec<AnchorLink>, String> {
    let value: serde_json::Value =
        serde_json::from_str(text).map_err(|err| format!("anchor map: {err}"))?;
    let Some(items) = value.as_array() else {
        return Err("anchor map must be an array".to_string());
    };
    let mut links = Vec::new();
    for item in items {
        let function = item
            .get("function")
            .and_then(|v| v.as_str())
            .ok_or("anchor map entry needs function")?
            .to_string();
        let row_id = item
            .get("row_id")
            .and_then(|v| v.as_str())
            .ok_or("anchor map entry needs row_id")?
            .to_string();
        let declaration = item
            .get("declaration")
            .and_then(|v| v.as_str())
            .ok_or("anchor map entry needs declaration")?
            .to_string();
        let module = item
            .get("module")
            .and_then(|v| v.as_str())
            .ok_or("anchor map entry needs module")?
            .to_string();
        let classification = item
            .get("classification")
            .and_then(|v| v.as_str())
            .unwrap_or("unmapped")
            .to_string();
        let statement_expr = item
            .get("statement_expr")
            .and_then(|v| v.as_str())
            .map(str::to_string);
        let definition = item
            .get("definition")
            .and_then(|v| v.as_str())
            .map(str::to_string);
        links.push(AnchorLink {
            function,
            row_id,
            declaration,
            module,
            classification,
            statement_expr,
            definition,
        });
    }
    Ok(links)
}

pub fn overlay_for_links(
    links: &[AnchorLink],
    rows: &[CensusRow],
    sources: &dyn Fn(&AnchorLink) -> Result<String, String>,
    axioms_of: &dyn Fn(&AnchorLink) -> Result<Vec<String>, String>,
    build: &dyn Fn(&str) -> Result<(), String>,
    defeq: &dyn Fn(&str, &AnchorLink) -> Result<Defeq, String>,
) -> Result<EvidenceOverlay, String> {
    let mut overlay = EvidenceOverlay::empty();
    for link in links {
        let row = rows
            .iter()
            .find(|row| row.id == link.row_id)
            .ok_or_else(|| format!("row {} is not in the census", link.row_id))?;
        if link.classification == "lean_formula" || link.classification == "lean_model" {
            lean_census::reject_covered(row.class, true)?;
            if link.definition.as_deref().unwrap_or("").is_empty() {
                return Err(format!(
                    "{} needs the Lean definition it is about",
                    link.declaration
                ));
            }
        }
        if row.class != RowClass::Unmapped && link.classification != row.class.as_str() {
            return Err(format!(
                "row {} is {}, not {}",
                row.id,
                row.class.as_str(),
                link.classification
            ));
        }
        let source = sources(link)?;
        if let Some(hit) = sorry_or_admit(&source) {
            return Err(format!("{} contains {hit}", link.declaration));
        }
        declaration_present(&source, &link.declaration)?;
        if let Some(definition) = &link.definition {
            if !source.contains(definition) {
                return Err(format!(
                    "{} does not mention {definition}",
                    link.declaration
                ));
            }
        }
        build(&link.module)?;
        let found = axioms_of(link)?;
        let allow = allowlist();
        let extra = axioms_outside(found.iter().map(String::as_str), &allow);
        if !extra.is_empty() {
            return Err(format!(
                "axioms outside the allowlist: {}",
                extra.join(", ")
            ));
        }
        let status = match link.classification.as_str() {
            "lean_formula" => {
                let expr = link
                    .statement_expr
                    .as_deref()
                    .ok_or("lean_formula link needs statement_expr")?;
                let parsed: syn::Expr = syn::parse_str(expr)
                    .map_err(|err| format!("statement_expr did not parse: {err}"))?;
                let emitted = crate::parser::lean_emit::emit_lean_statement(&parsed)
                    .map_err(|err| format!("{}: {}", err.marker, err.detail))?;
                formula_defeq(defeq(&emitted, link)?)?;
                if !same_proposition(&link.classification) {
                    return Err("classification is not lean_formula".to_string());
                }
                LeanStatus::Formula
            }
            "lean_model" => LeanStatus::Model,
            _ => {
                return Err(format!(
                    "classification {} cannot cover an anchor",
                    link.classification
                ));
            }
        };
        overlay.insert(
            &link.function,
            AnchorLean {
                row_id: link.row_id.clone(),
                declaration: link.declaration.clone(),
                classification: link.classification.clone(),
                covered: true,
                status,
            },
        );
    }
    Ok(overlay)
}

pub fn run_required(root: &Path) -> Result<super::lean_evidence::EvidenceOverlay, String> {
    let head = read_pin_head(root)?;
    pin_matches(&head, PIN)?;
    run_static_gates(root)?;
    let rules = std::fs::read_to_string(root.join("spec/db/rules.yaml"))
        .map_err(|err| format!("read rules.yaml: {err}"))?;
    let rows = lean_census::parse_rules(&rules)?;
    if rows.len() != 726 {
        return Err(format!("census has {} rows, expected 726", rows.len()));
    }
    let counts = lean_census::count_classes(&rows);
    expect_count(&counts, "obsolete", 50)?;
    expect_count(&counts, "residual", 18)?;
    expect_count(&counts, "out_of_ledger", 6)?;
    expect_count(&counts, "consensus_false", 59)?;
    expect_count(&counts, "unmapped", 593)?;
    let map_path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("docs/btc-lean/anchor-map.json");
    let map_text =
        std::fs::read_to_string(&map_path).map_err(|err| format!("read anchor map: {err}"))?;
    let links = load_links(&map_text)?;
    if links.is_empty() {
        return Ok(super::lean_evidence::EvidenceOverlay::empty());
    }
    overlay_for_links(
        &links,
        &rows,
        &|link| read_decl_source(root, link),
        &|link| cited_axioms(root, link),
        &|module| build_module(root, module),
        &|emitted, link| check_defeq(root, emitted, link),
    )
}

fn expect_count(
    counts: &std::collections::BTreeMap<&str, usize>,
    key: &str,
    want: usize,
) -> Result<(), String> {
    let got = counts.get(key).copied().unwrap_or(0);
    if got == want {
        Ok(())
    } else {
        Err(format!("{key} count is {got}, expected {want}"))
    }
}

fn read_decl_source(root: &Path, link: &AnchorLink) -> Result<String, String> {
    let rel = link.module.replace('.', "/");
    let path = root.join("spec/proofs").join(format!("{rel}.lean"));
    std::fs::read_to_string(&path).map_err(|_| format!("could not read module {}", link.module))
}

fn cited_axioms(root: &Path, link: &AnchorLink) -> Result<Vec<String>, String> {
    let source = axiom_probe_source(&link.module, &link.declaration)?;
    let live = axioms_from_probe(spawn_probe(root, &source)?, &link.declaration)?;
    let manifest = axioms_from_manifest(root, link)?;
    if !same_axioms(&live, &manifest) {
        return Err(format!(
            "{} #print axioms does not match the manifest",
            link.declaration
        ));
    }
    Ok(live)
}

fn check_defeq(root: &Path, emitted: &str, link: &AnchorLink) -> Result<Defeq, String> {
    let source = defeq_probe_source(&link.module, &link.declaration, emitted)?;
    defeq_from_probe(spawn_probe(root, &source)?)
}

fn spawn_probe(root: &Path, source: &str) -> Result<ProbeStart, String> {
    static PROBE_SEQ: AtomicU64 = AtomicU64::new(0);
    let n = PROBE_SEQ.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!("spec-lock-lean-{}-{n}.lean", std::process::id()));
    std::fs::write(&path, source)
        .map_err(|_| "could not write the elaborator probe".to_string())?;
    let output = Command::new("lake")
        .args(["env", "lean"])
        .arg(&path)
        .current_dir(root.join("spec/proofs"))
        .output();
    let _ = std::fs::remove_file(&path);
    match output {
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => Ok(ProbeStart::Missing),
        Err(_) => Err("elaborator failed to start".to_string()),
        Ok(output) => Ok(ProbeStart::Ran {
            code: output.status.code().unwrap_or(1),
            stdout: String::from_utf8_lossy(&output.stdout).to_string(),
            stderr: String::from_utf8_lossy(&output.stderr).to_string(),
        }),
    }
}

fn axioms_from_manifest(root: &Path, link: &AnchorLink) -> Result<Vec<String>, String> {
    let path = root.join("spec/db/axiom-manifest.txt");
    let text = std::fs::read_to_string(&path)
        .map_err(|_| "could not read the axiom manifest".to_string())?;
    let needle = format!("'{}'", link.declaration);
    let Some(line) = text.lines().find(|line| line.contains(&needle)) else {
        return Err(format!(
            "{} has no #print axioms entry in the manifest",
            link.declaration
        ));
    };
    Ok(parse_print_axioms(line))
}

fn build_module(root: &Path, module: &str) -> Result<(), String> {
    let status = Command::new("lake")
        .args(["build", module])
        .current_dir(root.join("spec/proofs"))
        .status()
        .map_err(|err| format!("lake build failed to start: {err}"))?;
    module_built(status.code().unwrap_or(1))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pin_and_axioms_and_sorry() {
        assert!(pin_matches("abc", "abc").is_ok());
        assert!(pin_matches("abc", "def").is_err());
        assert_eq!(sorry_or_admit("theorem t : True := sorry"), Some("sorry"));
        assert_eq!(
            sorry_or_admit("-- sorry\ntheorem t : True := trivial"),
            None
        );
        assert_eq!(
            sorry_or_admit("theorem t : True := by admit"),
            Some("admit")
        );
        let extra = axioms_outside(
            ["propext", "sorryAx"],
            &["propext", "Classical.choice", "Quot.sound"],
        );
        assert_eq!(extra, vec!["sorryAx".to_string()]);
        assert!(module_built(1).is_err());
        assert!(formula_defeq(Defeq::Unavailable).is_err());
        assert!(formula_defeq(Defeq::Different).is_err());
        assert!(formula_defeq(Defeq::Equal).is_ok());
        let probe = axiom_probe_source(
            "BitcoinProofs.AF.PDW51",
            "BitcoinProofs.AF.PDW51.blockWeight_row",
        )
        .unwrap();
        assert!(probe.contains("#print axioms"));
        assert!(axiom_probe_source("Bad-Name", "T").is_err());
        assert!(defeq_probe_source("M", "T", "result = 0\nimport X").is_err());
        assert_eq!(
            defeq_from_probe(ProbeStart::Missing).unwrap(),
            Defeq::Unavailable
        );
        assert_eq!(
            defeq_from_probe(ProbeStart::Ran {
                code: 1,
                stdout: String::new(),
                stderr: "type mismatch".to_string(),
            })
            .unwrap(),
            Defeq::Different
        );
        assert!(
            defeq_from_probe(ProbeStart::Ran {
                code: 1,
                stdout: String::new(),
                stderr: "unknown module".to_string(),
            })
            .is_err()
        );
        let names = axiom_line(
            "'Bitcoin.Data.moneyRange_zero' does not depend on any axioms\n",
            "Bitcoin.Data.moneyRange_zero",
        )
        .unwrap();
        assert!(names.is_empty());
        let names = axiom_line(
            "'Bitcoin.DataLaws.bip68Enabled_iff' depends on axioms: [propext]\n",
            "Bitcoin.DataLaws.bip68Enabled_iff",
        )
        .unwrap();
        assert_eq!(names, vec!["propext".to_string()]);
        assert!(same_axioms(
            &["Quot.sound".to_string(), "propext".to_string()],
            &["propext".to_string(), "Quot.sound".to_string()]
        ));
        assert!(axioms_from_probe(ProbeStart::Missing, "T").is_err());
    }
}
