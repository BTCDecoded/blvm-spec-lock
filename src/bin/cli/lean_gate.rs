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
        links.push(AnchorLink {
            function,
            row_id,
            declaration,
            module,
            classification,
            statement_expr,
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
    defeq: &dyn Fn(&str, &AnchorLink) -> Defeq,
) -> Result<EvidenceOverlay, String> {
    let mut overlay = EvidenceOverlay::empty();
    for link in links {
        let row = rows
            .iter()
            .find(|row| row.id == link.row_id)
            .ok_or_else(|| format!("row {} is not in the census", link.row_id))?;
        if link.classification == "lean_formula" || link.classification == "lean_model" {
            lean_census::reject_covered(row.class, true)?;
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
                formula_defeq(defeq(&emitted, link))?;
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
        &|link| axioms_from_manifest(root, link),
        &|module| build_module(root, module),
        &|_emitted, _link| Defeq::Unavailable,
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
    std::fs::read_to_string(&path).map_err(|err| format!("read {}: {err}", path.display()))
}

fn axioms_from_manifest(root: &Path, link: &AnchorLink) -> Result<Vec<String>, String> {
    let path = root.join("spec/db/axiom-manifest.txt");
    let text =
        std::fs::read_to_string(&path).map_err(|err| format!("read axiom manifest: {err}"))?;
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
    }
}
