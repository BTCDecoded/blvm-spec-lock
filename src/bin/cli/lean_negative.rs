//! Each of these cases must fail the Lean gate.

use super::lean_census::{CensusRow, RowClass};
use super::lean_gate::{AnchorLink, Defeq, overlay_for_links};

fn row(id: &str, class: RowClass) -> CensusRow {
    CensusRow {
        id: id.to_string(),
        status: "proven".to_string(),
        consensus: class != RowClass::ConsensusFalse,
        lean_target: String::new(),
        class,
    }
}

fn link(classification: &str) -> AnchorLink {
    AnchorLink {
        function: "block_weight".to_string(),
        row_id: "BLK-025".to_string(),
        declaration: "BitcoinProofs.AF.PDW51.blockWeight_row".to_string(),
        module: "BitcoinProofs.AF.PDW51.PDW51".to_string(),
        classification: classification.to_string(),
        statement_expr: Some("result >= 0".to_string()),
        definition: Some("blockWeight".to_string()),
    }
}

fn ok_source() -> String {
    "theorem blockWeight_row : blockWeight = 0 := rfl\n".to_string()
}

fn run(
    links: &[AnchorLink],
    rows: &[CensusRow],
    source: &str,
    axioms: &[&str],
    build_ok: bool,
    defeq: Defeq,
) -> Result<(), String> {
    overlay_for_links(
        links,
        rows,
        &|_| Ok(source.to_string()),
        &|_| Ok(axioms.iter().map(|s| (*s).to_string()).collect()),
        &|_| {
            if build_ok {
                Ok(())
            } else {
                Err("cited module build exited 1".to_string())
            }
        },
        &|_, _| Ok(defeq),
    )
    .map(|_| ())
}

#[test]
fn sorry_fails_the_gate() {
    let err = run(
        &[link("lean_model")],
        &[row("BLK-025", RowClass::Unmapped)],
        "theorem blockWeight_row : blockWeight = 0 := sorry\n",
        &["propext"],
        true,
        Defeq::Equal,
    );
    assert!(err.unwrap_err().contains("sorry"));
}

#[test]
fn added_axiom_fails_the_gate() {
    let err = run(
        &[link("lean_model")],
        &[row("BLK-025", RowClass::Unmapped)],
        &ok_source(),
        &["propext", "sorryAx"],
        true,
        Defeq::Equal,
    );
    assert!(err.unwrap_err().contains("allowlist"));
}

#[test]
fn changed_statement_fails_the_gate() {
    let err = run(
        &[link("lean_formula")],
        &[row("BLK-025", RowClass::Unmapped)],
        &ok_source(),
        &["propext"],
        true,
        Defeq::Different,
    );
    assert!(err.unwrap_err().contains("definitionally"));
}

#[test]
fn renamed_theorem_fails_the_gate() {
    let err = run(
        &[link("lean_model")],
        &[row("BLK-025", RowClass::Unmapped)],
        "theorem other_name : blockWeight = 0 := rfl\n",
        &["propext"],
        true,
        Defeq::Equal,
    );
    assert!(err.unwrap_err().contains("not in the cited source"));
}

#[test]
fn different_definition_fails_the_gate() {
    let mut linked = link("lean_model");
    linked.definition = Some("getBlockSubsidy".to_string());
    let err = run(
        &[linked],
        &[row("BLK-025", RowClass::Unmapped)],
        &ok_source(),
        &["propext"],
        true,
        Defeq::Equal,
    );
    assert!(err.unwrap_err().contains("getBlockSubsidy"));
}

#[test]
fn residual_row_is_not_covered() {
    let mut linked = link("lean_formula");
    linked.row_id = "BLK-008".to_string();
    let err = run(
        &[linked],
        &[row("BLK-008", RowClass::Residual)],
        &ok_source(),
        &["propext"],
        true,
        Defeq::Equal,
    );
    assert!(err.unwrap_err().contains("residual"));
}

#[test]
fn covering_link_needs_a_definition() {
    let mut linked = link("lean_model");
    linked.definition = None;
    let err = run(
        &[linked],
        &[row("BLK-025", RowClass::Unmapped)],
        &ok_source(),
        &["propext"],
        true,
        Defeq::Equal,
    );
    assert!(err.unwrap_err().contains("definition"));
}

#[test]
fn cited_module_that_does_not_build_fails() {
    let err = run(
        &[link("lean_model")],
        &[row("BLK-025", RowClass::Unmapped)],
        &ok_source(),
        &["propext"],
        false,
        Defeq::Equal,
    );
    assert!(err.unwrap_err().contains("build"));
}
