//! Evidence set on one Orange Paper anchor.
//!
//! A set can name more than one status. The summary counts each anchor in
//! one slot, so the slot totals add up to the number of anchors.

use super::verify::{FunctionToVerify, VerificationResult};
use std::collections::BTreeMap;

pub const Z3_CONTRACT: &str = "z3_contract";
pub const LEAN_FORMULA: &str = "lean_formula";
pub const LEAN_MODEL: &str = "lean_model";
pub const DIFFERENTIAL: &str = "differential";
pub const NONE: &str = "none";
pub const CHAIN_SLOT: &str = "z3_contract+lean_formula";

pub const SLOTS: &[&str] = &[
    NONE,
    Z3_CONTRACT,
    LEAN_FORMULA,
    LEAN_MODEL,
    DIFFERENTIAL,
    CHAIN_SLOT,
];

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LeanStatus {
    Formula,
    Model,
    Differential,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AnchorLean {
    pub row_id: String,
    pub declaration: String,
    pub classification: String,
    pub covered: bool,
    pub status: LeanStatus,
}

#[derive(Clone, Debug, Default)]
pub struct EvidenceOverlay {
    by_function: BTreeMap<String, AnchorLean>,
}

impl EvidenceOverlay {
    pub fn empty() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, function: &str, lean: AnchorLean) {
        self.by_function.insert(function.to_string(), lean);
    }

    pub fn get(&self, function: &str) -> Option<&AnchorLean> {
        self.by_function.get(function)
    }

    pub fn len(&self) -> usize {
        self.by_function.len()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Assigned {
    pub evidence: Vec<&'static str>,
    pub slot: &'static str,
    pub lean_row_id: Option<String>,
    pub lean_declaration: Option<String>,
    pub lean_classification: String,
    pub lean_covered: bool,
}

pub fn assign(body_translated: bool, lean: Option<&AnchorLean>) -> Assigned {
    let mut evidence = Vec::new();
    if body_translated {
        evidence.push(Z3_CONTRACT);
    }
    let (row_id, declaration, classification, covered) =
        if let Some(item) = lean.filter(|item| item.covered) {
            match item.status {
                LeanStatus::Formula => evidence.push(LEAN_FORMULA),
                LeanStatus::Model => evidence.push(LEAN_MODEL),
                LeanStatus::Differential => evidence.push(DIFFERENTIAL),
            }
            (
                Some(item.row_id.clone()),
                Some(item.declaration.clone()),
                item.classification.clone(),
                true,
            )
        } else if let Some(item) = lean {
            (
                Some(item.row_id.clone()),
                Some(item.declaration.clone()),
                item.classification.clone(),
                false,
            )
        } else {
            (None, None, "unmapped".to_string(), false)
        };
    if evidence.is_empty() {
        evidence.push(NONE);
    }
    let slot = exclusive_slot(&evidence);
    Assigned {
        evidence,
        slot,
        lean_row_id: row_id,
        lean_declaration: declaration,
        lean_classification: classification,
        lean_covered: covered,
    }
}

pub fn exclusive_slot(evidence: &[&str]) -> &'static str {
    let has = |name: &str| evidence.contains(&name);
    if has(Z3_CONTRACT) && has(LEAN_FORMULA) {
        CHAIN_SLOT
    } else if has(LEAN_FORMULA) {
        LEAN_FORMULA
    } else if has(LEAN_MODEL) {
        LEAN_MODEL
    } else if has(DIFFERENTIAL) {
        DIFFERENTIAL
    } else if has(Z3_CONTRACT) {
        Z3_CONTRACT
    } else {
        NONE
    }
}

pub fn tally(rows: &[Assigned]) -> BTreeMap<&'static str, usize> {
    let mut counts = BTreeMap::new();
    for slot in SLOTS {
        counts.insert(*slot, 0);
    }
    for row in rows {
        *counts.get_mut(row.slot).expect("slot") += 1;
    }
    counts
}

pub fn from_verify(
    func: &FunctionToVerify,
    result: &VerificationResult,
    overlay: &EvidenceOverlay,
) -> Assigned {
    let body = matches!(
        result,
        VerificationResult::Passed {
            body_translated: true
        }
    );
    assign(body, overlay.get(&func.function_name))
}

pub fn human_line(
    results: &[(FunctionToVerify, VerificationResult)],
    overlay: &EvidenceOverlay,
) -> String {
    let rows: Vec<Assigned> = results
        .iter()
        .map(|(func, result)| from_verify(func, result, overlay))
        .collect();
    let counts = tally(&rows);
    let mut line = String::from("  Evidence slots:");
    for slot in SLOTS {
        line.push_str(&format!(" {slot}={}", counts[slot]));
    }
    line.push('\n');
    line
}

#[cfg(test)]
mod tests {
    use super::*;

    fn formula(covered: bool) -> AnchorLean {
        AnchorLean {
            row_id: "BLK-025".to_string(),
            declaration: "BitcoinProofs.AF.PDW51.blockWeight_row".to_string(),
            classification: "lean_formula".to_string(),
            covered,
            status: LeanStatus::Formula,
        }
    }

    #[test]
    fn body_pass_is_only_z3() {
        let row = assign(true, None);
        assert_eq!(row.evidence, vec![Z3_CONTRACT]);
        assert_eq!(row.slot, Z3_CONTRACT);
        assert!(!row.lean_covered);
        assert_eq!(row.lean_classification, "unmapped");
    }

    #[test]
    fn static_pass_is_none() {
        let row = assign(false, None);
        assert_eq!(row.evidence, vec![NONE]);
        assert_eq!(row.slot, NONE);
    }

    #[test]
    fn formula_and_z3_count_once() {
        let lean = formula(true);
        let row = assign(true, Some(&lean));
        assert_eq!(row.evidence, vec![Z3_CONTRACT, LEAN_FORMULA]);
        assert_eq!(row.slot, CHAIN_SLOT);
        let counts = tally(&[row, assign(true, None)]);
        assert_eq!(counts[CHAIN_SLOT], 1);
        assert_eq!(counts[Z3_CONTRACT], 1);
        assert_eq!(counts[LEAN_FORMULA], 0);
        assert_eq!(counts.values().sum::<usize>(), 2);
    }

    #[test]
    fn uncovered_formula_does_not_enter_the_set() {
        let lean = formula(false);
        let row = assign(true, Some(&lean));
        assert_eq!(row.evidence, vec![Z3_CONTRACT]);
        assert_eq!(row.lean_row_id.as_deref(), Some("BLK-025"));
        assert!(!row.lean_covered);
    }

    #[test]
    fn model_and_z3_count_as_model() {
        let lean = AnchorLean {
            status: LeanStatus::Model,
            classification: "lean_model".to_string(),
            ..formula(true)
        };
        let row = assign(true, Some(&lean));
        assert_eq!(row.evidence, vec![Z3_CONTRACT, LEAN_MODEL]);
        assert_eq!(row.slot, LEAN_MODEL);
    }
}
