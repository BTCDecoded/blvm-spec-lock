//! Row census from a btc-lean `rules.yaml`. Counts are rows.
//! Wallet rows are not read. A row is in one class.

use std::collections::BTreeMap;

pub const RESIDUAL: &[&str] = &[
    "BLK-008", "BLK-086", "BLK-087", "INV-022", "INV-023", "INV-057", "INV-117", "INV-130",
    "SCR-030", "SCR-066", "SCR-067", "SCR-070", "SCR-074", "SCR-086", "SWT-026", "TPR-007",
    "TPR-071", "TXV-069",
];

pub const OUT_OF_LEDGER: &[&str] = &[
    "INV-046", "SCR-008", "INV-114", "INV-115", "INV-119", "INV-138",
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RowClass {
    Obsolete,
    Residual,
    OutOfLedger,
    ConsensusFalse,
    Unmapped,
}

impl RowClass {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Obsolete => "obsolete",
            Self::Residual => "residual",
            Self::OutOfLedger => "out_of_ledger",
            Self::ConsensusFalse => "consensus_false",
            Self::Unmapped => "unmapped",
        }
    }

    pub fn excluded_from_coverage(self) -> bool {
        !matches!(self, Self::Unmapped)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CensusRow {
    pub id: String,
    pub status: String,
    pub consensus: bool,
    pub lean_target: String,
    pub class: RowClass,
}

pub fn classify(id: &str, status: &str, consensus: bool) -> RowClass {
    if status == "obsolete" {
        RowClass::Obsolete
    } else if OUT_OF_LEDGER.contains(&id) {
        RowClass::OutOfLedger
    } else if RESIDUAL.contains(&id) {
        RowClass::Residual
    } else if !consensus {
        RowClass::ConsensusFalse
    } else {
        RowClass::Unmapped
    }
}

/// A residual, obsolete, out-of-ledger, or consensus-false row is not covered.
pub fn reject_covered(class: RowClass, covered: bool) -> Result<(), String> {
    if covered && class.excluded_from_coverage() {
        Err(format!(
            "row class {} is excluded from coverage",
            class.as_str()
        ))
    } else {
        Ok(())
    }
}

pub fn parse_rules(text: &str) -> Result<Vec<CensusRow>, String> {
    let mut rows = Vec::new();
    let mut cur: Option<BTreeMap<String, String>> = None;
    let flush = |rows: &mut Vec<CensusRow>, cur: &mut Option<BTreeMap<String, String>>| {
        let Some(map) = cur.take() else {
            return;
        };
        let id = map.get("id").cloned().unwrap_or_default();
        if id.is_empty() {
            return;
        }
        let status = map.get("status").cloned().unwrap_or_default();
        let consensus = map.get("consensus").map(|v| v == "true").unwrap_or(false);
        let lean_target = map.get("lean_target").cloned().unwrap_or_default();
        rows.push(CensusRow {
            class: classify(&id, &status, consensus),
            id,
            status,
            consensus,
            lean_target,
        });
    };
    for raw in text.lines() {
        let line = raw.trim_end();
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        if let Some(rest) = trimmed.strip_prefix("- id:") {
            flush(&mut rows, &mut cur);
            let mut map = BTreeMap::new();
            map.insert("id".to_string(), unquote(rest.trim()));
            cur = Some(map);
            continue;
        }
        if let Some(map) = cur.as_mut() {
            if let Some((key, value)) = trimmed.split_once(':') {
                let key = key.trim();
                if key.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
                    map.insert(key.to_string(), unquote(value.trim()));
                }
            }
        }
    }
    flush(&mut rows, &mut cur);
    if rows.is_empty() {
        return Err("rules.yaml has no rows".to_string());
    }
    Ok(rows)
}

fn unquote(value: &str) -> String {
    let value = value.trim().trim_matches('"').trim_matches('\'');
    value.to_string()
}

pub fn count_classes(rows: &[CensusRow]) -> BTreeMap<&'static str, usize> {
    let mut counts = BTreeMap::new();
    for row in rows {
        *counts.entry(row.class.as_str()).or_insert(0) += 1;
    }
    counts
}

#[cfg(test)]
mod tests {
    use super::*;

    const SAMPLE: &str = r#"
rules:
- id: INV-001
  status: proven
  consensus: true
  lean_target: "BitcoinProofs.AF.PDW22.checkTransaction_vin_empty_reject"
- id: BLK-008
  status: proven
  consensus: true
  lean_target: "BitcoinProofs.AF.PDW50.merkleLevel_append_singleton"
- id: INV-046
  status: proven
  consensus: false
  lean_target: "Bitcoin.Somewhere.policy"
- id: OLD-1
  status: obsolete
  consensus: false
  lean_target: ""
- id: POL-1
  status: proven
  consensus: false
  lean_target: "Bitcoin.Policy.boundary"
"#;

    #[test]
    fn sample_rows_have_one_class_each() {
        let rows = parse_rules(SAMPLE).unwrap();
        assert_eq!(rows.len(), 5);
        assert_eq!(rows[0].class, RowClass::Unmapped);
        assert_eq!(rows[1].class, RowClass::Residual);
        assert_eq!(rows[2].class, RowClass::OutOfLedger);
        assert_eq!(rows[3].class, RowClass::Obsolete);
        assert_eq!(rows[4].class, RowClass::ConsensusFalse);
        assert!(reject_covered(RowClass::Residual, true).is_err());
        assert!(reject_covered(RowClass::Unmapped, false).is_ok());
    }
}
