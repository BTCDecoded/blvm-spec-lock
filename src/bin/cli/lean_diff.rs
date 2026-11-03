//! Differential comparison. Agreement is not a proof and is not `lean_formula`.

use sha2::{Digest, Sha256};
use std::path::Path;

pub const DATA_ARCHIVE_SHA256: &str =
    "1ac846bdc24740cfdcf599c3ccf357e48bed50d7fd32071efae605d2a84168b8";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompareRow {
    pub anchor: String,
    pub rust_out: String,
    pub lean_out: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DiffReport {
    pub agreements: Vec<String>,
    pub disagreements: Vec<String>,
}

pub fn sha256_hex(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    format!("{:x}", hasher.finalize())
}

pub fn check_archive(bytes: &[u8], expected: &str) -> Result<(), String> {
    let got = sha256_hex(bytes);
    if got == expected.trim() {
        Ok(())
    } else {
        Err("archive sha256 does not match the pinned release digest".to_string())
    }
}

pub fn read_and_check(path: &Path, expected: &str) -> Result<(), String> {
    let bytes = std::fs::read(path).map_err(|_| "could not read the archive".to_string())?;
    check_archive(&bytes, expected)
}

pub fn compare(rows: &[CompareRow]) -> DiffReport {
    let mut agreements = Vec::new();
    let mut disagreements = Vec::new();
    for row in rows {
        if row.rust_out == row.lean_out {
            agreements.push(row.anchor.clone());
        } else {
            disagreements.push(row.anchor.clone());
        }
    }
    DiffReport {
        agreements,
        disagreements,
    }
}

pub fn load_vectors(text: &str) -> Result<Vec<CompareRow>, String> {
    let value: serde_json::Value =
        serde_json::from_str(text).map_err(|_| "vector file is not JSON".to_string())?;
    let Some(items) = value.as_array() else {
        return Err("vector file must be an array".to_string());
    };
    let mut rows = Vec::new();
    for item in items {
        let anchor = item
            .get("anchor")
            .and_then(|v| v.as_str())
            .ok_or("vector row needs anchor")?
            .to_string();
        let rust_out = item
            .get("rust")
            .and_then(|v| v.as_str())
            .ok_or("vector row needs rust")?
            .to_string();
        let lean_out = item
            .get("lean")
            .and_then(|v| v.as_str())
            .ok_or("vector row needs lean")?
            .to_string();
        rows.push(CompareRow {
            anchor,
            rust_out,
            lean_out,
        });
    }
    Ok(rows)
}

pub fn report_json(report: &DiffReport) -> String {
    serde_json::json!({
        "evidence": "differential",
        "meaning": "agreement of the Rust function and the btc-lean executable on the same inputs; not a proof",
        "agreements": report.agreements,
        "disagreements": report.disagreements,
    })
    .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn digest_rejects_a_different_byte() {
        let bytes = b"not-the-release";
        assert!(check_archive(bytes, DATA_ARCHIVE_SHA256).is_err());
        assert!(check_archive(bytes, &sha256_hex(bytes)).is_ok());
    }

    #[test]
    fn only_matching_rows_are_agreements() {
        let rows = vec![
            CompareRow {
                anchor: "a".to_string(),
                rust_out: "1".to_string(),
                lean_out: "1".to_string(),
            },
            CompareRow {
                anchor: "b".to_string(),
                rust_out: "1".to_string(),
                lean_out: "2".to_string(),
            },
        ];
        let report = compare(&rows);
        assert_eq!(report.agreements, vec!["a".to_string()]);
        assert_eq!(report.disagreements, vec!["b".to_string()]);
        let json = report_json(&report);
        assert!(json.contains("\"evidence\":\"differential\""));
        assert!(!json.contains("lean_formula"));
    }
}
