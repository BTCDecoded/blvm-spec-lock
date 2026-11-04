//! Golden snapshots for Orange Paper parsing (`SpecParser`).
//!
//! Run with `INSTA_UPDATE=always cargo test golden_` after intentional parser changes.

#[allow(dead_code)]
#[path = "../src/parser/mod.rs"]
mod parser;

use parser::orange_paper::SpecParser;
use std::path::PathBuf;

fn format_parser_snapshot(parser: &SpecParser) -> String {
    let mut ids: Vec<_> = parser.iter_sections().map(|(id, _)| id.clone()).collect();
    ids.sort();
    let mut out = String::new();
    for id in ids {
        let sec = parser
            .find_section(&id)
            .unwrap_or_else(|| panic!("missing section {id}"));
        out.push_str(&format!("## section {} | {}\n", sec.id, sec.title.trim()));

        for c in &sec.constants {
            out.push_str(&format!(
                "  const {} = {} | rust_expr={} | rust_type={} | desc={}\n",
                c.name, c.value, c.rust_expr, c.rust_type, c.description
            ));
        }

        for sp in &sec.standalone_properties {
            out.push_str(&format!(
                "  standalone {} | type={:?} | outer={:?} | inner={:?} | constraint={:?}\n",
                sp.name, sp.property_type, sp.outer_func, sp.inner_func, sp.constraint
            ));
            out.push_str(&format!("    formula_raw: {}\n", sp.formula_raw));
        }

        for f in &sec.functions {
            out.push_str(&format!(
                "  fn {} | signature={:?} | formulas={:?}\n",
                f.name, f.signature, f.formula
            ));
            for p in &f.properties {
                out.push_str(&format!(
                    "    property {} {:?}: {}\n",
                    p.name, p.property_type, p.statement
                ));
            }
            for t in &f.theorems {
                out.push_str(&format!(
                    "    theorem {} ({}): {}\n",
                    t.number, t.name, t.statement
                ));
            }
            for ctr in &f.contracts {
                out.push_str(&format!(
                    "    contract {:?}: {}\n",
                    ctr.contract_type, ctr.condition
                ));
            }
        }
    }
    out
}

fn golden_path(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/golden")
        .join(format!("{name}.md"))
}

#[test]
fn protocol_calculate_checksum_contracts() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../blvm-spec/PROTOCOL.md");
    if !path.exists() {
        return;
    }
    let parser = SpecParser::from_paths(&[&path]).expect("parse PROTOCOL.md");
    let func = parser
        .find_function("10.1.1", Some("CalculateChecksum"))
        .expect("CalculateChecksum in 10.1.1");
    for ctr in &func.contracts {
        eprintln!("contract {:?}: {}", ctr.contract_type, ctr.condition);
    }
    assert!(
        func.contracts
            .iter()
            .all(|c| !c.condition.contains("|result")),
        "contracts must use result.len(), got: {:?}",
        func.contracts
    );
}

#[test]
fn golden_minimal_function() {
    let path = golden_path("minimal_function");
    let parser = SpecParser::from_paths(&[&path]).expect("parse golden minimal_function");
    insta::assert_snapshot!(format_parser_snapshot(&parser));
}

#[test]
fn golden_constants_fragment() {
    let path = golden_path("constants_fragment");
    let parser = SpecParser::from_paths(&[&path]).expect("parse golden constants_fragment");
    insta::assert_snapshot!(format_parser_snapshot(&parser));
}

#[test]
fn golden_standalone_property() {
    let path = golden_path("standalone_property");
    let parser = SpecParser::from_paths(&[&path]).expect("parse golden standalone_property");
    insta::assert_snapshot!(format_parser_snapshot(&parser));
}
