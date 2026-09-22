//! Mutation harness. Each mutant is a source patch of the production arm.
//!
//! The query is `body ∧ ¬clause`, built by re-parsing that arm.
//! Unpatched is UNSAT. A patch that breaks the clause is SAT.

use crate::translator::production_lock::{
    ProductionFacts, der_high_bit_query, der_leading_zero_query, der_len_query, der_tag_query,
    dup_query, facts_of, merkle_query, money_in_range_query, negative_rejected_query,
    overflow_query,
};
use z3::SatResult;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Shape {
    Pointwise,
    Inductive,
}

impl Shape {
    fn as_str(self) -> &'static str {
        match self {
            Shape::Pointwise => "pointwise",
            Shape::Inductive => "inductive step",
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mutant {
    M1,
    M2,
    M3,
    M4,
    M5,
    M6,
    M7,
    M8,
    M9,
    M10,
    M11,
    M12,
    M13,
    M14,
    M15,
}

impl Mutant {
    const ALL: [Mutant; 15] = [
        Mutant::M1,
        Mutant::M2,
        Mutant::M3,
        Mutant::M4,
        Mutant::M5,
        Mutant::M6,
        Mutant::M7,
        Mutant::M8,
        Mutant::M9,
        Mutant::M10,
        Mutant::M11,
        Mutant::M12,
        Mutant::M13,
        Mutant::M14,
        Mutant::M15,
    ];

    fn id(self) -> &'static str {
        match self {
            Mutant::M1 => "M1",
            Mutant::M2 => "M2",
            Mutant::M3 => "M3",
            Mutant::M4 => "M4",
            Mutant::M5 => "M5",
            Mutant::M6 => "M6",
            Mutant::M7 => "M7",
            Mutant::M8 => "M8",
            Mutant::M9 => "M9",
            Mutant::M10 => "M10",
            Mutant::M11 => "M11",
            Mutant::M12 => "M12",
            Mutant::M13 => "M13",
            Mutant::M14 => "M14",
            Mutant::M15 => "M15",
        }
    }

    fn function(self) -> &'static str {
        match self {
            Mutant::M1
            | Mutant::M2
            | Mutant::M3
            | Mutant::M4
            | Mutant::M5
            | Mutant::M12
            | Mutant::M13 => "check_transaction",
            Mutant::M6 | Mutant::M7 | Mutant::M8 | Mutant::M9 | Mutant::M14 => "is_strict_der",
            Mutant::M10 | Mutant::M11 | Mutant::M15 => "merkle_tree_from_hashes",
        }
    }

    fn change(self) -> &'static str {
        match self {
            Mutant::M1 => "delete the duplicate-input HashSet check",
            Mutant::M2 | Mutant::M13 => "insert txid only",
            Mutant::M3 => "wrapping_add on the production output sum",
            Mutant::M4 => "every production MAX_MONEY compare is >=",
            Mutant::M5 => "drop sign and u64-cast rejects so a negative i64 is Ok",
            Mutant::M6 | Mutant::M14 => "DER length bound 74",
            Mutant::M7 => "drop the leading-zero check on R",
            Mutant::M8 => "drop the high bit check on R",
            Mutant::M9 => "accept tag 0x31",
            Mutant::M10 => "drop the unpadded equal-hash check",
            Mutant::M11 | Mutant::M15 => "compare adjacent hashes after the odd pad",
            Mutant::M12 => "later production value_u64 compare is >=; fast path stays >",
        }
    }

    fn shape(self) -> Shape {
        match self {
            Mutant::M3 | Mutant::M10 | Mutant::M11 | Mutant::M15 => Shape::Inductive,
            _ => Shape::Pointwise,
        }
    }
}

fn consensus_src(file: &str) -> String {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../blvm-consensus/src")
        .join(file);
    std::fs::read_to_string(&path).unwrap_or_else(|err| panic!("read {}: {err}", path.display()))
}

fn extract_fn(src: &str, name: &str) -> String {
    let marker = format!("fn {name}(");
    let start = src
        .find(&marker)
        .unwrap_or_else(|| panic!("missing {name}"));
    let rest = &src[start..];
    let mut depth = 0i32;
    let mut started = false;
    for (i, c) in rest.char_indices() {
        if c == '{' {
            depth += 1;
            started = true;
        } else if c == '}' {
            depth -= 1;
            if started && depth == 0 {
                return rest[..=i].to_string();
            }
        }
    }
    panic!("unbalanced {name}");
}

fn parse_fn(src: &str) -> syn::ItemFn {
    syn::parse_str(src).unwrap_or_else(|err| panic!("parse failed: {err}\n{src}"))
}

fn merge_money(fast: ProductionFacts, main: ProductionFacts) -> ProductionFacts {
    let mut facts = main;
    let mut money = fast.money;
    money.append(&mut facts.money);
    facts.money = money;
    facts
}

fn tx_facts(fast_src: &str, check_src: &str) -> ProductionFacts {
    let fast = facts_of(&parse_fn(fast_src));
    let main = facts_of(&parse_fn(check_src));
    merge_money(fast, main)
}

const DUP_IF: &str = r#"        if !seen_prevouts.insert(&input.prevout) {
            return Ok(ValidationResult::Invalid(format!(
                "Duplicate input prevout at index {i}"
            )));
        }"#;

const MERKLE_CMP: &str = r#"        for pos in (0..hashes.len().saturating_sub(1)).step_by(2) {
            if hashes[pos] == hashes[pos + 1] {
                mutated = true;
            }
        }"#;

const MERKLE_PAD: &str = r#"        if hashes.len() & 1 != 0 {
            hashes.push(hashes[hashes.len() - 1]);
        }"#;

const DER_LEADING: &str = r#"    if len_r > 1 && signature[4] == 0x00 && (signature[5] & 0x80) == 0 {
        return Ok(false);
    }"#;

const DER_HIGH: &str = r#"    if (signature[4] & 0x80) != 0 {
        return Ok(false);
    }"#;

fn patch(
    mutant: Mutant,
    fast: &str,
    check: &str,
    der: &str,
    merkle: &str,
) -> (String, String, String, String) {
    let mut fast = fast.to_string();
    let mut check = check.to_string();
    let mut der = der.to_string();
    let mut merkle = merkle.to_string();
    match mutant {
        Mutant::M1 => {
            check = check.replace(DUP_IF, "");
        }
        Mutant::M2 | Mutant::M13 => {
            check = check.replace(
                "seen_prevouts.insert(&input.prevout)",
                "seen_prevouts.insert(&input.prevout.txid)",
            );
        }
        Mutant::M3 => {
            check = check.replace(".checked_add(output.value)", ".wrapping_add(output.value)");
        }
        Mutant::M4 => {
            fast = fast.replace("value_u64 > MAX_MONEY_U64", "value_u64 >= MAX_MONEY_U64");
            check = check.replace("value_u64 > MAX_MONEY_U64", "value_u64 >= MAX_MONEY_U64");
            check = check.replace("total_u64 > MAX_MONEY_U64", "total_u64 >= MAX_MONEY_U64");
        }
        Mutant::M5 => {
            for src in [&mut fast, &mut check] {
                *src = src.replace(
                    "output.value < 0 || value_u64 > MAX_MONEY_U64",
                    "output.value > MAX_MONEY",
                );
            }
            check = check.replace(
                "total_output_value < 0 || total_u64 > MAX_MONEY_U64",
                "total_output_value > MAX_MONEY",
            );
        }
        Mutant::M6 | Mutant::M14 => {
            der = der.replace("signature.len() > 73", "signature.len() > 74");
        }
        Mutant::M7 => {
            der = der.replace(DER_LEADING, "");
        }
        Mutant::M8 => {
            der = der.replace(DER_HIGH, "");
        }
        Mutant::M9 => {
            der = der.replace(
                "signature[0] != 0x30",
                "signature[0] != 0x30 && signature[0] != 0x31",
            );
        }
        Mutant::M10 => {
            merkle = merkle.replace(MERKLE_CMP, "");
        }
        Mutant::M11 | Mutant::M15 => {
            merkle = merkle.replace(MERKLE_CMP, "");
            merkle = merkle.replace(MERKLE_PAD, &format!("{MERKLE_PAD}\n{MERKLE_CMP}"));
        }
        Mutant::M12 => {
            check = check.replacen("value_u64 > MAX_MONEY_U64", "value_u64 >= MAX_MONEY_U64", 1);
        }
    }
    (fast, check, der, merkle)
}

fn sat_of(result: SatResult) -> &'static str {
    match result {
        SatResult::Unsat => "UNSAT",
        SatResult::Sat => "SAT",
        SatResult::Unknown => "UNKNOWN",
    }
}

fn judge(mutant: Mutant) -> SatResult {
    let tx = consensus_src("transaction.rs");
    let der_file = consensus_src("bip_validation.rs");
    let mining = consensus_src("mining.rs");
    let fast0 = extract_fn(&tx, "check_transaction_fast_path");
    let check0 = extract_fn(&tx, "check_transaction");
    let der0 = extract_fn(&der_file, "is_strict_der");
    let merkle0 = extract_fn(&mining, "merkle_tree_from_hashes");
    let (fast, check, der, merkle) = patch(mutant, &fast0, &check0, &der0, &merkle0);
    match mutant {
        Mutant::M1
        | Mutant::M2
        | Mutant::M3
        | Mutant::M4
        | Mutant::M5
        | Mutant::M12
        | Mutant::M13 => {
            let facts = tx_facts(&fast, &check);
            match mutant {
                Mutant::M1 | Mutant::M2 | Mutant::M13 => dup_query(&facts),
                Mutant::M3 => overflow_query(&facts),
                Mutant::M4 | Mutant::M12 => money_in_range_query(&facts),
                Mutant::M5 => negative_rejected_query(&facts),
                _ => unreachable!(),
            }
        }
        Mutant::M6 | Mutant::M7 | Mutant::M8 | Mutant::M9 | Mutant::M14 => {
            let facts = facts_of(&parse_fn(&der));
            match mutant {
                Mutant::M6 | Mutant::M14 => der_len_query(&facts),
                Mutant::M7 => der_leading_zero_query(&facts),
                Mutant::M8 => der_high_bit_query(&facts),
                Mutant::M9 => der_tag_query(&facts),
                _ => unreachable!(),
            }
        }
        Mutant::M10 | Mutant::M11 | Mutant::M15 => merkle_query(&facts_of(&parse_fn(&merkle))),
    }
}

fn unpatched(which: &str) -> SatResult {
    let tx = consensus_src("transaction.rs");
    let facts = tx_facts(
        &extract_fn(&tx, "check_transaction_fast_path"),
        &extract_fn(&tx, "check_transaction"),
    );
    match which {
        "money" => money_in_range_query(&facts),
        "negative" => negative_rejected_query(&facts),
        "dup" => dup_query(&facts),
        "overflow" => overflow_query(&facts),
        "der_len" => der_len_query(&facts_of(&parse_fn(&extract_fn(
            &consensus_src("bip_validation.rs"),
            "is_strict_der",
        )))),
        "der_high" => der_high_bit_query(&facts_of(&parse_fn(&extract_fn(
            &consensus_src("bip_validation.rs"),
            "is_strict_der",
        )))),
        "der_lead" => der_leading_zero_query(&facts_of(&parse_fn(&extract_fn(
            &consensus_src("bip_validation.rs"),
            "is_strict_der",
        )))),
        "der_tag" => der_tag_query(&facts_of(&parse_fn(&extract_fn(
            &consensus_src("bip_validation.rs"),
            "is_strict_der",
        )))),
        "merkle" => merkle_query(&facts_of(&parse_fn(&extract_fn(
            &consensus_src("mining.rs"),
            "merkle_tree_from_hashes",
        )))),
        _ => panic!("unknown unpatched query {which}"),
    }
}

fn render_table() -> String {
    let mut out = String::new();
    out.push_str("# Spec-lock mutation coverage\n\n");
    out.push_str(
        "Query is `body ∧ ¬clause` on the production arm after a source patch and a re-parse. \
         Unpatched UNSAT means the body meets the clause. Patched SAT means the patch breaks it. \
         A patched query that stays UNSAT is not a lock.\n\n",
    );
    out.push_str("| mutant | function | change | shape | patched |\n");
    out.push_str("|---|---|---|---|---|\n");
    for mutant in Mutant::ALL {
        let result = judge(mutant);
        out.push_str(&format!(
            "| {} | {} | {} | {} | {} |\n",
            mutant.id(),
            mutant.function(),
            mutant.change(),
            mutant.shape().as_str(),
            sat_of(result)
        ));
    }
    out.push_str("\nUnpatched production arms:\n\n");
    for (name, which) in [
        ("output at MAX_MONEY", "money"),
        ("negative output", "negative"),
        ("duplicate prevout", "dup"),
        ("output-sum step", "overflow"),
        ("DER length 74", "der_len"),
        ("DER high bit", "der_high"),
        ("DER leading zero", "der_lead"),
        ("DER tag 0x31", "der_tag"),
        ("merkle mutation", "merkle"),
    ] {
        out.push_str(&format!("- {name}: {}\n", sat_of(unpatched(which))));
    }
    out.push_str(&crate::translator::consensus_set::coverage_markdown());
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::translator::production_lock::mir_matches;

    #[test]
    fn unpatched_production_is_unsat() {
        if !crate::parser::spec_expr::consensus_workspace_present() {
            return;
        }
        for which in [
            "money", "negative", "dup", "overflow", "der_len", "der_high", "der_lead", "der_tag",
            "merkle",
        ] {
            assert_eq!(
                unpatched(which),
                SatResult::Unsat,
                "unpatched {which} must be UNSAT"
            );
        }
    }

    #[test]
    fn every_mutant_is_sat() {
        if !crate::parser::spec_expr::consensus_workspace_present() {
            return;
        }
        for mutant in Mutant::ALL {
            assert_eq!(
                judge(mutant),
                SatResult::Sat,
                "{} stayed UNSAT; the patch did not touch what Z3 sees",
                mutant.id()
            );
        }
    }

    fn mir_text() -> String {
        let deps = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../blvm-consensus/target/debug/deps");
        let mut mirs: Vec<_> = std::fs::read_dir(&deps)
            .unwrap_or_else(|err| panic!("MIR dir {}: {err}", deps.display()))
            .filter_map(|ent| ent.ok())
            .map(|ent| ent.path())
            .filter(|p| p.extension().and_then(|e| e.to_str()) == Some("mir"))
            .collect();
        mirs.sort();
        let path = mirs
            .pop()
            .unwrap_or_else(|| panic!("no production MIR under {}", deps.display()));
        std::fs::read_to_string(path).unwrap()
    }

    fn mir_fn(mir: &str, name: &str) -> String {
        let marker = format!("{name}(");
        let mut out = String::new();
        let mut on = false;
        for line in mir.lines() {
            if line.starts_with("fn ") && line.contains(&marker) && !line.contains("fast_path") {
                on = true;
                out.push_str(line);
                out.push('\n');
                continue;
            }
            if on
                && (line.starts_with("fn ")
                    || line.starts_with("const ")
                    || line.starts_with("static "))
            {
                break;
            }
            if on {
                out.push_str(line);
                out.push('\n');
            }
        }
        assert!(!out.is_empty(), "MIR has no {name}");
        out
    }

    #[test]
    fn mir_correspondence_fails_closed_when_the_compare_changes() {
        let deps = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../blvm-consensus/target/debug/deps");
        if !deps.is_dir() || !crate::parser::spec_expr::consensus_workspace_present() {
            return;
        }
        let mir = mir_text();
        let tx = consensus_src("transaction.rs");
        let tx_mir = mir_fn(&mir, "check_transaction");
        let unpatched_tx = tx_facts(
            &extract_fn(&tx, "check_transaction_fast_path"),
            &extract_fn(&tx, "check_transaction"),
        );
        assert!(
            mir_matches(&unpatched_tx, &tx_mir),
            "unpatched money compare and prevout insert must match the MIR"
        );
        let der = mir_fn(&mir, "is_strict_der");
        let der_facts = facts_of(&parse_fn(&extract_fn(
            &consensus_src("bip_validation.rs"),
            "is_strict_der",
        )));
        assert!(mir_matches(&der_facts, &der));
        let merkle_mir = mir_fn(&mir, "merkle_tree_from_hashes");
        let merkle_facts = facts_of(&parse_fn(&extract_fn(
            &consensus_src("mining.rs"),
            "merkle_tree_from_hashes",
        )));
        assert!(mir_matches(&merkle_facts, &merkle_mir));
        for mutant in [
            Mutant::M1,
            Mutant::M4,
            Mutant::M12,
            Mutant::M6,
            Mutant::M10,
            Mutant::M11,
        ] {
            let tx_src = consensus_src("transaction.rs");
            let (fast, check, der_src, merkle_src) = patch(
                mutant,
                &extract_fn(&tx_src, "check_transaction_fast_path"),
                &extract_fn(&tx_src, "check_transaction"),
                &extract_fn(&consensus_src("bip_validation.rs"), "is_strict_der"),
                &extract_fn(&consensus_src("mining.rs"), "merkle_tree_from_hashes"),
            );
            let (facts, slice) = match mutant {
                Mutant::M1 | Mutant::M4 | Mutant::M12 => (tx_facts(&fast, &check), tx_mir.as_str()),
                Mutant::M6 => (facts_of(&parse_fn(&der_src)), der.as_str()),
                Mutant::M10 | Mutant::M11 => {
                    (facts_of(&parse_fn(&merkle_src)), merkle_mir.as_str())
                }
                _ => unreachable!(),
            };
            assert!(
                !mir_matches(&facts, slice),
                "{} still matches the unpatched MIR",
                mutant.id()
            );
        }
    }

    #[test]
    fn shipping_source_still_has_the_checks_the_mutants_delete() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../blvm-consensus/src");
        if !root.exists() {
            return;
        }
        let tx = std::fs::read_to_string(root.join("transaction.rs")).unwrap();
        let check = tx
            .split("pub fn check_transaction(")
            .nth(1)
            .expect("check_transaction");
        let check = check.split("\npub fn ").next().unwrap();
        assert!(
            check.contains("seen_prevouts.insert"),
            "M1: duplicate-input HashSet check is gone"
        );
        assert!(
            check.contains("&input.prevout"),
            "M2: duplicate check no longer uses the full prevout"
        );
        assert!(
            check.contains("checked_add(output.value)")
                || check.contains(".checked_add(output.value)"),
            "M3: output sum no longer uses checked_add"
        );
        assert!(
            check.contains("output.value > MAX_MONEY")
                || check.contains("value_u64 > MAX_MONEY_U64"),
            "M4: MAX_MONEY comparison is not a strict greater-than"
        );
        assert!(
            check.contains("output.value < 0"),
            "M5: negative output check is gone"
        );
        let der = std::fs::read_to_string(root.join("bip_validation.rs")).unwrap();
        let der = der
            .split("fn is_strict_der(")
            .nth(1)
            .expect("is_strict_der");
        let der = der.split("\nfn ").next().unwrap();
        assert!(
            der.contains("signature.len() > 73"),
            "M6: length 74 is accepted"
        );
        assert!(
            der.contains("== 0x00") && der.contains("0x80"),
            "M7: leading-zero check is gone"
        );
        assert!(
            der.contains("signature[4] & 0x80"),
            "M8: high-bit check on R is gone"
        );
        assert!(
            der.contains("signature[0] != 0x30"),
            "M9: tag is not required to be 0x30"
        );
        let mining = std::fs::read_to_string(root.join("mining.rs")).unwrap();
        let merkle = mining
            .split("fn merkle_tree_from_hashes(")
            .nth(1)
            .expect("merkle_tree_from_hashes");
        let cmp = merkle
            .find("hashes[pos] == hashes[pos + 1]")
            .expect("M10: equal-adjacent check is gone");
        let pad = merkle.find("hashes.len() & 1").expect("odd pad");
        assert!(cmp < pad, "M11: equal-adjacent check is after the odd pad");
        let connect = std::fs::read_to_string(root.join("block/connect.rs")).unwrap();
        assert!(
            !connect.contains("merkle_mutated && !ibd_mode"),
            "IBD still skips the merkle mutation reject"
        );
    }

    #[test]
    fn mutation_table_matches_committed_report() {
        if !crate::parser::spec_expr::consensus_workspace_present() {
            return;
        }
        let table = render_table();
        let path =
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("docs/MUTATION_COVERAGE.md");
        if std::env::var("MUTATION_WRITE").ok().as_deref() == Some("1") {
            if let Some(dir) = path.parent() {
                std::fs::create_dir_all(dir).unwrap();
            }
            std::fs::write(&path, &table).unwrap();
        }
        let on_disk = std::fs::read_to_string(&path).unwrap_or_default();
        assert_eq!(
            on_disk, table,
            "mutation table drifted; write docs/MUTATION_COVERAGE.md from render_table()"
        );
    }
}
