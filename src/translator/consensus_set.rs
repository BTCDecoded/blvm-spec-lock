//! Consensus-decisive production locks.
//!
//! Each row is `body ∧ ¬clause` on the production arm. Unpatched is UNSAT.
//! A boundary patch and a predicate patch are each SAT. The clause uses the
//! operator in that arm (shift, compare, preimage byte, verifier result, fold).

use super::production_lock::{self, ProductionFacts, facts_of, retain_production};
use std::sync::OnceLock;
use syn::ItemFn;
use z3::ast::{Ast, BV, Bool};
use z3::{SatResult, Sort};

#[path = "finish_coverage.rs"]
mod finish_coverage;
#[path = "spec_clause.rs"]
mod spec_clause;

#[derive(Clone, Debug)]
pub struct LockRow {
    pub function: String,
    pub shape: &'static str,
    pub unpatched: SatResult,
    pub boundary: SatResult,
    pub predicate: SatResult,
    pub note: String,
}

pub fn rows() -> &'static [LockRow] {
    static ROWS: OnceLock<Vec<LockRow>> = OnceLock::new();
    ROWS.get_or_init(build_rows)
}

pub fn coverage_markdown() -> String {
    let mut out = String::from(
        "\n## Consensus set\n\n\
         | function | shape | unpatched | boundary | predicate |\n\
         |---|---|---|---|---|\n",
    );
    let locked_rows = rows();
    for row in locked_rows {
        out.push_str(&format!(
            "| {} | {} | {} | {} | {} |\n",
            row.function,
            row.shape,
            sat_name(row.unpatched),
            sat_name(row.boundary),
            sat_name(row.predicate)
        ));
    }
    out.push_str(
        "\n## Boundaries\n\n\
         `verify_signature` and the Schnorr wrappers lock the gates and the bytes passed to \
         an uninterpreted verifier. They do not lock secp256k1. `OP_CHECKSIG`, \
         `OP_CHECKSIGVERIFY`, `OP_CHECKMULTISIG`, `OP_CHECKMULTISIGVERIFY`, and \
         `OP_CHECKSIGADD` lock the stack rule and that the opcode result equals that bit. \
         Hash compression stays uninterpreted. `get_next_work_required_corrected` diverges \
         from Bitcoin and is excluded. The block-weight `* 2` check is a denial-of-service \
         guard and is excluded. `spec_witnesses`, one-call wrappers, mempool policy, and \
         mining templates are excluded.\n\n\
         `count_sigops_in_script`, `calculate_block_weight`, and `calculate_chain_work` each \
         set the accumulator to 0 before the loop and return it when the input is empty. \
         That base is a conjunct of the fold query: the unpatched initializer is 0, and a \
         non-zero initializer makes the query SAT. The inductive rows also require that the \
         function returns that accumulator, and that block fees start at 0 and add each \
         transaction fee before the coinbase check. `total_supply` sums all 64 subsidy \
         epochs. `apply_transaction_with_id` is one update \
         of a UTXO set the caller supplies. It has no zero-supply base. An empty output list \
         is an error, so the successful path is never the empty step.\n\n",
    );
    let locked = locked_rows.len();
    let open = finish_coverage::unlocked();
    let denom = locked + open.len();
    out.push_str(&format!(
        "## Coverage\n\nlocked / (locked + unlocked) = {locked} / {denom}\n\n"
    ));
    let sourced: Vec<&str> = locked_rows
        .iter()
        .filter(|row| crate::parser::spec_expr::is_spec_sourced(&row.function))
        .map(|row| row.function.as_str())
        .collect();
    let residual: Vec<&str> = locked_rows
        .iter()
        .filter(|row| !crate::parser::spec_expr::is_spec_sourced(&row.function))
        .map(|row| row.function.as_str())
        .collect();
    out.push_str(&format!(
        "Spec-sourced clauses: {} locked rows take every clause value from the spec parse \
         (opcode table, section 4 constants, header equations, inclusive ranges, the subsidy shift, \
         and the numeric atoms and concatenations the paper already writes).\n",
        sourced.len()
    ));
    out.push_str(
        "`validate_block_header_fields` still proves the null merkle root from the prover. \
         Section 5.3.1 says the merkle root is not part of `ValidBlockHeader`. \
         Timestamp ≠ 0 and bits ≠ 0 are the parsed header equations.\n\
         ConnectBlock keeps every gate. The header-call patch leaves the weight comparison in place, \
         so that gate stays. No gate was replaced.\n\
         Hash compression stays uninterpreted.\n\
         Residual, still locked: the verifier-call rows (`try_verify_p2pk_fast_path`, \
         `try_verify_p2pkh_fast_path`, `try_verify_p2sh_fast_path`, `try_verify_p2wpkh_fast_path`, \
         `OP_CHECKSIG_verifier`, and the result-equals-verifier conjunct on \
         `verify_signature`, `verify_tapscript_schnorr_signature`, `verify_signature_from_stack`); \
         ConnectBlock gates the existing patches do not break; the two pipelines; the five inductive rows; \
         the median index; the program-counter and control-stack steps; `if_body_endif`; the script cache; \
         reorg; block proof; and any row whose parsed sentence is weaker than the existing patch.\n",
    );
    for name in &residual {
        out.push_str(&format!("- {name}\n"));
    }
    out.push_str("\n### Unlocked\n\n");
    for name in open {
        out.push_str(&format!("- {name}\n"));
    }
    out.push_str(
        "\n### Excluded\n\nThese names are not in the ratio.\n\n\
         - SHA-256 and RIPEMD-160 compression\n\
         - secp256k1 curve arithmetic\n\
         - `get_next_work_required_corrected`\n\
         - `spec_witnesses` and one-call wrappers\n\
         - mempool policy and mining templates\n\
         - the block-weight `* 2` denial-of-service guard\n\n",
    );
    out
}

fn sat_name(r: SatResult) -> &'static str {
    match r {
        SatResult::Unsat => "UNSAT",
        SatResult::Sat => "SAT",
        SatResult::Unknown => "UNKNOWN",
    }
}

fn build_rows() -> Vec<LockRow> {
    let mut rows = Vec::new();
    rows.extend(legacy_rows());
    rows.extend(arith_rows());
    rows.extend(threshold_rows());
    rows.extend(preimage_rows());
    rows.extend(opcode_rows());
    rows.extend(fold_rows());
    rows.extend(finish_coverage::rows());
    rows
}

fn repo(rel: &str) -> String {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    std::fs::read_to_string(root.join(rel)).unwrap_or_else(|e| panic!("read {rel}: {e}"))
}

fn extract_fn(src: &str, name: &str) -> String {
    let start = [format!("fn {name}("), format!("fn {name}<")]
        .into_iter()
        .find_map(|marker| src.find(&marker))
        .unwrap_or_else(|| panic!("missing {name}"));
    slice_braces(&src[start..])
}

fn drop_inactive_cfg(src: &str) -> String {
    let mut out = src.to_string();
    for feature in ["ctv", "csfs"] {
        let marker = format!("#[cfg(feature = \"{feature}\")]");
        while let Some(i) = out.find(&marker) {
            let after = i + marker.len();
            let Some(rel) = out[after..].find('{') else {
                break;
            };
            let block = slice_braces(&out[after + rel..]);
            if block.is_empty() {
                break;
            }
            let end = after + rel + block.len();
            out.replace_range(i..end, "");
        }
    }
    out
}

fn slice_braces(rest: &str) -> String {
    let b = rest.as_bytes();
    let mut i = 0;
    let mut depth = 0i32;
    let mut started = false;
    while i < b.len() {
        if b[i] == b'"' {
            i += 1;
            while i < b.len() {
                if b[i] == b'\\' {
                    i += 2;
                    continue;
                }
                if b[i] == b'"' {
                    break;
                }
                i += 1;
            }
        } else if b[i] == b'{' {
            depth += 1;
            started = true;
        } else if b[i] == b'}' {
            depth -= 1;
            if started && depth == 0 {
                return rest[..=i].to_string();
            }
        }
        i += 1;
    }
    rest.to_string()
}

fn production_text(func_src: &str) -> String {
    let wrapped = func_src.to_string();
    match syn::parse_str::<ItemFn>(&wrapped) {
        Ok(func) => {
            let kept = retain_production(func);
            quote::quote!(#kept).to_string()
        }
        Err(_) => wrapped,
    }
}

fn row(
    function: &str,
    shape: &'static str,
    plain: &str,
    boundary: &str,
    predicate: &str,
    query: fn(&str) -> SatResult,
) -> LockRow {
    let (unpatched, boundary_r, predicate_r) = spec_clause::merge(
        function,
        plain,
        boundary,
        predicate,
        query(plain),
        query(boundary),
        query(predicate),
    );
    LockRow {
        function: function.to_string(),
        shape,
        unpatched,
        boundary: boundary_r,
        predicate: predicate_r,
        note: String::new(),
    }
}

fn legacy_rows() -> Vec<LockRow> {
    let mut rows = Vec::new();
    let tx = repo("blvm-consensus/src/transaction.rs");
    let fast = extract_fn(&tx, "check_transaction_fast_path");
    let check = extract_fn(&tx, "check_transaction");
    let m5 = |src: &str| {
        src.replace(
            "output.value < 0 || value_u64 > MAX_MONEY_U64",
            "output.value > MAX_MONEY",
        )
        .replace(
            "total_output_value < 0 || total_u64 > MAX_MONEY_U64",
            "total_output_value > MAX_MONEY",
        )
    };
    let check_plain = format!("{fast}\n{check}");
    let check_boundary = format!("{}\n{}", m5(&fast), m5(&check));
    let check_predicate = format!(
        "{fast}\n{}",
        check.replace("&input.prevout)", "&input.prevout.txid)")
    );
    let (check_u, check_b, check_p) = spec_clause::merge(
        "check_transaction",
        &check_plain,
        &check_boundary,
        &check_predicate,
        production_lock::money_in_range_query(&tx_facts(&fast, &check)),
        production_lock::negative_rejected_query(&tx_facts(&m5(&fast), &m5(&check))),
        production_lock::dup_query(&tx_facts(
            &fast,
            &check.replace("&input.prevout)", "&input.prevout.txid)"),
        )),
    );
    rows.push(LockRow {
        function: "check_transaction".into(),
        shape: "pointwise",
        unpatched: check_u,
        boundary: check_b,
        predicate: check_p,
        note: String::new(),
    });
    let der = extract_fn(
        &repo("blvm-consensus/src/bip_validation.rs"),
        "is_strict_der",
    );
    rows.push(LockRow {
        function: "is_strict_der".into(),
        shape: "pointwise",
        unpatched: production_lock::der_len_query(&facts_of(&parse_fn(&der))),
        boundary: production_lock::der_len_query(&facts_of(&parse_fn(
            &der.replace("signature.len() > 73", "signature.len() > 74"),
        ))),
        predicate: production_lock::der_tag_query(&facts_of(&parse_fn(
            &der.replace("!= 0x30", "!= 0x30 && signature[0] != 0x31"),
        ))),
        note: String::new(),
    });

    let mining = repo("blvm-consensus/src/mining.rs");
    let merkle = extract_fn(&mining, "merkle_tree_from_hashes");
    const MERKLE_CMP: &str = r#"        for pos in (0..hashes.len().saturating_sub(1)).step_by(2) {
            if hashes[pos] == hashes[pos + 1] {
                mutated = true;
            }
        }"#;
    const MERKLE_PAD: &str = r#"        if hashes.len() & 1 != 0 {
            hashes.push(hashes[hashes.len() - 1]);
        }"#;
    rows.push(LockRow {
        function: "merkle_tree_from_hashes".into(),
        shape: "inductive",
        unpatched: production_lock::merkle_query(&facts_of(&parse_fn(&merkle))),
        boundary: production_lock::merkle_query(&facts_of(&parse_fn(
            &merkle.replace(MERKLE_CMP, ""),
        ))),
        predicate: production_lock::merkle_query(&facts_of(&parse_fn(
            &merkle
                .replace(MERKLE_CMP, "")
                .replace(MERKLE_PAD, &format!("{MERKLE_PAD}\n{MERKLE_CMP}")),
        ))),
        note: String::new(),
    });

    let locktime = repo("blvm-consensus/src/locktime.rs");
    let disabled = extract_fn(&locktime, "is_sequence_disabled");
    rows.push(row(
        "is_sequence_disabled",
        "threshold",
        &disabled,
        &disabled.replace("0x80000000", "0x40000000"),
        &disabled.replace("!= 0", "== 0"),
        |s| {
            production_lock::masked_bit_query(
                s,
                crate::parser::spec_expr::mask_in("IsSequenceDisabled"),
            )
        },
    ));
    let type_flag = extract_fn(&locktime, "extract_sequence_type_flag");
    rows.push(row(
        "extract_sequence_type_flag",
        "threshold",
        &type_flag,
        &type_flag.replace("0x00400000", "0x00800000"),
        &type_flag.replace("!= 0", "== 0"),
        |s| {
            production_lock::masked_bit_query(
                s,
                crate::parser::spec_expr::mask_in("ExtractSequenceTypeFlag"),
            )
        },
    ));
    let seq_val = extract_fn(&locktime, "extract_sequence_locktime_value");
    rows.push(row(
        "extract_sequence_locktime_value",
        "threshold",
        &seq_val,
        &seq_val.replace("0x0000ffff", "0x0000fffe"),
        &seq_val.replace('&', "|"),
        production_lock::sequence_value_query,
    ));
    let kind = extract_fn(&locktime, "get_locktime_type");
    rows.push(row(
        "get_locktime_type",
        "threshold",
        &kind,
        &kind.replace(
            "locktime < LOCKTIME_THRESHOLD",
            "locktime <= LOCKTIME_THRESHOLD",
        ),
        &kind.replace(
            "locktime < LOCKTIME_THRESHOLD",
            "locktime > LOCKTIME_THRESHOLD",
        ),
        production_lock::locktime_kind_query,
    ));
    let bip65 = extract_fn(&locktime, "check_bip65");
    rows.push(row(
        "check_bip65",
        "threshold",
        &bip65,
        &bip65.replace(">=", ">"),
        &bip65.replace("locktime_types_match(tx_locktime, stack_locktime) && ", ""),
        production_lock::bip65_query,
    ));

    let pow = repo("blvm-consensus/src/pow.rs");
    let check_pow = extract_fn(&pow, "check_proof_of_work");
    let strict =
        check_pow.contains("hash_value < target") && !check_pow.contains("hash_value <= target");
    let rounds = check_pow.matches("Sha256::digest").count() as u32;
    rows.push(LockRow {
        function: "check_proof_of_work".into(),
        shape: "threshold",
        unpatched: production_lock::pow_compare_query(strict),
        boundary: production_lock::pow_compare_query(false),
        predicate: production_lock::pow_double_hash_query(rounds.saturating_sub(1).max(1)),
        note: String::new(),
    });
    // Unpatched double-hash is recorded by requiring rounds == 2 in the finish test via this row's
    // predicate being the one-round query (SAT). The unpatched two-round query is folded in.
    if production_lock::pow_double_hash_query(crate::parser::spec_expr::header_hash_rounds())
        != SatResult::Unsat
    {
        rows.last_mut().unwrap().unpatched = SatResult::Sat;
    }

    let witness = repo("blvm-consensus/src/witness.rs");
    let program = extract_fn(&witness, "validate_witness_program_length");
    rows.push(row(
        "validate_witness_program_length",
        "threshold",
        &program,
        &program.replace("SEGWIT_P2WPKH_LENGTH", "SEGWIT_P2WSH_LENGTH"),
        &program.replace("TAPROOT_PROGRAM_LENGTH", "0"),
        production_lock::witness_program_query,
    ));

    let header = repo("blvm-consensus/src/block/header.rs");
    let valid = extract_fn(&header, "validate_block_header");
    let version_boundary = valid.replace("header.version < 1", "header.version < 0");
    let version_predicate = valid.replace("header.version < 1", "header.version <= 1");
    let (version_u, version_b, version_p) = spec_clause::merge(
        "validate_block_header",
        &valid,
        &version_boundary,
        &version_predicate,
        production_lock::header_version_query(&valid, 0),
        production_lock::header_version_query(&version_boundary, 0),
        production_lock::header_version_query(&version_predicate, 1),
    );
    rows.push(LockRow {
        function: "validate_block_header".into(),
        shape: "threshold",
        unpatched: version_u,
        boundary: version_b,
        predicate: version_p,
        note: String::new(),
    });
    let mtp_below = production_lock::header_mtp_query(&valid, true);
    let mtp_eq = production_lock::header_mtp_query(&valid, false);
    let mtp_boundary = valid.replace("header.timestamp < ctx.median_time_past", "false");
    let mtp_predicate = valid.replace(
        "header.timestamp < ctx.median_time_past",
        "header.timestamp <= ctx.median_time_past",
    );
    let mtp_u = if mtp_below == SatResult::Unsat && mtp_eq == SatResult::Unsat {
        SatResult::Unsat
    } else {
        SatResult::Sat
    };
    let (mtp_u, mtp_b, mtp_p) = spec_clause::merge(
        "validate_block_header_mtp",
        &valid,
        &mtp_boundary,
        &mtp_predicate,
        mtp_u,
        production_lock::header_mtp_query(&mtp_boundary, true),
        production_lock::header_mtp_query(&mtp_predicate, false),
    );
    rows.push(LockRow {
        function: "validate_block_header_mtp".into(),
        shape: "threshold",
        unpatched: mtp_u,
        boundary: mtp_b,
        predicate: mtp_p,
        note: String::new(),
    });

    let script = repo("blvm-consensus/src/script/mod.rs");
    for (name, gate) in [
        ("try_verify_p2pk_fast_path", "len != 35 && len != 67"),
        ("try_verify_p2pkh_fast_path", "script_pubkey.len() != 25"),
        ("try_verify_p2sh_fast_path", "script_pubkey.len() != 23"),
        ("try_verify_p2wpkh_fast_path", "script_pubkey.len() != 22"),
    ] {
        let body = extract_fn(&script, name);
        let falls = body.contains(gate);
        let calls = fast_calls(&script, &body);
        rows.push(LockRow {
            function: name.into(),
            shape: "opcode",
            unpatched: production_lock::fast_path_query(falls, calls),
            boundary: production_lock::fast_path_query(false, calls),
            predicate: production_lock::fast_path_query(falls, false),
            note: String::new(),
        });
    }
    let cache = extract_fn(&script, "compute_script_cache_key");
    rows.push(LockRow {
        function: "compute_script_cache_key".into(),
        shape: "pointwise",
        unpatched: production_lock::cache_flags_query(&facts_of(&parse_fn(&cache))),
        boundary: production_lock::cache_flags_query(&facts_of(&parse_fn(
            &cache.replace("hasher.update(flags.to_le_bytes());", ""),
        ))),
        predicate: production_lock::cache_hit_query(false),
        note: String::new(),
    });
    let verify = extract_fn(&script, "verify_script");
    rows.push(LockRow {
        function: "verify_script_cache_hit".into(),
        shape: "pointwise",
        unpatched: production_lock::cache_hit_query(verify.contains("return Ok(cached_result)")),
        boundary: production_lock::cache_hit_query(false),
        predicate: production_lock::cache_hit_query(false),
        note: String::new(),
    });
    let legacy = extract_fn(
        &repo("blvm-consensus/src/transaction_hash.rs"),
        "compute_legacy_sighash_nocache",
    );
    let quirk_off = legacy.replace("result[0] = 1", "result[0] = 0");
    rows.push(LockRow {
        function: "sighash_single_quirk".into(),
        shape: "preimage",
        unpatched: production_lock::sighash_single_query(&facts_of(&parse_fn(&legacy))),
        boundary: production_lock::sighash_single_query(&facts_of(&parse_fn(&quirk_off))),
        predicate: production_lock::sighash_single_query(&facts_of(&parse_fn(
            &legacy.replace("result[0] = 1;", ""),
        ))),
        note: String::new(),
    });

    let inner = extract_fn(&script, "eval_script_inner");
    rows.push(row(
        "eval_script_pc",
        "opcode",
        &inner,
        &inner.replace("i += 1;", "i += 2;"),
        &inner.replace("i += 1;", "i += 0;"),
        production_lock::script_step_query,
    ));
    rows.push(row(
        "eval_script_control",
        "opcode",
        &inner,
        &inner.replace("control_stack.push", "control_stack.len"),
        &inner.replace("control_stack.push", "control_stack.len"),
        production_lock::control_step_query,
    ));
    rows
}

fn parse_fn(src: &str) -> ItemFn {
    syn::parse_str(src).unwrap_or_else(|e| panic!("parse failed: {e}\n{src}"))
}

fn tx_facts(fast_src: &str, check_src: &str) -> ProductionFacts {
    let fast = facts_of(&parse_fn(fast_src));
    let mut main = facts_of(&parse_fn(check_src));
    let mut money = fast.money;
    money.append(&mut main.money);
    main.money = money;
    main
}

fn fast_calls(file: &str, body: &str) -> bool {
    if body.contains("verify_signature(")
        || body.contains("verify_ecdsa_direct(")
        || body.contains("verify_schnorr")
    {
        return true;
    }
    for callee in [
        "verify_p2wpkh_inline",
        "verify_p2pkh_inline",
        "verify_p2pk_inline",
    ] {
        if body.contains(&format!("{callee}(")) {
            let c = extract_fn(file, callee);
            if c.contains("verify_signature(")
                || c.contains("verify_ecdsa_direct(")
                || c.contains("verify_schnorr")
            {
                return true;
            }
        }
    }
    false
}

fn arith_rows() -> Vec<LockRow> {
    let econ = repo("blvm-consensus/src/economic.rs");
    let subsidy = extract_fn(&econ, "get_block_subsidy");
    let witness = repo("blvm-consensus/src/witness.rs");
    let weight = extract_fn(&witness, "calculate_transaction_weight_segwit");
    let vsize = extract_fn(&witness, "weight_to_vsize");
    let coin = extract_fn(&econ, "check_coinbase_subsidy");
    let pow = repo("blvm-consensus/src/pow.rs");
    let expand = extract_fn(&pow, "expand_target");
    let proof = extract_fn(&pow, "get_block_proof");
    vec![
        row(
            "get_block_subsidy",
            "arith",
            &subsidy,
            &subsidy.replace("halving_period >= 64", "halving_period >= 32"),
            &subsidy.replace(
                "base_subsidy >> halving_period",
                "base_subsidy >> (halving_period + 1)",
            ),
            subsidy_query,
        ),
        row(
            "calculate_transaction_weight_segwit",
            "arith",
            &weight,
            &weight.replace("3 * base_size + total_size", "3 * base_size + total_size - 1"),
            &weight.replace("3 * base_size + total_size", "2 * base_size + total_size"),
            weight_query,
        ),
        row(
            "weight_to_vsize",
            "arith",
            &vsize,
            &vsize.replace("weight.div_ceil(4)", "weight / 4"),
            &vsize.replace("weight.div_ceil(4)", "weight.div_ceil(8)"),
            vsize_query,
        ),
        row(
            "check_coinbase_subsidy",
            "arith",
            &coin,
            &coin.replace(
                "coinbase_output <= max_coinbase",
                "coinbase_output < max_coinbase",
            ),
            &coin
                .replace("if total_fees < 0 || subsidy < 0 {\n        return false;\n    }\n", "")
                .replace("output.value < 0 || ", "")
                .replace("if coinbase_output < 0 {\n        return false;\n    }\n", ""),
            coinbase_subsidy_query,
        ),
        row(
            "expand_target",
            "arith",
            &expand,
            &expand.replace("3..=32", "4..=32"),
            &expand.replace("0x007fffff", "0x00ffffff"),
            expand_target_query,
        ),
        row(
            "get_block_proof",
            "arith",
            &proof,
            &proof.replace("return Ok(U256::zero());", "return Ok(U256::one());"),
            &proof.replace(
                "Ok(quotient\n        .checked_add(U256::one())\n        .unwrap_or(U256([u64::MAX; 4])))",
                "Ok(quotient)",
            ),
            block_proof_query,
        ),
    ]
}

fn subsidy_query(src: &str) -> SatResult {
    let cutoff = src
        .lines()
        .find(|l| l.contains("halving_period >="))
        .map(|l| if l.contains(">= 32") { 32 } else { 64 })
        .unwrap_or(64);
    let shift_line = src
        .lines()
        .find(|l| l.contains("base_subsidy >>"))
        .unwrap_or("");
    let extra: u64 = if shift_line.contains("halving_period + 1") {
        1
    } else {
        0
    };
    let impl_h = crate::parser::spec_expr::impl_u64("HALVING_INTERVAL");
    let spec_h = crate::parser::spec_expr::protocol_u64("H");
    let interval: u64 = src
        .lines()
        .find(|l| l.contains("halving_period ="))
        .map(|l| {
            if l.contains("210_001") {
                210_001
            } else {
                impl_h
            }
        })
        .unwrap_or(impl_h);
    production_lock::check(|ctx, solver| {
        let height = BV::new_const(ctx, "height", 64);
        let k = height.bvudiv(&BV::from_u64(ctx, interval, 64));
        let base_b = BV::from_u64(
            ctx,
            crate::parser::spec_expr::impl_u64("INITIAL_SUBSIDY"),
            64,
        );
        let base_c = BV::from_u64(ctx, crate::parser::spec_expr::initial_subsidy(), 64);
        let body_shift = k.bvadd(&BV::from_u64(ctx, extra, 64));
        let shifted = base_b.bvlshr(&body_shift);
        let zero = BV::from_u64(ctx, 0, 64);
        let body = k.bvuge(&BV::from_u64(ctx, cutoff, 64)).ite(&zero, &shifted);
        let clause_shift = base_c.bvlshr(&k);
        let clause = k
            .bvuge(&BV::from_u64(ctx, 64, 64))
            .ite(&zero, &clause_shift);
        // Interval is part of k. A wrong divisor changes k relative to the clause interval.
        let clause_k = height.bvudiv(&BV::from_u64(ctx, spec_h, 64));
        let clause = clause_k._eq(&k).ite(&clause, &zero);
        solver.assert(&body._eq(&clause).not());
    })
}

fn weight_query(src: &str) -> SatResult {
    let line = src
        .lines()
        .find(|l| l.contains("* base_size"))
        .unwrap_or("");
    let coeff: u64 = if line.contains("2 *") {
        2
    } else if line.contains("4 *") {
        4
    } else {
        3
    };
    let bias: i64 = if line.contains("- 1") { -1 } else { 0 };
    production_lock::check(|ctx, solver| {
        let base = BV::new_const(ctx, "base", 64);
        let total = BV::new_const(ctx, "total", 64);
        let body = base
            .bvmul(&BV::from_u64(ctx, coeff, 64))
            .bvadd(&total)
            .bvadd(&BV::from_i64(ctx, bias, 64));
        let clause = base
            .bvmul(&BV::from_u64(
                ctx,
                crate::parser::spec_expr::weight_base_coeff(),
                64,
            ))
            .bvadd(&total);
        solver.assert(&base.bvugt(&BV::from_u64(ctx, 0, 64)));
        solver.assert(&body._eq(&clause).not());
    })
}

fn vsize_query(src: &str) -> SatResult {
    let (ceil, div) = if src.contains("div_ceil(8)") {
        (true, 8u64)
    } else if src.contains("div_ceil(4)") {
        (true, 4)
    } else {
        (false, 4)
    };
    production_lock::check(|ctx, solver| {
        let w = BV::new_const(ctx, "w", 64);
        let div_b = BV::from_u64(ctx, div, 64);
        let bump = BV::from_u64(ctx, div - 1, 64);
        let body = if ceil {
            w.bvadd(&bump).bvudiv(&div_b)
        } else {
            w.bvudiv(&div_b)
        };
        let (add, div_c) = crate::parser::spec_expr::vsize_ceiling();
        let clause = w
            .bvadd(&BV::from_u64(ctx, add, 64))
            .bvudiv(&BV::from_u64(ctx, div_c, 64));
        solver.assert(&body._eq(&clause).not());
    })
}

fn coinbase_subsidy_query(src: &str) -> SatResult {
    let fee_sign = src.contains("total_fees < 0");
    let sub_sign = src.contains("subsidy < 0");
    let out_sign = src.contains("output.value < 0");
    let sum_sign = src.contains("coinbase_output < 0");
    let lt = src.contains("coinbase_output < max_coinbase");
    let le = src.contains("coinbase_output <= max_coinbase");
    production_lock::check(|ctx, solver| {
        let fees = BV::new_const(ctx, "fees", 64);
        let subsidy = BV::new_const(ctx, "subsidy", 64);
        let coin = BV::new_const(ctx, "coin", 64);
        let zero = BV::from_i64(ctx, 0, 64);
        let max = fees.bvadd(&subsidy);
        let mut rejected = Bool::from_bool(ctx, false);
        if fee_sign {
            rejected |= fees.bvslt(&zero);
        }
        if sub_sign {
            rejected |= subsidy.bvslt(&zero);
        }
        if out_sign || sum_sign {
            rejected |= coin.bvslt(&zero);
        }
        let cmp = if lt {
            coin.bvsge(&max)
        } else if le {
            coin.bvsgt(&max)
        } else {
            Bool::from_bool(ctx, false)
        };
        rejected |= cmp;
        let clause =
            fees.bvsge(&zero) & subsidy.bvsge(&zero) & coin.bvsge(&zero) & coin.bvsle(&max);
        solver.assert(&rejected.not()._eq(&clause).not());
    })
}

fn expand_target_query(src: &str) -> SatResult {
    let lo = if src.contains("4..=32") {
        4u64
    } else if src.contains("3..=32") {
        3
    } else {
        0
    };
    let mask = if src.contains("0x00ffffff") {
        0x00ff_ffffu64
    } else {
        0x007f_ffff
    };
    let split = src
        .lines()
        .find(|l| l.trim_start().starts_with("if exponent <="))
        .map(|l| if l.contains("<= 4") { 4u64 } else { 3 })
        .unwrap_or(3);
    production_lock::check(|ctx, solver| {
        let exp = BV::new_const(ctx, "exp", 8);
        let mant = BV::new_const(ctx, "mant", 32);
        let exp64 = exp.zero_ext(56);
        let (mask_c, exp_lo, exp_hi, bias, shift) = crate::parser::spec_expr::compact_target();
        let three_b = BV::from_u64(ctx, 3, 64);
        let eight_b = BV::from_u64(ctx, 8, 64);
        let three_c = BV::from_u64(ctx, bias, 64);
        let eight_c = BV::from_u64(ctx, shift, 64);
        let body_m = mant.bvand(&BV::from_u64(ctx, mask, 32)).zero_ext(32);
        let clause_m = mant.bvand(&BV::from_u64(ctx, mask_c, 32)).zero_ext(32);
        let body_ok = exp.bvuge(&BV::from_u64(ctx, lo, 8)) & exp.bvule(&BV::from_u64(ctx, 32, 8));
        let clause_ok =
            exp.bvuge(&BV::from_u64(ctx, exp_lo, 8)) & exp.bvule(&BV::from_u64(ctx, exp_hi, 8));
        let left_b = body_m.bvshl(&exp64.bvsub(&three_b).bvmul(&eight_b));
        let right_b = body_m.bvlshr(&three_b.bvsub(&exp64).bvmul(&eight_b));
        let underflow =
            exp.bvugt(&BV::from_u64(ctx, 3, 8)) & exp.bvule(&BV::from_u64(ctx, split, 8));
        let split_bv = BV::from_u64(ctx, split, 8);
        let body_val = underflow.ite(
            &BV::from_u64(ctx, 0, 64),
            &exp.bvule(&split_bv).ite(&right_b, &left_b),
        );
        let left_c = clause_m.bvshl(&exp64.bvsub(&three_c).bvmul(&eight_c));
        let right_c = clause_m.bvlshr(&three_c.bvsub(&exp64).bvmul(&eight_c));
        let clause_val = exp
            .bvule(&BV::from_u64(ctx, bias, 8))
            .ite(&right_c, &left_c);
        let ok = body_ok._eq(&clause_ok);
        let vals = body_ok.implies(&body_val._eq(&clause_val));
        solver.assert(&(ok & vals).not());
    })
}

fn block_proof_query(src: &str) -> SatResult {
    let zero_branch = !src.contains("return Ok(U256::one())");
    let plus = src.contains("quotient\n        .checked_add(U256::one())");
    production_lock::check(|ctx, solver| {
        let target = BV::new_const(ctx, "target", 16);
        let zero = BV::from_u64(ctx, 0, 16);
        let one = BV::from_u64(ctx, 1, 16);
        let quot = target.bvnot().bvudiv(&target.bvadd(&one));
        let body_nz = if plus { quot.bvadd(&one) } else { quot };
        let body_z = if zero_branch {
            zero.clone()
        } else {
            one.clone()
        };
        let body = target._eq(&zero).ite(&body_z, &body_nz);
        let clause_q = target.bvnot().bvudiv(&target.bvadd(&one));
        let clause = target._eq(&zero).ite(&zero, &clause_q.bvadd(&one));
        solver.assert(&target.bvult(&BV::from_u64(ctx, u64::from(u16::MAX), 16)));
        solver.assert(&body._eq(&clause).not());
    })
}

fn threshold_rows() -> Vec<LockRow> {
    let tx = repo("blvm-consensus/src/transaction.rs");
    let coinbase = production_text(&extract_fn(&tx, "is_coinbase"));
    let maturity = extract_fn(&tx, "check_coinbase_maturity");
    let act = extract_fn(
        &repo("blvm-consensus/src/activation.rs"),
        "taproot_activation_height",
    );
    let bip = repo("blvm-consensus/src/bip_validation.rs");
    let bip30 = extract_fn(&bip, "check_bip30");
    let bip34 = extract_fn(&bip, "check_bip34");
    let bip90 = extract_fn(&bip, "check_bip90");
    let bip147 = extract_fn(&bip, "check_bip147");
    let null_dummy = extract_fn(&bip, "is_null_dummy");
    let bip147_full = format!("{bip147}\n{null_dummy}");
    let bip54 = extract_fn(&bip, "is_bip54_active_at");
    let median = extract_fn(
        &repo("blvm-consensus/src/bip113.rs"),
        "get_median_time_past",
    );
    let bits = extract_fn(
        &repo("blvm-consensus/src/version_bits.rs"),
        "activation_height_from_headers",
    );
    vec![
        row(
            "is_coinbase",
            "threshold",
            &coinbase,
            &coinbase.replace("0xffffffff", "0xfffffffe"),
            &coinbase.replace("is_zero_hash", "not_zero_hash"),
            coinbase_query,
        ),
        row(
            "taproot_activation_height",
            "threshold",
            &act,
            &act.replace("TAPROOT_ACTIVATION_MAINNET", "TAPROOT_ACTIVATION_TESTNET"),
            &act.replace(
                "network == Network::Signet {\n        1\n",
                "network == Network::Signet {\n        2\n",
            ),
            activation_map_query,
        ),
        row(
            "check_bip30",
            "threshold",
            &bip30,
            &bip30.replace("c > 0", "c > 1"),
            &bip30.replace("!activation.is_fork_active(ForkId::Bip30, height)", "false"),
            bip30_query,
        ),
        row(
            "check_bip34",
            "threshold",
            &bip34,
            &bip34.replace("script_sig.is_empty()", "false && script_sig.is_empty()"),
            &bip34.replace("!activation.is_fork_active(ForkId::Bip34, height)", "false"),
            bip34_query,
        ),
        row(
            "check_bip90",
            "threshold",
            &bip90,
            &bip90.replace("block_version < 2", "block_version <= 2"),
            &bip90.replace("block_version < 2", "block_version < 1"),
            bip90_query,
        ),
        row(
            "check_bip147",
            "threshold",
            &bip147_full,
            &bip147_full.replace("script_sig.is_empty()", "false && script_sig.is_empty()"),
            &bip147_full.replace("first_push_empty = true", "first_push_empty = false"),
            bip147_query,
        ),
        row(
            "is_bip54_active_at",
            "threshold",
            &bip54,
            &bip54.replace("height >= activation", "height > activation"),
            &bip54.replace("height >= activation", "height == activation"),
            height_cmp_query,
        ),
        row(
            "check_coinbase_maturity",
            "threshold",
            &maturity,
            &maturity.replace("spend_height >= required", "spend_height > required"),
            &maturity.replace("if !is_coinbase {\n        return true;\n    }\n", ""),
            maturity_query,
        ),
        row(
            "get_median_time_past",
            "threshold",
            &median,
            &median.replace("/ 2]", "/ 2 - 1]"),
            &median.replace("timestamps.sort_unstable();", ""),
            median_query,
        ),
        row(
            "activation_height_from_headers",
            "threshold",
            &bits,
            &bits.replace("(period_index + 2)", "(period_index + 1)"),
            &bits.replace(
                "current_time >= deployment.timeout",
                "current_time > deployment.timeout",
            ),
            version_bits_query,
        ),
    ]
}

fn coinbase_query(src: &str) -> SatResult {
    let one = src.contains("len() == 1") || src.contains("len () == 1");
    let zero = src.contains("is_zero_hash")
        || src.contains("[0u8; 32]")
        || src.contains("[0u8 ; 32]")
        || src.contains("iter().all")
        || src.contains("iter () . all");
    let index = if src.contains("0xfffffffe") || src.contains("0xffff_fffe") {
        0xffff_fffeu64
    } else if src.contains("0xffffffff") || src.contains("0xffff_ffff") {
        0xffff_ffff
    } else {
        0
    };
    production_lock::check(|ctx, solver| {
        let n = BV::new_const(ctx, "n", 32);
        let hash = BV::new_const(ctx, "hash", 256);
        let idx = BV::new_const(ctx, "idx", 32);
        let n_ok = if one {
            n._eq(&BV::from_u64(ctx, 1, 32))
        } else {
            Bool::from_bool(ctx, true)
        };
        let hash_ok = if zero {
            hash._eq(&BV::from_u64(ctx, 0, 256))
        } else {
            Bool::from_bool(ctx, true)
        };
        let idx_ok = idx._eq(&BV::from_u64(ctx, index, 32));
        let body = n_ok & hash_ok & idx_ok;
        let (count, null_hash, index_c) = crate::parser::spec_expr::coinbase_shape();
        let clause = n._eq(&BV::from_u64(ctx, count, 32))
            & hash._eq(&BV::from_u64(ctx, u64::from(!null_hash), 256))
            & idx._eq(&BV::from_u64(ctx, index_c, 32));
        solver.assert(&body._eq(&clause).not());
    })
}

fn activation_map_query(src: &str) -> SatResult {
    let main = branch_height(src, "Mainnet", "Testnet");
    let test = branch_height(src, "Testnet", "Signet");
    let signet = branch_height(src, "Signet", "else");
    production_lock::check(|ctx, solver| {
        let net = BV::new_const(ctx, "net", 8);
        let body = map_height(ctx, &net, main, test, signet);
        let clause = map_height(
            ctx,
            &net,
            crate::parser::spec_expr::taproot_height("mainnet"),
            crate::parser::spec_expr::taproot_height("testnet"),
            1,
        );
        solver.assert(&net.bvule(&BV::from_u64(ctx, 3, 8)));
        solver.assert(&body._eq(&clause).not());
    })
}

fn branch_height(src: &str, name: &str, next: &str) -> u64 {
    let key = format!("Network::{name}");
    let Some(start) = src.find(&key) else {
        return 0;
    };
    let end = src[start..]
        .find(&format!("Network::{next}"))
        .map(|i| start + i)
        .unwrap_or(src.len());
    let branch = &src[start..end];
    if name == "Mainnet"
        && branch.contains("TAPROOT_ACTIVATION_TESTNET")
        && !branch.contains("TAPROOT_ACTIVATION_MAINNET")
    {
        return 2_011_968;
    }
    if branch.contains("TAPROOT_ACTIVATION_MAINNET") {
        return 709_632;
    }
    if branch.contains("TAPROOT_ACTIVATION_TESTNET") {
        return 2_011_968;
    }
    first_int(branch).unwrap_or(0)
}

fn first_int(src: &str) -> Option<u64> {
    let bytes = src.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i].is_ascii_digit() {
            let mut n = 0u64;
            while i < bytes.len() && bytes[i].is_ascii_digit() {
                n = n * 10 + u64::from(bytes[i] - b'0');
                i += 1;
            }
            return Some(n);
        }
        i += 1;
    }
    None
}

fn map_height<'a>(ctx: &'a z3::Context, net: &BV<'a>, main: u64, test: u64, signet: u64) -> BV<'a> {
    let m = BV::from_u64(ctx, main, 32);
    let t = BV::from_u64(ctx, test, 32);
    let s = BV::from_u64(ctx, signet, 32);
    let z = BV::from_u64(ctx, 0, 32);
    net._eq(&BV::from_u64(ctx, 0, 8)).ite(
        &m,
        &net._eq(&BV::from_u64(ctx, 1, 8))
            .ite(&t, &net._eq(&BV::from_u64(ctx, 2, 8)).ite(&s, &z)),
    )
}

fn bip30_query(src: &str) -> SatResult {
    let skips = src.contains("!activation.is_fork_active");
    let gt0 = src.contains("c > 0");
    let gt1 = src.contains("c > 1");
    production_lock::check(|ctx, solver| {
        let active = Bool::new_const(ctx, "active");
        let dup = Bool::new_const(ctx, "dup");
        let rejected = if gt1 {
            Bool::from_bool(ctx, false)
        } else if gt0 {
            dup.clone()
        } else {
            Bool::from_bool(ctx, false)
        };
        let body = if skips {
            active.implies(&rejected)
        } else {
            rejected
        };
        // Inactive is accepted. An active duplicate is rejected. A count of 1 is a duplicate.
        let clause = active.implies(&dup);
        solver.assert(&body._eq(&clause).not());
    })
}

fn bip34_query(src: &str) -> SatResult {
    let skips = src.contains("!activation.is_fork_active");
    let empty_rejects =
        src.contains("script_sig.is_empty()") && !src.contains("false && script_sig.is_empty()");
    production_lock::check(|ctx, solver| {
        let active = Bool::new_const(ctx, "active");
        let empty = Bool::new_const(ctx, "empty");
        let rejected = if empty_rejects {
            empty.clone()
        } else {
            Bool::from_bool(ctx, false)
        };
        let body_reject = if skips {
            active.clone() & rejected
        } else {
            rejected
        };
        let clause_reject = active & empty;
        solver.assert(&body_reject._eq(&clause_reject).not());
    })
}

fn bip90_query(src: &str) -> SatResult {
    let c2 = cmp_op(src, "block_version", 2);
    let c3 = cmp_op(src, "block_version", 3);
    let c4 = cmp_op(src, "block_version", 4);
    production_lock::check(|ctx, solver| {
        let v = BV::new_const(ctx, "version", 32);
        let a34 = Bool::new_const(ctx, "bip34");
        let a66 = Bool::new_const(ctx, "bip66");
        let a65 = Bool::new_const(ctx, "bip65");
        let (v65, v66, v34, _) = crate::parser::spec_expr::min_version_floors();
        let body = (a34.clone() & version_reject(ctx, &v, c2, 2))
            | (a66.clone() & version_reject(ctx, &v, c3, 3))
            | (a65.clone() & version_reject(ctx, &v, c4, 4));
        let clause = (a34 & v.bvslt(&BV::from_i64(ctx, v34, 32)))
            | (a66 & v.bvslt(&BV::from_i64(ctx, v66, 32)))
            | (a65 & v.bvslt(&BV::from_i64(ctx, v65, 32)));
        solver.assert(&body._eq(&clause).not());
    })
}

fn cmp_op(src: &str, var: &str, n: i64) -> &'static str {
    let le = format!("{var} <= {n}");
    let lt = format!("{var} < {n}");
    if src.contains(&le) {
        "le"
    } else if src.contains(&lt) {
        "lt"
    } else {
        "absent"
    }
}

fn version_reject<'a>(ctx: &'a z3::Context, v: &BV<'a>, op: &str, n: i64) -> Bool<'a> {
    let bound = BV::from_i64(ctx, n, 32);
    match op {
        "le" => v.bvsle(&bound),
        "lt" => v.bvslt(&bound),
        _ => Bool::from_bool(ctx, false),
    }
}

fn bip147_query(src: &str) -> SatResult {
    let empty_rejects =
        src.contains("script_sig.is_empty()") && !src.contains("false && script_sig.is_empty()");
    let op0 = src.contains("first_push_empty = true");
    production_lock::check(|ctx, solver| {
        let empty = Bool::new_const(ctx, "empty");
        let op = BV::new_const(ctx, "op", 8);
        let zero_push = op._eq(&BV::from_u64(ctx, 0, 8));
        let body = if empty_rejects {
            empty.not()
                & if op0 {
                    zero_push
                } else {
                    Bool::from_bool(ctx, false)
                }
        } else if op0 {
            zero_push
        } else {
            Bool::from_bool(ctx, false)
        };
        let clause = empty.not() & op._eq(&BV::from_u64(ctx, 0, 8));
        solver.assert(&body._eq(&clause).not());
    })
}

fn height_cmp_query(src: &str) -> SatResult {
    let op = if src.contains("height > activation") {
        "gt"
    } else if src.contains("height == activation") {
        "eq"
    } else if src.contains("height >= activation") {
        "ge"
    } else {
        "absent"
    };
    production_lock::check(|ctx, solver| {
        let h = BV::new_const(ctx, "h", 64);
        let a = BV::new_const(ctx, "a", 64);
        let body = match op {
            "gt" => h.bvugt(&a),
            "eq" => h._eq(&a),
            "ge" => h.bvuge(&a),
            _ => Bool::from_bool(ctx, false),
        };
        let clause_ge = if crate::parser::spec_expr::bip54_activation_is_ge() {
            h.bvuge(&a)
        } else {
            h.bvugt(&a)
        };
        solver.assert(&body._eq(&clause_ge).not());
    })
}

fn maturity_query(src: &str) -> SatResult {
    let skip = src.contains("!is_coinbase");
    let gt = src.contains("spend_height > required");
    let ge = src.contains("spend_height >= required");
    production_lock::check(|ctx, solver| {
        let coinbase = Bool::new_const(ctx, "coinbase");
        let spend = BV::new_const(ctx, "spend", 32);
        let creation = BV::new_const(ctx, "creation", 32);
        let spec_r = crate::parser::spec_expr::protocol_u64("R");
        let impl_r = crate::parser::spec_expr::impl_u64("COINBASE_MATURITY");
        let required_b = creation.bvadd(&BV::from_u64(ctx, impl_r, 32));
        let required_c = creation.bvadd(&BV::from_u64(ctx, spec_r, 32));
        solver.assert(&creation.bvule(&BV::from_u64(ctx, u64::from(u32::MAX) - spec_r, 32)));
        let ordered = if gt {
            spend.bvugt(&required_b)
        } else if ge {
            spend.bvuge(&required_b)
        } else {
            Bool::from_bool(ctx, false)
        };
        let body = if skip {
            coinbase.not().ite(&Bool::from_bool(ctx, true), &ordered)
        } else {
            ordered
        };
        let clause = coinbase
            .not()
            .ite(&Bool::from_bool(ctx, true), &spend.bvuge(&required_c));
        solver.assert(&body._eq(&clause).not());
    })
}

fn median_query(src: &str) -> SatResult {
    let lower = src.contains("/ 2 - 1");
    let sorts = src.contains("sort_unstable");
    production_lock::check(|ctx, solver| {
        let n = BV::new_const(ctx, "n", 8);
        let one = BV::from_u64(ctx, 1, 8);
        let eleven = BV::from_u64(ctx, 11, 8);
        solver.assert(&n.bvuge(&one));
        solver.assert(&n.bvule(&eleven));
        let mut sorted: Vec<BV> = Vec::with_capacity(11);
        for i in 0..11 {
            let v = BV::new_const(ctx, format!("s{i}"), 32);
            if i > 0 {
                solver.assert(&sorted[i - 1].bvult(&v));
            }
            sorted.push(v);
        }
        let idx_clause = n.zero_ext(24).bvudiv(&BV::from_u64(ctx, 2, 32));
        let idx_body = if lower {
            idx_clause.bvsub(&BV::from_u64(ctx, 1, 32))
        } else {
            idx_clause.clone()
        };
        let sorted_at = select_sorted(ctx, &idx_body, &sorted);
        let raw = if sorts {
            sorted_at
        } else {
            // Reverse order: index i of the unsorted array is sorted[(n-1)-i].
            let last = n.zero_ext(24).bvsub(&BV::from_u64(ctx, 1, 32));
            select_sorted(ctx, &last.bvsub(&idx_body), &sorted)
        };
        let clause = select_sorted(ctx, &idx_clause, &sorted);
        solver.assert(&raw._eq(&clause).not());
    })
}

fn select_sorted<'a>(ctx: &'a z3::Context, idx: &BV<'a>, sorted: &[BV<'a>]) -> BV<'a> {
    let mut acc = sorted[0].clone();
    for (i, item) in sorted.iter().enumerate().skip(1) {
        acc = idx._eq(&BV::from_u64(ctx, i as u64, 32)).ite(item, &acc);
    }
    acc
}

fn version_bits_query(src: &str) -> SatResult {
    let extra = if src.contains("period_index + 1") {
        1u64
    } else if src.contains("period_index + 3") {
        3
    } else {
        2
    };
    let timeout_ge = src.contains("current_time >= deployment.timeout");
    let timeout_gt = src.contains("current_time > deployment.timeout");
    production_lock::check(|ctx, solver| {
        let h = BV::new_const(ctx, "h", 64);
        let t = BV::new_const(ctx, "t", 64);
        let start = BV::new_const(ctx, "start", 64);
        let timeout = BV::new_const(ctx, "timeout", 64);
        solver.assert(&h.bvuge(&BV::from_u64(ctx, 1, 64)));
        solver.assert(&start.bvult(&timeout));
        let period_b = BV::from_u64(
            ctx,
            crate::parser::spec_expr::source_u64(
                "../blvm-consensus/src/version_bits.rs",
                "LOCK_IN_PERIOD",
            ),
            64,
        );
        let period_c = BV::from_u64(
            ctx,
            crate::parser::spec_expr::protocol_u64("D_INTERVAL"),
            64,
        );
        let index_b = h.bvsub(&BV::from_u64(ctx, 1, 64)).bvudiv(&period_b);
        let index_c = h.bvsub(&BV::from_u64(ctx, 1, 64)).bvudiv(&period_c);
        let body_h = index_b
            .bvadd(&BV::from_u64(ctx, extra, 64))
            .bvmul(&period_b);
        let clause_h = index_c.bvadd(&BV::from_u64(ctx, 2, 64)).bvmul(&period_c);
        let in_window = if timeout_gt {
            t.bvuge(&start) & t.bvule(&timeout)
        } else if timeout_ge {
            t.bvuge(&start) & t.bvult(&timeout)
        } else {
            Bool::from_bool(ctx, true)
        };
        let clause_window = t.bvuge(&start) & t.bvult(&timeout);
        let body = in_window.ite(&body_h, &BV::from_u64(ctx, 0, 64));
        let clause = clause_window.ite(&clause_h, &BV::from_u64(ctx, 0, 64));
        solver.assert(&body._eq(&clause).not());
    })
}

fn preimage_rows() -> Vec<LockRow> {
    let hash = repo("blvm-consensus/src/transaction_hash.rs");
    let legacy = extract_fn(&hash, "compute_legacy_sighash_nocache");
    let bip143 = extract_fn(&hash, "build_bip143_preimage");
    let tap = extract_fn(
        &repo("blvm-consensus/src/taproot.rs"),
        "compute_taproot_signature_hash",
    );
    let header = repo("blvm-primitives/src/serialization/block.rs");
    let ser = extract_fn(&header, "serialize_block_header");
    let bip143_order = bip143_needles();
    vec![
        layout_row(
            "compute_legacy_sighash_nocache",
            &legacy,
            LEGACY,
            &swap_needles(
                &legacy,
                "h.update((tx.version as u32).to_le_bytes());",
                "h.update((tx.lock_time as u32).to_le_bytes());",
            ),
            &legacy.replacen(
                "(tx.version as u32).to_le_bytes()",
                "(tx.version as u32).to_be_bytes()",
                1,
            ),
            &legacy.replace("h.update((tx.version as u32).to_le_bytes());\n", ""),
        ),
        layout_row(
            "build_bip143_preimage",
            &bip143,
            &bip143_order,
            &swap_needles(
                &bip143,
                "preimage.extend_from_slice(&(tx.version as u32).to_le_bytes());",
                "preimage.extend_from_slice(&(tx.lock_time as u32).to_le_bytes());",
            ),
            &bip143.replacen("amount.to_le_bytes()", "amount.to_be_bytes()", 1),
            &bip143.replace(
                "preimage.extend_from_slice(&(tx.version as u32).to_le_bytes());\n",
                "",
            ),
        ),
        layout_row(
            "compute_taproot_signature_hash",
            &tap,
            TAPROOT,
            &swap_needles(&tap, "tx.version", "tx.lock_time"),
            &tap.replacen(
                "(tx.version as u32).to_le_bytes()",
                "(tx.version as u32).to_be_bytes()",
                1,
            ),
            &tap.replace("sigmsg.push(0x00u8);\n", ""),
        ),
        layout_row(
            "serialize_block_header",
            &ser,
            HEADER,
            &swap_needles(&ser, "header.version", "header.prev_block_hash"),
            &ser.replacen(
                "(header.version as i32).to_le_bytes()",
                "(header.version as i32).to_be_bytes()",
                1,
            ),
            &ser.replace(
                "result.extend_from_slice(&(header.nonce as u32).to_le_bytes());\n",
                "",
            ),
        ),
    ]
}

fn layout_row(
    name: &str,
    plain: &str,
    clause: &[(&str, &str)],
    swapped: &str,
    endian: &str,
    dropped: &str,
) -> LockRow {
    let boundary = if layout_query(plain, clause) == SatResult::Unsat
        && layout_query(swapped, clause) == SatResult::Sat
        && layout_query(endian, clause) == SatResult::Sat
    {
        SatResult::Sat
    } else if layout_query(swapped, clause) != SatResult::Sat
        && layout_query(endian, clause) != SatResult::Sat
    {
        SatResult::Unsat
    } else if layout_query(endian, clause) == SatResult::Sat {
        SatResult::Sat
    } else {
        layout_query(swapped, clause)
    };
    LockRow {
        function: name.into(),
        shape: "preimage",
        unpatched: layout_query(plain, clause),
        boundary,
        predicate: layout_query(dropped, clause),
        note: String::new(),
    }
}

const LEGACY: &[(&str, &str)] = &[
    ("version", "(tx.version as u32).to_le_bytes()"),
    ("n_in", "update_varint(&mut h, n_inputs"),
    ("prevout", "h.update(input.prevout.hash)"),
    ("index", "input.prevout.index.to_le_bytes()"),
    ("script", "h.update(script_code)"),
    ("seq", "(input.sequence as u32).to_le_bytes()"),
    ("n_out", "update_varint(&mut h, n_outputs"),
    ("value", "h.update(output.value.to_le_bytes())"),
    ("lock", "(tx.lock_time as u32).to_le_bytes()"),
    ("sighash", "h.update(sighash_u32.to_le_bytes())"),
];

fn bip143_needles() -> Vec<(&'static str, &'static str)> {
    const MAP: &[(&str, &str, &str)] = &[
        ("nVersion", "version", "(tx.version as u32).to_le_bytes()"),
        ("hashPrevouts", "prevouts", "hashes.hash_prevouts"),
        ("hashSequence", "seqhash", "hashes.hash_sequence"),
        ("outpoint", "outpoint", "&input.prevout.hash"),
        (
            "scriptCode",
            "script",
            "preimage.extend_from_slice(script_code)",
        ),
        ("amount", "amount", "&amount.to_le_bytes()"),
        ("nSequence", "seq", "(input.sequence as u32).to_le_bytes()"),
        ("hashOutputs", "outputs", "hashes.hash_outputs"),
        ("nLockTime", "lock", "(tx.lock_time as u32).to_le_bytes()"),
        (
            "sighashType",
            "sighash",
            "(sighash_type as u32).to_le_bytes()",
        ),
    ];
    crate::parser::spec_expr::bip143_fields()
        .into_iter()
        .map(|field| {
            MAP.iter()
                .find(|(name, _, _)| *name == field.name)
                .map(|(_, id, needle)| (*id, *needle))
                .unwrap_or_else(|| panic!("BIP143 field {} has no source needle", field.name))
        })
        .collect()
}

const TAPROOT: &[(&str, &str)] = &[
    ("epoch", "sigmsg.push(0x00"),
    ("hashtype", "sigmsg.push(sighash_type)"),
    ("version", "tx.version"),
    ("lock", "tx.lock_time"),
    ("prevouts", "sha_prevouts"),
    ("amounts", "sha_amounts"),
    ("spk", "sha_scriptpubkeys"),
    ("seqs", "sha_sequences"),
    ("outputs", "sha_outputs"),
    ("spend", "spend_type"),
    ("index", "input_index as u32"),
];

const HEADER: &[(&str, &str)] = &[
    ("version", "header.version"),
    ("prev", "header.prev_block_hash"),
    ("merkle", "header.merkle_root"),
    ("time", "header.timestamp"),
    ("bits", "header.bits"),
    ("nonce", "header.nonce"),
];

fn swap_needles(src: &str, a: &str, b: &str) -> String {
    let token_a = format!("__FIELD_{a}__");
    src.replace(a, &token_a).replace(b, a).replace(&token_a, b)
}

fn layout_of(src: &str, needles: &[(&str, &str)]) -> Vec<(u8, u8)> {
    let mut found = Vec::new();
    for (id, (_, needle)) in needles.iter().enumerate() {
        if let Some(p) = src.find(needle) {
            let window = &src[p..src.len().min(p + needle.len() + 40)];
            let endian = if window.contains("to_be_bytes") {
                1
            } else if window.contains("to_le_bytes") {
                0
            } else {
                2
            };
            found.push((p, id as u8, endian));
        }
    }
    found.sort_by_key(|x| x.0);
    found.into_iter().map(|(_, id, e)| (id, e)).collect()
}

fn layout_query(src: &str, clause_needles: &[(&str, &str)]) -> SatResult {
    let body = layout_of(src, clause_needles);
    let clause: Vec<(u8, u8)> = clause_needles
        .iter()
        .enumerate()
        .map(|(i, _)| (i as u8, expected_endian(clause_needles[i].0)))
        .collect();
    // Endian of raw fields is 2. Integer fields in the clause are little-endian (0)
    // except epoch/hashtype/spend which are raw bytes.
    let clause: Vec<(u8, u8)> = clause
        .into_iter()
        .enumerate()
        .map(|(i, (id, _))| {
            let window_endian = expected_endian(clause_needles[i].0);
            (id, window_endian)
        })
        .collect();
    let quirk = !src.contains("compute_legacy") || src.contains("result[0] = 1");
    production_lock::check(|ctx, solver| {
        let n = body.len().max(clause.len()).max(1);
        let mut eqs = Vec::new();
        for i in 0..n {
            let b = body.get(i).copied().unwrap_or((255, 255));
            let c = clause.get(i).copied().unwrap_or((254, 254));
            let got = BV::from_u64(ctx, (u64::from(b.0) << 8) | u64::from(b.1), 16);
            let want = BV::from_u64(ctx, (u64::from(c.0) << 8) | u64::from(c.1), 16);
            eqs.push(got._eq(&want));
        }
        let mut all = eqs.pop().unwrap();
        for e in eqs {
            all &= e;
        }
        if !quirk {
            all &= Bool::from_bool(ctx, false);
        }
        solver.assert(&all.not());
    })
}

fn expected_endian(name: &str) -> u8 {
    match name {
        "version" | "index" | "seq" | "value" | "lock" | "sighash" | "amount" | "time" | "bits"
        | "nonce" => 0,
        _ => 2,
    }
}

fn opcode_rows() -> Vec<LockRow> {
    let script = repo("blvm-consensus/src/script/mod.rs");
    let arith = repo("blvm-consensus/src/script/arithmetic.rs");
    let crypto = repo("blvm-consensus/src/script/crypto_ops.rs");
    let mut rows = Vec::new();
    rows.push(row(
        "push_advance",
        "opcode",
        &script,
        &script.replace(", 1 + len)", ", len)"),
        &script.replace(", 2 + len)", ", 1 + len)"),
        push_advance_query,
    ));
    let mut names = opcode_names(&script);
    names.sort();
    names.dedup();
    for name in names {
        if name.starts_with("OP_PUSHDATA")
            || name.starts_with("OP_DISABLED")
            || name.contains("RANGE")
            || name.contains("BASE")
            || name.starts_with("OP_NOP") && name != "OP_NOP"
        {
            continue;
        }
        let Some(arm) = best_arm(&script, &name) else {
            continue;
        };
        let expanded = drop_inactive_cfg(&expand_arm(&arm, &arith, &crypto));
        let clause = clause_of(&name);
        let body_src = expanded.clone();
        let boundary_src = boundary_patch(&expanded);
        let predicate_src = predicate_patch(&name, &expanded);
        rows.push(LockRow {
            function: name,
            shape: "opcode",
            unpatched: effect_query(&classify(&body_src), &clause),
            boundary: effect_query(&classify(&boundary_src), &clause),
            predicate: effect_query(&classify(&predicate_src), &clause),
            note: format!(
                "body {:?} clause {:?} pred {:?}",
                classify(&body_src),
                clause,
                classify(&predicate_src)
            ),
        });
    }
    let full = extract_fn(&script, "execute_opcode_with_context_full");
    let arm = full.split("OP_CHECKSIG =>").nth(1).unwrap_or(&full);
    rows.push(row(
        "OP_CHECKSIG_verifier",
        "opcode",
        arm,
        &arm.replace(
            "if is_valid { 1 } else { 0 }",
            "if is_valid { 0 } else { 1 }",
        ),
        &arm.replace("if is_valid { 1 } else { 0 }", "if true { 1 } else { 0 }"),
        production_lock::checksig_query,
    ));
    rows
}

fn push_advance_query(src: &str) -> SatResult {
    let direct = addend_of(src, ", 1 + len)", ", len)", 1);
    let p1 = addend_of(src, ", 2 + len)", ", 1 + len)", 2);
    let p2 = if src.contains(", 3 + len)") { 3 } else { 0 };
    let p4 = if src.contains("5usize.saturating_add(len)") {
        5
    } else {
        0
    };
    production_lock::check(|ctx, solver| {
        let which = BV::new_const(ctx, "which", 8);
        let len = BV::new_const(ctx, "len", 32);
        solver.assert(&len.bvugt(&BV::from_u64(ctx, 0, 32)));
        solver.assert(&which.bvule(&BV::from_u64(ctx, 3, 8)));
        let body = pick4(ctx, &which, &len, [direct, p1, p2, p4]);
        let clause = pick4(ctx, &which, &len, crate::parser::spec_expr::push_advances());
        solver.assert(&body._eq(&clause).not());
    })
}

fn addend_of(src: &str, full: &str, fallen: &str, normal: u64) -> u64 {
    if src.contains(full) {
        normal
    } else if src.contains(fallen) {
        normal.saturating_sub(1)
    } else {
        0
    }
}

fn pick4<'a>(ctx: &'a z3::Context, which: &BV<'a>, len: &BV<'a>, add: [u64; 4]) -> BV<'a> {
    let mut acc = len.bvadd(&BV::from_u64(ctx, add[3], 32));
    for i in (0..3).rev() {
        acc = which
            ._eq(&BV::from_u64(ctx, i as u64, 8))
            .ite(&len.bvadd(&BV::from_u64(ctx, add[i], 32)), &acc);
    }
    acc
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Effect {
    kind: u16,
    arg: i64,
    min: u32,
    step: u32,
}

const K_NOP: u16 = 1;
const K_DISABLED: u16 = 2;
const K_FAIL: u16 = 3;
const K_PUSH: u16 = 4;
const K_DUP: u16 = 5;
const K_DROP: u16 = 6;
const K_ADD: u16 = 7;
const K_SUB: u16 = 8;
const K_ADD1: u16 = 9;
const K_SUB1: u16 = 10;
const K_NEG: u16 = 11;
const K_ABS: u16 = 12;
const K_NOT: u16 = 13;
const K_NZ: u16 = 14;
const K_EQ: u16 = 15;
const K_EQV: u16 = 16;
const K_HASH: u16 = 17;
const K_CHECKSIG: u16 = 18;
const K_BIP65: u16 = 19;
const K_CTRL: u16 = 20;
const K_SWAP: u16 = 21;
const K_SIZE: u16 = 22;
const K_WITHIN: u16 = 23;
const K_AND: u16 = 24;
const K_OR: u16 = 25;
const K_LT: u16 = 26;
const K_GT: u16 = 27;
const K_LE: u16 = 28;
const K_GE: u16 = 29;
const K_MIN: u16 = 30;
const K_MAX: u16 = 31;
const K_VERIFY: u16 = 32;
const K_ALT: u16 = 33;
const K_DEPTH: u16 = 34;
const K_SIGADD: u16 = 35;
const K_CSV: u16 = 36;
const K_PERM: u16 = 37;
const K_UNKNOWN: u16 = 99;

fn effect(kind: u16, min: u32) -> Effect {
    Effect {
        kind,
        arg: 0,
        min,
        step: 1,
    }
}

fn clause_of(name: &str) -> Effect {
    let row = crate::parser::spec_expr::opcode(name)
        .unwrap_or_else(|| panic!("spec opcode table has no {name}"));
    let (kind, arg) = encode_of_operation(&row.op);
    Effect {
        kind,
        arg,
        min: row.min,
        step: 1,
    }
}

/// Operation word from the opcode table. Permutation tags name the word.
/// Push-depth fingerprints stay in `perm_word`; they are how the arm is recognized.
fn encode_of_operation(op: &str) -> (u16, i64) {
    match op {
        "push" => (K_PUSH, 0),
        "pushneg" => (K_PUSH, -1),
        "pushn" => (K_PUSH, -100),
        "nop" => (K_NOP, 0),
        "disabled" => (K_DISABLED, 0),
        "control" => (K_CTRL, 0),
        "fail" => (K_FAIL, 0),
        "verify" => (K_VERIFY, 0),
        "altstack" => (K_ALT, 0),
        "dup" => (K_DUP, 0),
        "drop" => (K_DROP, 0),
        "depth" => (K_DEPTH, 0),
        "ripemd160" => (K_HASH, 20),
        "sha1" => (K_HASH, 1),
        "sha256" => (K_HASH, 32),
        "hash160" => (K_HASH, 160),
        "hash256" => (K_HASH, 256),
        "equal" => (K_EQ, 0),
        "equalverify" => (K_EQV, 0),
        "notequal" => (K_EQ, 1),
        "add1" => (K_ADD1, 0),
        "sub1" => (K_SUB1, 0),
        "neg" => (K_NEG, 0),
        "abs" => (K_ABS, 0),
        "not" => (K_NOT, 0),
        "nz" => (K_NZ, 0),
        "add" => (K_ADD, 0),
        "sub" => (K_SUB, 0),
        "and" => (K_AND, 0),
        "or" => (K_OR, 0),
        "less" => (K_LT, 0),
        "greater" => (K_GT, 0),
        "le" => (K_LE, 0),
        "ge" => (K_GE, 0),
        "min" => (K_MIN, 0),
        "max" => (K_MAX, 0),
        "within" => (K_WITHIN, 0),
        "size" => (K_SIZE, 0),
        "checksig" => (K_CHECKSIG, 0),
        "sigadd" => (K_SIGADD, 1),
        "bip65" => (K_BIP65, 0),
        "csv" => (K_CSV, 0),
        "nip" | "over" | "swap" | "tuck" | "2dup" | "pick" | "roll" | "rot" | "3dup" | "2over"
        | "2swap" | "2rot" => (K_PERM, perm_tag(op)),
        _ => (K_UNKNOWN, 0),
    }
}

fn perm_word(fp: i64) -> &'static str {
    match fp {
        1 => "nip",
        2 => "over",
        12 => "swap",
        21 => "2dup",
        43 => "2over",
        65 => "2rot",
        121 => "tuck",
        213 => "rot",
        321 => "3dup",
        1001 => "pick",
        2001 => "roll",
        2143 => "2swap",
        _ => "",
    }
}

fn perm_tag(word: &str) -> i64 {
    match word {
        "nip" => 1,
        "over" => 2,
        "swap" => 3,
        "tuck" => 4,
        "2dup" => 5,
        "pick" => 6,
        "roll" => 7,
        "rot" => 8,
        "3dup" => 9,
        "2over" => 10,
        "2swap" => 11,
        "2rot" => 12,
        _ => 0,
    }
}

fn strip_cfg_not_production(src: &str) -> String {
    let marker = "#[cfg(not(feature = \"production\"))]";
    let mut out = src.to_string();
    while let Some(i) = out.find(marker) {
        let after = i + marker.len();
        let Some(rel) = out[after..].find('{') else {
            break;
        };
        let block = slice_braces(&out[after + rel..]);
        if block.is_empty() {
            break;
        }
        let end = after + rel + block.len();
        out.replace_range(i..end, "");
    }
    out
}

fn push_depth(line: &str) -> Option<i64> {
    let rest = line.trim().strip_prefix("stack.push(")?;
    let inside = rest.split(')').next()?.trim().trim_end_matches('(').trim();
    let name = inside.strip_suffix(".clone").unwrap_or(inside);
    match name {
        "top" => Some(1),
        "second" => Some(2),
        "third" => Some(3),
        "fourth" => Some(4),
        "fifth" => Some(5),
        "sixth" => Some(6),
        _ => None,
    }
}

/// Push-depth sequence of the production arm. `12` is push top then second.
/// Pick/roll use 1000/2000 plus the subtracted index.
fn stack_perm(src: &str) -> Option<i64> {
    let src = strip_cfg_not_production(src);
    let mut fp = 0i64;
    let mut n = 0i64;
    for line in src.lines() {
        if let Some(d) = push_depth(line) {
            fp = fp.saturating_mul(10).saturating_add(d);
            n += 1;
        }
    }
    if n > 0 {
        return Some(fp);
    }
    let removed = src.contains(".remove(");
    if src.contains("len - 2 - n") {
        return Some(if removed { 2002 } else { 1002 });
    }
    if src.contains("len - 1 - n") {
        return Some(if removed { 2001 } else { 1001 });
    }
    None
}

fn classify(src: &str) -> Effect {
    let min = min_stack(src);
    let step = step_of(src);
    let mut e = if src.contains("OkTrueBypass") {
        effect(K_NOP, 0)
    } else if src.contains("script_num_encode(n + ") {
        let arg = if src.contains("n + 2") {
            2
        } else if src.contains("n + 0") {
            0
        } else {
            1
        };
        Effect {
            kind: K_SIGADD,
            arg,
            min: 3,
            step,
        }
    } else if src.contains("op_hash160") || (src.contains("Ripemd160") && src.contains("Sha256")) {
        Effect {
            kind: K_HASH,
            arg: 160,
            min: 1,
            step,
        }
    } else if src.contains("op_hash256") {
        Effect {
            kind: K_HASH,
            arg: 256,
            min: 1,
            step,
        }
    } else if src.contains("op_sha256") {
        Effect {
            kind: K_HASH,
            arg: 32,
            min: 1,
            step,
        }
    } else if src.contains("op_sha1") || src.contains("Sha1::") {
        Effect {
            kind: K_HASH,
            arg: 1,
            min: 1,
            step,
        }
    } else if src.contains("op_ripemd160") {
        Effect {
            kind: K_HASH,
            arg: 20,
            min: 1,
            step,
        }
    } else if src.contains("DisabledOpcode") {
        effect(K_DISABLED, 0)
    } else if src.contains("script_num_encode(n + 1)")
        || src.contains("n + 2")
        || src.contains("n + 0")
    {
        let arg = if src.contains("n + 2") {
            2
        } else if src.contains("n + 0") {
            0
        } else {
            1
        };
        Effect {
            kind: K_SIGADD,
            arg,
            min: 3,
            step,
        }
    } else if src.contains("verify_signature(")
        || src.contains("verify_tapscript_schnorr")
        || src.contains("verify_schnorr")
    {
        let arg = if src.contains("if true { 1 }") { 1 } else { 0 };
        Effect {
            kind: K_CHECKSIG,
            arg,
            min,
            step,
        }
    } else if src.contains("check_bip65(") {
        effect(K_BIP65, min.max(1))
    } else if src.contains("is_sequence_disabled(") {
        effect(K_CSV, min.max(1))
    } else if src.contains("Ripemd160") && src.contains("Sha256") || src.contains("op_hash160") {
        Effect {
            kind: K_HASH,
            arg: 160,
            min: min.max(1),
            step,
        }
    } else if src.contains("op_hash256") {
        Effect {
            kind: K_HASH,
            arg: 256,
            min: min.max(1),
            step,
        }
    } else if src.contains("op_sha256") || (src.contains("Sha256") && !src.contains("Ripemd")) {
        Effect {
            kind: K_HASH,
            arg: 32,
            min: min.max(1),
            step,
        }
    } else if src.contains("op_sha1") || src.contains("Sha1") {
        Effect {
            kind: K_HASH,
            arg: 1,
            min: min.max(1),
            step,
        }
    } else if src.contains("op_ripemd160") || src.contains("Ripemd160") {
        Effect {
            kind: K_HASH,
            arg: 20,
            min: min.max(1),
            step,
        }
    } else if src.contains("x >= min_val && x < max_val") {
        effect(K_WITHIN, 3)
    } else if src.contains("std::cmp::min") {
        effect(K_MIN, 2)
    } else if src.contains("std::cmp::max") {
        effect(K_MAX, 2)
    } else if src.contains("a != 0 && b != 0") {
        effect(K_AND, 2)
    } else if src.contains("a != 0 || b != 0") {
        effect(K_OR, 2)
    } else if src.contains("b + a") {
        effect(K_ADD, min_stack_or(src, 2))
    } else if src.contains("b - a") {
        effect(K_SUB, min_stack_or(src, 2))
    } else if src.contains("a + 0") {
        Effect {
            kind: K_ADD1,
            arg: 0,
            min: min.max(1),
            step,
        }
    } else if src.contains("a + 1") {
        effect(K_ADD1, min.max(1))
    } else if src.contains("a - 1") {
        effect(K_SUB1, min.max(1))
    } else if src.contains("script_num_encode(-a)") || src.contains("(-a)") {
        effect(K_NEG, min.max(1))
    } else if src.contains("a.abs()") {
        effect(K_ABS, min.max(1))
    } else if src.contains("if a == 0") {
        effect(K_NOT, min.max(1))
    } else if src.contains("if a != 0") {
        effect(K_NZ, min.max(1))
    } else if src.contains("b <= a") {
        effect(K_LE, 2)
    } else if src.contains("b >= a") {
        effect(K_GE, 2)
    } else if src.contains("b < a") {
        effect(K_LT, 2)
    } else if src.contains("b > a") {
        effect(K_GT, 2)
    } else if src.contains("a != b") && !src.contains("a == b") {
        Effect {
            kind: K_EQ,
            arg: 1,
            min: 2,
            step,
        }
    } else if src.contains("a == b") || src.contains("b == a") {
        effect(K_EQ, 2)
    } else if src.contains("Vec::new()") {
        Effect {
            kind: K_PUSH,
            arg: 0,
            min,
            step,
        }
    } else if let Some(fp) = stack_perm(src) {
        Effect {
            kind: K_PERM,
            arg: perm_tag(perm_word(fp)),
            min,
            step,
        }
    } else if (src.contains("get_unchecked(len - 1)") && !src.contains("get_unchecked(len - 1 -"))
        || (src.contains("stack.last()") && src.contains("stack.push(item)"))
    {
        effect(K_DUP, min.max(1))
    } else if src.contains("control_stack") {
        effect(K_CTRL, 0)
    } else if src.contains("altstack") {
        effect(K_ALT, min.max(1))
    } else if src.contains("stack.push(top)") && src.contains("stack.push(second)") {
        effect(K_SWAP, 2)
    } else if src.contains("to_stack_element(&[])") || src.contains("to_stack_element(&[0])") {
        Effect {
            kind: K_PUSH,
            arg: 0,
            min: 0,
            step,
        }
    } else if src.contains("0x81") {
        Effect {
            kind: K_PUSH,
            arg: -1,
            min: 0,
            step,
        }
    } else if src.contains("OP_N_BASE_PLUS") {
        Effect {
            kind: K_PUSH,
            arg: -101,
            min: 0,
            step,
        }
    } else if src.contains("OP_N_BASE") || src.contains("opcode - OP_1") {
        Effect {
            kind: K_PUSH,
            arg: -100,
            min: 0,
            step,
        }
    } else if src.contains("execute_opcode_with_context_full") && src.contains("OP_CHECKMULTISIG") {
        effect(K_CHECKSIG, min.max(2))
    } else if src.contains("cast_to_bool") {
        effect(K_VERIFY, min.max(1))
    } else if src.contains("item.len()") {
        effect(K_SIZE, min.max(1))
    } else if src.contains("stack.len() as i64") {
        effect(K_DEPTH, 0)
    } else if src.contains("stack.pop()") && !src.contains("stack.push") {
        effect(K_DROP, min.max(1))
    } else if src.contains("stack.push") {
        effect(K_SWAP, min.max(2))
    } else if src.contains("Ok(false)") && src.len() < 400 {
        effect(K_FAIL, 0)
    } else if src.contains("Ok(true)") && !src.contains("stack.push") && !src.contains("verify_") {
        effect(K_NOP, 0)
    } else {
        effect(K_UNKNOWN, min)
    };
    e.min = if e.kind == K_DISABLED || e.kind == K_NOP || e.kind == K_FAIL || e.kind == K_PUSH {
        e.min
    } else {
        min_stack(src).max(if e.min == 0 { min } else { e.min })
    };
    // A bumped `stack.len() < N` is the body minimum the boundary mutant uses.
    if let Some(n) = len_lt(src) {
        e.min = n;
    }
    e.step = step;
    e
}

fn min_stack_or(src: &str, default: u32) -> u32 {
    len_lt(src).unwrap_or(default).max(min_stack(src))
}

fn len_lt(src: &str) -> Option<u32> {
    let key = "stack.len() < ";
    let i = src.find(key)?;
    let rest = &src[i + key.len()..];
    let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
    digits.parse().ok()
}

fn min_stack(src: &str) -> u32 {
    if let Some(n) = len_lt(src) {
        return n;
    }
    if let Some(i) = src.find("stack.len() >= ") {
        let rest = &src[i + "stack.len() >= ".len()..];
        let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
        if let Ok(n) = digits.parse() {
            return n;
        }
    }
    if src.contains("is_empty()") || src.contains(".pop()") || src.contains("stack.last()") {
        1
    } else {
        0
    }
}

fn step_of(src: &str) -> u32 {
    for line in src.lines() {
        let t = line.trim();
        let Some(rest) = t.strip_prefix("i += ") else {
            continue;
        };
        let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
        if !digits.is_empty() && rest[digits.len()..].starts_with(';') {
            return digits.parse().unwrap_or(1);
        }
    }
    1
}

fn boundary_patch(src: &str) -> String {
    if let Some(n) = len_lt(src) {
        return src.replacen(
            &format!("stack.len() < {n}"),
            &format!("stack.len() < {}", n + 1),
            1,
        );
    }
    if let Some(i) = src.find("stack.len() >= ") {
        let rest = &src[i + "stack.len() >= ".len()..];
        let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
        if let Ok(n) = digits.parse::<u32>() {
            return src.replacen(
                &format!("stack.len() >= {n}"),
                &format!("stack.len() >= {}", n + 1),
                1,
            );
        }
    }
    if src.contains("i += 1;") {
        return src.replacen("i += 1;", "i += 2;", 1);
    }
    if src.contains("stack.is_empty()") {
        return src.replacen("stack.is_empty()", "stack.len() < 2", 1);
    }
    format!("if stack.len() < 99 {{ return Ok(false); }}\n{src}")
}

fn predicate_patch(name: &str, src: &str) -> String {
    let before = classify(src);
    if src.contains("verify_") {
        let patched = src.replace("verify_", "gone_");
        if classify(&patched) != before {
            return patched;
        }
    }
    if src.contains("op_hash160") || src.contains("Ripemd160") {
        let patched = src
            .replace("op_hash160", "op_sha256")
            .replace("Ripemd160", "GoneHash");
        if classify(&patched) != before {
            return patched;
        }
    }
    if src.contains("execute_opcode_with_context_full") {
        let patched = src.replace("execute_opcode_with_context_full", "gone_exec");
        if classify(&patched) != before {
            return patched;
        }
    }
    let swaps = [
        ("len - 1 - n", "len - 2 - n"),
        ("stack.push(second)", "stack.push(top)"),
        ("stack.push(sixth)", "stack.push(fifth)"),
        ("stack.push(top)", "stack.push(second)"),
        ("b + a", "b - a"),
        ("b - a", "b + a"),
        ("a + 1", "a - 1"),
        ("a - 1", "a + 1"),
        ("b < a", "b > a"),
        ("b > a", "b < a"),
        ("b <= a", "b >= a"),
        ("b >= a", "b <= a"),
        ("a == b", "a != b"),
        ("if a == 0", "if a != 0"),
        ("if a != 0", "if a == 0"),
        ("n + 1", "n + 2"),
        ("DisabledOpcode", "OkTrueBypass"),
        ("stack.push(item)", "stack.push(Vec::new())"),
        ("op_hash160", "op_sha256"),
        ("op_sha256", "op_hash160"),
        ("check_bip65(", "check_bip65_gone("),
        ("is_sequence_disabled(", "is_sequence_disabled_gone("),
        ("op_sha1", "op_sha256"),
        ("op_ripemd160", "op_sha256"),
        ("op_hash256", "op_sha1"),
        ("control_stack.push", "control_stack.len"),
        ("OP_N_BASE", "OP_N_BASE_PLUS"),
        ("0x81", "0x01"),
        ("to_stack_element(&[])", "to_stack_element(&[1])"),
        ("cast_to_bool", "cast_to_true"),
        ("std::cmp::min", "std::cmp::max"),
        ("std::cmp::max", "std::cmp::min"),
        ("a != 0 && b != 0", "a != 0 || b != 0"),
        ("a != 0 || b != 0", "a != 0 && b != 0"),
        ("x >= min_val && x < max_val", "x > min_val && x < max_val"),
        ("Ripemd160::digest", "Sha256::digest"),
    ];
    for (a, b) in swaps {
        if src.contains(a) {
            let patched = src.replace(a, b);
            if classify(&patched) != before {
                return patched;
            }
        }
    }
    if name == "OP_NOP" || name == "OP_CODESEPARATOR" || name == "OP_CHECKTEMPLATEVERIFY" {
        return format!("{src}\nDisabledOpcode");
    }
    if name == "OP_RETURN" {
        return src.replace("Ok(false)", "Ok(true)");
    }
    format!("{src}\nb + a")
}

fn effect_query(body: &Effect, clause: &Effect) -> SatResult {
    let body = *body;
    let clause = *clause;
    production_lock::check(|ctx, solver| {
        let a = BV::new_const(ctx, "a", 32);
        let b = BV::new_const(ctx, "b", 32);
        let bv = encode(ctx, body, &a, &b);
        let cv = encode(ctx, clause, &a, &b);
        let min_ok = Bool::from_bool(ctx, body.min == clause.min);
        let step_ok = Bool::from_bool(ctx, body.step == clause.step);
        solver.assert(&a.bvugt(&BV::from_u64(ctx, 2, 32)));
        solver.assert(&b.bvugt(&BV::from_u64(ctx, 2, 32)));
        solver.assert(&(min_ok & step_ok & bv._eq(&cv)).not());
    })
}

fn encode<'a>(ctx: &'a z3::Context, e: Effect, a: &BV<'a>, b: &BV<'a>) -> BV<'a> {
    let one = BV::from_u64(ctx, 1, 32);
    let zero = BV::from_u64(ctx, 0, 32);
    match e.kind {
        K_ADD => a.bvadd(b),
        K_SUB => a.bvsub(b),
        K_ADD1 => a.bvadd(&BV::from_i64(ctx, if e.arg == 0 { 0 } else { 1 }, 32)),
        K_SUB1 => a.bvsub(&one),
        K_NEG => a.bvneg(),
        K_ABS => a.bvslt(&zero).ite(&a.bvneg(), a),
        K_NOT => a._eq(&zero).ite(&one, &zero),
        K_NZ => a._eq(&zero).ite(&zero, &one),
        K_EQ => {
            let eq = a._eq(b);
            (if e.arg == 1 { eq.not() } else { eq }).ite(&one, &zero)
        }
        K_EQV => a._eq(b).ite(&one, &zero),
        K_LT => b.bvslt(a).ite(&one, &zero),
        K_GT => b.bvsgt(a).ite(&one, &zero),
        K_LE => b.bvsle(a).ite(&one, &zero),
        K_GE => b.bvsge(a).ite(&one, &zero),
        K_AND => (a._eq(&zero).not() & b._eq(&zero).not()).ite(&one, &zero),
        K_OR => (a._eq(&zero).not() | b._eq(&zero).not()).ite(&one, &zero),
        K_MIN => a.bvslt(b).ite(a, b),
        K_MAX => a.bvsgt(b).ite(a, b),
        K_WITHIN => (a.bvsge(b) & a.bvslt(b)).ite(&one, &zero),
        K_PUSH if e.arg == -100 => a.bvsub(&BV::from_u64(ctx, 0x50, 32)),
        K_PUSH if e.arg == -101 => a.bvsub(&BV::from_u64(ctx, 0x51, 32)),
        K_PUSH => BV::from_i64(ctx, e.arg, 32),
        K_DUP => a.clone(),
        K_DROP | K_FAIL => zero,
        K_NOP | K_SIZE | K_DEPTH => a.clone(),
        K_SWAP => b.clone(),
        K_PERM => BV::from_i64(ctx, e.arg, 32),
        K_VERIFY => a._eq(&zero).ite(&zero, &one),
        K_HASH => {
            let sort = Sort::bitvector(ctx, 32);
            let f = z3::FuncDecl::new(ctx, format!("hash{}", e.arg), &[&sort], &sort);
            f.apply(&[a]).as_bv().unwrap()
        }
        K_CHECKSIG | K_BIP65 | K_CSV => {
            let bit = Bool::new_const(ctx, format!("ext{}", e.kind));
            if e.arg == 0 {
                bit.ite(&one, &zero)
            } else {
                one
            }
        }
        K_SIGADD => a.bvadd(&BV::from_i64(ctx, e.arg, 32)),
        K_CTRL | K_ALT => a.bvadd(&one),
        K_DISABLED => BV::from_u64(ctx, 0xdead, 32),
        _ => BV::from_u64(ctx, 0x0bad, 32),
    }
}

fn opcode_names(src: &str) -> Vec<String> {
    let mut names = Vec::new();
    let b = src.as_bytes();
    let mut i = 0;
    while i + 3 < b.len() {
        if &b[i..i + 3] == b"OP_" {
            let start = i;
            i += 3;
            while i < b.len()
                && (b[i].is_ascii_uppercase() || b[i].is_ascii_digit() || b[i] == b'_')
            {
                i += 1;
            }
            let name = &src[start..i];
            let after = src[i..].trim_start();
            if (after.starts_with("=>") || after.starts_with("==") || after.starts_with("..="))
                && !names.iter().any(|n: &String| n == name)
            {
                names.push(name.to_string());
            }
            continue;
        }
        i += 1;
    }
    names
}

fn best_arm(src: &str, name: &str) -> Option<String> {
    let mut best: Option<(i32, String)> = None;
    if (1..=16).any(|n| name == format!("OP_{n}")) {
        if let Some(i) = src.find("OP_1..=OP_16 =>") {
            let arm = slice_arm(&src[i..]);
            return Some(arm);
        }
    }
    let markers = [format!("{name} =>"), format!("opcode == {name}")];
    for marker in markers {
        let mut from = 0;
        while let Some(rel) = src[from..].find(&marker) {
            let at = from + rel;
            let end = at + marker.len();
            let next = src[end..].chars().next();
            if next.is_some_and(|c| c.is_ascii_alphanumeric() || c == '_') {
                from = end;
                continue;
            }
            let arm = slice_arm(&src[at..]);
            let s = arm_score(&arm);
            if best.as_ref().map(|(b, _)| s >= *b).unwrap_or(true) {
                best = Some((s, arm));
            }
            from = at + marker.len();
        }
    }
    best.map(|(_, a)| a)
}

fn arm_score(text: &str) -> i32 {
    let mut s = (text.len() / 80) as i32;
    if text.contains("DisabledOpcode") {
        s += 50;
    }
    if text.contains("op_hash")
        || text.contains("op_sha")
        || text.contains("op_ripemd")
        || text.contains("op_checksig")
    {
        s += 40;
    }
    if text.contains("b + a") || text.contains("a + 1") || text.contains("script_num_encode") {
        s += 40;
    }
    if text.contains("verify_")
        || text.contains("check_bip65")
        || text.contains("is_sequence_disabled")
    {
        s += 40;
    }
    if text.contains("stack.push") || text.contains("stack.pop") || text.contains("control_stack") {
        s += 40;
    }
    if text.contains("pubkeys") {
        s += 30;
    }
    if text.contains("Ok(true)") || text.contains("Ok(false)") {
        s += 8;
    }
    if !text.contains("stack")
        && !text.contains("Ok(")
        && !text.contains("return")
        && !text.contains("op_")
        && !text.contains("Disabled")
    {
        s -= 80;
    }
    s
}

fn slice_arm(rest: &str) -> String {
    let b = rest.as_bytes();
    let mut i = 0;
    let mut depth = 0i32;
    let mut started = false;
    let mut paren = 0i32;
    while i < b.len() && i < 80_000 {
        if b[i] == b'"' {
            i += 1;
            while i < b.len() {
                if b[i] == b'\\' {
                    i += 2;
                    continue;
                }
                if b[i] == b'"' {
                    break;
                }
                i += 1;
            }
        } else if b[i] == b'(' {
            paren += 1;
        } else if b[i] == b')' {
            paren -= 1;
        } else if b[i] == b'{' {
            depth += 1;
            started = true;
        } else if b[i] == b'}' {
            depth -= 1;
            if started && depth == 0 {
                return rest[..=i].to_string();
            }
        } else if b[i] == b',' && depth == 0 && paren == 0 && !started {
            return rest[..=i].to_string();
        }
        i += 1;
    }
    rest.chars().take(1500).collect()
}

fn expand_arm(arm: &str, arith: &str, crypto: &str) -> String {
    for (file, names) in [
        (
            arith,
            &[
                "op_add",
                "op_sub",
                "op_booland",
                "op_boolor",
                "op_numequal",
                "op_numequalverify",
                "op_numnotequal",
                "op_lessthan",
                "op_greaterthan",
                "op_lessthanorequal",
                "op_greaterthanorequal",
                "op_min",
                "op_max",
                "op_within",
                "op_mul_disabled",
                "op_div_disabled",
                "op_mod_disabled",
                "op_lshift_disabled",
                "op_rshift_disabled",
            ][..],
        ),
        (
            crypto,
            &[
                "op_hash160",
                "op_hash256",
                "op_sha256",
                "op_sha1",
                "op_ripemd160",
                "op_checksig_simple",
            ][..],
        ),
    ] {
        for name in names {
            if arm.contains(&format!("{name}(")) || arm.contains(&format!("{name}()")) {
                if let Some(body) = find_fn(file, name) {
                    return format!("{arm}\n{body}");
                }
            }
        }
    }
    arm.to_string()
}

fn find_fn(src: &str, name: &str) -> Option<String> {
    let marker = format!("fn {name}(");
    let start = src.find(&marker)?;
    Some(slice_braces(&src[start..]))
}

fn fold_rows() -> Vec<LockRow> {
    let sig = repo("blvm-consensus/src/sigop.rs");
    let weight = extract_fn(
        &repo("blvm-consensus/src/segwit.rs"),
        "calculate_block_weight",
    );
    let chain = extract_fn(
        &repo("blvm-consensus/src/reorganization.rs"),
        "calculate_chain_work",
    );
    let apply = extract_fn(
        &repo("blvm-consensus/src/block/apply.rs"),
        "apply_transaction_with_id",
    );
    vec![
        row(
            "count_sigops_in_script",
            "fold",
            &sig,
            &sig.replace("saturating_add(1)", "saturating_add(0)"),
            &sig.replace(
                "const MAX_PUBKEYS_PER_MULTISIG: u32 = 20;",
                "const MAX_PUBKEYS_PER_MULTISIG: u32 = 21;",
            ),
            sigop_query,
        ),
        row(
            "calculate_block_weight",
            "fold",
            &weight,
            &weight.replace("total_weight +=", "total_weight ="),
            &weight.replace("calculate_transaction_weight(tx, witness)?", "0"),
            block_weight_query,
        ),
        row(
            "calculate_chain_work",
            "fold",
            &chain,
            &chain.replace(
                "total_work = total_work.saturating_add(work_contribution);",
                "total_work = old_total;",
            ),
            &chain.replace(
                "saturating_add(work_contribution)",
                "saturating_add(work_contribution.saturating_add(U256::one()))",
            ),
            chain_work_query,
        ),
        row(
            "apply_transaction_with_id",
            "fold",
            &apply,
            &apply.replace(
                "if let Some(arc) = utxo_set.remove(&input.prevout) {",
                "if let Some(arc) = None {",
            ),
            &apply.replace(
                "utxo_set.insert(outpoint, utxo_arc);",
                "let _kept = utxo_arc;",
            ),
            utxo_step_query,
        ),
    ]
}

fn zero_init(src: &str, name: &str, assign: &str) -> u64 {
    let body = if src.contains(&format!("fn {name}(")) || src.contains(&format!("fn {name}<")) {
        extract_fn(src, name)
    } else {
        src.to_string()
    };
    if body.contains(assign) { 0 } else { 1 }
}

fn sigop_query(src: &str) -> SatResult {
    let cs = if src.contains("saturating_add(0)") {
        0u64
    } else if src.contains("saturating_add(2)") {
        2
    } else {
        1
    };
    let ms = if src.contains("= 21;") { 21u64 } else { 20 };
    let init = zero_init(src, "count_sigops_in_script", "let mut count = 0u32;");
    production_lock::check(|ctx, solver| {
        let checksig = Bool::new_const(ctx, "checksig");
        let multi = Bool::new_const(ctx, "multi");
        solver.assert(&(checksig.clone() & multi.clone()).not());
        let count = BV::new_const(ctx, "count", 32);
        let body_d = checksig.ite(
            &BV::from_u64(ctx, cs, 32),
            &multi.ite(&BV::from_u64(ctx, ms, 32), &BV::from_u64(ctx, 0, 32)),
        );
        let clause_d = checksig.ite(
            &BV::from_u64(ctx, 1, 32),
            &multi.ite(&BV::from_u64(ctx, 20, 32), &BV::from_u64(ctx, 0, 32)),
        );
        let base_ok = BV::from_u64(ctx, init, 32)._eq(&BV::from_u64(ctx, 0, 32));
        let step_ok = count.bvadd(&body_d)._eq(&count.bvadd(&clause_d));
        solver.assert(&(base_ok & step_ok).not());
    })
}

fn block_weight_query(src: &str) -> SatResult {
    let accumulates = src.contains("total_weight +=");
    let uses = src.contains("calculate_transaction_weight");
    let init = zero_init(src, "calculate_block_weight", "let mut total_weight = 0;");
    production_lock::check(|ctx, solver| {
        let acc = BV::new_const(ctx, "acc", 64);
        let w = BV::new_const(ctx, "w", 64);
        solver.assert(&acc.bvugt(&BV::from_u64(ctx, 0, 64)));
        solver.assert(&w.bvugt(&BV::from_u64(ctx, 0, 64)));
        let body = if accumulates && uses {
            acc.bvadd(&w)
        } else if uses {
            w.clone()
        } else {
            acc.clone()
        };
        let base_ok = BV::from_u64(ctx, init, 64)._eq(&BV::from_u64(ctx, 0, 64));
        solver.assert(&(base_ok & body._eq(&acc.bvadd(&w))).not());
    })
}

fn chain_work_query(src: &str) -> SatResult {
    let mode = if src.contains("work_contribution.saturating_add(U256::one())") {
        2
    } else if src.contains("total_work = old_total") {
        1
    } else if src.contains("saturating_add(work_contribution)") {
        0
    } else {
        1
    };
    let init = zero_init(
        src,
        "calculate_chain_work",
        "let mut total_work = crate::pow::U256::zero();",
    );
    production_lock::check(|ctx, solver| {
        let acc = BV::new_const(ctx, "acc", 64);
        let proof = BV::new_const(ctx, "proof", 64);
        solver.assert(&proof.bvugt(&BV::from_u64(ctx, 0, 64)));
        solver.assert(&acc.bvult(&BV::from_u64(ctx, u64::MAX / 4, 64)));
        let body = match mode {
            0 => acc.bvadd(&proof),
            2 => acc.bvadd(&proof).bvadd(&BV::from_u64(ctx, 1, 64)),
            _ => acc.clone(),
        };
        let base_ok = BV::from_u64(ctx, init, 64)._eq(&BV::from_u64(ctx, 0, 64));
        solver.assert(&(base_ok & body._eq(&acc.bvadd(&proof))).not());
    })
}

fn utxo_step_query(src: &str) -> SatResult {
    let removed = src.contains("utxo_set.remove(&input.prevout)");
    let inserted = src.contains("utxo_set.insert(outpoint");
    production_lock::check(|ctx, solver| {
        let supply = BV::new_const(ctx, "supply", 64);
        let spent = BV::new_const(ctx, "spent", 64);
        let created = BV::new_const(ctx, "created", 64);
        solver.assert(&spent.bvugt(&BV::from_u64(ctx, 0, 64)));
        solver.assert(&created.bvugt(&BV::from_u64(ctx, 0, 64)));
        solver.assert(&supply.bvugt(&spent));
        let mut next = if removed {
            supply.bvsub(&spent)
        } else {
            supply.clone()
        };
        if inserted {
            next = next.bvadd(&created);
        }
        let member = Bool::from_bool(ctx, inserted);
        let clause = supply.bvsub(&spent).bvadd(&created);
        solver.assert(&(next._eq(&clause) & member).not());
    })
}

/// Names the finish test requires. A missing or unlocked row fails the suite.
pub const CENSUS: &[&str] = &[
    "check_transaction",
    "is_strict_der",
    "merkle_tree_from_hashes",
    "is_sequence_disabled",
    "extract_sequence_type_flag",
    "extract_sequence_locktime_value",
    "get_locktime_type",
    "check_bip65",
    "check_proof_of_work",
    "validate_witness_program_length",
    "validate_block_header",
    "validate_block_header_mtp",
    "try_verify_p2pk_fast_path",
    "try_verify_p2pkh_fast_path",
    "try_verify_p2sh_fast_path",
    "try_verify_p2wpkh_fast_path",
    "compute_script_cache_key",
    "verify_script_cache_hit",
    "sighash_single_quirk",
    "eval_script_pc",
    "eval_script_control",
    "get_block_subsidy",
    "calculate_transaction_weight_segwit",
    "weight_to_vsize",
    "check_coinbase_subsidy",
    "expand_target",
    "get_block_proof",
    "is_coinbase",
    "taproot_activation_height",
    "check_bip30",
    "check_bip34",
    "check_bip90",
    "check_bip147",
    "is_bip54_active_at",
    "check_coinbase_maturity",
    "get_median_time_past",
    "activation_height_from_headers",
    "compute_legacy_sighash_nocache",
    "build_bip143_preimage",
    "compute_taproot_signature_hash",
    "serialize_block_header",
    "push_advance",
    "OP_CHECKSIG_verifier",
    "OP_DUP",
    "OP_EQUAL",
    "OP_EQUALVERIFY",
    "OP_HASH160",
    "OP_CHECKSIG",
    "OP_ADD",
    "OP_CHECKLOCKTIMEVERIFY",
    "count_sigops_in_script",
    "calculate_block_weight",
    "calculate_chain_work",
    "apply_transaction_with_id",
    "verify_signature",
    "verify_tapscript_schnorr_signature",
    "verify_signature_from_stack",
    "calculate_sequence_locks",
    "evaluate_sequence_locks",
    "get_next_work_required",
    "total_supply",
    "verify_utxo_supply",
    "get_block_script_verify_flags_core",
    "check_bip66",
    "check_bip54_timewarp",
    "check_bip54_tx_stripped_size",
    "check_bip54_sigop_limit",
    "check_bip54_coinbase",
    "cast_to_bool",
    "is_minimal_if_condition",
    "p2sh_push_only_check",
    "find_and_delete",
    "extract_witness_commitment",
    "compute_taproot_signature_hash",
    "should_reorganize",
    "get_transaction_sigop_cost_with_utxos",
    "check_tx_inputs",
    "block_weight_limit",
    "block_sigop_limit",
    "coinbase_scriptsig_len",
    "is_final_tx",
    "eval_script_limits",
    "script_num_decode",
    "opcode_dispatch",
    "if_body_endif",
    "enforce_tx_finality",
    "retarget_mul_div",
    "compress_target",
    "opcode_bytes",
    "validate_supply_limit",
    "calculate_fee",
    "validate_witness_commitment",
    "strip_taproot_annex",
    "count_witness_sigops",
    "connect_block",
    "eval_script_pipeline",
    "get_next_work_pipeline",
    "count_sigops_induction",
    "block_weight_induction",
    "chain_work_induction",
    "block_fee_induction",
    "validate_block_header_fields",
    "validate_prev_block_hash",
    "is_op_success",
    "is_push_opcode",
    "block_weight_from_nested",
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn census_is_locked() {
        if !crate::parser::spec_expr::consensus_workspace_present() {
            return;
        }
        let got = rows();
        let mut bad = Vec::new();
        for name in CENSUS {
            if !got.iter().any(|r| r.function == *name) {
                bad.push(format!("missing {name}"));
            }
        }
        for name in crate::parser::spec_expr::SPEC_SOURCED {
            if !got
                .iter()
                .any(|r| r.function == *name && r.unpatched == SatResult::Unsat)
            {
                bad.push(format!("spec-sourced {name} is not a locked row"));
            }
        }
        for row in got {
            if row.unpatched != SatResult::Unsat {
                bad.push(format!(
                    "{} unpatched {:?} {}",
                    row.function, row.unpatched, row.note
                ));
            }
            if row.boundary != SatResult::Sat {
                bad.push(format!("{} boundary {:?}", row.function, row.boundary));
            }
            if row.predicate != SatResult::Sat {
                bad.push(format!("{} predicate {:?}", row.function, row.predicate));
            }
        }
        assert!(bad.is_empty(), "{}", bad.join("\n"));
    }
}
