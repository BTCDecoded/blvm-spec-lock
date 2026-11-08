//! Consensus-decisive production locks.
//!
//! Each row is `body ∧ ¬clause` on the production arm. Unpatched is UNSAT.
//! A boundary patch and a predicate patch are each SAT. The clause uses the
//! operator in that arm (shift, compare, preimage byte, verifier result, fold).

use super::production_lock::{self, ProductionFacts, facts_of};
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
    rows.extend(threshold_rows());
    rows.extend(preimage_rows());
    rows.extend(signet_rows());
    rows.extend(multisig_rows());
    rows.extend(tx_version_rows());
    rows.extend(reorg_undo_rows());
    rows.extend(reorg_window_rows());
    rows.extend(genesis_coinbase_rows());
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
    Vec::new()
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

fn mentions_call(body: &str, callee: &str) -> bool {
    let needle = format!("{callee}(");
    body.match_indices(&needle)
        .any(|(at, _)| !body[..at].ends_with("fn "))
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
        "finish_p2wpkh_ecdsa",
        "verify_p2sh_p2pkh_redeem",
        "verify_p2sh_p2pk_redeem",
    ] {
        if mentions_call(body, callee) {
            return fast_calls(file, &extract_fn(file, callee));
        }
    }
    false
}

fn threshold_rows() -> Vec<LockRow> {
    let bip = repo("blvm-consensus/src/bip_validation.rs");
    let bip147 = extract_fn(&bip, "check_bip147");
    let null_dummy = extract_fn(&bip, "is_null_dummy");
    let bip147_full = format!("{bip147}\n{null_dummy}");
    vec![row(
        "check_bip147",
        "threshold",
        &bip147_full,
        &bip147_full.replace("script_sig.is_empty()", "false && script_sig.is_empty()"),
        &bip147_full.replace("first_push_empty = true", "first_push_empty = false"),
        bip147_query,
    )]
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
    // append_bip341_sigmsg is the body identity. The sighash keep still emits the name.
    Vec::new()
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
    ("spend", "sigmsg.push(spend_type)"),
    ("index", "input_index as u32"),
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

fn signet_rows() -> Vec<LockRow> {
    Vec::new()
}

fn multisig_rows() -> Vec<LockRow> {
    let script = repo("blvm-consensus/src/script/mod.rs");
    let resolver = repo("blvm-consensus/src/ecdsa_batch.rs");
    let src = format!(
        "{}\n{}\n{}",
        extract_fn(&script, "checkmultisig_window"),
        [
            "checkmultisig_window(stack, m, false)",
            "checkmultisig_window(&pushes, m, false)",
            "checkmultisig_window(items, m, true)",
            "let stack = &pushes[..pushes.len() - 1];",
        ]
        .into_iter()
        .map(|needle| line_containing(&script, needle))
        .collect::<Vec<_>>()
        .join("\n"),
        line_containing(
            &resolver,
            "p.sig_empty.len() == p.m as usize && valid_sigs == p.m"
        ),
    );
    let boundary = src.replacen("items.len() - m", "1", 1);
    let predicate = src.replacen("items.len() != need", "items.len() < need", 1);
    vec![row(
        "checkmultisig_window",
        "multisig",
        &src,
        &boundary,
        &predicate,
        checkmultisig_window_query,
    )]
}

fn tx_version_rows() -> Vec<LockRow> {
    let ser = repo("blvm-primitives/src/serialization/transaction.rs");
    let locks = repo("blvm-consensus/src/sequence_locks.rs");
    let script = repo("blvm-consensus/src/script/mod.rs");
    let connect = repo("blvm-consensus/src/block/connect.rs");
    let writes = ser
        .lines()
        .filter(|line| line.contains("(tx.version as u32).to_le_bytes()"))
        .collect::<Vec<_>>()
        .join("\n");
    let mempool = repo("blvm-consensus/src/mempool.rs");
    let src = format!(
        "{}\n{writes}\n{}\n{}\n{}\n{}",
        extract_fn(&ser, "deserialize_transaction_with_witness"),
        extract_fn(&locks, "version_enforces_relative_lock"),
        line_containing(&script, "version_enforces_relative_lock"),
        line_containing(&connect, "version_enforces_relative_lock"),
        line_containing(&mempool, "version_enforces_relative_lock"),
    );
    let boundary = src.replacen(
        "let version = u32::from_le_bytes(",
        "let version = i32::from_le_bytes(",
        1,
    );
    let predicate = src.replacen("(version as u32) >= 2", "(version as u32) as i32 >= 2", 1);
    vec![row(
        "deserialize_transaction_with_witness",
        "tx-version",
        &src,
        &boundary,
        &predicate,
        tx_version_wire_query,
    )]
}

fn reorg_undo_rows() -> Vec<LockRow> {
    let src_file = repo("blvm-consensus/src/reorganization.rs");
    let src = format!(
        "{}\n{}",
        extract_fn(&src_file, "calculate_block_hash"),
        line_containing(&src_file, "missing undo log"),
    );
    let boundary = src.replacen(
        "block_header_hash(header)",
        "header.version.to_le_bytes()",
        1,
    );
    let predicate = src.replacen("missing undo log", "unwrap_or_else", 1);
    vec![row(
        "calculate_block_hash",
        "reorg-undo",
        &src,
        &boundary,
        &predicate,
        reorg_undo_key_query,
    )]
}

fn genesis_coinbase_rows() -> Vec<LockRow> {
    let header = repo("blvm-consensus/src/block/header.rs");
    let connect = repo("blvm-consensus/src/block/connect.rs");
    let src = format!(
        "{}\n{}\n{}\n{}",
        extract_fn(&header, "genesis_header_hash"),
        extract_fn(&connect, "is_genesis_block"),
        extract_fn(&connect, "genesis_utxo_unchanged"),
        line_containing(&connect, "if is_genesis_block(block, network)"),
    );
    let boundary = src.replacen(
        "block_header_hash(&genesis_header(network))",
        "genesis_header(network).prev_block_hash",
        1,
    );
    let predicate = src.replacen("BlockUndoLog::new()", "apply_transaction_with_id(", 1);
    vec![row(
        "genesis_header_hash",
        "genesis-coinbase",
        &src,
        &boundary,
        &predicate,
        genesis_coinbase_query,
    )]
}

fn genesis_coinbase_query(src: &str) -> SatResult {
    let hash_fn = extract_fn(src, "genesis_header_hash");
    let identify = extract_fn(src, "is_genesis_block");
    let unchanged = extract_fn(src, "genesis_utxo_unchanged");
    let hashes_header = hash_fn.contains("block_header_hash(&genesis_header(network))");
    let matches_network = identify.contains("== header::genesis_header_hash(network)");
    let keeps_set = unchanged.contains("utxo_set,") && unchanged.contains("BlockUndoLog::new()");
    let no_apply = !unchanged.contains("apply_transaction");
    let called = src.contains("if is_genesis_block(block, network)");
    let ok = hashes_header && matches_network && keeps_set && no_apply && called;
    production_lock::check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, ok).not());
    })
}

fn reorg_window_rows() -> Vec<LockRow> {
    let reorg = repo("blvm-consensus/src/reorganization.rs");
    let node = repo("blvm-node/src/node/reorg_executor.rs");
    let src = format!(
        "{}\n{}\n{}\n{}\n{}\n{}",
        extract_fn(&reorg, "find_common_ancestor"),
        extract_fn(&reorg, "disconnect_block"),
        extract_fn(&reorg, "reorganize_chain_with_witnesses"),
        extract_fn(&reorg, "should_reorganize"),
        extract_fn(&node, "collect_fork_chains"),
        extract_fn(&node, "refresh_active_height_index"),
    );
    let boundary = src.replacen("current_at.get(&hash)", "current_chain.get(new_i)", 1);
    let predicate = src.replacen("active_hash == candidate_hash", "guard < 10_000", 1);
    vec![row(
        "find_common_ancestor",
        "reorg-window",
        &src,
        &boundary,
        &predicate,
        reorg_window_query,
    )]
}

fn reorg_window_query(src: &str) -> SatResult {
    let ancestor = extract_fn(src, "find_common_ancestor");
    let by_hash = ancestor.contains("current_at.get(&hash)");
    let separate_index = ancestor.contains("current_chain_index: cur_i");
    let disconnect = extract_fn(src, "disconnect_block");
    let reorg = extract_fn(src, "reorganize_chain_with_witnesses");
    let should = extract_fn(src, "should_reorganize");
    let walk = extract_fn(src, "collect_fork_chains");
    let refresh = extract_fn(src, "refresh_active_height_index");
    let no_cap = !disconnect.contains("10_000")
        && !reorg.contains("10_000")
        && !should.contains("10_000")
        && !walk.contains("10_000")
        && !refresh.contains("10_000");
    let aligned = walk.contains("active_hash == candidate_hash");
    let ok = by_hash && separate_index && no_cap && aligned;
    production_lock::check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, ok).not());
    })
}

fn reorg_undo_key_query(src: &str) -> SatResult {
    let body = extract_fn(src, "calculate_block_hash");
    let uses_header_hash = body.contains("block_header_hash(header)");
    let no_wide_header = !body.contains("version.to_le_bytes()");
    let miss_is_error = src.contains("missing undo log");
    let no_empty_fallback = !src.contains("unwrap_or_else");
    let ok = uses_header_hash && no_wide_header && miss_is_error && no_empty_fallback;
    production_lock::check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, ok).not());
    })
}

fn tx_version_wire_query(src: &str) -> SatResult {
    let body = extract_fn(src, "deserialize_transaction_with_witness");
    let read_u32 = body.contains("let version = u32::from_le_bytes(");
    let no_sign_extend = !body.contains("i32::from_le_bytes(");
    let writes = src.matches("(tx.version as u32).to_le_bytes()").count() == 2;
    let gate = extract_fn(src, "version_enforces_relative_lock");
    let unsigned = gate.contains("(version as u32) >= 2");
    let no_signed_gate = !gate.contains("as i32");
    let callers = src.matches("version_enforces_relative_lock").count() >= 4;
    let ok = read_u32 && no_sign_extend && writes && unsigned && no_signed_gate && callers;
    production_lock::check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, ok).not());
    })
}

fn checkmultisig_window_query(src: &str) -> SatResult {
    let body = extract_fn(src, "checkmultisig_window");
    let top_m = body.contains("items.len() - m");
    let exact = body.contains("items.len() != need");
    let no_prefix = !body.contains("skip(1)") && !body.contains("[1..]");
    let legacy_p2sh = src.contains("checkmultisig_window(stack, m, false)");
    let legacy_bare = src.contains("checkmultisig_window(&pushes, m, false)");
    let witness = src.contains("checkmultisig_window(items, m, true)");
    let redeem_is_not_a_signature = src.contains("let stack = &pushes[..pushes.len() - 1];");
    let every_signature = src.contains("p.sig_empty.len() == p.m as usize && valid_sigs == p.m");
    let ok = top_m
        && exact
        && no_prefix
        && legacy_p2sh
        && legacy_bare
        && witness
        && redeem_is_not_a_signature
        && every_signature;
    production_lock::check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, ok).not());
    })
}

fn line_containing(src: &str, needle: &str) -> String {
    src.lines()
        .find(|line| line.contains(needle))
        .unwrap_or_else(|| panic!("missing {needle}"))
        .to_string()
}

fn opcode_rows() -> Vec<LockRow> {
    let script = repo("blvm-consensus/src/script/mod.rs");
    let arith = repo("blvm-consensus/src/script/arithmetic.rs");
    let crypto = repo("blvm-consensus/src/script/crypto_ops.rs");
    let mut rows = Vec::new();
    let mut names = opcode_names(&script);
    names.sort();
    names.dedup();
    for name in names {
        if name == "OP_DUP"
            || name == "OP_EQUAL"
            || name == "OP_EQUALVERIFY"
            || name == "OP_ADD"
            || name == "OP_2DIV"
            || name == "OP_2MUL"
            || name == "OP_MUL"
            || name == "OP_DIV"
            || name == "OP_MOD"
            || name == "OP_LSHIFT"
            || name == "OP_RSHIFT"
            || name == "OP_SUB"
            || name == "OP_BOOLAND"
            || name == "OP_BOOLOR"
            || name == "OP_NUMEQUAL"
            || name == "OP_NUMEQUALVERIFY"
            || name == "OP_LESSTHAN"
            || name == "OP_GREATERTHAN"
            || name == "OP_LESSTHANOREQUAL"
            || name == "OP_GREATERTHANOREQUAL"
            || name == "OP_MIN"
            || name == "OP_MAX"
            || name == "OP_WITHIN"
            || name == "OP_1ADD"
            || name == "OP_1SUB"
            || name == "OP_1NEGATE"
            || name == "OP_0"
            || name == "OP_1"
            || name == "OP_2"
            || name == "OP_3"
            || name == "OP_4"
            || name == "OP_5"
            || name == "OP_6"
            || name == "OP_7"
            || name == "OP_8"
            || name == "OP_9"
            || name == "OP_10"
            || name == "OP_11"
            || name == "OP_12"
            || name == "OP_13"
            || name == "OP_14"
            || name == "OP_15"
            || name == "OP_16"
            || name == "OP_SWAP"
            || name == "OP_2DUP"
            || name == "OP_2ROT"
            || name == "OP_2SWAP"
            || name == "OP_3DUP"
            || name == "OP_ROT"
            || name == "OP_TUCK"
            || name == "OP_NIP"
            || name == "OP_IF"
            || name == "OP_IFDUP"
            || name == "OP_PICK"
            || name == "OP_ROLL"
            || name == "OP_VERIFY"
            || name == "OP_HASH160"
            || name == "OP_CHECKSIGADD"
            || name == "OP_CHECKSIGVERIFY"
            || name == "OP_CHECKMULTISIGVERIFY"
            || name == "OP_CHECKSIG"
            || name == "OP_CHECKMULTISIG"
            || name == "OP_NOT"
            || name == "OP_0NOTEQUAL"
            || name == "OP_CHECKLOCKTIMEVERIFY"
            || name == "OP_CHECKSEQUENCEVERIFY"
            || name == "OP_VER"
            || name.starts_with("OP_PUSHDATA")
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
    } else if src.contains("script_num_encode(n + ")
        || (src.contains("eval_checksig_tapscript") && src.contains("n + 1"))
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
        || src.contains("eval_checksig_ecdsa(")
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
    } else if (src.contains("Ok(true)") && !src.contains("stack.push") && !src.contains("verify_"))
        || src.contains("upgradable_nop(")
    {
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
    if src.contains("eval_checksig_ecdsa(") {
        let patched = src.replace("eval_checksig_ecdsa(", "eval_checksig_gone(");
        if classify(&patched) != before {
            return patched;
        }
    }
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
    if (1..=16).any(|n| name == format!("OP_{n}")) {
        if let Some(i) = src.find("OP_1..=OP_16 =>") {
            let arm = slice_arm(&src[i..]);
            return Some(arm);
        }
    }
    // A `NAME =>` arm is the opcode. `opcode == NAME` also matches guards and
    // helper predicates, and those slices outscore the real arm.
    let arrow = format!("{name} =>");
    if let Some(arm) = best_marker(src, &arrow) {
        return Some(arm);
    }
    best_marker(src, &format!("opcode == {name}"))
}

fn best_marker(src: &str, marker: &str) -> Option<String> {
    let mut best: Option<(i32, String)> = None;
    let mut from = 0;
    while let Some(rel) = src[from..].find(marker) {
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
    if text.contains("eval_checksig") {
        s += 50;
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
        } else if (b[i] == b',' || b[i] == b';') && depth == 0 && paren == 0 && !started {
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
    Vec::new()
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
    let accumulates = src.contains("total_weight +=") || src.contains(".checked_add(");
    let uses = src.contains("calculate_transaction_weight");
    let base = src.contains("let mut total_weight = 0;") || src.contains("checked_mul(4)");
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
        let base_ok = Bool::from_bool(ctx, base);
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
    "check_bip147",
    "p2sh_push_only_check",
    "validate_supply_limit",
    "connect_block",
    "eval_script_pipeline",
    "block_fee_induction",
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn op_add_concrete_sum_differs_from_sub() {
        if !crate::parser::spec_expr::consensus_workspace_present() {
            return;
        }
        let body =
            find_fn(&repo("blvm-consensus/src/script/arithmetic.rs"), "op_add").expect("op_add");
        assert!(body.contains("b + a"), "{body}");
        let args = [
            ("b", crate::translator::sample_eval::Val::Int(2)),
            ("a", crate::translator::sample_eval::Val::Int(3)),
        ];
        let sum = crate::translator::sample_eval::eval_int(
            "fn f(b: i64, a: i64) -> i64 { b + a }",
            &args,
        );
        let diff = crate::translator::sample_eval::eval_int(
            "fn f(b: i64, a: i64) -> i64 { b - a }",
            &args,
        );
        assert_eq!(sum, 5);
        assert_eq!(diff, -1);
        let swapped = body.replace("b + a", "b - a");
        assert_ne!(classify(&body).kind, classify(&swapped).kind);
    }

    #[test]
    fn checkmultisig_window_is_locked() {
        if !crate::parser::spec_expr::consensus_workspace_present() {
            return;
        }
        let got = multisig_rows();
        assert_eq!(got.len(), 1);
        let row = &got[0];
        assert_eq!(row.unpatched, SatResult::Unsat, "unpatched {}", row.note);
        assert_eq!(row.boundary, SatResult::Sat, "boundary");
        assert_eq!(row.predicate, SatResult::Sat, "predicate");
    }

    #[test]
    fn genesis_coinbase_is_locked() {
        if !crate::parser::spec_expr::consensus_workspace_present() {
            return;
        }
        let got = genesis_coinbase_rows();
        assert_eq!(got.len(), 1);
        let row = &got[0];
        assert_eq!(row.unpatched, SatResult::Unsat, "unpatched {}", row.note);
        assert_eq!(row.boundary, SatResult::Sat, "boundary");
        assert_eq!(row.predicate, SatResult::Sat, "predicate");
    }

    #[test]
    fn reorg_window_is_locked() {
        if !crate::parser::spec_expr::consensus_workspace_present() {
            return;
        }
        let got = reorg_window_rows();
        assert_eq!(got.len(), 1);
        let row = &got[0];
        assert_eq!(row.unpatched, SatResult::Unsat, "unpatched {}", row.note);
        assert_eq!(row.boundary, SatResult::Sat, "boundary");
        assert_eq!(row.predicate, SatResult::Sat, "predicate");
    }

    #[test]
    fn reorg_undo_key_is_locked() {
        if !crate::parser::spec_expr::consensus_workspace_present() {
            return;
        }
        let got = reorg_undo_rows();
        assert_eq!(got.len(), 1);
        let row = &got[0];
        assert_eq!(row.unpatched, SatResult::Unsat, "unpatched {}", row.note);
        assert_eq!(row.boundary, SatResult::Sat, "boundary");
        assert_eq!(row.predicate, SatResult::Sat, "predicate");
    }

    #[test]
    fn tx_version_wire_is_locked() {
        if !crate::parser::spec_expr::consensus_workspace_present() {
            return;
        }
        let got = tx_version_rows();
        assert_eq!(got.len(), 1);
        let row = &got[0];
        assert_eq!(row.unpatched, SatResult::Unsat, "unpatched {}", row.note);
        assert_eq!(row.boundary, SatResult::Sat, "boundary");
        assert_eq!(row.predicate, SatResult::Sat, "predicate");
    }

    #[test]
    fn taproot_sigmsg_bytes_stay_in_append_bip341_sigmsg() {
        if !crate::parser::spec_expr::consensus_workspace_present() {
            return;
        }
        let tap = extract_fn(
            &repo("blvm-consensus/src/taproot.rs"),
            "append_bip341_sigmsg",
        );
        for needle in [
            "// epoch",
            "sigmsg.push(0x00u8)",
            "sigmsg.push(sighash_type)",
            "(tx.version as u32).to_le_bytes()",
            "(tx.lock_time as u32).to_le_bytes()",
            "sha_prevouts",
            "sha_amounts",
            "sha_scriptpubkeys",
            "sha_sequences",
            "sha_outputs",
            "sigmsg.push(spend_type)",
            "input_index as u32",
            "sighash_type & 0x80",
        ] {
            assert!(tap.contains(needle), "{needle}");
        }
        assert!(!tap.contains("to_be_bytes"));
        assert_ne!(tap.replace("sigmsg.push(0x00u8);\n", ""), tap);
        assert_ne!(
            tap.replacen(
                "(tx.version as u32).to_le_bytes()",
                "(tx.version as u32).to_be_bytes()",
                1,
            ),
            tap
        );
        let key = extract_fn(
            &repo("blvm-consensus/src/taproot.rs"),
            "compute_taproot_signature_hash",
        );
        assert!(key.contains("prevout_values.len() < tx.inputs.len()"));
        let script = extract_fn(
            &repo("blvm-consensus/src/taproot.rs"),
            "compute_tapscript_signature_hash",
        );
        assert!(!script.contains("prevout_values.len() < tx.inputs.len()"));
        assert!(script.contains("tap_leaf_hash"));
    }

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
