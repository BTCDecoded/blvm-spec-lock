//! Operator rows past the original census.
//!
//! A row is emitted only when unpatched is UNSAT and both patches are SAT.
//! Unknown stays on the unlocked list.

use super::{LockRow, extract_fn, repo};
use crate::translator::production_lock;
use std::sync::OnceLock;
use z3::SatResult;
use z3::ast::{Ast, BV, Bool};

struct Finish {
    rows: Vec<LockRow>,
    unlocked: Vec<String>,
}

pub fn rows() -> Vec<LockRow> {
    finish().rows.clone()
}

pub fn unlocked() -> &'static [String] {
    &finish().unlocked
}

fn finish() -> &'static Finish {
    static FINISH: OnceLock<Finish> = OnceLock::new();
    FINISH.get_or_init(build)
}

#[allow(clippy::too_many_arguments)]
fn keep(
    rows: &mut Vec<LockRow>,
    unlocked: &mut Vec<String>,
    function: &str,
    shape: &'static str,
    plain: &str,
    boundary: &str,
    predicate: &str,
    query: fn(&str) -> SatResult,
) {
    let row = super::row(function, shape, plain, boundary, predicate, query);
    if row.unpatched == SatResult::Unsat
        && row.boundary == SatResult::Sat
        && row.predicate == SatResult::Sat
    {
        rows.push(row);
    } else {
        unlocked.push(format!(
            "{function} unpatched={:?} boundary={:?} predicate={:?}",
            row.unpatched, row.boundary, row.predicate
        ));
    }
}

/// Present in the dump and disagreeing with the source operator blocks a row.
/// Absence does not.
pub fn mir_blocks(present: bool, agrees: bool) -> bool {
    present && !agrees
}

fn u64b<'a>(ctx: &'a z3::Context, v: u64) -> BV<'a> {
    BV::from_u64(ctx, v, 64)
}

fn build() -> Finish {
    let mut rows = Vec::new();
    let mut unlocked = Vec::new();

    let sig = repo("blvm-consensus/src/script/signature.rs");
    let verify = extract_fn(&sig, "verify_signature");
    keep(
        &mut rows,
        &mut unlocked,
        "verify_signature",
        "signature",
        &verify,
        &verify.replace("signature_bytes.is_empty()", "false"),
        &verify.replace("0x01..=0x03", "0x00..=0x03"),
        verify_signature_query,
    );

    let bip348 = repo("blvm-consensus/src/bip348.rs");
    let taps = extract_fn(&bip348, "verify_tapscript_schnorr_signature");
    keep(
        &mut rows,
        &mut unlocked,
        "verify_tapscript_schnorr_signature",
        "signature",
        &taps,
        &taps.replace("pubkey.len() != 32", "pubkey.len() != 33"),
        &taps.replace("signature.try_into()", "signature.len()"),
        schnorr_len_query,
    );
    let from_stack = extract_fn(&bip348, "verify_signature_from_stack");
    keep(
        &mut rows,
        &mut unlocked,
        "verify_signature_from_stack",
        "signature",
        &from_stack,
        &from_stack.replace("signature.len() != 64", "signature.len() != 65"),
        &from_stack.replace("pubkey.len() == 32", "pubkey.len() == 33"),
        schnorr_from_stack_query,
    );

    let seq = repo("blvm-consensus/src/sequence_locks.rs");
    let calc = extract_fn(&seq, "calculate_sequence_locks");
    keep(
        &mut rows,
        &mut unlocked,
        "calculate_sequence_locks",
        "sequence",
        &calc,
        &calc.replace("min_height: i64 = -1", "min_height: i64 = 0"),
        &calc.replace(
            "locktime_value << SEQUENCE_LOCKTIME_GRANULARITY",
            "locktime_value",
        ),
        calculate_sequence_query,
    );
    let eval = extract_fn(&seq, "evaluate_sequence_locks");
    keep(
        &mut rows,
        &mut unlocked,
        "evaluate_sequence_locks",
        "sequence",
        &eval,
        &eval.replace("block_height <= min_height", "block_height < min_height"),
        &eval.replace("min_height >= 0 && ", ""),
        evaluate_sequence_query,
    );

    let pow = repo("blvm-consensus/src/pow.rs");
    let wrapper = extract_fn(&pow, "get_next_work_required");
    let internal = extract_fn(&pow, "get_next_work_required_internal");
    let retarget = format!("{wrapper}\n{internal}");
    keep(
        &mut rows,
        &mut unlocked,
        "get_next_work_required",
        "retarget",
        &retarget,
        &retarget.replace(
            "time_span.max(expected_time / 4)",
            "time_span.max(expected_time / 1)",
        ),
        &retarget.replace(", false)", ", true)"),
        retarget_query,
    );

    let econ = repo("blvm-consensus/src/economic.rs");
    let supply = extract_fn(&econ, "total_supply");
    keep(
        &mut rows,
        &mut unlocked,
        "total_supply",
        "supply",
        &supply,
        &supply.replace("period_start > end", "period_start >= end"),
        &supply.replace("INITIAL_SUBSIDY >> k", "INITIAL_SUBSIDY >> 0"),
        total_supply_query,
    );
    let utxo = extract_fn(&econ, "verify_utxo_supply");
    keep(
        &mut rows,
        &mut unlocked,
        "verify_utxo_supply",
        "supply",
        &utxo,
        &utxo.replace("actual == expected", "actual >= expected"),
        &utxo.replace("checked_add(utxo.value)", "checked_sub(utxo.value)"),
        utxo_supply_query,
    );

    let flags = extract_fn(
        &repo("blvm-consensus/src/block/script_cache.rs"),
        "get_block_script_verify_flags_core",
    );
    keep(
        &mut rows,
        &mut unlocked,
        "get_block_script_verify_flags_core",
        "flags",
        &flags,
        &flags.replace("flags = v;", ""),
        &flags.replace("flags |= 0x04", "flags |= 0x08"),
        flags_query,
    );

    let bip = repo("blvm-consensus/src/bip_validation.rs");
    let bip66 = extract_fn(&bip, "check_bip66");
    keep(
        &mut rows,
        &mut unlocked,
        "check_bip66",
        "activation",
        &bip66,
        &bip66.replace("return Ok(true);", "return Ok(false);"),
        &bip66.replace("ForkId::Bip66", "ForkId::Bip65"),
        bip66_query,
    );
    let timewarp = extract_fn(&bip, "check_bip54_timewarp");
    keep(
        &mut rows,
        &mut unlocked,
        "check_bip54_timewarp",
        "activation",
        &timewarp,
        &timewarp.replace(
            "header.timestamp >= b.timestamp_n_minus_2015",
            "header.timestamp > b.timestamp_n_minus_2015",
        ),
        &timewarp.replace("7200", "3600"),
        timewarp_query,
    );
    let stripped = extract_fn(&bip, "check_bip54_tx_stripped_size");
    keep(
        &mut rows,
        &mut unlocked,
        "check_bip54_tx_stripped_size",
        "activation",
        &stripped,
        &stripped.replace("!= 64", "!= 65"),
        &stripped.replace("is_coinbase(tx) || ", ""),
        stripped_query,
    );
    let sigop_lim = extract_fn(&bip, "check_bip54_sigop_limit");
    keep(
        &mut rows,
        &mut unlocked,
        "check_bip54_sigop_limit",
        "activation",
        &sigop_lim,
        &sigop_lim.replace("sigop_count > ", "sigop_count >= "),
        &sigop_lim.replace("!bip54_active || is_coinbase(tx)", "!bip54_active"),
        bip54_sigop_query,
    );
    let coin54 = extract_fn(&bip, "check_bip54_coinbase");
    keep(
        &mut rows,
        &mut unlocked,
        "check_bip54_coinbase",
        "activation",
        &coin54,
        &coin54.replace("saturating_sub(13)", "saturating_sub(12)"),
        &coin54.replace("sequence == 0xffff_ffff", "sequence == 0"),
        bip54_coinbase_query,
    );

    let script = repo("blvm-consensus/src/script/mod.rs");
    let decode = extract_fn(&script, "script_num_decode");
    keep(
        &mut rows,
        &mut unlocked,
        "script_num_decode",
        "scriptnum",
        &decode,
        &decode.replace("data.is_empty()", "data.len() > usize::MAX"),
        &decode.replace("if byte & 0x80 != 0", "if byte & 0x01 != 0"),
        script_num_query,
    );
    let limits = extract_fn(&script, "eval_script_inner");
    keep(
        &mut rows,
        &mut unlocked,
        "eval_script_limits",
        "limit",
        &limits,
        &limits.replace(
            "script.len() > MAX_SCRIPT_SIZE",
            "script.len() >= MAX_SCRIPT_SIZE",
        ),
        &limits.replace("> MAX_STACK_SIZE", ">= MAX_STACK_SIZE"),
        script_limits_query,
    );
    let cast = extract_fn(&repo("blvm-consensus/src/script/stack.rs"), "cast_to_bool");
    keep(
        &mut rows,
        &mut unlocked,
        "cast_to_bool",
        "script",
        &cast,
        &cast.replace("v[i] == 0x80", "false"),
        &cast.replace("v[i] == 0x80", "v[i] == 0x81"),
        cast_query,
    );
    let minimal = extract_fn(
        &repo("blvm-consensus/src/script/control_flow.rs"),
        "is_minimal_if_condition",
    );
    keep(
        &mut rows,
        &mut unlocked,
        "is_minimal_if_condition",
        "script",
        &minimal,
        &minimal.replace("0 => true", "0 => false"),
        &minimal.replace("(1..=16)", "(1..=15)"),
        minimal_if_query,
    );
    let parse = extract_fn(&script, "parse_script_sig_push_only");
    keep(
        &mut rows,
        &mut unlocked,
        "p2sh_push_only_check",
        "script",
        &parse,
        &parse.replace("!is_push_opcode(opcode)", "false"),
        &parse.replace("opcode <= 0x4b", "opcode <= 0x40"),
        p2sh_query,
    );
    let fad = extract_fn(&script, "find_and_delete");
    keep(
        &mut rows,
        &mut unlocked,
        "find_and_delete",
        "script",
        &fad,
        &fad.replace("pattern.is_empty()", "pattern.len() < 0"),
        &fad.replace("pc += pattern.len()", "pc += 1"),
        find_delete_query,
    );

    let segwit = repo("blvm-consensus/src/segwit.rs");
    let commit = extract_fn(&segwit, "extract_witness_commitment");
    keep(
        &mut rows,
        &mut unlocked,
        "extract_witness_commitment",
        "witness",
        &commit,
        &commit.replace("0xaa, 0x21, 0xa9, 0xed", "0xab, 0x21, 0xa9, 0xed"),
        &commit.replace("script[6..38]", "script[7..39]"),
        witness_commit_query,
    );
    let tap = extract_fn(
        &repo("blvm-consensus/src/taproot.rs"),
        "compute_taproot_signature_hash",
    );
    keep(
        &mut rows,
        &mut unlocked,
        "compute_taproot_signature_hash",
        "sighash",
        &tap,
        &tap.replacen("sigmsg.push(0x00u8)", "sigmsg.push(0x01u8)", 1),
        &tap.replace("to_le_bytes()", "to_be_bytes()"),
        tapscript_sighash_query,
    );

    let reorg = extract_fn(
        &repo("blvm-consensus/src/reorganization.rs"),
        "should_reorganize",
    );
    keep(
        &mut rows,
        &mut unlocked,
        "should_reorganize",
        "chain",
        &reorg,
        &reorg.replace("new_work > current_work", "new_work >= current_work"),
        &reorg.replace("new_work > current_work", "new_work < current_work"),
        reorg_query,
    );

    let cost = extract_fn(
        &repo("blvm-consensus/src/sigop.rs"),
        "get_transaction_sigop_cost_with_utxos",
    );
    keep(
        &mut rows,
        &mut unlocked,
        "get_transaction_sigop_cost_with_utxos",
        "sigop",
        &cost,
        &cost.replace("saturating_mul(WITNESS_SCALE_FACTOR)", "saturating_mul(1)"),
        &cost.replace("flags & 0x01", "flags & 0x02"),
        sigop_cost_query,
    );

    let tx = repo("blvm-consensus/src/transaction.rs");
    let inputs = extract_fn(&tx, "check_tx_inputs_with_utxos");
    keep(
        &mut rows,
        &mut unlocked,
        "check_tx_inputs",
        "tx",
        &inputs,
        &inputs.replace("0xffffffff", "0xfffffffe"),
        &inputs.replace(
            "checked_sub(total_output_value)",
            "checked_add(total_output_value)",
        ),
        tx_inputs_query,
    );

    let connect = repo("blvm-consensus/src/block/connect.rs");
    keep(
        &mut rows,
        &mut unlocked,
        "block_weight_limit",
        "limit",
        &connect,
        &connect.replace(
            "block_weight > crate::constants::MAX_BLOCK_WEIGHT as u64 {",
            "block_weight >= crate::constants::MAX_BLOCK_WEIGHT as u64 {",
        ),
        &connect.replace(
            "block_weight > crate::constants::MAX_BLOCK_WEIGHT as u64 {",
            "block_weight > 1 {",
        ),
        weight_query,
    );
    keep(
        &mut rows,
        &mut unlocked,
        "block_sigop_limit",
        "limit",
        &connect,
        &connect.replace(
            "total_sigop_cost > MAX_BLOCK_SIGOPS_COST",
            "total_sigop_cost >= MAX_BLOCK_SIGOPS_COST",
        ),
        &connect.replace(
            "total_sigop_cost > MAX_BLOCK_SIGOPS_COST",
            "total_sigop_cost > 1",
        ),
        block_sigop_query,
    );
    keep(
        &mut rows,
        &mut unlocked,
        "coinbase_scriptsig_len",
        "limit",
        &connect,
        &connect.replace("(2..=100)", "(1..=100)"),
        &connect.replace("(2..=100)", "(2..=101)"),
        coinbase_len_query,
    );

    let final_tx = extract_fn(&repo("blvm-consensus/src/mempool.rs"), "is_final_tx");
    keep(
        &mut rows,
        &mut unlocked,
        "is_final_tx",
        "limit",
        &final_tx,
        &final_tx.replace("tx.lock_time == 0", "tx.lock_time == 1"),
        &final_tx.replace("< LOCKTIME_THRESHOLD", "<= LOCKTIME_THRESHOLD"),
        final_tx_query,
    );

    dispatch_and_chain(&mut rows, &mut unlocked, &script);

    let inner = extract_fn(&connect, "connect_block_inner");
    let finality = extract_fn(&connect, "enforce_tx_finality");
    let finality_src = format!("{inner}\n{finality}");
    keep(
        &mut rows,
        &mut unlocked,
        "enforce_tx_finality",
        "finality",
        &finality_src,
        &finality_src.replace("is_final_tx(", "is_final_gone("),
        &finality_src.replace("ForkId::Bip112", "ForkId::Bip66"),
        finality_call_query,
    );

    let mul = extract_fn(&pow, "checked_mul_u64");
    let div = extract_fn(&pow, "div_u64");
    let mul_div = format!("{mul}\n{div}");
    keep(
        &mut rows,
        &mut unlocked,
        "retarget_mul_div",
        "retarget",
        &mul_div,
        &mul_div.replace("product >> 64", "product >> 32"),
        &mul_div.replace(
            "(remainder << 64) | (self.0[3] as u128)",
            "(remainder << 64) | (self.0[0] as u128)",
        ),
        retarget_mul_div_query,
    );

    let compressed = extract_fn(&pow, "compress_target");
    keep(
        &mut rows,
        &mut unlocked,
        "compress_target",
        "retarget",
        &compressed,
        &compressed.replace("(n_compact & 0x00800000)", "(n_compact & 0x00000000)"),
        &compressed.replace("n_size_final << 24", "n_size_final << 16"),
        compress_target_query,
    );

    let opcodes = repo("blvm-primitives/src/opcodes.rs");
    keep(
        &mut rows,
        &mut unlocked,
        "opcode_bytes",
        "dispatch",
        &opcodes,
        &opcodes.replace("const OP_ADD: u8 = 0x93", "const OP_ADD: u8 = 0x94"),
        &opcodes.replace(
            "const OP_CHECKSIG: u8 = 0xac",
            "const OP_CHECKSIG: u8 = 0xad",
        ),
        opcode_bytes_query,
    );

    let supply_limit = extract_fn(&econ, "validate_supply_limit");
    keep(
        &mut rows,
        &mut unlocked,
        "validate_supply_limit",
        "supply",
        &supply_limit,
        &supply_limit.replace("<= MAX_MONEY", "< MAX_MONEY"),
        &supply_limit.replace("MAX_MONEY", "0"),
        supply_limit_query,
    );

    let fee = extract_fn(&econ, "calculate_fee");
    keep(
        &mut rows,
        &mut unlocked,
        "calculate_fee",
        "supply",
        &fee,
        &fee.replace("checked_sub(total_output)", "checked_add(total_output)"),
        &fee.replace("is_coinbase(tx)", "false"),
        calculate_fee_query,
    );

    let segwit_src = repo("blvm-consensus/src/segwit.rs");
    let witness_commit = extract_fn(&segwit_src, "validate_witness_commitment");
    keep(
        &mut rows,
        &mut unlocked,
        "validate_witness_commitment",
        "witness",
        &witness_commit,
        &witness_commit.replace("w[0].len() == 32", "w[0].len() == 33"),
        &witness_commit.replace("w.is_empty()", "false"),
        witness_commitment_query,
    );

    let tap_src = repo("blvm-consensus/src/taproot.rs");
    let tag_line = tap_src
        .lines()
        .find(|line| line.contains("const TAPROOT_ANNEX_TAG"))
        .unwrap_or("");
    let annex = extract_fn(&tap_src, "strip_taproot_annex");
    let annex_src = format!("{tag_line}\n{annex}");
    keep(
        &mut rows,
        &mut unlocked,
        "strip_taproot_annex",
        "taproot",
        &annex_src,
        &annex_src.replace(
            "TAPROOT_ANNEX_TAG: u8 = 0x50",
            "TAPROOT_ANNEX_TAG: u8 = 0x51",
        ),
        &annex_src.replace("witness.len() >= 2", "witness.len() >= 3"),
        strip_annex_query,
    );

    let witness_sigops = extract_fn(&repo("blvm-consensus/src/sigop.rs"), "count_witness_sigops");
    keep(
        &mut rows,
        &mut unlocked,
        "count_witness_sigops",
        "sigop",
        &witness_sigops,
        &witness_sigops.replace("(flags & 0x800)", "(flags & 0x801)"),
        &witness_sigops.replace("script_pubkey.len() == 22", "script_pubkey.len() == 21"),
        witness_sigops_query,
    );

    let connect_src = super::spec_clause::connect_source();
    keep(
        &mut rows,
        &mut unlocked,
        "connect_block",
        "pipeline",
        &connect_src,
        &connect_src.replace("if !header::validate_block_header(", "if false {"),
        &connect_src.replace("if !verify_script_with_context_full(", "if false {"),
        super::spec_clause::connect_query,
    );
    let script_src = super::spec_clause::script_source();
    keep(
        &mut rows,
        &mut unlocked,
        "eval_script_pipeline",
        "pipeline",
        &script_src,
        &script_src.replace(
            "script.len() > MAX_SCRIPT_SIZE",
            "script.len() >= MAX_SCRIPT_SIZE",
        ),
        &script_src.replace("if !execute_opcode_with_context_full(", "if false {"),
        super::spec_clause::script_query,
    );
    let retarget_src = super::spec_clause::retarget_source();
    keep(
        &mut rows,
        &mut unlocked,
        "get_next_work_pipeline",
        "pipeline",
        &retarget_src,
        &retarget_src.replace(
            "time_span.max(expected_time / 4)",
            "time_span.max(expected_time / 1)",
        ),
        &retarget_src.replace("new_bits.min(MAX_TARGET", "new_bits.max(MAX_TARGET"),
        super::spec_clause::retarget_query,
    );

    let sigops = repo("blvm-consensus/src/sigop.rs");
    keep(
        &mut rows,
        &mut unlocked,
        "count_sigops_induction",
        "inductive",
        &sigops,
        &sigops.replace("saturating_add(1)", "saturating_add(0)"),
        &sigops.replace(
            "const MAX_PUBKEYS_PER_MULTISIG: u32 = 20;",
            "const MAX_PUBKEYS_PER_MULTISIG: u32 = 21;",
        ),
        sigop_induct,
    );
    let weight = extract_fn(
        &repo("blvm-consensus/src/segwit.rs"),
        "calculate_block_weight",
    );
    keep(
        &mut rows,
        &mut unlocked,
        "block_weight_induction",
        "inductive",
        &weight,
        &weight.replace("total_weight +=", "total_weight ="),
        &weight.replace("calculate_transaction_weight(tx, witness)?", "0"),
        block_weight_induct,
    );
    let chain = extract_fn(
        &repo("blvm-consensus/src/reorganization.rs"),
        "calculate_chain_work",
    );
    keep(
        &mut rows,
        &mut unlocked,
        "chain_work_induction",
        "inductive",
        &chain,
        &chain.replace(
            "total_work = total_work.saturating_add(work_contribution);",
            "total_work = old_total;",
        ),
        &chain.replace(
            "saturating_add(work_contribution)",
            "saturating_add(work_contribution.saturating_add(U256::one()))",
        ),
        chain_work_induct,
    );
    let fees = extract_fn(&connect, "connect_block_inner");
    keep(
        &mut rows,
        &mut unlocked,
        "block_fee_induction",
        "inductive",
        &fees,
        &fees.replace("let mut total_fees = 0i64;", "let mut total_fees = 1i64;"),
        &fees.replace(".checked_add(fee)", ".checked_sub(fee)"),
        block_fee_induct,
    );

    let header = extract_fn(
        &repo("blvm-consensus/src/block/header.rs"),
        "validate_block_header",
    );
    let future = repo("blvm-primitives/src/constants.rs")
        .lines()
        .find(|line| line.contains("MAX_FUTURE_BLOCK_TIME"))
        .unwrap_or("")
        .to_string();
    let header_src = format!("{future}\n{header}");
    keep(
        &mut rows,
        &mut unlocked,
        "validate_block_header_fields",
        "threshold",
        &header_src,
        &header_src.replace("header.timestamp == 0", "header.timestamp == 1"),
        &header_src.replace("header.bits == 0", "header.bits == 1"),
        header_fields_query,
    );
    let prev = extract_fn(
        &repo("blvm-consensus/src/block/header.rs"),
        "validate_prev_block_hash",
    );
    keep(
        &mut rows,
        &mut unlocked,
        "validate_prev_block_hash",
        "threshold",
        &prev,
        &prev.replace(
            "child.prev_block_hash == block_header_hash(parent)",
            "child.prev_block_hash != block_header_hash(parent)",
        ),
        &prev.replace("block_header_hash(parent)", "block_header_hash(child)"),
        prev_hash_query,
    );
    let script_mod = repo("blvm-consensus/src/script/mod.rs");
    let success = extract_fn(&script_mod, "is_op_success");
    keep(
        &mut rows,
        &mut unlocked,
        "is_op_success",
        "dispatch",
        &success,
        &success.replace("187..=254", "188..=254"),
        &success.replace("80 | 98", "81 | 98"),
        op_success_query,
    );
    let push = extract_fn(&script_mod, "is_push_opcode");
    keep(
        &mut rows,
        &mut unlocked,
        "is_push_opcode",
        "dispatch",
        &push,
        &push.replace("opcode <= 0x60", "opcode < 0x60"),
        &push.replace("opcode <= 0x60", "opcode <= 0x61"),
        push_opcode_query,
    );
    let nested = extract_fn(
        &repo("blvm-consensus/src/segwit.rs"),
        "calculate_block_weight_from_nested",
    );
    keep(
        &mut rows,
        &mut unlocked,
        "block_weight_from_nested",
        "inductive",
        &nested,
        &nested.replace("let mut total_weight = 0;", "let mut total_weight = 1;"),
        &nested.replace("total_weight +=", "total_weight ="),
        nested_weight_query,
    );

    Finish { rows, unlocked }
}

fn dispatch_and_chain(rows: &mut Vec<LockRow>, unlocked: &mut Vec<String>, script: &str) {
    let arith = repo("blvm-consensus/src/script/arithmetic.rs");
    let crypto = repo("blvm-consensus/src/script/crypto_ops.rs");
    let Some(add) = super::best_arm(script, "OP_ADD") else {
        unlocked.push("opcode_dispatch".into());
        return;
    };
    let expanded = super::drop_inactive_cfg(&super::expand_arm(&add, &arith, &crypto));
    keep(
        rows,
        unlocked,
        "opcode_dispatch",
        "dispatch",
        &expanded,
        &expanded.replacen("stack.len() < 2", "stack.len() < 3", 1),
        &expanded.replace("b + a", "b - a"),
        dispatch_query,
    );
    let (Some(if_arm), Some(endif_arm)) = (
        super::best_arm(script, "OP_IF"),
        super::best_arm(script, "OP_ENDIF"),
    ) else {
        unlocked.push("if_body_endif".into());
        return;
    };
    let chain = format!("{if_arm}\n{expanded}\n{endif_arm}");
    keep(
        rows,
        unlocked,
        "if_body_endif",
        "dispatch",
        &chain,
        &chain.replace("control_stack.pop()", "control_stack.len()"),
        &chain.replace("b + a", "b - a"),
        chain_query,
    );
}

fn flag_on<'a>(ctx: &'a z3::Context, flags: &BV<'a>, mask: u64) -> Bool<'a> {
    flags
        .bvand(&BV::from_u64(ctx, mask, 32))
        ._eq(&BV::from_u64(ctx, mask, 32))
}

fn ecdsa_uses_der(src: &str) -> bool {
    let Some(i) = src.find("verify_ecdsa_direct(") else {
        return false;
    };
    let rest = &src[i..];
    let end = rest.find(')').unwrap_or(rest.len());
    let args = &rest[..end];
    args.contains("der_sig") && !args.contains("signature_bytes")
}

fn verify_signature_query(src: &str) -> SatResult {
    let empty_gate = src.contains("signature_bytes.is_empty()");
    let lo: u64 = if src.contains("0x00..=0x03") { 0 } else { 1 };
    let hi: u64 = if src.contains("0x01..=0x04") { 4 } else { 3 };
    let der = ecdsa_uses_der(src);
    let low_s = src.contains("flags & 0x08");
    let pk = src.contains("!= 65") && src.contains("!= 33");
    let witness = src.contains("SigVersion::WitnessV0");
    let dersig = src.contains("flags & 0x04");
    production_lock::check(|ctx, solver| {
        let sig_len = BV::new_const(ctx, "sig_len", 16);
        let sh = BV::new_const(ctx, "sh", 8);
        let flags = BV::new_const(ctx, "flags", 32);
        let pk_len = BV::new_const(ctx, "pk_len", 16);
        let pk0 = BV::new_const(ctx, "pk0", 8);
        let strict_ok = Bool::new_const(ctx, "strict_ok");
        let verifier = Bool::new_const(ctx, "verifier");
        let wit = Bool::new_const(ctx, "witv0");
        let base = sh.bvand(&BV::from_u64(ctx, 0x7f, 8));
        let in_body = base.bvuge(&BV::from_u64(ctx, lo, 8)) & base.bvule(&BV::from_u64(ctx, hi, 8));
        let (lo_c, hi_c) = crate::parser::spec_expr::sighash_standard_bounds();
        let in_clause =
            base.bvuge(&BV::from_u64(ctx, lo_c, 8)) & base.bvule(&BV::from_u64(ctx, hi_c, 8));
        let is04 = pk0._eq(&BV::from_u64(ctx, 4, 8));
        let is_c = pk0._eq(&BV::from_u64(ctx, 2, 8)) | pk0._eq(&BV::from_u64(ctx, 3, 8));
        let len65 = pk_len._eq(&BV::from_u64(ctx, 65, 16));
        let len33 = pk_len._eq(&BV::from_u64(ctx, 33, 16));
        let pk_shape = is04.ite(&len65, &is_c.ite(&len33, &Bool::from_bool(ctx, false)));
        let empty = sig_len._eq(&BV::from_u64(ctx, 0, 16));
        let d_on = flag_on(ctx, &flags, 0x04);
        let s_on = flag_on(ctx, &flags, 0x02);
        let l_on = flag_on(ctx, &flags, 0x08);
        let w_on = flag_on(ctx, &flags, 0x8000);
        let d_c = flag_on(
            ctx,
            &flags,
            crate::parser::spec_expr::flag_bit("SCRIPT_VERIFY_DERSIG"),
        );
        let s_c = flag_on(
            ctx,
            &flags,
            crate::parser::spec_expr::flag_bit("SCRIPT_VERIFY_STRICTENC"),
        );
        let l_c = flag_on(
            ctx,
            &flags,
            crate::parser::spec_expr::flag_bit("SCRIPT_VERIFY_LOW_S"),
        );
        let w_c = flag_on(
            ctx,
            &flags,
            crate::parser::spec_expr::flag_bit("SCRIPT_VERIFY_WITNESS_PUBKEYTYPE"),
        );
        let mut gates_b = Bool::from_bool(ctx, true);
        if empty_gate {
            gates_b &= empty.not();
        }
        if dersig {
            gates_b = gates_b.clone() & (d_on.not() | strict_ok.clone());
        }
        gates_b &= s_on.not() | in_body;
        if pk {
            gates_b = gates_b.clone() & (s_on.not() | pk_shape.clone());
        }
        if witness {
            gates_b &= (w_on.clone() & wit.clone()).not() | (len33.clone() & is_c.clone());
        }
        let low_b = if low_s {
            l_on.clone()
        } else {
            Bool::from_bool(ctx, false)
        };
        let gates_c = empty.not()
            & (d_c.not() | strict_ok)
            & (s_c.not() | in_clause)
            & (s_c.not() | pk_shape)
            & ((w_c & wit).not() | (len33 & is_c));
        let bit_b = if der {
            verifier.clone()
        } else {
            verifier.not()
        };
        let false_b = Bool::from_bool(ctx, false);
        let accept_b = gates_b.ite(&bit_b, &false_b);
        let accept_c = gates_c.ite(&verifier, &false_b);
        solver.assert(&(accept_b._eq(&accept_c) & low_b._eq(&l_c)).not());
    })
}

fn schnorr_len_query(src: &str) -> SatResult {
    let pk = if src.contains("pubkey.len() != 32") {
        32
    } else if src.contains("pubkey.len() != 33") {
        33
    } else {
        0
    };
    let sig64 = src.contains("signature.try_into()");
    production_lock::check(|ctx, solver| {
        let pk_len = BV::new_const(ctx, "pk", 16);
        let sig_len = BV::new_const(ctx, "sig", 16);
        let verifier = Bool::new_const(ctx, "verifier");
        let pk_b = pk_len._eq(&BV::from_u64(ctx, pk, 16));
        let pk_c = pk_len._eq(&BV::from_u64(ctx, 32, 16));
        let sig_b = if sig64 {
            sig_len._eq(&BV::from_u64(ctx, 64, 16))
        } else {
            Bool::from_bool(ctx, true)
        };
        let sig_c = sig_len._eq(&BV::from_u64(ctx, 64, 16));
        let false_b = Bool::from_bool(ctx, false);
        let body = (pk_b & sig_b).ite(&verifier, &false_b);
        let clause = (pk_c & sig_c).ite(&verifier, &false_b);
        solver.assert(&body._eq(&clause).not());
    })
}

fn schnorr_from_stack_query(src: &str) -> SatResult {
    let pk = if src.contains("pubkey.len() == 32") {
        32
    } else if src.contains("pubkey.len() == 33") {
        33
    } else {
        0
    };
    let sig = if src.contains("signature.len() != 64") {
        64
    } else if src.contains("signature.len() != 65") {
        65
    } else {
        0
    };
    let empty_err = src.contains("pubkey.is_empty()");
    production_lock::check(|ctx, solver| {
        let pk_len = BV::new_const(ctx, "pk", 16);
        let sig_len = BV::new_const(ctx, "sig", 16);
        let verifier = Bool::new_const(ctx, "verifier");
        let zero = BV::from_u64(ctx, 0, 16);
        let empty = pk_len._eq(&zero);
        let pk_b = pk_len._eq(&BV::from_u64(ctx, pk, 16));
        let pk_c = pk_len._eq(&BV::from_u64(ctx, 32, 16));
        let sig_b = sig_len._eq(&BV::from_u64(ctx, sig, 16));
        let sig_c = sig_len._eq(&BV::from_u64(ctx, 64, 16));
        let false_b = Bool::from_bool(ctx, false);
        let ready_b = if empty_err {
            empty.not() & pk_b & sig_b
        } else {
            pk_b & sig_b
        };
        let ready_c = empty.not() & pk_c & sig_c;
        let body = ready_b.ite(&verifier, &false_b);
        let clause = ready_c.ite(&verifier, &false_b);
        solver.assert(&body._eq(&clause).not());
    })
}

fn calculate_sequence_query(src: &str) -> SatResult {
    let init = if src.contains("min_height: i64 = -1") {
        -1
    } else {
        0
    };
    let ver = if src.contains("tx.version >= 2") {
        2
    } else {
        1
    };
    let shift: u64 = if src.contains("<< SEQUENCE_LOCKTIME_GRANULARITY") {
        9
    } else {
        0
    };
    production_lock::check(|ctx, solver| {
        let version = BV::new_const(ctx, "ver", 32);
        let value = BV::new_const(ctx, "lockv", 32);
        let flags = BV::new_const(ctx, "flags", 32);
        let flag = flags
            .bvand(&BV::from_u64(ctx, 1, 32))
            ._eq(&BV::from_u64(ctx, 1, 32));
        let enf_b = version.bvuge(&BV::from_u64(ctx, ver, 32)) & flag.clone();
        let enf_c = version.bvuge(&BV::from_u64(ctx, 2, 32)) & flag;
        let sec_b = value.bvshl(&BV::from_u64(ctx, shift, 32));
        let sec_c = value.bvshl(&BV::from_u64(ctx, 9, 32));
        let idle_b = BV::from_i64(ctx, init, 32);
        let idle_c = BV::from_i64(ctx, -1, 32);
        let body = enf_b.ite(&sec_b, &idle_b);
        let clause = enf_c.ite(&sec_c, &idle_c);
        solver.assert(&body._eq(&clause).not());
    })
}

fn evaluate_sequence_query(src: &str) -> SatResult {
    let le = src.contains("block_height <= min_height");
    let guard = src.contains("min_height >= 0 &&");
    production_lock::check(|ctx, solver| {
        let min_h = BV::new_const(ctx, "min_h", 64);
        let height = BV::new_const(ctx, "height", 64);
        let zero = BV::from_i64(ctx, 0, 64);
        solver.assert(&height.bvsge(&zero));
        let active = min_h.bvsge(&zero);
        let cmp_b = if guard {
            if le {
                height.bvsle(&min_h)
            } else {
                height.bvslt(&min_h)
            }
        } else {
            // Dropping the `>= 0` guard compares the raw bits as u64.
            height.bvule(&min_h)
        };
        let cmp_c = height.bvsle(&min_h);
        let rej_b = if guard { active.clone() & cmp_b } else { cmp_b };
        let rej_c = active & cmp_c;
        solver.assert(&rej_b._eq(&rej_c).not());
    })
}

fn retarget_query(src: &str) -> SatResult {
    let corrected = src.contains(", true)");
    let floor4 = src.contains("time_span.max(expected_time / 4)");
    let cap = src.contains("new_bits.min(MAX_TARGET");
    production_lock::check(|ctx, solver| {
        let span = BV::new_const(ctx, "span", 64);
        let bits = BV::new_const(ctx, "bits", 32);
        let interval_b = u64b(
            ctx,
            crate::parser::spec_expr::impl_u64("DIFFICULTY_ADJUSTMENT_INTERVAL"),
        );
        let interval_c = u64b(ctx, crate::parser::spec_expr::protocol_u64("D_INTERVAL"));
        let time_b = u64b(
            ctx,
            crate::parser::spec_expr::impl_u64("TARGET_TIME_PER_BLOCK"),
        );
        let time_c = u64b(ctx, crate::parser::spec_expr::protocol_u64("T_BLOCK"));
        let one = u64b(ctx, 1);
        let expected_c = interval_c.bvmul(&time_c);
        let expected_b = if corrected {
            interval_b.bvsub(&one).bvmul(&time_b)
        } else {
            interval_b.bvmul(&time_b)
        };
        let div = u64b(ctx, if floor4 { 4 } else { 1 });
        let four = u64b(ctx, 4);
        let floor_b = expected_b.bvudiv(&div);
        let floor_c = expected_c.bvudiv(&u64b(ctx, 4));
        let ceil_b = expected_b.bvmul(&four);
        let ceil_c = expected_c.bvmul(&four);
        let clamped_b = span
            .bvult(&floor_b)
            .ite(&floor_b, &span.bvugt(&ceil_b).ite(&ceil_b, &span));
        let clamped_c = span
            .bvult(&floor_c)
            .ite(&floor_c, &span.bvugt(&ceil_c).ite(&ceil_c, &span));
        let max_t = BV::from_u64(ctx, 0x1d00ffff, 32);
        let capped_b = if cap {
            bits.bvule(&max_t).ite(&bits, &max_t)
        } else {
            bits.clone()
        };
        let capped_c = bits.bvule(&max_t).ite(&bits, &max_t);
        solver.assert(&(clamped_b._eq(&clamped_c) & capped_b._eq(&capped_c)).not());
    })
}

fn total_supply_query(src: &str) -> SatResult {
    let strict = src.contains("period_start > end");
    let shift_k = src.contains("INITIAL_SUBSIDY >> k");
    production_lock::check(|ctx, solver| {
        let h = BV::new_const(ctx, "height", 64);
        let interval_b = crate::parser::spec_expr::impl_u64("HALVING_INTERVAL");
        let interval_c = crate::parser::spec_expr::protocol_u64("H");
        let eras = 64u64;
        solver.assert(&h.bvult(&u64b(ctx, eras * interval_b)));
        let zero = u64b(ctx, 0);
        let one = u64b(ctx, 1);
        let initial_b = crate::parser::spec_expr::impl_u64("INITIAL_SUBSIDY");
        let initial_c = crate::parser::spec_expr::initial_subsidy();
        let mut total_b = zero.clone();
        let mut total_c = zero.clone();
        for k in 0..eras {
            let start_b = u64b(ctx, k * interval_b);
            let end_b = u64b(ctx, (k + 1) * interval_b - 1);
            let start_c = u64b(ctx, k * interval_c);
            let end_c = u64b(ctx, (k + 1) * interval_c - 1);
            let in_c = h.bvuge(&start_c);
            let in_b = if strict {
                h.bvuge(&start_b)
            } else {
                h.bvugt(&start_b)
            };
            let hi_b = h.bvule(&end_b).ite(&h, &end_b);
            let hi_c = h.bvule(&end_c).ite(&h, &end_c);
            let count_b = hi_b.bvsub(&start_b).bvadd(&one);
            let count_c = hi_c.bvsub(&start_c).bvadd(&one);
            let sub_c = initial_c >> k;
            let sub_b = if shift_k { initial_b >> k } else { initial_b };
            let contrib_c = count_c.bvmul(&u64b(ctx, sub_c));
            let contrib_b = count_b.bvmul(&u64b(ctx, sub_b));
            total_c = in_c.ite(&contrib_c, &zero).bvadd(&total_c);
            total_b = in_b.ite(&contrib_b, &zero).bvadd(&total_b);
        }
        solver.assert(&total_b._eq(&total_c).not());
    })
}

fn returns_tail(src: &str, name: &str, tail: &str) -> bool {
    let body = if src.contains(&format!("fn {name}(")) {
        super::extract_fn(src, name)
    } else {
        src.to_string()
    };
    body.trim_end().ends_with(tail)
}

fn with_return(step: SatResult, returns: bool) -> SatResult {
    match step {
        SatResult::Unsat if returns => SatResult::Unsat,
        SatResult::Unknown => SatResult::Unknown,
        _ => SatResult::Sat,
    }
}

fn sigop_induct(src: &str) -> SatResult {
    with_return(
        super::sigop_query(src),
        returns_tail(src, "count_sigops_in_script", "count\n}"),
    )
}

fn block_weight_induct(src: &str) -> SatResult {
    with_return(
        super::block_weight_query(src),
        returns_tail(src, "calculate_block_weight", "Ok(total_weight)\n}"),
    )
}

fn chain_work_induct(src: &str) -> SatResult {
    with_return(
        super::chain_work_query(src),
        returns_tail(src, "calculate_chain_work", "Ok(total_work)\n}"),
    )
}

fn needles_hold(src: &str, required: &[(&str, u64)]) -> SatResult {
    production_lock::check(|ctx, solver| {
        let mut ok = Bool::from_bool(ctx, true);
        for (needle, n) in required {
            let measured = if src.contains(needle) {
                *n
            } else {
                n.saturating_add(1)
            };
            let body = BV::from_u64(ctx, measured, 64);
            let clause = BV::from_u64(ctx, *n, 64);
            ok &= body._eq(&clause);
        }
        solver.assert(&ok.not());
    })
}

fn header_fields_query(src: &str) -> SatResult {
    let bits = crate::parser::spec_expr::bits_rejected();
    let future = crate::parser::spec_expr::future_window();
    let bits_needle = format!("header.bits == {bits}");
    let future_needle = format!("MAX_FUTURE_BLOCK_TIME: u64 = {future}");
    let ts = crate::parser::spec_expr::timestamp_rejected();
    let ts_needle = format!("header.timestamp == {ts}");
    needles_hold(
        src,
        &[
            (ts_needle.as_str(), 1),
            (bits_needle.as_str(), 1),
            ("header.merkle_root == [0u8; 32]", 1),
            ("header.timestamp > max_ts", 1),
            (future_needle.as_str(), future),
        ],
    )
}

fn prev_hash_query(src: &str) -> SatResult {
    if !crate::parser::spec_expr::parent_hash_equal() {
        return SatResult::Sat;
    }
    needles_hold(
        src,
        &[("child.prev_block_hash == block_header_hash(parent)", 1)],
    )
}

fn op_success_query(src: &str) -> SatResult {
    let ranges = crate::parser::spec_expr::op_success_ranges();
    let singles: Vec<u64> = ranges
        .iter()
        .filter(|(lo, hi)| lo == hi)
        .map(|(lo, _)| *lo)
        .collect();
    let joined = format!("{} | {}", singles[0], singles[1]);
    let mut owned = vec![(joined, singles[0])];
    for (lo, hi) in &ranges {
        if lo != hi {
            owned.push((format!("{lo}..={hi}"), *lo));
        }
    }
    let needles: Vec<(&str, u64)> = owned.iter().map(|(s, n)| (s.as_str(), *n)).collect();
    needles_hold(src, &needles)
}

fn push_opcode_query(src: &str) -> SatResult {
    let max = crate::parser::spec_expr::push_opcode_max();
    let needle = format!("opcode <= {max:#x}");
    needles_hold(src, &[(&needle, max)])
}

fn nested_weight_query(src: &str) -> SatResult {
    let init = src.contains("let mut total_weight = 0;");
    let add = src.contains("total_weight +=");
    let uses = src.contains("calculate_transaction_weight_segwit(");
    let returns = src.trim_end().ends_with("Ok(total_weight)\n}");
    production_lock::check(|ctx, solver| {
        let acc = BV::new_const(ctx, "acc", 64);
        let w = BV::new_const(ctx, "w", 64);
        solver.assert(&w.bvugt(&u64b(ctx, 0)));
        let body = if init && add && uses {
            acc.bvadd(&w)
        } else {
            acc.clone()
        };
        let base_ok = Bool::from_bool(ctx, init);
        let step_ok = body._eq(&acc.bvadd(&w));
        let ret_ok = Bool::from_bool(ctx, returns && uses);
        solver.assert(&(base_ok & step_ok & ret_ok).not());
    })
}

fn block_fee_induct(src: &str) -> SatResult {
    let init = src.contains("let mut total_fees = 0i64;");
    let add = src.contains(".checked_add(fee)") && !src.contains(".checked_sub(fee)");
    let uses = src.contains("check_coinbase_subsidy(coinbase, subsidy, total_fees)");
    production_lock::check(|ctx, solver| {
        let acc = BV::new_const(ctx, "acc", 64);
        let fee = BV::new_const(ctx, "fee", 64);
        solver.assert(&fee.bvugt(&u64b(ctx, 0)));
        let body = if init && add {
            acc.bvadd(&fee)
        } else if add {
            fee.clone()
        } else {
            acc.clone()
        };
        let base_ok = Bool::from_bool(ctx, init);
        let step_ok = body._eq(&acc.bvadd(&fee));
        let ret_ok = Bool::from_bool(ctx, uses);
        solver.assert(&(base_ok & step_ok & ret_ok).not());
    })
}

fn utxo_supply_query(src: &str) -> SatResult {
    let ge = src.contains("actual >= expected");
    let add = src.contains("checked_add(utxo.value)");
    production_lock::check(|ctx, solver| {
        let v = BV::new_const(ctx, "v", 64);
        let expected = BV::new_const(ctx, "expected", 64);
        let zero = BV::from_i64(ctx, 0, 64);
        solver.assert(&v.bvsge(&zero));
        solver.assert(&expected.bvsge(&zero));
        let sum = if add { v.clone() } else { zero.bvsub(&v) };
        let body = if ge {
            sum.bvsge(&expected)
        } else {
            sum._eq(&expected)
        };
        let clause = v._eq(&expected);
        solver.assert(&body._eq(&clause).not());
    })
}

fn flags_query(src: &str) -> SatResult {
    let base_ok = src.contains("SCRIPT_VERIFY_P2SH")
        && src.contains("SCRIPT_VERIFY_WITNESS_PUBKEYTYPE")
        && src.contains("SCRIPT_VERIFY_TAPROOT");
    let replace = src.contains("flags = v;");
    let or04 = src.contains("flags |= 0x04");
    let or08 = src.contains("flags |= 0x08");
    let or200 = src.contains("flags |= 0x200");
    let or400 = src.contains("flags |= 0x400");
    let or10 = src.contains("flags |= 0x10");
    production_lock::check(|ctx, solver| {
        let exc = Bool::new_const(ctx, "exc");
        let ev = BV::new_const(ctx, "ev", 32);
        let b66 = Bool::new_const(ctx, "b66");
        let b65 = Bool::new_const(ctx, "b65");
        let b112 = Bool::new_const(ctx, "b112");
        let b147 = Bool::new_const(ctx, "b147");
        let base = BV::from_u64(ctx, if base_ok { 0x28801 } else { 0 }, 32);
        let start_c = exc.ite(&ev, &base);
        let mut body = if replace {
            exc.ite(&ev, &base)
        } else {
            base.clone()
        };
        if or04 {
            body = b66.ite(&body.bvor(&BV::from_u64(ctx, 0x04, 32)), &body);
        } else if or08 {
            body = b66.ite(&body.bvor(&BV::from_u64(ctx, 0x08, 32)), &body);
        }
        if or200 {
            body = b65.ite(&body.bvor(&BV::from_u64(ctx, 0x200, 32)), &body);
        }
        if or400 {
            body = b112.ite(&body.bvor(&BV::from_u64(ctx, 0x400, 32)), &body);
        }
        if or10 {
            body = b147.ite(&body.bvor(&BV::from_u64(ctx, 0x10, 32)), &body);
        }
        let c1 = b66.ite(
            &start_c.bvor(&BV::from_u64(
                ctx,
                crate::parser::spec_expr::flag_bit("SCRIPT_VERIFY_DERSIG"),
                32,
            )),
            &start_c,
        );
        let c2 = b65.ite(
            &c1.bvor(&BV::from_u64(
                ctx,
                crate::parser::spec_expr::flag_bit("SCRIPT_VERIFY_CHECKLOCKTIMEVERIFY"),
                32,
            )),
            &c1,
        );
        let c3 = b112.ite(
            &c2.bvor(&BV::from_u64(
                ctx,
                crate::parser::spec_expr::flag_bit("SCRIPT_VERIFY_CHECKSEQUENCEVERIFY"),
                32,
            )),
            &c2,
        );
        let clause = b147.ite(
            &c3.bvor(&BV::from_u64(
                ctx,
                crate::parser::spec_expr::flag_bit("SCRIPT_VERIFY_NULLDUMMY"),
                32,
            )),
            &c3,
        );
        solver.assert(&body._eq(&clause).not());
    })
}

fn bip66_query(src: &str) -> SatResult {
    let fork66 = src.contains("ForkId::Bip66");
    let inactive_true = src.contains("return Ok(true)");
    production_lock::check(|ctx, solver| {
        let a66 = Bool::new_const(ctx, "a66");
        let a65 = Bool::new_const(ctx, "a65");
        let der = Bool::new_const(ctx, "der");
        let active = if fork66 { a66.clone() } else { a65 };
        let t = Bool::from_bool(ctx, true);
        let body = if inactive_true {
            active.not().ite(&t, &der)
        } else {
            der.clone()
        };
        let clause = a66.not().ite(&t, &der);
        solver.assert(&body._eq(&clause).not());
    })
}

fn timewarp_query(src: &str) -> SatResult {
    let ge = src.contains("header.timestamp >= b.timestamp_n_minus_2015");
    let hours: u64 = if src.contains("7200") { 7200 } else { 3600 };
    let bypass = src.contains("if !bip54_active");
    production_lock::check(|ctx, solver| {
        let ts = BV::new_const(ctx, "ts", 64);
        let bound = BV::new_const(ctx, "bound", 64);
        let active = Bool::new_const(ctx, "active");
        let cmp_b = if ge {
            ts.bvuge(&bound)
        } else {
            ts.bvugt(&bound)
        };
        let cmp_c = ts.bvuge(&bound);
        let t = Bool::from_bool(ctx, true);
        let body = if bypass {
            active.not().ite(&t, &cmp_b)
        } else {
            cmp_b
        };
        let clause = active.not().ite(&t, &cmp_c);
        let hours_ok = Bool::from_bool(
            ctx,
            hours == crate::parser::spec_expr::bip54_timewarp_grace(),
        );
        solver.assert(&(body._eq(&clause) & hours_ok).not());
    })
}

fn stripped_query(src: &str) -> SatResult {
    let coin_ok = src.contains("is_coinbase(tx)");
    let bound: u64 = if src.contains("!= 64") { 64 } else { 65 };
    production_lock::check(|ctx, solver| {
        let size = BV::new_const(ctx, "size", 64);
        let coin = Bool::new_const(ctx, "coin");
        let ne_b = size._eq(&u64b(ctx, bound)).not();
        let ne_c = size
            ._eq(&u64b(
                ctx,
                crate::parser::spec_expr::stripped_size_rejected(),
            ))
            .not();
        let body = if coin_ok { coin.clone() | ne_b } else { ne_b };
        let clause = coin | ne_c;
        solver.assert(&body._eq(&clause).not());
    })
}

fn bip54_sigop_query(src: &str) -> SatResult {
    let ge = src.contains("sigop_count >= ");
    let exempt = src.contains("is_coinbase(tx)");
    production_lock::check(|ctx, solver| {
        let n = BV::new_const(ctx, "n", 64);
        let coin = Bool::new_const(ctx, "coin");
        let active = Bool::new_const(ctx, "active");
        let cap_b = u64b(
            ctx,
            crate::parser::spec_expr::impl_u64("BIP54_MAX_SIGOPS_PER_TX"),
        );
        let cap_c = u64b(ctx, crate::parser::spec_expr::bip54_sigop_cap());
        let over_b = if ge { n.bvuge(&cap_b) } else { n.bvugt(&cap_b) };
        let over_c = n.bvugt(&cap_c);
        let skip_b = if exempt {
            active.not() | coin.clone()
        } else {
            active.not()
        };
        let skip_c = active.not() | coin;
        let f = Bool::from_bool(ctx, false);
        let body = skip_b.ite(&f, &over_b);
        let clause = skip_c.ite(&f, &over_c);
        solver.assert(&body._eq(&clause).not());
    })
}

fn bip54_coinbase_query(src: &str) -> SatResult {
    let sub: u64 = if src.contains("saturating_sub(13)") {
        13
    } else {
        12
    };
    let final_seq = src.contains("0xffff_ffff");
    production_lock::check(|ctx, solver| {
        let height = BV::new_const(ctx, "height", 64);
        let lock = BV::new_const(ctx, "lock", 64);
        solver.assert(&height.bvuge(&u64b(ctx, 20)));
        let seq_final = Bool::new_const(ctx, "seqf");
        let req_b = height.bvsub(&u64b(ctx, sub));
        let req_c = height.bvsub(&u64b(ctx, crate::parser::spec_expr::bip54_locktime_delta()));
        let lock_b = lock._eq(&req_b);
        let lock_c = lock._eq(&req_c);
        let bad_b = if final_seq {
            seq_final.clone()
        } else {
            seq_final.not()
        };
        let body = lock_b & bad_b.not();
        let spec_seq = crate::parser::spec_expr::bip54_sequence_rejected();
        let bad_c = if spec_seq == 0xffff_ffff {
            seq_final.not()
        } else {
            seq_final
        };
        let clause = lock_c & bad_c;
        solver.assert(&body._eq(&clause).not());
    })
}

fn script_num_query(src: &str) -> SatResult {
    let empty_gate = src.contains("data.is_empty()");
    let overflow = src.contains("data.len() > max_num_size");
    let mask: u64 = if src.contains("if byte & 0x80 != 0") {
        0x80
    } else {
        0x01
    };
    production_lock::check(|ctx, solver| {
        let len = BV::new_const(ctx, "len", 16);
        let last = BV::new_const(ctx, "last", 16);
        solver.assert(&last.bvult(&BV::from_u64(ctx, 256, 16)));
        let max = BV::from_u64(ctx, 4, 16);
        let zero = BV::from_u64(ctx, 0, 16);
        let err = BV::from_u64(ctx, 0x7fff, 16);
        let decode = |mask: u64| {
            let sign = last.bvand(&BV::from_u64(ctx, mask, 16))._eq(&zero).not();
            let mag = last.bvand(&BV::from_u64(ctx, 0x7f, 16));
            sign.ite(&mag.bvneg(), &last)
        };
        let val_b = decode(mask);
        let val_c = decode(0x80);
        let over = len.bvugt(&max);
        let empty = len._eq(&zero);
        let body_val = if empty_gate {
            empty.ite(&zero, &val_b)
        } else {
            val_b
        };
        let clause_val = empty.ite(&zero, &val_c);
        let body = if overflow {
            over.ite(&err, &body_val)
        } else {
            body_val
        };
        let clause = over.ite(&err, &clause_val);
        solver.assert(&body._eq(&clause).not());
    })
}

fn rel_op(src: &str, ge: &str, gt: &str) -> u8 {
    if src.contains(ge) {
        1
    } else if src.contains(gt) {
        0
    } else {
        2
    }
}

fn rejects<'a>(ctx: &'a z3::Context, op: u8, value: &BV<'a>, cap: u64) -> Bool<'a> {
    let c = BV::from_u64(ctx, cap, 64);
    match op {
        0 => value.bvugt(&c),
        1 => value.bvuge(&c),
        _ => Bool::from_bool(ctx, false),
    }
}

fn script_limits_query(src: &str) -> SatResult {
    let script = rel_op(
        src,
        "script.len() >= MAX_SCRIPT_SIZE",
        "script.len() > MAX_SCRIPT_SIZE",
    );
    let stack = rel_op(src, ">= MAX_STACK_SIZE", "> MAX_STACK_SIZE");
    let elem = rel_op(src, "data.len() >= max_element", "data.len() > max_element");
    production_lock::check(|ctx, solver| {
        let s = BV::new_const(ctx, "slen", 64);
        let k = BV::new_const(ctx, "kstack", 64);
        let e = BV::new_const(ctx, "elen", 64);
        let script_impl = crate::parser::spec_expr::impl_u64("MAX_SCRIPT_SIZE");
        let stack_impl = crate::parser::spec_expr::impl_u64("MAX_STACK_SIZE");
        let script_spec = crate::parser::spec_expr::upper_bound("L_SCRIPT");
        let stack_spec = crate::parser::spec_expr::upper_bound("L_STACK");
        let elem_impl = crate::parser::spec_expr::impl_u64("MAX_SCRIPT_ELEMENT_SIZE");
        let elem_spec = crate::parser::spec_expr::protocol_u64("L_ELEMENT");
        let ops = rel_op(
            src,
            "op_count >= MAX_SCRIPT_OPS",
            "op_count > MAX_SCRIPT_OPS",
        );
        let ops_impl = crate::parser::spec_expr::impl_u64("MAX_SCRIPT_OPS");
        let ops_spec = crate::parser::spec_expr::protocol_u64("L_OPS");
        let nops = BV::new_const(ctx, "nops", 64);
        let body = rejects(ctx, script, &s, script_impl)
            & rejects(ctx, stack, &k, stack_impl)
            & rejects(ctx, elem, &e, elem_impl)
            & rejects(ctx, ops, &nops, ops_impl);
        let clause = rejects(ctx, 0, &s, script_spec)
            & rejects(ctx, 0, &k, stack_spec)
            & rejects(ctx, 0, &e, elem_spec)
            & rejects(ctx, 0, &nops, ops_spec);
        solver.assert(&body._eq(&clause).not());
    })
}

fn cast_query(src: &str) -> SatResult {
    let special: u64 = if src.contains("v[i] == 0x80") {
        0x80
    } else if src.contains("v[i] == 0x81") {
        0x81
    } else {
        0
    };
    production_lock::check(|ctx, solver| {
        let b = BV::new_const(ctx, "b", 8);
        let nonempty = Bool::new_const(ctx, "nonempty");
        let zero = b._eq(&BV::from_u64(ctx, 0, 8));
        let clause_byte = zero.not() & b._eq(&BV::from_u64(ctx, 0x80, 8)).not();
        let body_byte = if special == 0 {
            zero.not()
        } else {
            zero.not() & b._eq(&BV::from_u64(ctx, special, 8)).not()
        };
        let body = nonempty.ite(&body_byte, &Bool::from_bool(ctx, false));
        let clause = nonempty.ite(&clause_byte, &Bool::from_bool(ctx, false));
        solver.assert(&body._eq(&clause).not());
    })
}

fn minimal_if_query(src: &str) -> SatResult {
    let empty_true = src.contains("0 => true");
    let hi: u64 = if src.contains("(1..=16)") { 16 } else { 15 };
    let opcodes = src.contains("OP_1..=OP_16");
    production_lock::check(|ctx, solver| {
        let len = BV::new_const(ctx, "len", 16);
        let b = BV::new_const(ctx, "b", 16);
        let zero = BV::from_u64(ctx, 0, 16);
        let one = BV::from_u64(ctx, 1, 16);
        let small_b = b.bvuge(&one) & b.bvule(&BV::from_u64(ctx, hi, 16));
        let small_c = b.bvuge(&one) & b.bvule(&BV::from_u64(ctx, 16, 16));
        let op_b = if opcodes {
            b.bvuge(&BV::from_u64(ctx, 0x51, 16)) & b.bvule(&BV::from_u64(ctx, 0x60, 16))
        } else {
            Bool::from_bool(ctx, false)
        };
        let op_c = b.bvuge(&BV::from_u64(ctx, 0x51, 16)) & b.bvule(&BV::from_u64(ctx, 0x60, 16));
        let one_b = b._eq(&zero) | small_b | op_b;
        let one_c = b._eq(&zero) | small_c | op_c;
        let empty_b = if empty_true {
            Bool::from_bool(ctx, true)
        } else {
            Bool::from_bool(ctx, false)
        };
        let is0 = len._eq(&zero);
        let is1 = len._eq(&one);
        let f = Bool::from_bool(ctx, false);
        let body = is0.ite(&empty_b, &is1.ite(&one_b, &f));
        let clause = is0.ite(&Bool::from_bool(ctx, true), &is1.ite(&one_c, &f));
        solver.assert(&body._eq(&clause).not());
    })
}

fn p2sh_query(src: &str) -> SatResult {
    let guard = src.contains("!is_push_opcode(opcode)");
    let max_direct: u64 = if src.contains("opcode <= 0x4b") {
        0x4b
    } else if src.contains("opcode <= 0x40") {
        0x40
    } else {
        0
    };
    production_lock::check(|ctx, solver| {
        let op = BV::new_const(ctx, "op", 8);
        let direct_b = op.bvule(&BV::from_u64(ctx, max_direct, 8));
        let direct_c = op.bvule(&BV::from_u64(
            ctx,
            crate::parser::spec_expr::direct_push_max(),
            8,
        ));
        let rej_b = if guard {
            op._eq(&BV::from_u64(ctx, 0x61, 8))
        } else {
            Bool::from_bool(ctx, false)
        };
        let rej_c = op._eq(&BV::from_u64(
            ctx,
            crate::parser::spec_expr::first_non_push_byte(),
            8,
        ));
        solver.assert(&(direct_b._eq(&direct_c) & rej_b._eq(&rej_c)).not());
    })
}

fn find_delete_query(src: &str) -> SatResult {
    let empty_noop = src.contains("pattern.is_empty()");
    let by_len = src.contains("pc += pattern.len()");
    production_lock::check(|ctx, solver| {
        let plen = BV::new_const(ctx, "plen", 64);
        solver.assert(&plen.bvule(&u64b(ctx, 64)));
        let keeps_b = if empty_noop {
            plen._eq(&u64b(ctx, 0))
        } else {
            Bool::from_bool(ctx, false)
        };
        let keeps_c = if crate::parser::spec_expr::empty_pattern_is_noop() {
            plen._eq(&u64b(ctx, 0))
        } else {
            Bool::from_bool(ctx, false)
        };
        let step_b = if by_len { plen.clone() } else { u64b(ctx, 1) };
        let step_c = plen;
        solver.assert(&(keeps_b._eq(&keeps_c) & step_b._eq(&step_c)).not());
    })
}

fn witness_commit_query(src: &str) -> SatResult {
    let magic = src.contains("0xaa, 0x21, 0xa9, 0xed");
    let off: u64 = if src.contains("script[6..38]") {
        6
    } else if src.contains("script[7..39]") {
        7
    } else {
        0
    };
    let tag = src.contains("script[0] == OP_RETURN") && src.contains("script[1] == 0x24");
    production_lock::check(|ctx, solver| {
        let magic_b = Bool::from_bool(ctx, magic && tag);
        let magic_c = Bool::from_bool(ctx, crate::parser::spec_expr::witness_magic_present());
        let off_b = BV::from_u64(ctx, off, 8);
        let off_c = BV::from_u64(
            ctx,
            crate::parser::spec_expr::witness_commitment_offset(),
            8,
        );
        solver.assert(&(magic_b._eq(&magic_c) & off_b._eq(&off_c)).not());
    })
}

fn tapscript_sighash_query(src: &str) -> SatResult {
    let epoch = epoch_byte(src);
    let le = src.contains("to_le_bytes()") && !src.contains("to_be_bytes()");
    let acp = src.contains("sighash_type & 0x80");
    production_lock::check(|ctx, solver| {
        let ver = BV::new_const(ctx, "ver", 32);
        let epoch_b = BV::from_u64(ctx, epoch, 8);
        let epoch_c = BV::from_u64(ctx, 0, 8);
        let word_b = if le { ver.clone() } else { bswap32(&ver) };
        let word_c = ver;
        let acp_ok = Bool::from_bool(ctx, acp);
        solver.assert(&(epoch_b._eq(&epoch_c) & word_b._eq(&word_c) & acp_ok).not());
    })
}

fn epoch_byte(src: &str) -> u64 {
    let Some(i) = src.find("// epoch") else {
        return 0xff;
    };
    let rest = &src[i..];
    let one = rest.find("sigmsg.push(0x01u8)");
    let zero = rest.find("sigmsg.push(0x00u8)");
    match (one, zero) {
        (Some(a), Some(b)) if a < b => 1,
        (_, Some(_)) => 0,
        (Some(_), None) => 1,
        _ => 0xff,
    }
}

fn bswap32<'a>(v: &BV<'a>) -> BV<'a> {
    let b0 = v.extract(7, 0);
    let b1 = v.extract(15, 8);
    let b2 = v.extract(23, 16);
    let b3 = v.extract(31, 24);
    b0.concat(&b1).concat(&b2).concat(&b3)
}

fn reorg_query(src: &str) -> SatResult {
    let op = if src.contains("new_work >= current_work") {
        1
    } else if src.contains("new_work > current_work") {
        0
    } else if src.contains("new_work < current_work") {
        2
    } else {
        3
    };
    production_lock::check(|ctx, solver| {
        let new_w = BV::new_const(ctx, "neww", 64);
        let cur = BV::new_const(ctx, "curw", 64);
        let body = match op {
            0 => new_w.bvugt(&cur),
            1 => new_w.bvuge(&cur),
            2 => new_w.bvult(&cur),
            _ => Bool::from_bool(ctx, false),
        };
        let clause = new_w.bvugt(&cur);
        solver.assert(&body._eq(&clause).not());
    })
}

fn sigop_cost_query(src: &str) -> SatResult {
    let scale: u64 = if src.contains("saturating_mul(WITNESS_SCALE_FACTOR)") {
        4
    } else {
        1
    };
    let bit: u64 = if src.contains("flags & 0x01") { 1 } else { 2 };
    production_lock::check(|ctx, solver| {
        let legacy = BV::new_const(ctx, "legacy", 64);
        solver.assert(&legacy.bvugt(&u64b(ctx, 0)));
        let scale_c = crate::parser::spec_expr::sigop_legacy_scale();
        let bit_c = crate::parser::spec_expr::p2sh_flag_bit();
        let cost_b = legacy.bvmul(&u64b(ctx, scale));
        let cost_c = legacy.bvmul(&u64b(ctx, scale_c));
        let bit_b = BV::from_u64(ctx, bit, 8);
        let bit_clause = BV::from_u64(ctx, bit_c, 8);
        solver.assert(&(cost_b._eq(&cost_c) & bit_b._eq(&bit_clause)).not());
    })
}

fn tx_inputs_query(src: &str) -> SatResult {
    let null_reject =
        src.contains("0xffffffff") && (src.contains("is_zero_hash") || src.contains("[0u8; 32]"));
    let fee_sub = src.contains("checked_sub(total_output_value)");
    production_lock::check(|ctx, solver| {
        let inn = BV::new_const(ctx, "inn", 64);
        let out = BV::new_const(ctx, "outv", 64);
        solver.assert(&out.bvugt(&u64b(ctx, 0)));
        let null = Bool::new_const(ctx, "nullp");
        let fee_b = if fee_sub {
            inn.bvsub(&out)
        } else {
            inn.bvadd(&out)
        };
        let fee_c = inn.bvsub(&out);
        let rej_b = if null_reject {
            null.clone()
        } else {
            Bool::from_bool(ctx, false)
        };
        solver.assert(&(fee_b._eq(&fee_c) & rej_b._eq(&null)).not());
    })
}

fn weight_query(src: &str) -> SatResult {
    let op = rel_op(
        src,
        "block_weight >= crate::constants::MAX_BLOCK_WEIGHT as u64 {",
        "block_weight > crate::constants::MAX_BLOCK_WEIGHT as u64 {",
    );
    let absent = !src.contains("block_weight > crate::constants::MAX_BLOCK_WEIGHT as u64 {")
        && !src.contains("block_weight >= crate::constants::MAX_BLOCK_WEIGHT as u64 {");
    let op = if absent { 2 } else { op };
    cap_query(
        op,
        crate::parser::spec_expr::impl_u64("MAX_BLOCK_WEIGHT"),
        crate::parser::spec_expr::upper_bound("W_MAX"),
    )
}

fn block_sigop_query(src: &str) -> SatResult {
    let op = if src.contains("total_sigop_cost >= MAX_BLOCK_SIGOPS_COST") {
        1
    } else if src.contains("total_sigop_cost > MAX_BLOCK_SIGOPS_COST") {
        0
    } else {
        2
    };
    cap_query(
        op,
        crate::parser::spec_expr::impl_u64("MAX_BLOCK_SIGOPS_COST"),
        crate::parser::spec_expr::upper_bound("S_MAX"),
    )
}

fn cap_query(op: u8, impl_cap: u64, spec_cap: u64) -> SatResult {
    production_lock::check(|ctx, solver| {
        let n = BV::new_const(ctx, "n", 64);
        let body = rejects(ctx, op, &n, impl_cap);
        let clause = rejects(ctx, 0, &n, spec_cap);
        solver.assert(&body._eq(&clause).not());
    })
}

fn coinbase_len_query(src: &str) -> SatResult {
    let (spec_lo, spec_hi) = crate::parser::spec_expr::range_near("scriptSig");
    let (lo, hi) = if src.contains(&format!("({spec_lo}..={spec_hi})")) {
        (spec_lo, spec_hi)
    } else if src.contains("(1..=100)") {
        (1, 100)
    } else if src.contains("(2..=101)") {
        (2, 101)
    } else {
        (0, 0)
    };
    production_lock::check(|ctx, solver| {
        let n = BV::new_const(ctx, "n", 16);
        let body = n.bvult(&BV::from_u64(ctx, lo, 16)) | n.bvugt(&BV::from_u64(ctx, hi, 16));
        let clause =
            n.bvult(&BV::from_u64(ctx, spec_lo, 16)) | n.bvugt(&BV::from_u64(ctx, spec_hi, 16));
        solver.assert(&body._eq(&clause).not());
    })
}

fn final_tx_query(src: &str) -> SatResult {
    let zero_final = src.contains("tx.lock_time == 0");
    let thresh_lt = src.contains("< LOCKTIME_THRESHOLD");
    production_lock::check(|ctx, solver| {
        let lock = BV::new_const(ctx, "lock", 64);
        let height = BV::new_const(ctx, "height", 64);
        let block_time = BV::new_const(ctx, "btime", 64);
        let seq_final = Bool::new_const(ctx, "allfinal");
        let zero = u64b(ctx, 0);
        let thresh_b = u64b(
            ctx,
            crate::parser::spec_expr::impl_u64("LOCKTIME_THRESHOLD"),
        );
        let thresh_c = u64b(ctx, crate::parser::spec_expr::locktime_threshold());
        let below_b = if thresh_lt {
            lock.bvult(&thresh_b)
        } else {
            lock.bvule(&thresh_b)
        };
        let below_c = lock.bvult(&thresh_c);
        let by_height = lock.bvult(&height);
        let by_time = lock.bvult(&block_time);
        let t = Bool::from_bool(ctx, true);
        let satisfied = below_b.ite(&by_height, &by_time);
        let body_lock = if zero_final {
            lock._eq(&zero).ite(&t, &satisfied)
        } else {
            satisfied
        };
        let clause_sat = below_c.ite(&by_height, &by_time);
        let clause = lock._eq(&zero).ite(&t, &clause_sat);
        let body = body_lock | seq_final.clone();
        let clause = clause | seq_final;
        solver.assert(&body._eq(&clause).not());
    })
}

fn stack_floor(src: &str) -> u64 {
    if let Some(i) = src.find("stack.len() < ") {
        let rest = &src[i + "stack.len() < ".len()..];
        let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
        return digits.parse().unwrap_or(0);
    }
    0
}

fn dispatch_query(src: &str) -> SatResult {
    let adds = src.contains("b + a");
    let floor = stack_floor(src);
    production_lock::check(|ctx, solver| {
        let op = BV::new_const(ctx, "op", 8);
        let add = crate::parser::spec_expr::opcode("OP_ADD").expect("OP_ADD");
        let selected = op._eq(&BV::from_u64(ctx, add.byte, 8));
        let effect_b = BV::from_u64(ctx, if adds { 1 } else { 2 }, 8);
        let effect_c = BV::from_u64(ctx, if add.op == "add" { 1 } else { 2 }, 8);
        let body = selected.ite(&effect_b, &BV::from_u64(ctx, 0, 8));
        let clause = selected.ite(&effect_c, &BV::from_u64(ctx, 0, 8));
        let floor_ok = Bool::from_bool(ctx, floor == u64::from(add.min));
        solver.assert(&(body._eq(&clause) & floor_ok).not());
    })
}

fn finality_call_query(src: &str) -> SatResult {
    let calls = src.contains("enforce_tx_finality(");
    let uses = src.contains("is_final_tx(");
    let csv_gate = src.contains("ForkId::Bip112");
    production_lock::check(|ctx, solver| {
        let csv_on = Bool::new_const(ctx, "csv");
        let mtp = BV::new_const(ctx, "mtp", 64);
        let hdr = BV::new_const(ctx, "hdr", 64);
        solver.assert(&mtp._eq(&hdr).not());
        let cutoff_b = if csv_gate {
            csv_on.ite(&mtp, &hdr)
        } else {
            hdr.clone()
        };
        let cutoff_c = csv_on.ite(&mtp, &hdr);
        let called = Bool::from_bool(ctx, calls && uses);
        let must_call = Bool::from_bool(ctx, true);
        solver.assert(&(cutoff_b._eq(&cutoff_c) & called._eq(&must_call)).not());
    })
}

fn retarget_mul_div_query(src: &str) -> SatResult {
    let shift: u64 = if src.contains("product >> 64") {
        64
    } else {
        32
    };
    let high_first = src.contains("(remainder << 64) | (self.0[3] as u128)");
    production_lock::check(|ctx, solver| {
        let low = BV::new_const(ctx, "low", 64);
        let high = BV::new_const(ctx, "high", 64);
        let rhs = BV::new_const(ctx, "rhs", 64);
        let divisor = BV::new_const(ctx, "div", 64);
        solver.assert(&low._eq(&BV::from_u64(ctx, 1 << 32, 64)));
        solver.assert(&high._eq(&BV::from_u64(ctx, 7, 64)));
        solver.assert(&rhs._eq(&BV::from_u64(ctx, 2, 64)));
        solver.assert(&divisor._eq(&BV::from_u64(ctx, 3, 64)));
        let product = low.zero_ext(64).bvmul(&rhs.zero_ext(64));
        let carry_b = if shift == 64 {
            product.extract(127, 64)
        } else {
            product.extract(95, 32)
        };
        let carry_c = product.extract(127, 64);
        let word_b = if high_first {
            high.clone()
        } else {
            low.clone()
        };
        let quot_b = word_b
            .zero_ext(64)
            .bvudiv(&divisor.zero_ext(64))
            .extract(63, 0);
        let quot_c = high
            .zero_ext(64)
            .bvudiv(&divisor.zero_ext(64))
            .extract(63, 0);
        solver.assert(&(carry_b._eq(&carry_c) & quot_b._eq(&quot_c)).not());
    })
}

fn u64_after(src: &str, needle: &str) -> Option<u64> {
    let rest = &src[src.find(needle)? + needle.len()..];
    let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
    digits.parse().ok()
}

fn hex_after(src: &str, needle: &str) -> Option<u64> {
    let rest = &src[src.find(needle)? + needle.len()..];
    let hex: String = rest.chars().take_while(|c| c.is_ascii_hexdigit()).collect();
    u64::from_str_radix(&hex, 16).ok()
}

fn compress_target_query(src: &str) -> SatResult {
    let mask = hex_after(src, "let mantissa = (n_compact & 0x").unwrap_or(0);
    let sign = hex_after(src, "while (n_compact & 0x").unwrap_or(0);
    let exp_shift = u64_after(src, "n_size_final << ").unwrap_or(0);
    let zero_bits = hex_after(src, "Ok(0x").unwrap_or(0);
    let byte = u64_after(src, ".div_ceil(").unwrap_or(0);
    let left_scale = u64_after(src, "<< (").unwrap_or(0);
    let right_scale = u64_after(src, "shift_bytes * ").unwrap_or(0);
    let limit = u64_after(src, "n_size_final > ").unwrap_or(0);
    production_lock::check(|ctx, solver| {
        let target = BV::new_const(ctx, "target", 32);
        let body = compress_bits(
            ctx,
            &target,
            mask,
            sign,
            exp_shift,
            zero_bits,
            byte,
            left_scale,
            right_scale,
            limit,
        );
        let clause = compress_bits(
            ctx,
            &target,
            0x007f_ffff,
            0x0080_0000,
            24,
            0x1d00_0000,
            8,
            8,
            8,
            29,
        );
        solver.assert(&body._eq(&clause).not());
    })
}

#[allow(clippy::too_many_arguments)]
fn compress_bits<'a>(
    ctx: &'a z3::Context,
    target: &BV<'a>,
    mask: u64,
    sign: u64,
    exp_shift: u64,
    zero_bits: u64,
    byte: u64,
    left_scale: u64,
    right_scale: u64,
    limit: u64,
) -> BV<'a> {
    let width = 32u32;
    let zero = BV::from_u64(ctx, 0, width);
    let one = BV::from_u64(ctx, 1, 1);
    let mut idx = zero.clone();
    let mut found = Bool::from_bool(ctx, false);
    for i in (0..width).rev() {
        let bit = target.extract(i, i)._eq(&one);
        let take = bit.clone() & found.clone().not();
        idx = take.ite(&BV::from_u64(ctx, u64::from(i), width), &idx);
        found |= bit;
    }
    let divisor = BV::from_u64(ctx, byte, width);
    let n_size = idx.bvadd(&divisor).bvudiv(&divisor);
    let three = BV::from_u64(ctx, 3, width);
    let le3 = n_size.bvule(&three);
    let shift_l = three
        .bvsub(&n_size)
        .bvmul(&BV::from_u64(ctx, left_scale, width));
    let shift_r = n_size
        .bvsub(&three)
        .bvmul(&BV::from_u64(ctx, right_scale, width));
    let mut compact = le3.ite(&target.bvshl(&shift_l), &target.bvlshr(&shift_r));
    let mut size = n_size;
    let sign_bv = BV::from_u64(ctx, sign, width);
    for _ in 0..4 {
        let hit = compact.bvand(&sign_bv)._eq(&zero).not();
        let next = compact.bvlshr(&BV::from_u64(ctx, 8, width));
        compact = hit.ite(&next, &compact);
        size = hit.ite(&size.bvadd(&BV::from_u64(ctx, 1, width)), &size);
    }
    let mantissa = compact.bvand(&BV::from_u64(ctx, mask, width));
    let bits = size
        .bvshl(&BV::from_u64(ctx, exp_shift, width))
        .bvor(&mantissa);
    let over = size.bvugt(&BV::from_u64(ctx, limit, width));
    let err = BV::from_u64(ctx, 0xffff_ffff, width);
    let normal = over.ite(&err, &bits);
    target
        ._eq(&zero)
        .ite(&BV::from_u64(ctx, zero_bits, width), &normal)
}

fn opcode_byte(src: &str, name: &str) -> Option<u64> {
    hex_after(src, &format!("const {name}: u8 = 0x"))
}

fn opcode_bytes_query(src: &str) -> SatResult {
    let table = crate::parser::spec_expr::opcodes();
    production_lock::check(|ctx, solver| {
        let mut same = Bool::from_bool(ctx, true);
        for row in table {
            let eq = match opcode_byte(src, &row.name) {
                Some(got) => BV::from_u64(ctx, got, 16)._eq(&BV::from_u64(ctx, row.byte, 16)),
                None => Bool::from_bool(ctx, false),
            };
            same &= eq;
        }
        solver.assert(&same.not());
    })
}

fn supply_limit_query(src: &str) -> SatResult {
    let calls = src.contains("total_supply(");
    let le = src.contains("<=");
    let cap = if src.contains("MAX_MONEY") {
        crate::parser::spec_expr::impl_i64("MAX_MONEY")
    } else {
        0
    };
    let spec_cap = crate::parser::spec_expr::upper_bound("M_MAX") as i64;
    production_lock::check(|ctx, solver| {
        let supply = BV::new_const(ctx, "supply", 64);
        let cap_b = BV::from_i64(ctx, cap, 64);
        let cap_c = BV::from_i64(ctx, spec_cap, 64);
        let cmp_b = if le {
            supply.bvsle(&cap_b)
        } else {
            supply.bvslt(&cap_b)
        };
        let cmp_c = supply.bvsle(&cap_c);
        let body = if calls {
            cmp_b
        } else {
            Bool::from_bool(ctx, false)
        };
        solver.assert(&body._eq(&cmp_c).not());
    })
}

fn all_u64_after(src: &str, needle: &str) -> Vec<u64> {
    let mut out = Vec::new();
    let mut rest = src;
    while let Some(i) = rest.find(needle) {
        rest = &rest[i + needle.len()..];
        let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
        if let Ok(v) = digits.parse() {
            out.push(v);
        }
    }
    out
}

fn all_hex_after(src: &str, needle: &str) -> Vec<u64> {
    let mut out = Vec::new();
    let mut rest = src;
    while let Some(i) = rest.find(needle) {
        rest = &rest[i + needle.len()..];
        let hex: String = rest.chars().take_while(|c| c.is_ascii_hexdigit()).collect();
        if let Ok(v) = u64::from_str_radix(&hex, 16) {
            out.push(v);
        }
    }
    out
}

fn calculate_fee_query(src: &str) -> SatResult {
    let coinbase_zero = src.contains("is_coinbase(tx)");
    let sub = src.contains("checked_sub(total_output)");
    let neg_out = src.contains("total_output < 0");
    let neg_fee = src.contains("if fee < 0");
    let in_add = src.contains("acc.checked_add(utxo.value)");
    let out_add = src.contains("acc.checked_add(output.value)");
    production_lock::check(|ctx, solver| {
        let coinbase = Bool::new_const(ctx, "coinbase");
        let input = BV::new_const(ctx, "fee_in", 64);
        let output = BV::new_const(ctx, "fee_out", 64);
        let (ok_b, fee_b) = fee_outcome(
            ctx,
            &coinbase,
            &input,
            &output,
            coinbase_zero,
            sub,
            neg_out,
            neg_fee,
            in_add,
            out_add,
        );
        let (ok_c, fee_c) = fee_outcome(
            ctx, &coinbase, &input, &output, true, true, true, true, true, true,
        );
        let same = ok_b._eq(&ok_c) & (ok_c.not() | fee_b._eq(&fee_c));
        solver.assert(&same.not());
    })
}

#[allow(clippy::too_many_arguments)]
fn fee_outcome<'a>(
    ctx: &'a z3::Context,
    coinbase: &Bool<'a>,
    input: &BV<'a>,
    output: &BV<'a>,
    coinbase_zero: bool,
    sub: bool,
    neg_out: bool,
    neg_fee: bool,
    in_add: bool,
    out_add: bool,
) -> (Bool<'a>, BV<'a>) {
    let zero = BV::from_i64(ctx, 0, 64);
    let input_sum = if in_add {
        input.clone()
    } else {
        zero.bvsub(input)
    };
    let output_sum = if out_add {
        output.clone()
    } else {
        zero.bvsub(output)
    };
    let computed = if sub {
        input_sum.bvsub(&output_sum)
    } else {
        input_sum.bvadd(&output_sum)
    };
    let neg_out_bad = if neg_out {
        output.bvslt(&zero)
    } else {
        Bool::from_bool(ctx, false)
    };
    let neg_fee_bad = if neg_fee {
        computed.bvslt(&zero)
    } else {
        Bool::from_bool(ctx, false)
    };
    let bad = neg_out_bad | neg_fee_bad;
    let ok_fee = bad.clone().not();
    let fee = bad.ite(&zero, &computed);
    if coinbase_zero {
        let yes = Bool::from_bool(ctx, true);
        (coinbase.ite(&yes, &ok_fee), coinbase.ite(&zero, &fee))
    } else {
        (ok_fee, fee)
    }
}

fn witness_commitment_query(src: &str) -> SatResult {
    let item_len = u64_after(src, "w[0].len() == ").unwrap_or(0);
    let nitems = u64_after(src, "w.len() == ").unwrap_or(0);
    let empty_zero = src.contains("w.is_empty()");
    let absent_ok = src.contains("None => 1");
    let equal = src.contains("commitment == expected_commitment");
    let root_at = src.find("copy_from_slice(witness_merkle_root)");
    let nonce_at = src.find("copy_from_slice(&reserved_nonce)");
    let root_first = match (root_at, nonce_at) {
        (Some(r), Some(n)) => r < n,
        _ => false,
    };
    production_lock::check(|ctx, solver| {
        let sort64 = z3::Sort::bitvector(ctx, 64);
        let sort32 = z3::Sort::bitvector(ctx, 32);
        let sha = z3::FuncDecl::new(ctx, "sha256d", &[&sort64], &sort32);
        let present = Bool::new_const(ctx, "wit_present");
        let empty = Bool::new_const(ctx, "wit_empty");
        let items = BV::new_const(ctx, "wit_items", 16);
        let len = BV::new_const(ctx, "wit_len", 16);
        let root = BV::new_const(ctx, "wit_root", 32);
        let nonce = BV::new_const(ctx, "wit_nonce", 32);
        let commitment = BV::new_const(ctx, "wit_commit", 32);
        let has_commit = Bool::new_const(ctx, "has_commit");
        let body = commitment_ok(
            ctx,
            &sha,
            &present,
            &empty,
            &items,
            &len,
            &root,
            &nonce,
            &commitment,
            &has_commit,
            item_len,
            nitems,
            empty_zero,
            absent_ok,
            equal,
            root_first,
        );
        let clause = commitment_ok(
            ctx,
            &sha,
            &present,
            &empty,
            &items,
            &len,
            &root,
            &nonce,
            &commitment,
            &has_commit,
            32,
            1,
            true,
            true,
            true,
            true,
        );
        solver.assert(&body._eq(&clause).not());
    })
}

#[allow(clippy::too_many_arguments)]
fn commitment_ok<'a>(
    ctx: &'a z3::Context,
    sha: &z3::FuncDecl<'a>,
    present: &Bool<'a>,
    empty: &Bool<'a>,
    items: &BV<'a>,
    len: &BV<'a>,
    root: &BV<'a>,
    nonce: &BV<'a>,
    commitment: &BV<'a>,
    has_commit: &Bool<'a>,
    item_len: u64,
    nitems: u64,
    empty_zero: bool,
    absent_ok: bool,
    equal: bool,
    root_first: bool,
) -> Bool<'a> {
    let one = BV::from_u64(ctx, nitems, 16);
    let want = BV::from_u64(ctx, item_len, 16);
    let shaped = items._eq(&one) & len._eq(&want);
    let bad = if empty_zero {
        present.clone() & empty.clone().not() & shaped.clone().not()
    } else {
        present.clone() & (empty.clone() | shaped.clone().not())
    };
    let use_item = present.clone() & empty.clone().not() & shaped;
    let zero32 = BV::from_u64(ctx, 0, 32);
    let nonce_word = use_item.ite(nonce, &zero32);
    let preimage = pack_preimage(ctx, root, &nonce_word, root_first);
    let expected = sha.apply(&[&preimage]).as_bv().unwrap();
    let cmp = if equal {
        commitment._eq(&expected)
    } else {
        commitment._eq(&expected).not()
    };
    let missing_ok = Bool::from_bool(ctx, absent_ok);
    let matched = has_commit.ite(&cmp, &missing_ok);
    bad.ite(&Bool::from_bool(ctx, false), &matched)
}

fn pack_preimage<'a>(
    ctx: &'a z3::Context,
    root: &BV<'a>,
    nonce: &BV<'a>,
    root_first: bool,
) -> BV<'a> {
    let hi = root.zero_ext(32);
    let lo = nonce.zero_ext(32);
    let shift = BV::from_u64(ctx, 32, 64);
    if root_first {
        hi.bvshl(&shift).bvor(&lo)
    } else {
        lo.bvshl(&shift).bvor(&hi)
    }
}

fn strip_annex_query(src: &str) -> SatResult {
    let tag = hex_after(src, "TAPROOT_ANNEX_TAG: u8 = 0x").unwrap_or(0);
    let min = u64_after(src, "witness.len() >= ").unwrap_or(0);
    production_lock::check(|ctx, solver| {
        let n = BV::new_const(ctx, "annex_n", 16);
        let first = BV::new_const(ctx, "annex_b", 8);
        let out_b = annex_len(ctx, &n, &first, tag, min);
        let (tag_c, min_c) = crate::parser::spec_expr::annex_rule();
        let out_c = annex_len(ctx, &n, &first, tag_c, min_c);
        solver.assert(&out_b._eq(&out_c).not());
    })
}

fn annex_len<'a>(ctx: &'a z3::Context, n: &BV<'a>, first: &BV<'a>, tag: u64, min: u64) -> BV<'a> {
    let strips = n.bvuge(&BV::from_u64(ctx, min, 16)) & first._eq(&BV::from_u64(ctx, tag, 8));
    let popped = n.bvsub(&BV::from_u64(ctx, 1, 16));
    strips.ite(&popped, n)
}

fn witness_sigops_query(src: &str) -> SatResult {
    let mask = hex_after(src, "(flags & 0x").unwrap_or(0);
    let coinbase = src.contains("is_coinbase(tx)");
    let lens = all_u64_after(src, "script_pubkey.len() == ");
    let push = all_hex_after(src, "script_pubkey[1] == 0x");
    let op0 = src.matches("script_pubkey[0] == OP_0").count() == 2;
    let nonempty = src.contains("!witness.is_empty()");
    let p2wpkh_len = lens.first().copied().unwrap_or(0);
    let p2wsh_len = lens.get(1).copied().unwrap_or(0);
    let p2wpkh_push = push.first().copied().unwrap_or(0);
    let p2wsh_push = push.get(1).copied().unwrap_or(0);
    production_lock::check(|ctx, solver| {
        let flags = BV::new_const(ctx, "ws_flags", 32);
        let coin = Bool::new_const(ctx, "ws_coin");
        let spk_len = BV::new_const(ctx, "ws_len", 16);
        let spk1 = BV::new_const(ctx, "ws_p1", 8);
        let empty = Bool::new_const(ctx, "ws_empty");
        let inner = BV::new_const(ctx, "ws_inner", 32);
        let body = witness_sigop_count(
            ctx,
            &flags,
            &coin,
            &spk_len,
            &spk1,
            &empty,
            &inner,
            mask,
            coinbase,
            op0,
            nonempty,
            p2wpkh_len,
            p2wpkh_push,
            p2wsh_len,
            p2wsh_push,
        );
        let clause = witness_sigop_count(
            ctx, &flags, &coin, &spk_len, &spk1, &empty, &inner, 0x800, true, true, true, 22, 0x14,
            34, 0x20,
        );
        solver.assert(&body._eq(&clause).not());
    })
}

#[allow(clippy::too_many_arguments)]
fn witness_sigop_count<'a>(
    ctx: &'a z3::Context,
    flags: &BV<'a>,
    coinbase: &Bool<'a>,
    spk_len: &BV<'a>,
    spk1: &BV<'a>,
    empty: &Bool<'a>,
    inner: &BV<'a>,
    mask: u64,
    coinbase_zero: bool,
    op0: bool,
    nonempty: bool,
    p2wpkh_len: u64,
    p2wpkh_push: u64,
    p2wsh_len: u64,
    p2wsh_push: u64,
) -> BV<'a> {
    let zero = BV::from_u64(ctx, 0, 32);
    let one = BV::from_u64(ctx, 1, 32);
    let flagged = flags.bvand(&BV::from_u64(ctx, mask, 32))._eq(&zero);
    let blocked = if coinbase_zero {
        flagged | coinbase.clone()
    } else {
        flagged
    };
    let byte0_ok = Bool::from_bool(ctx, op0);
    let live = if nonempty {
        empty.clone().not()
    } else {
        empty.clone()
    };
    let p2wpkh = spk_len._eq(&BV::from_u64(ctx, p2wpkh_len, 16))
        & spk1._eq(&BV::from_u64(ctx, p2wpkh_push, 8))
        & byte0_ok.clone()
        & live;
    let p2wsh = spk_len._eq(&BV::from_u64(ctx, p2wsh_len, 16))
        & spk1._eq(&BV::from_u64(ctx, p2wsh_push, 8))
        & byte0_ok;
    let added = p2wpkh.ite(&one, &p2wsh.ite(inner, &zero));
    blocked.ite(&zero, &added)
}

fn chain_query(src: &str) -> SatResult {
    let pushes = src.contains("control_stack.push");
    let pops = src.contains("control_stack.pop()");
    let adds = src.contains("b + a");
    production_lock::check(|ctx, solver| {
        let branch = Bool::new_const(ctx, "branch");
        let depth_b: i64 = i64::from(pushes) - i64::from(pops);
        let depth_ok = Bool::from_bool(ctx, depth_b == 0);
        let mid_b = if adds {
            Bool::from_bool(ctx, true)
        } else {
            Bool::from_bool(ctx, false)
        };
        let f = Bool::from_bool(ctx, false);
        let ran_b = branch.ite(&mid_b, &f);
        let ran_c = branch.ite(&Bool::from_bool(ctx, true), &f);
        solver.assert(&(depth_ok & ran_b._eq(&ran_c)).not());
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn spec_constant_and_ge_patch_are_sat() {
        assert_eq!(cap_query(0, 4_000_000, 4_000_000), z3::SatResult::Unsat);
        assert_eq!(cap_query(0, 4_000_000, 1), z3::SatResult::Sat);
        assert_eq!(cap_query(1, 4_000_000, 4_000_000), z3::SatResult::Sat);
    }

    #[test]
    fn induction_fails_when_the_accumulator_is_not_returned() {
        if !crate::parser::spec_expr::consensus_workspace_present() {
            return;
        }
        let weight = extract_fn(
            &repo("blvm-consensus/src/segwit.rs"),
            "calculate_block_weight",
        );
        assert_eq!(block_weight_induct(&weight), z3::SatResult::Unsat);
        let dropped = weight.replace("Ok(total_weight)", "Ok(0)");
        assert_eq!(block_weight_induct(&dropped), z3::SatResult::Sat);
        let fees = extract_fn(
            &repo("blvm-consensus/src/block/connect.rs"),
            "connect_block_inner",
        );
        assert_eq!(block_fee_induct(&fees), z3::SatResult::Unsat);
        let started = fees.replace("let mut total_fees = 0i64;", "let mut total_fees = 1i64;");
        assert_eq!(block_fee_induct(&started), z3::SatResult::Sat);
    }

    #[test]
    fn missing_call_is_unlocked_and_mir_absence_does_not_block() {
        if !crate::parser::spec_expr::consensus_workspace_present() {
            return;
        }
        let rows = super::super::rows();
        assert!(rows.iter().any(|r| r.function == "is_final_tx"));
        assert!(rows.iter().any(|r| r.function == "enforce_tx_finality"));
        assert!(rows.iter().any(|r| r.function == "retarget_mul_div"));
        for name in [
            "compress_target",
            "opcode_bytes",
            "validate_supply_limit",
            "calculate_fee",
            "validate_witness_commitment",
            "strip_taproot_annex",
            "count_witness_sigops",
        ] {
            let why = unlocked().iter().find(|n| n.contains(name));
            assert!(rows.iter().any(|r| r.function == name), "{name} {why:?}");
        }
        assert!(unlocked().iter().all(|n| !n.contains("is_final_tx")));
        assert!(unlocked().iter().all(|n| !n.contains("checked_mul")));
        assert!(!mir_blocks(false, false));
        assert!(mir_blocks(true, false));
        assert!(!mir_blocks(true, true));
        let present = mir_dump_has("fn_not_in_this_dump");
        if let Some(found) = present {
            assert!(!found);
            assert!(!mir_blocks(found, false));
        }
    }

    fn mir_dump_has(name: &str) -> Option<bool> {
        use std::io::BufRead;
        let deps = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../blvm-consensus/target/debug/deps");
        let mut mirs: Vec<_> = std::fs::read_dir(&deps)
            .ok()?
            .filter_map(|ent| ent.ok())
            .map(|ent| ent.path())
            .filter(|p| p.extension().and_then(|e| e.to_str()) == Some("mir"))
            .collect();
        mirs.sort();
        let path = mirs.pop()?;
        let file = std::fs::File::open(path).ok()?;
        let marker = format!("fn {name}(");
        for line in std::io::BufReader::new(file).lines() {
            let line = line.ok()?;
            if line.starts_with("fn ") && line.contains(&marker) {
                return Some(true);
            }
        }
        Some(false)
    }
}
