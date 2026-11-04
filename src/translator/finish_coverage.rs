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

    let econ = repo("blvm-consensus/src/economic.rs");
    let script = repo("blvm-consensus/src/script/mod.rs");
    let parse = format!(
        "{}\n{}",
        extract_fn(&script, "p2sh_push_only_check"),
        extract_fn(&script, "parse_one_data_push"),
    );
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

    let connect = repo("blvm-consensus/src/block/connect.rs");

    let supply_limit = format!(
        "TotalSupply(height) <= MAX_MONEY\n{}",
        extract_fn(&econ, "validate_supply_limit")
    );
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

    Finish { rows, unlocked }
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

fn nested_weight_query(src: &str) -> SatResult {
    let init = src.contains("let mut total_weight = 0;") || src.contains("checked_mul(4)");
    let add = src.contains("total_weight +=") || src.contains(".checked_add(");
    let uses = src.contains("calculate_transaction_weight_segwit(")
        || src.contains("transaction_weight_from_stacks(");
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

fn rejects<'a>(ctx: &'a z3::Context, op: u8, value: &BV<'a>, cap: u64) -> Bool<'a> {
    let c = BV::from_u64(ctx, cap, 64);
    match op {
        0 => value.bvugt(&c),
        1 => value.bvuge(&c),
        _ => Bool::from_bool(ctx, false),
    }
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

fn cap_query(op: u8, impl_cap: u64, spec_cap: u64) -> SatResult {
    production_lock::check(|ctx, solver| {
        let n = BV::new_const(ctx, "n", 64);
        let body = rejects(ctx, op, &n, impl_cap);
        let clause = rejects(ctx, 0, &n, spec_cap);
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
    let calls = src.contains("total_supply(") || src.contains("TotalSupply(");
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

fn witness_commitment_query(src: &str) -> SatResult {
    let item_len = u64_after(src, "w[0].len() == ")
        .or_else(|| src.contains("stack[0].len() != 32").then_some(32))
        .unwrap_or(0);
    let nitems = u64_after(src, "w.len() == ")
        .or_else(|| src.contains("stack.len() != 1").then_some(1))
        .unwrap_or(0);
    let empty_zero = src.contains("w.is_empty()");
    let absent_ok = src.contains("None => 1") || src.contains("return Ok(true)");
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
            false,
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

fn witness_sigops_query(src: &str) -> SatResult {
    let mask = hex_after(src, "(flags & 0x")
        .or_else(|| hex_after(src, "flags & 0x"))
        .unwrap_or(0);
    let coinbase = src.contains("is_coinbase(tx)");
    let pubkey_lens = all_u64_after(src, "script_pubkey.len() == ");
    let lens = if pubkey_lens.is_empty() {
        all_u64_after(src, "script.len() == ")
    } else {
        pubkey_lens
    };
    let pubkey_push = all_hex_after(src, "script_pubkey[1] == 0x");
    let push = if pubkey_push.is_empty() {
        all_hex_after(src, "script[1] == 0x")
    } else {
        pubkey_push
    };
    let op0 = src.matches("script_pubkey[0] == OP_0").count() == 2
        || src.matches("script[0] == OP_0").count() >= 2;
    let nonempty = src.contains("!witness.is_empty()") || src.contains("!w.is_empty()");
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
        {
            let name = "validate_supply_limit";
            let why = unlocked().iter().find(|n| n.contains(name));
            assert!(rows.iter().any(|r| r.function == name), "{name} {why:?}");
        }
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
