//! Pipeline rows whose clause is that each source check is reached.
//!
//! These rows do not read a `F_*` formula. A missing or discarded check is SAT.
//! `merge` leaves the census query in place.

use crate::parser::condition::extract_parseable_condition;
use z3::SatResult;

/// The census query is the clause. A formula id does not replace it.
pub fn merge(
    _function: &str,
    _plain: &str,
    _boundary: &str,
    _predicate: &str,
    unpatched: SatResult,
    boundary_r: SatResult,
    predicate_r: SatResult,
) -> (SatResult, SatResult, SatResult) {
    (unpatched, boundary_r, predicate_r)
}

pub fn connect_query(src: &str) -> SatResult {
    all_present(
        src,
        &[
            "if let Err(msg) = enforce_tx_finality(",
            "if !header::validate_block_header(",
            "computed_merkle_root != block.header.merkle_root",
            "if merkle_mutated {",
            "if !matches!(check_transaction(tx)?, ValidationResult::Valid)",
            "check_tx_inputs(tx, &overlay, height)",
            "if !matches!(input_valid, ValidationResult::Valid)",
            "if !crate::economic::check_coinbase_subsidy(",
            "if !bip30_result",
            "if !bip34_result",
            "if !crate::bip_validation::check_bip54_timewarp(",
            "if !crate::bip_validation::check_bip54_tx_stripped_size(tx)",
            "if let Some(msg) = crate::bip_validation::check_bip54_sigop_limit(",
            "if !crate::bip_validation::check_bip54_coinbase(",
            "block_weight > crate::constants::MAX_BLOCK_WEIGHT as u64 {",
            "if total_sigop_cost > MAX_BLOCK_SIGOPS_COST",
            "if !validate_witness_commitment(",
            "if !verify_script_with_context_full(",
        ],
    )
}

pub fn script_query(src: &str) -> SatResult {
    all_present(
        src,
        &[
            "script.len() > MAX_SCRIPT_SIZE",
            "> MAX_STACK_SIZE",
            "script_num_decode(",
            "if !execute_opcode_with_context_full(",
            "control_stack.push(control_flow::ControlBlock::If",
            "const OP_ADD: u8 = 0x93",
            "const OP_CHECKSIG: u8 = 0xac",
            "b + a",
        ],
    )
}

pub fn retarget_query(src: &str) -> SatResult {
    all_present(
        src,
        &[
            "prev_headers.len() < 2",
            "return Ok(previous_bits)",
            "time_span.max(expected_time / 4)",
            "expand_target(previous_bits)",
            "old_target.checked_mul_u64(",
            "product >> 64",
            "(remainder << 64) | (self.0[3] as u128)",
            "compress_target(&new_target)",
            "n_size_final << 24",
            "new_bits.min(MAX_TARGET",
        ],
    )
}

fn all_present(src: &str, needles: &[&str]) -> SatResult {
    if needles.iter().all(|needle| src.contains(needle)) {
        SatResult::Unsat
    } else {
        SatResult::Sat
    }
}

fn dispatch_plain() -> Option<String> {
    let script = super::repo("blvm-consensus/src/script/mod.rs");
    let add = super::best_arm(&script, "OP_ADD")?;
    let arith = super::repo("blvm-consensus/src/script/arithmetic.rs");
    let crypto = super::repo("blvm-consensus/src/script/crypto_ops.rs");
    Some(super::drop_inactive_cfg(&super::expand_arm(
        &add, &arith, &crypto,
    )))
}

pub fn connect_source() -> String {
    let connect = super::repo("blvm-consensus/src/block/connect.rs");
    super::drop_inactive_cfg(&super::extract_fn(&connect, "connect_block_inner"))
}

pub fn script_source() -> String {
    let script = super::repo("blvm-consensus/src/script/mod.rs");
    let inner = super::extract_fn(&script, "eval_script_with_context_full_inner");
    let exec = super::extract_fn(&script, "execute_opcode_with_context_full");
    let ops = super::repo("blvm-primitives/src/opcodes.rs");
    let add = dispatch_plain().unwrap_or_default();
    format!("{inner}\n{exec}\n{ops}\n{add}")
}

pub fn retarget_source() -> String {
    let pow = super::repo("blvm-consensus/src/pow.rs");
    format!(
        "{}\n{}\n{}\n{}\n{}",
        super::extract_fn(&pow, "get_next_work_required_internal"),
        super::extract_fn(&pow, "expand_target"),
        super::extract_fn(&pow, "checked_mul_u64"),
        super::extract_fn(&pow, "div_u64"),
        super::extract_fn(&pow, "compress_target"),
    )
}

/// A formula the parser turns into `true`, a tautology, or a bare call is not a clause.
pub fn text_usable(body: &str) -> bool {
    let Some(parsed) = extract_parseable_condition(body) else {
        return false;
    };
    let compact = parsed.replace(' ', "");
    if parsed.trim() == "true" || compact == "result==result" || compact == "result!=result" {
        return false;
    }
    parsed.contains('=') || parsed.contains('<') || parsed.contains('>')
}

fn formula_body(id: &str) -> Option<String> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../blvm-spec/PROTOCOL.md");
    let text = std::fs::read_to_string(path).unwrap_or_default();
    let mut rest = text.as_str();
    let mut found = None;
    while let Some(i) = rest.find("**Formula**") {
        let after = &rest[i..];
        let Some(id_rel) = after.find("**F_") else {
            rest = &after[10..];
            continue;
        };
        let id_start = id_rel + 2;
        let Some(id_end) = after[id_start..].find("**") else {
            break;
        };
        let name = &after[id_start..id_start + id_end];
        let Some(math) = after.find("$$") else {
            break;
        };
        let inner = &after[math + 2..];
        let Some(end) = inner.find("$$") else {
            break;
        };
        if name == id && found.is_none() {
            found = Some(inner[..end].trim().to_string());
        }
        rest = &inner[end + 2..];
    }
    found
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn noise_and_tautology_are_not_clauses() {
        assert!(!text_usable("true"));
        assert!(!text_usable("result == result"));
        assert!(!text_usable("CheckFinalTx(tx)"));
        assert!(text_usable("result > 0 && result <= 486604799"));
    }

    #[test]
    fn weight_dos_guard_does_not_discharge_the_cap() {
        if !crate::parser::spec_expr::consensus_workspace_present() {
            return;
        }
        let cap = "block_weight > crate::constants::MAX_BLOCK_WEIGHT as u64 {";
        let dos = "if block_weight > crate::constants::MAX_BLOCK_WEIGHT as u64 * 2 {";
        assert!(!dos.contains(cap));
        assert_eq!(
            connect_query(&connect_source().replace(cap, dos)),
            SatResult::Sat
        );
    }

    #[test]
    fn pipelines_reject_a_missing_or_discarded_check() {
        if !crate::parser::spec_expr::consensus_workspace_present() {
            return;
        }
        let connect = connect_source();
        assert_eq!(connect_query(&connect), SatResult::Unsat);
        let dropped = connect.replace("if !header::validate_block_header(", "if false {");
        assert_eq!(connect_query(&dropped), SatResult::Sat);
        let discarded = connect.replace("if !bip30_result", "let _kept = bip30_result;");
        assert_eq!(connect_query(&discarded), SatResult::Sat);

        let script = script_source();
        assert_eq!(script_query(&script), SatResult::Unsat);
        let no_exec = script.replace("if !execute_opcode_with_context_full(", "if false {");
        assert_eq!(script_query(&no_exec), SatResult::Sat);

        let retarget = retarget_source();
        assert_eq!(retarget_query(&retarget), SatResult::Unsat);
        let outside = retarget.replace("old_target.checked_mul_u64(", "old_target.other_mul(");
        assert_eq!(retarget_query(&outside), SatResult::Sat);
        let clamped = formula_body("F_NextWorkClamped").expect("F_NextWorkClamped");
        assert!(text_usable(&clamped));
        assert!(!clamped.contains("2015"));
    }
}
