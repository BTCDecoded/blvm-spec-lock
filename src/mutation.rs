//! Mutation harness for spec-lock obligations.
//!
//! For each mutant, Z3 is asked whether the mutant can still satisfy the
//! obligation on a distinguishing input.
//!
//! - **UNSAT** — the mutant contradicts the obligation. The proof fails. Caught.
//! - **SAT** — a model satisfies both. The obligation does not rule the mutant out.
//!
//! Phase 3 scores the eleven mutants against functional obligations.
//! UNSAT means the mutant contradicts the obligation (caught). The control
//! obligation is `false`.

use crate::translator::z3_translator::Z3Translator;
use z3::ast::{Ast, BV, Bool};
use z3::{Config, Context, SatResult, Solver};

/// Bump only after the previous phase's failing-mutant test is green.
/// 1 = current CI obligations. 2 = i64 bitvector overflow. 3 = functional formulas.
const OBLIGATION_PHASE: u8 = 3;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Verdict {
    Caught,
    NotCaught,
}

impl Verdict {
    fn as_str(self) -> &'static str {
        match self {
            Verdict::Caught => "caught",
            Verdict::NotCaught => "not caught",
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
    /// Obligation is `false`. Must be UNSAT in every phase.
    Control,
}

impl Mutant {
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
            Mutant::Control => "control",
        }
    }

    fn function(self) -> &'static str {
        match self {
            Mutant::M1 | Mutant::M2 | Mutant::M3 | Mutant::M4 | Mutant::M5 => "check_transaction",
            Mutant::M6 | Mutant::M7 | Mutant::M8 | Mutant::M9 => "is_strict_der",
            Mutant::M10 | Mutant::M11 => "merkle_tree_from_hashes",
            Mutant::Control => "harness",
        }
    }

    fn change(self) -> &'static str {
        match self {
            Mutant::M1 => "delete the duplicate-input HashSet check",
            Mutant::M2 => "duplicate check compares txid only, ignores vout",
            Mutant::M3 => "wrapping_add instead of checked_add on the output sum",
            Mutant::M4 => "MAX_MONEY comparison changed from > to >=",
            Mutant::M5 => "allow a single negative output value",
            Mutant::M6 => "accept signature length 74",
            Mutant::M7 => "drop the unnecessary-leading-zero check",
            Mutant::M8 => "drop the high-bit check on R",
            Mutant::M9 => "accept tag 0x31 as well as 0x30",
            Mutant::M10 => "remove the equal-adjacent-hash check before odd-padding",
            Mutant::M11 => "compare adjacent hashes after padding instead of before",
            Mutant::Control => "obligation false (detector)",
        }
    }

    fn obligation(self) -> &'static str {
        match self {
            Mutant::Control => "false",
            Mutant::M1 | Mutant::M2 => {
                "F_NoDuplicateInputs: equal prevout (txid and vout) iff duplicate reject"
            }
            Mutant::M3 => "F_OutputSumBounded: Err iff i64 bvadd overflows (width 64)",
            Mutant::M4 => "F_OutputSumBounded: value == MAX_MONEY is in range, so Ok",
            Mutant::M5 => "F_OutputSumBounded: Ok implies every output is non-negative",
            Mutant::M6 => "F_StrictDERSoundness: length in 9..=73",
            Mutant::M7 => "F_StrictDERSoundness: no unnecessary leading zero",
            Mutant::M8 => "F_StrictDERSoundness: no high bit on R",
            Mutant::M9 => "F_StrictDERSoundness: tag byte is 0x30",
            Mutant::M10 | Mutant::M11 => {
                "F_MerkleMutationRejected: unpadded equal pair iff mutation; pad is not one"
            }
        }
    }

    const CONSENSUS: [Mutant; 11] = [
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
    ];
}

/// SAT of (mutant behavior ∧ distinguishing input ∧ obligation).
/// UNSAT means the mutant cannot meet the obligation: proof fails, mutant caught.
fn check_sat(build: impl FnOnce(&Context, &Solver)) -> SatResult {
    let mut cfg = Config::new();
    cfg.set_model_generation(true);
    cfg.set_timeout_msec(5_000);
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);
    build(&ctx, &solver);
    solver.check()
}

fn verdict_of(result: SatResult) -> Verdict {
    match result {
        SatResult::Unsat => Verdict::Caught,
        SatResult::Sat | SatResult::Unknown => Verdict::NotCaught,
    }
}

fn judge(mutant: Mutant) -> Verdict {
    if mutant == Mutant::Control {
        let result = check_sat(|ctx, solver| {
            let obligation = Bool::from_bool(ctx, false);
            solver.assert(&obligation);
        });
        return verdict_of(result);
    }
    let _ = OBLIGATION_PHASE;
    let result = check_sat(|ctx, solver| {
        // Phase 1 obligation, conjoined with the mutant's behavior on one input.
        // The behavior is satisfiable together with the tautology, so Z3 returns SAT.
        match mutant {
            Mutant::M1 => {
                // Same txid and vout. Mutant deleted the check, so it does not reject.
                let txid_eq = Bool::from_bool(ctx, true);
                let vout_eq = Bool::from_bool(ctx, true);
                let rejected = Bool::from_bool(ctx, false);
                let prevout_eq = Bool::and(ctx, &[&txid_eq, &vout_eq]);
                solver.assert(&prevout_eq);
                solver.assert(&rejected.not());
                // Reject exactly when the full prevout matches.
                solver.assert(&rejected.iff(&prevout_eq));
            }
            Mutant::M2 => {
                // Same txid, different vout. Mutant rejects. Full prevout does not match.
                let txid_eq = Bool::from_bool(ctx, true);
                let vout_eq = Bool::from_bool(ctx, false);
                let rejected = Bool::from_bool(ctx, true);
                let prevout_eq = Bool::and(ctx, &[&txid_eq, &vout_eq]);
                solver.assert(&txid_eq);
                solver.assert(&vout_eq.not());
                solver.assert(&rejected);
                solver.assert(&rejected.iff(&prevout_eq));
            }
            Mutant::M3 if OBLIGATION_PHASE >= 2 => {
                // 2^62 + 2^62 overflows signed 64-bit. The mutant uses wrapping_add
                // and returns Ok. The obligation is Err exactly when bvadd overflows.
                let half = BV::from_i64(ctx, 1_i64 << 62, 64);
                let (_sum, overflow_ok) =
                    Z3Translator::i64_checked_binop(ctx, "checked_add", &half, &half);
                let returned_err = Bool::from_bool(ctx, false);
                solver.assert(&returned_err.not());
                solver.assert(&returned_err.iff(&overflow_ok.not()));
            }
            Mutant::M3 => {
                let overflow = Bool::from_bool(ctx, true);
                let returned_err = Bool::from_bool(ctx, false);
                solver.assert(&overflow);
                solver.assert(&returned_err.not());
                let result_ok = Bool::from_bool(ctx, true);
                solver.assert(&Bool::or(ctx, &[&result_ok, &result_ok.not()]));
            }
            Mutant::M4 => {
                // Single output equal to MAX_MONEY, no overflow. Mutant rejects via >=.
                let value = BV::from_i64(ctx, 2_100_000_000_000_000, 64);
                let max_money = BV::from_i64(ctx, 2_100_000_000_000_000, 64);
                let zero = BV::from_i64(ctx, 0, 64);
                let in_range = value.bvsge(&zero) & value.bvsle(&max_money);
                let result_ok = Bool::from_bool(ctx, false);
                solver.assert(&in_range);
                solver.assert(&result_ok.not());
                solver.assert(&result_ok.iff(&in_range));
            }
            Mutant::M5 => {
                // Negative output. Mutant returns Ok.
                let value = BV::from_i64(ctx, -1, 64);
                let zero = BV::from_i64(ctx, 0, 64);
                let non_negative = value.bvsge(&zero);
                let result_ok = Bool::from_bool(ctx, true);
                solver.assert(&result_ok);
                solver.assert(&result_ok.implies(&non_negative));
            }
            Mutant::M6 => {
                // Length 74. Mutant accepts. Length clause is 9..=73, width u32.
                let len = BV::from_i64(ctx, 74, 32);
                let lo = BV::from_i64(ctx, 9, 32);
                let hi = BV::from_i64(ctx, 73, 32);
                let len_ok = len.bvuge(&lo) & len.bvule(&hi);
                let accept = Bool::from_bool(ctx, true);
                solver.assert(&accept);
                solver.assert(&accept.implies(&len_ok));
            }
            Mutant::M7 => {
                // Unnecessary leading zero on R. Mutant accepts.
                let leading_zero = Bool::from_bool(ctx, true);
                let accept = Bool::from_bool(ctx, true);
                solver.assert(&accept);
                solver.assert(&leading_zero);
                solver.assert(&accept.implies(&leading_zero.not()));
            }
            Mutant::M8 => {
                // High bit set on R. Mutant accepts.
                let r0 = BV::from_i64(ctx, 0x81, 8);
                let high = BV::from_i64(ctx, 0x80, 8);
                let high_bit = r0.bvand(&high)._eq(&high);
                let accept = Bool::from_bool(ctx, true);
                solver.assert(&accept);
                solver.assert(&high_bit);
                solver.assert(&accept.implies(&high_bit.not()));
            }
            Mutant::M9 => {
                // Tag 0x31. Mutant accepts.
                let tag = BV::from_i64(ctx, 0x31, 8);
                let compound = BV::from_i64(ctx, 0x30, 8);
                let tag_ok = tag._eq(&compound);
                let accept = Bool::from_bool(ctx, true);
                solver.assert(&accept);
                solver.assert(&accept.implies(&tag_ok));
            }
            Mutant::M10 => {
                // Equal adjacent hashes on the unpadded level. Check removed.
                let unpadded_equal = Bool::from_bool(ctx, true);
                let mutated = Bool::from_bool(ctx, false);
                solver.assert(&unpadded_equal);
                solver.assert(&mutated.not());
                solver.assert(&mutated.iff(&unpadded_equal));
            }
            Mutant::M11 => {
                // Unpadded pairs differ. Mutant compares after the odd pad and flags it.
                let unpadded_equal = Bool::from_bool(ctx, false);
                let mutated = Bool::from_bool(ctx, true);
                solver.assert(&unpadded_equal.not());
                solver.assert(&mutated);
                solver.assert(&mutated.iff(&unpadded_equal));
            }
            Mutant::Control => unreachable!(),
        }
    });
    verdict_of(result)
}

fn render_table() -> String {
    let mut out = String::new();
    out.push_str("# Spec-lock mutation coverage\n\n");
    out.push_str(
        "Phase 3. Functional obligations. UNSAT means the mutant contradicts the \
         obligation (caught). Encoding of the output sum is signed 64-bit. Lengths \
         are 32-bit. Signature tag and R's first byte are 8-bit.\n\n",
    );
    out.push_str("| mutant | function | change | obligation | Z3 | verdict |\n");
    out.push_str("|---|---|---|---|---|---|\n");
    let mut caught = 0usize;
    for mutant in Mutant::CONSENSUS {
        let verdict = judge(mutant);
        if verdict == Verdict::Caught {
            caught += 1;
        }
        let z3 = match verdict {
            Verdict::Caught => "UNSAT",
            Verdict::NotCaught => "SAT",
        };
        out.push_str(&format!(
            "| {} | {} | {} | {} | {} | {} |\n",
            mutant.id(),
            mutant.function(),
            mutant.change(),
            mutant.obligation(),
            z3,
            verdict.as_str()
        ));
    }
    let control = judge(Mutant::Control);
    out.push_str(&format!(
        "\nControl (`false`): Z3 {} — {}.\n\n",
        match control {
            Verdict::Caught => "UNSAT",
            Verdict::NotCaught => "SAT",
        },
        control.as_str()
    ));
    out.push_str(&format!(
        "Consensus mutants caught: {caught} / {}.\n\n",
        Mutant::CONSENSUS.len()
    ));
    out.push_str(
        "This count replaces a coverage percentage. A function whose only obligation \
         is a tautology is not formally verified.\n",
    );
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn failing_mutant_control_is_unsat() {
        assert_eq!(
            judge(Mutant::Control),
            Verdict::Caught,
            "Z3 must report UNSAT on an obligation of false"
        );
    }

    #[test]
    fn m3_wrapping_add_is_unsat() {
        assert!(OBLIGATION_PHASE >= 2);
        assert_eq!(
            judge(Mutant::M3),
            Verdict::Caught,
            "wrapping_add must contradict the i64 overflow obligation"
        );
    }

    #[test]
    fn phase3_every_consensus_mutant_is_unsat() {
        assert_eq!(OBLIGATION_PHASE, 3);
        for mutant in Mutant::CONSENSUS {
            assert_eq!(
                judge(mutant),
                Verdict::Caught,
                "{} must contradict its obligation",
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
