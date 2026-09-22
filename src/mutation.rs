//! Mutation harness for spec-lock obligations.
//!
//! For each mutant, Z3 is asked whether the mutant can still satisfy the
//! obligation on a distinguishing input.
//!
//! - **UNSAT** — the mutant contradicts the obligation. The proof fails. Caught.
//! - **SAT** — a model satisfies both. The obligation does not rule the mutant out.
//!
//! Step 1 scores mutants against the obligations CI uses today
//! (`F_CheckTransactionTotality` is the auto type-contract
//! `result == true || result == false`, `F_BIP66PreActivationPass` is
//! `result == 1` when the fork flag is 0, `F_MerkleRootDeterminism` is
//! `result(H1) == result(H2)`). Those formulas do not mention the checks
//! the mutants delete, so the mutants stay SAT.
//!
//! The control mutant is an obligation of `false`. Z3 reports UNSAT. That is
//! the proof the harness can fail a mutant.

use crate::translator::z3_translator::Z3Translator;
use z3::ast::{Bool, BV};
use z3::{Config, Context, SatResult, Solver};

/// Bump only after the previous phase's failing-mutant test is green.
/// 1 = current CI obligations. 2 = i64 bitvector overflow. 3 = functional formulas.
const OBLIGATION_PHASE: u8 = 2;

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
            Mutant::M3 if OBLIGATION_PHASE >= 2 => {
                "i64 checked_add: Err iff bvadd overflows (width 64)"
            }
            Mutant::M1 | Mutant::M2 | Mutant::M4 | Mutant::M5 => {
                "F_CheckTransactionTotality: result == true || result == false"
            }
            Mutant::M6 | Mutant::M7 | Mutant::M8 | Mutant::M9 => {
                "F_BIP66PreActivationPass: bip66_active == 0 => result == 1"
            }
            Mutant::M10 | Mutant::M11 => "F_MerkleRootDeterminism: result(H1) == result(H2)",
            Mutant::M3 => "F_CheckTransactionTotality: result == true || result == false",
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
                // Same prevout, HashSet check deleted, result stays Valid.
                let dup = Bool::from_bool(ctx, true);
                let rejected = Bool::from_bool(ctx, false);
                solver.assert(&dup);
                solver.assert(&rejected.not());
                let result_ok = Bool::from_bool(ctx, true);
                solver.assert(&Bool::or(ctx, &[&result_ok, &result_ok.not()]));
            }
            Mutant::M2 => {
                // Same txid, different vout. Mutant rejects; totality does not care.
                let txid_eq = Bool::from_bool(ctx, true);
                let vout_eq = Bool::from_bool(ctx, false);
                let rejected = Bool::from_bool(ctx, true);
                solver.assert(&txid_eq);
                solver.assert(&vout_eq.not());
                solver.assert(&rejected);
                let result_ok = Bool::from_bool(ctx, false);
                solver.assert(&Bool::or(ctx, &[&result_ok, &result_ok.not()]));
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
                // Value == MAX_MONEY. Mutant uses >= and rejects. Totality accepts either result.
                let equal_max = Bool::from_bool(ctx, true);
                let rejected = Bool::from_bool(ctx, true);
                solver.assert(&equal_max);
                solver.assert(&rejected);
                let result_ok = Bool::from_bool(ctx, false);
                solver.assert(&Bool::or(ctx, &[&result_ok, &result_ok.not()]));
            }
            Mutant::M5 => {
                // One negative output. Mutant accepts it.
                let negative = Bool::from_bool(ctx, true);
                let result_ok = Bool::from_bool(ctx, true);
                solver.assert(&negative);
                solver.assert(&result_ok);
                solver.assert(&Bool::or(ctx, &[&result_ok, &result_ok.not()]));
            }
            Mutant::M6 | Mutant::M7 | Mutant::M8 | Mutant::M9 => {
                // Byte mutant accepts a bad signature. The pre-activation formula
                // only talks about the inactive fork, where the parser is not called.
                let parser_accepts_bad = Bool::from_bool(ctx, true);
                let active = Bool::from_bool(ctx, false);
                let result_pass = Bool::from_bool(ctx, true);
                solver.assert(&parser_accepts_bad);
                solver.assert(&active.not().implies(&result_pass));
            }
            Mutant::M10 => {
                // Equal adjacent hashes, check removed, mutated flag stays false.
                // Determinism (same inputs, same output) still holds.
                let equal_adj = Bool::from_bool(ctx, true);
                let mutated = Bool::from_bool(ctx, false);
                solver.assert(&equal_adj);
                solver.assert(&mutated.not());
                let deterministic = Bool::from_bool(ctx, true);
                solver.assert(&deterministic);
            }
            Mutant::M11 => {
                // Distinct leaves, odd count. Comparing after the pad sees the
                // padded copy as a duplicate. Determinism still holds.
                let unpadded_equal = Bool::from_bool(ctx, false);
                let mutated = Bool::from_bool(ctx, true);
                solver.assert(&unpadded_equal.not());
                solver.assert(&mutated);
                let deterministic = Bool::from_bool(ctx, true);
                solver.assert(&deterministic);
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
        "Phase 2. `checked_add` is signed 64-bit `bvadd` plus an overflow predicate. \
         M3 (wrapping_add) must be UNSAT. The other mutants are still scored against \
         the tautologies CI proves today. UNSAT means the mutant contradicts the \
         obligation (caught).\n\n",
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
    fn phase2_other_mutants_still_survive_tautologies() {
        assert_eq!(OBLIGATION_PHASE, 2);
        for mutant in Mutant::CONSENSUS {
            if mutant == Mutant::M3 {
                continue;
            }
            assert_eq!(
                judge(mutant),
                Verdict::NotCaught,
                "{} is not covered by the bitvector sum obligation yet",
                mutant.id()
            );
        }
    }

    #[test]
    fn mutation_table_matches_committed_report() {
        let table = render_table();
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("docs/MUTATION_COVERAGE.md");
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
