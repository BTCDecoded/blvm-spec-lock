# Lean evidence

One Orange Paper sentence is checked twice, from one parsed formula.

Z3 checks the Rust function body against the clause emitted from that sentence. Z3 is the only check that reads the Rust. Lean checks that the same sentence is a theorem of the model in `blvm-spec/lean/`. Lean does not verify the Rust.

A locked model matches the spec. It catches an inconsistent sentence and a transcription error. It does not, by itself, show that the spec matches Bitcoin Core. `spec_model` means the sentence follows from the locked model and the abstracted list is empty. `spec_model_conditional` still depends on the hypotheses the entry lists. Neither status shows that the spec matches Bitcoin Core.

## Status per sentence

`z3`, `spec_model`, `spec_model_conditional`, `spec_disputed`, `both`, or `none`.

`unsupported` is why a tool did not close. It is not a status. The reason is `parse_failed`, `emitter_shape_missing`, `model_unwritten`, or `out_of_scope`.

`both` means the Rust returns the clause's value for every `u64` in the emitted range, and the Lean theorem is the same sentence over all naturals. It is not a claim that the Rust was checked at unbounded heights.

`spec_disputed` means the emitted statement was not proved. The emission is not weakened to make it provable. The real-valued series beside Theorem 6.2.3 is the first such sentence: issued supply is not that series.

## What is locked

A Lean definition carries `@[spec_lock "<file>#<sentence>"]`. The attribute is the sentence id. One id locks one declaration. The body is a computable `def`. `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, and `noncomputable` fail the gate.

Cryptographic assumptions are fields of `CryptoAssumptions`, passed as a hypothesis. They are not axioms. Theorem 8.3 is that kind of hypothesis.

## Commands

`cargo spec-lock inventory --spec-path PROTOCOL.md ARCHITECTURE.md` prints the sentence classes and the status counts. `--baseline docs/sentence-inventory.tsv` fails when an unsupported id is new, the unsupported count rises, a listed id is now supported and still listed, or a reason code changes.

`cargo spec-lock verify --require-lean` fails when `lean/` is missing beside the spec, or when `lake` is missing. Without the flag, a missing project leaves Lean open and the exit code stays the Z3 result. When the project is present, an open supported sentence fails the run.

The committed baselines are `docs/sentence-inventory.tsv` and `docs/unlocked-definitions.txt`.
