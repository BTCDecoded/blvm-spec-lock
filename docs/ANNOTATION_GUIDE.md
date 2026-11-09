# How to Annotate Functions with `#[spec_locked]`

This guide explains how to add `#[spec_locked("section")]` to functions so they are verified against the Orange Paper.

## Mechanics

1. **Add the attribute** above the function:
   ```rust
   #[spec_locked("5.2")]
   pub fn verify_script(...) -> Result<bool> { ... }
   ```

2. **Use the correct section** from the Orange Paper (e.g. `5.2` for Script Execution, `11.1` for SegWit).

3. **Run check-drift** so spec contracts stay parseable:

   ```bash
   cargo spec-lock check-drift --spec-path ../blvm-spec/PROTOCOL.md ../blvm-spec/ARCHITECTURE.md --crate-path ../blvm-consensus
   ```

4. **Verify** (with Z3 for full SMT solving):

   ```bash
   cargo run --features z3 -p blvm-spec-lock --bin cargo-spec-lock -- verify \
     --spec-path ../blvm-spec/PROTOCOL.md ../blvm-spec/ARCHITECTURE.md --crate-path ../blvm-consensus
   # Partial exits 0. Gate CI on .summary.partial.
   ```

## Current Coverage

| Crate | Annotated (`#[spec_locked]`) | Verified (strict + Z3, CI target) |
|-------|------------------------------|-----------------------------------|
| **blvm-consensus** | 281 | re-run `verify`; a green run is not a body proof |
| **blvm-node** | 5 | 5 (Dandelion 10.6) |
| **blvm-protocol** | 6 | 6 (11.4 + 13.4; use `verify --section` when scoping) |

Re-check counts with `rg '#\[spec_locked' --glob '*.rs'` or **`cargo spec-lock coverage --format json`**. Stale hard-coded totals in docs are a recurring failure mode—prefer commands.

## What Remains to Annotate

### 1. Inline / Embedded Logic

Some Orange Paper functions are implemented inline rather than as standalone functions:

- **P2SHPushOnlyCheck** — ✅ Locked: `p2sh_push_only_check` in script/mod.rs (5.2.1)
- **BIP65Check** — ✅ Locked: `check_bip65` in locktime.rs (5.4.7)
- **FindAndDelete** — ✅ Locked: `find_and_delete` in script/mod.rs (5.1.1)

### 2. blvm-node (Beyond Dandelion)

Network protocol (10.1–10.5), peer management, block sync—these need Orange Paper sections first. The spec currently has high-level descriptions; add **FunctionName** + **Properties** blocks, then annotate.

### 3. blvm-primitives (Serialization, Constants)

Serialization (transaction/block encoding) and constants validation—add Orange Paper sections (e.g. appendix for serialization), then annotate the corresponding functions.

## Process Checklist

1. **Find the Orange Paper section** for the function (e.g. 5.2 Script, 11.1 SegWit, 11.2 Taproot).
2. **Ensure the spec has parseable Properties** — use [SPEC_WORDING.md](../SPEC_WORDING.md) patterns (`result \in \mathbb{N}`, `extracts lower N bits`, etc.).
3. **Add `#[spec_locked("X.Y")]`** above the function.
4. **Run drift check** to ensure spec and impl align:
   ```bash
   cargo spec-lock check-drift --spec-path ../blvm-spec/PROTOCOL.md ../blvm-spec/ARCHITECTURE.md --crate-path ../blvm-consensus
   ```
5. **Run verify** (with `--features z3` for full verification).

## Spec Requirements

For a function to receive contracts, the Orange Paper section must have either:

- **FunctionName**: $\mathbb{N} \rightarrow \mathbb{Z}$ with **Properties** list, or
- **Implementation Invariants** (e.g. 10.6 Dandelion)

The spec parser matches by name (PascalCase ↔ snake_case). If no exact match, it falls back to the first function in the section.

## Troubleshooting

| Issue | Fix |
|-------|-----|
| No contracts / no-contracts | Add **Properties** to the Orange Paper section; use parseable patterns from SPEC_WORDING.md |
| Unparseable | Rewrite condition using supported patterns (e.g. `\in {true, false}` not prose) |
| Z3 translation error | Add support in `z3_translator.rs` (e.g. BitAnd, new known functions) |
| Z3 counterexample | Align spec property with implementation semantics |

## References

- [LOCKING_MECHANISM.md](LOCKING_MECHANISM.md) — Full locking lifecycle, attribute syntax, status semantics
- [SPEC_WORDING.md](../SPEC_WORDING.md) — Parseable condition patterns (use these when adding spec Properties)
- [SPEC_AS_SOURCE_OF_TRUTH.md](../SPEC_AS_SOURCE_OF_TRUTH.md) — Contract flow
- [SPEC_LOCK_COVERAGE.md](../SPEC_LOCK_COVERAGE.md) — Current status
- Prefer **`SPEC_LOCK_COVERAGE.md`** and **`cargo spec-lock coverage`** over any external unpublished tracking notes — if you clone only **`blvm-spec-lock`**, this repo is authoritative for coverage tooling.
