# The Spec Lock Mechanism

This document describes how blvm-spec-lock links Rust code to the Orange Paper specification and verifies that implementations satisfy their contracts.

## What Is Locking?

**Locking** is the process of binding a Rust function to a specification section and verifying that the implementation satisfies the specified properties. A **locked** function has:

1. **Explicit linkage** — `#[spec_locked("section")]` points to an Orange Paper section
2. **Derived contracts** — Pre/postconditions extracted from the spec (when `--spec-path` is used)
3. **Verification** — Static analysis and/or Z3 SMT solving to check contracts hold

Locking prevents specification drift: if the spec changes, verification fails until the implementation is updated (or the spec is corrected).

## Lifecycle

```
┌─────────────────────────────────────────────────────────────────────────────┐
│ 1. DISCOVER                                                                 │
│    Walk crate sources, find #[spec_locked("X.Y")] on functions and impls   │
└─────────────────────────────────────────────────────────────────────────────┘
                                      │
                                      ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ 2. ENRICH (when --spec-path provided)                                        │
│    Parse Orange Paper: **Functions** (+ Properties / Invariants) OR explicit │
│    **`F_*`** **Formula** blocks when `#[spec_locked]` anchors a formula id │
│    Match by name / section; replace manual attrs with derived contracts       │
└─────────────────────────────────────────────────────────────────────────────┘
                                      │
                                      ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ 3. TRANSLATE                                                                 │
│    Convert contracts to Z3 SMT (or static checker)                          │
│    LaTeX → Rust: \land→&, ≥→>=, \text{Fn}(args)→result                       │
└─────────────────────────────────────────────────────────────────────────────┘
                                      │
                                      ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ 4. VERIFY                                                                   │
│    Run Z3 (or static checker) on each contract                              │
│    Emit: Passed | Failed | Partial | NoContracts                            │
└─────────────────────────────────────────────────────────────────────────────┘
```

## Attribute Syntax

```rust
use blvm_spec_lock::spec_locked;

// Minimal: section only, function name inferred from Rust
#[spec_locked("6.1")]
pub fn get_block_subsidy(height: u64) -> i64 { ... }

// Explicit function name (when spec uses different naming)
#[spec_locked("6.1", "GetBlockSubsidy")]
pub fn get_block_subsidy(height: u64) -> i64 { ... }

// Combined format
#[spec_locked("6.1::GetBlockSubsidy")]
pub fn get_block_subsidy(height: u64) -> i64 { ... }

// Named parameters
#[spec_locked(section = "6.1", function = "GetBlockSubsidy")]
pub fn get_block_subsidy(height: u64) -> i64 { ... }

// Explicit **Orange Paper Formula** id (`**Formula** (**F_*`)` block)
#[spec_locked("6.1", "F_SubsidyHalf")]
pub fn witness_subsidy_property(height: u64) -> i64 { ... }
// Same anchor in combined shorthand:
#[spec_locked("6.1::F_SubsidyHalf")]
pub fn witness_subsidy_property(height: u64) -> i64 { ... }

// Auto-infer section from function name (searches entire spec)
#[spec_locked]
pub fn get_block_subsidy(height: u64) -> i64 { ... }
```

## Contract Types

| Type | Meaning | Example |
|------|---------|---------|
| **requires** | Precondition — must hold before the function runs | `height >= 0` |
| **ensures** | Postcondition — must hold after the function returns | `result >= 0 && result <= INITIAL_SUBSIDY` |

When `--spec-path` is provided, contracts come **only** from the spec. Manual `#[requires]`/`#[ensures]` are ignored. Without `--spec-path`, only manual attributes are used.

## Named formulas (stable `F_*` ids)

Authoring lines use **`Formula`** headings with **`F_Id`** identifiers and **`$$ … $$`** display math — details in **`SPEC_WORDING.md`**.

- **`#[spec_locked("X.Y", "F_Id")]`**, **`X.Y::F_Id`**, or **`function = "F_Id"`** resolve to the **`Formula`** registry (**`cargo spec-lock list-formulas`** prints **TSV**: **`id`**, **`section`**, **`parse_gate`** (`ok`/`fail`), comma-separated **`depends_on`**, comma-separated **`missing_f_refs`** (**`F_*`** under **Depends on** missing after **`merge`**), comma-separated **`missing_c_refs`** (**`C_*`** under **Depends on** absent from merged §**4** **`$CONST = …$`** excerpts), condensed **`latex_body`**).
- **Unresolved **`F_*`** / **`C_*`** Depends on refs** — **`F_*`** absent from merged formula registry; **`C_*`** absent from merged §**4** **`$CONST = …$`** excerpts: **`verify`**, **`check-formulas`**, **`check-drift`**, **`coverage`**, **`summary`**, **`extract-constants`**, **`extract-formulas`**, **`extract-property-tests`** print stderr **`formula_id → dep`** (**non‑fatal**); **`list-formulas`** **`missing_f_refs`** / **`missing_c_refs`** columns.
- The **`#[spec_locked]`** section id must subsume the formula’s section heading id: exact match **or** the formula id extends it with **`.\`** and further segments (**`5.4`** anchors may bind **`Formula`** blocks under **`5.4.1`**, **`5.4.2`**, …).
- **`$$`** bodies go through **`extract_parseable_condition`**. When no Rust-ish obligation is derived, enrichment adds **nothing** for that **`F_*`** (no **`ensures(true)`** placeholder for anchored formulas).

## Verification Modes

| Mode | When | What it does |
|------|------|--------------|
| **Static** | Default (no Z3) | Simple expression checks; most contracts reported as Partial |
| **Z3** | `--features z3` | Full SMT solving; contracts either Passed or Failed |

Use Z3 for full verification. Static mode is a fallback when Z3 is not available.

**Experimental codegen:** **`cargo spec-lock extract-formulas`** and **`extract-property-tests`** emit **heuristic** Rust snippets. They are **not** **`verify`**, are **not** a substitute for **`check-formulas`** / **`verify`**, and should **not** gate releases until the tool defines a tested output contract tracked in-repo (**issues**, **`README`** — **`extract_cmds_integration`** is a minimal smoke only).

Per-function solver time can be raised with **`--timeout <secs>`** on **`verify`**, or with **`SPEC_LOCK_Z3_TIMEOUT_SECS`** in the environment (overrides **`--timeout`** when set to a positive integer), which helps when Orange Paper **Properties** are richer and Z3 returns **Unknown** under the default budget.

## Status Semantics

| Status | Meaning |
|--------|---------|
| **Passed** | All contracts verified for that function (static check and/or Z3 as applicable) |
| **Failed** | At least one obligation **refuted** or a hard error (parse failure, solver error, etc.). Machine-readable **`failure_kind`** is in JSON **`results[].detail.failure_kind`** when present. For **`solver_unknown`**, JSON may add **`detail.partial_reason`** (**`z3_timeout`** vs **`z3_unknown`**) from message text. |
| **Partial** | Solver or pipeline could not complete all obligations (missing Z3 build, incomplete coverage, unsupported translation, …). **`detail.partial_reason`** in JSON when the tool classifies it. |
| **NoContracts** | No spec-derived contracts for the function; add Properties to Orange Paper or `#[requires]` / `#[ensures]`. |

### Exit codes (`cargo spec-lock verify`)

| Condition | Exit code |
|-----------|-----------|
| Any **Failed** | 1 |
| Any **NoContracts** | 1 |
| Any **Partial** (and no failures above) | 0 |
| All **Passed** | 0 |

**`Partial` semantics:** A `Partial` result is emitted when all failures are on spec-derived (auto-enriched) contracts:

| `partial_reason` | Meaning | Exit code |
|------------------|---------|-----------|
| `unsupported_translation` | LaTeX/contract could not be parsed into Z3 | 0 |
| `spec_derived_counterexample` | Z3 counterexample or solver error on spec-derived contract (LaTeX→Z3 gap; informational) | 0 |

**Failed** (exit 1) is reserved for manually-written `#[requires]`/`#[ensures]` contract violations, mixed manual+spec failures, and **NoContracts**. Spec-derived counterexamples are visible in JSON as `partial` with `spec_derived_counterexample` — they do not block CI while the LaTeX→Z3 pipeline matures.

`--strict` / `SPEC_LOCK_STRICT=1` is accepted for backward compatibility but no longer changes exit behaviour for `Partial` results. **NoContracts** and **Failed** fail the process unconditionally. See **[VERIFY_JSON.md](VERIFY_JSON.md)** for the structured report alongside exit codes.

## Section Matching

The spec parser matches functions using this order:

1. **Exact name** in section (e.g. `VerifyScript` ↔ `verify_script`)
2. **Name anywhere** in spec
3. **First function** in section (one spec function applies to all impls in that section)
4. **Parent sections** (5.4.1 → 5.4 → 5) when granularity differs
5. **Implementation Invariants** (`*`) when section has invariants but no named function

See [SPEC_AS_SOURCE_OF_TRUTH.md](../SPEC_AS_SOURCE_OF_TRUTH.md) for spec format details.

## Spec Formats

### FunctionName + Properties

```
**GetBlockSubsidy**: $\mathbb{N} \rightarrow \mathbb{Z}$

**Properties**:
- Non-negative: $\text{GetBlockSubsidy}(h) \geq 0$
- Bounded: $\text{GetBlockSubsidy}(h) \leq \text{INITIAL\_SUBSIDY}$
```

### Implementation Invariants

For algorithm sections (e.g. Dandelion 10.6):

```
**Implementation Invariants (BLVM Specification Lock Verified)**:
1. **No Premature Broadcast**: $\text{phase} = \text{Stem} \implies \text{broadcast\_count}(tx) = 0$
2. **Bounded Stem Length**: $\text{stem\_hops}(tx) \leq \text{max\_stem\_hops}$
```

Any `#[spec_locked("section")]` in that section receives these contracts.

## Parseable Patterns

Orange Paper conditions must use patterns the condition parser recognizes. See [SPEC_WORDING.md](../SPEC_WORDING.md) for:

- `result \in \mathbb{N}` → `result >= 0`
- `\land` → `&` (bitwise AND)
- `extracts lower N bits` → `result >= 0 && result < 2^N`
- What to avoid (activation heights in conditions, mixed prose)

## Lock Summary

Use `cargo spec-lock summary` to see lock status without running full verification:

```bash
# Quick overview: functions, sections, enrichment
cargo spec-lock summary --crate-path ../blvm-consensus

# With spec: also shows how many received spec-derived contracts
cargo spec-lock summary --crate-path ../blvm-consensus --spec-path ../blvm-spec/THE_ORANGE_PAPER.md

# Badge format: one-line markdown for README
cargo spec-lock summary --crate-path . --format badge
# Output: [![spec-lock](https://img.shields.io/badge/spec--lock-138%20locked-brightgreen)](#)
```

## CI Integration

```bash
# Basic verification (fail on any Failed)
cargo spec-lock verify --spec-path ../blvm-spec/THE_ORANGE_PAPER.md --crate-path .

# Partial exits 0. Reject it by checking .summary.partial, not --strict.
cargo spec-lock verify --spec-path ../blvm-spec/PROTOCOL.md ../blvm-spec/ARCHITECTURE.md --crate-path .

# JUnit for CI reporting
cargo spec-lock verify --spec-path ... --crate-path . --format junit > spec-lock.xml
```

## Lock Coverage

| Crate | Locked | Notes |
|-------|--------|-------|
| blvm-consensus | 148 | 100% Z3 verified |
| blvm-node | 5 | Dandelion 10.6 |
| blvm-protocol | 3 | UTXO commitments 11.4 |

See [SPEC_LOCK_COVERAGE.md](../SPEC_LOCK_COVERAGE.md) for full status.

## Related

- [SPEC_AS_SOURCE_OF_TRUTH.md](../SPEC_AS_SOURCE_OF_TRUTH.md) — Spec-derived contract flow
- [SPEC_WORDING.md](../SPEC_WORDING.md) — Parseable condition patterns
- [ANNOTATION_GUIDE.md](ANNOTATION_GUIDE.md) — How to add `#[spec_locked]`
- [SPEC_LOCK_COVERAGE.md](../SPEC_LOCK_COVERAGE.md) — Verification status
