# BLVM Spec Lock

[![crates.io](https://img.shields.io/crates/v/blvm-spec-lock.svg)](https://crates.io/crates/blvm-spec-lock)
[![docs.rs](https://docs.rs/blvm-spec-lock/badge.svg)](https://docs.rs/blvm-spec-lock)
[![CI](https://github.com/BTCDecoded/blvm-spec-lock/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/BTCDecoded/blvm-spec-lock/actions/workflows/ci.yml)
[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg)](./LICENSE)

Purpose-built formal verification tool for Bitcoin Commons.

**Locking mechanism**: See [docs/LOCKING_MECHANISM.md](docs/LOCKING_MECHANISM.md) for the full lifecycle (discover → enrich → verify), attribute syntax, status semantics, and **exit codes** (Partial is non-fatal unless **`--strict`**). **Spec wording**: See [SPEC_WORDING.md](SPEC_WORDING.md) for parseable condition patterns. **How to annotate**: See [docs/ANNOTATION_GUIDE.md](docs/ANNOTATION_GUIDE.md) for adding `#[spec_locked]` to new functions. **Verify JSON (CI / attestation)**: See [docs/VERIFY_JSON.md](docs/VERIFY_JSON.md) (`report_format` **1**, `--json-out`, **`results[].anchor_kind`** — **`function` \| `formula` \| `constant`**, optional **`results[].detail`** — **`failure_kind`** on **`failed`**, **`partial_reason`** on **`partial`** or on **`solver_unknown`** **`failed`** rows as **`z3_timeout`** vs **`z3_unknown`**). **Dashboard `jq` examples** (summaries, anchor kinds): [docs/VERIFY_JSON.md — `jq` recipes](docs/VERIFY_JSON.md#jq-recipes); nested **`formula_registry`** (merged **`F_*`** gate) matches **`schemas/formula_verify_report_v1.json`** when **`verify`** runs with **`--spec-path`**.

## Overview

BLVM Spec Lock annotates Bitcoin consensus functions and Z3-checks their contracts by the steps below. A passing check is not formal verification of a function: in blvm-consensus only 3 of 182 anchors are mutation-validated (see [`docs/VERIFICATION.md`](https://github.com/BTCDecoded/blvm-consensus/blob/main/docs/VERIFICATION.md)).
- Linking Rust functions to Orange Paper specifications via `#[spec_locked]` attributes
- Verifying contracts (`#[requires]` and `#[ensures]`) using static analysis and Z3
- Providing a `cargo test`-like CLI experience

## Installation

```bash
cd blvm-spec-lock
cargo build --release --bin cargo-spec-lock
```

The binary will be at `target/release/cargo-spec-lock`.

To use as a cargo subcommand, create a symlink:
```bash
ln -s target/release/cargo-spec-lock ~/.cargo/bin/cargo-spec-lock
```

Parser and translator live under **`src/parser`** and **`src/translator`**; the proc-macro crate and **`cargo-spec-lock`** binary share those modules. Publish with **`./scripts/publish-crates-io.sh`** (**`cargo login`** required once).

## Usage

### Basic Verification

```bash
# Verify all functions with #[spec_locked]
cargo spec-lock verify

# With Orange Paper: derive contracts from spec (required for 0 no-contracts)
cargo spec-lock verify --spec-path path/to/THE_ORANGE_PAPER.md

# Strict mode: fail on Partial (CI); Failed / no-contracts fail regardless — see docs/LOCKING_MECHANISM.md
cargo spec-lock verify --strict

# Verify specific file
cargo spec-lock verify src/economic.rs

# Verify by subsystem
cargo spec-lock verify --subsystem economic

# Verify by function name
cargo spec-lock verify --name get_block_subsidy

# Verify by Orange Paper section
cargo spec-lock verify --section 6.1

# Experimental: inspect merged **`Formula`** registry (**tab-separated**: **`id`**, **`section`**, **`parse_gate`** (`ok`/`fail`), comma-separated **`depends_on`**, …). **stderr** warns on **cyclic **`F_*`→`F_*`** **`Depends on`** among defined formulas (informational — exit **0**).
cargo spec-lock list-formulas --spec-path path/to/THE_ORANGE_PAPER.md

# Every **`F_*`** body passes the static LaTeX→`syn` gate (same as drift/coverage).
# Optional: after static success, **`--z3-sat`** runs a lightweight satisfiability smoke per formula (requires **`cargo-spec-lock` built with `--features z3`**). Not a substitute for **`verify`** against code.
cargo spec-lock check-formulas --spec-path path/to/THE_ORANGE_PAPER.md
cargo spec-lock check-formulas --spec-path path/to/THE_ORANGE_PAPER.md --z3-sat --timeout 10

# Formula-only **`report_format` 1** JSON (command verify-formulas): static **`F_*`** gate + optional Z3 SAT smoke (requires `--features z3`; use **`--skip-z3`** for static-only; not **`verify`** against Rust).
cargo spec-lock verify-formulas --spec-path path/to/THE_ORANGE_PAPER.md --format human --json-out spec_lock_verify_formulas.json

# Experimental codegen (NOT verify — heuristic stubs; do not gate releases on these):
# `extract-formulas` / `extract-property-tests` emit helper Rust; **`cargo test --test extract_cmds_integration`** holds **P1** exit-path seeds — not **`verify`**; full output contract TBD (**issues** / changelogs).

# Lock status summary (no verification)
cargo spec-lock summary --crate-path .
cargo spec-lock summary --crate-path . --spec-path path/to/THE_ORANGE_PAPER.md
```

### Output Formats

```bash
# Human-readable (default)
cargo spec-lock verify

# JSON only on stdout
cargo spec-lock verify --format json

# Human stdout + JSON sidecar (one verify run — typical for tee + dashboards)
cargo spec-lock verify --format human --json-out spec_lock_verify.json

# JUnit XML (for CI)
cargo spec-lock verify --format junit
```

Field-level documentation, **`jq`** examples, and **`detail`** codes: **[docs/VERIFY_JSON.md](docs/VERIFY_JSON.md)**. Optional JSON Schemas: **`schemas/verify_report_v1.json`** (**`verify`**), **`schemas/formula_verify_report_v1.json`** (**`verify-formulas`**).

Coverage JSON (**`cargo spec-lock coverage --format json`**) is documented in **[docs/COVERAGE_JSON.md](docs/COVERAGE_JSON.md)**; schemas: **`schemas/coverage_inventory_v1.json`** (no **`--spec-path`**) and **`schemas/coverage_spec_rollup_v1.json`** (**`--spec-path`** set). Optional **`coverage --rollup-from-verify-json`** reads **`cargo spec-lock verify`** JSON (**`report_format` 1**) and adds **`formulas_verify_rollup`/`constants_verify_rollup`** (**`formula_anchor`** / **`constant_anchor`** row subsets).

## Writing Contracts

```rust
use blvm_spec_lock::spec_locked;

#[spec_locked("6.1")]
#[requires(height >= 0)]
#[ensures(result >= 0)]
#[ensures(result <= MAX_SUBSIDY)]
pub fn get_block_subsidy(height: u64) -> i64 {
    // Implementation...
}
```

### Related Projects (blvm-spec-lock sibling to blvm-consensus, blvm-spec)

From `blvm-spec-lock` directory:

```bash
# Verify blvm-consensus (140 functions)
cargo run --bin cargo-spec-lock -- verify \
  --spec-path ../blvm-spec/THE_ORANGE_PAPER.md \
  --crate-path ../blvm-consensus

# Verify blvm-node (Dandelion 10.6)
cargo run --bin cargo-spec-lock -- verify \
  --spec-path ../blvm-spec/THE_ORANGE_PAPER.md \
  --crate-path ../blvm-node
```

With Z3: add `--features z3` to the `cargo run` command.

## Validation

- **Golden parser snapshots**: `cargo test golden_ --features z3` (fixtures [`tests/golden/`](tests/golden/), snapshots [`tests/snapshots/`](tests/snapshots/). After intentional **`SpecParser`** changes run `INSTA_UPDATE=always cargo test golden_ --features z3`.
- **Negative verification**: `cargo test wrong_implementation_fails`; `cargo test bare_spec_locked_without_section_reports_no_contracts` — no § on **`#[spec_locked]`** ⇒ no-contracts gate.
- **Spec coverage**: `cargo spec-lock coverage --spec-path ...` — theorems → contracts → parseable % (JSON includes **`formulas_*`**, **`constants_*`**, and optional **`*_verify_rollup`** when **`--rollup-from-verify-json`** is passed; see **[docs/COVERAGE_JSON.md](docs/COVERAGE_JSON.md)**).
- **Drift**: `cargo spec-lock check-drift --spec-path …` — unparseable **Function** contracts; unparseable **`F_*`** **`$$`** bodies (same gate as **verify**/enrich); missing-impl bookkeeping. **`--scoped-unparseables`** and **`--scoped-formulas`** (when available) gate each drift class to § prefixes wired by **`#[spec_locked]`** in the crate — monorepo CI probes **`check-drift --help`** before **`--scoped-formulas`**, mirroring **`--json-out`** on **`verify`**.
- **Formula registry gate**: `cargo spec-lock check-formulas --spec-path …` — all **`F_*`** bodies pass the static parse gate; optional **`--z3-sat`** (Z3 build) adds a per-formula satisfiability smoke (see **Usage** above). **`cargo spec-lock verify-formulas`** writes the **`F_*`** run as **`report_format` 1** JSON (**`command`**: **`verify-formulas`**; see **`docs/VERIFY_JSON.md`**). **`cargo test --test verify_formulas_integration`** — static fail-fast, merged **`verify`**, Z3 **UNSAT** (`formula_verify_unsat_z3.md`), cycle stderr on **`check-formulas`**. **`cargo test --test list_formulas_cycles_integration`** — **`list-formulas`** cycle warnings.
- **Experimental extract codegen** (not **`verify`**): **`cargo test --test extract_cmds_integration`** — smoke exit 0; **`extract_formulas_snap`** / **`extract_property_tests_snap`** — **`insta`** goldens (regenerate: **`INSTA_UPDATE=always cargo test --test extract_*_snap`**).
- **Fuzz** (optional): lexer target under **`fuzz/`**. Scheduled build smoke: **`.github/workflows/fuzz-build-weekly.yml`** (**`cargo build --manifest-path fuzz/Cargo.toml --release --locked`** on **`[self-hosted, Linux, X64, builds]`**). With **[cargo-fuzz](https://github.com/rust-fuzz/cargo-fuzz)** installed: `cd fuzz && cargo +nightly fuzz run lexer_parse`.

## Spec Wording

Orange Paper conditions must be parseable for verification. See **[SPEC_WORDING.md](SPEC_WORDING.md)** for:
- Supported patterns (`\in {true, false}`, `extracts lower N bits`, etc.)
- LaTeX → Rust translation (`\land` → `&`, `≥` → `>=`)
- What to avoid (activation heights in conditions, mixed prose)

To add `#[spec_locked]` to new functions, see **[docs/ANNOTATION_GUIDE.md](docs/ANNOTATION_GUIDE.md)**.

## Features

- **Function Discovery**: Automatically finds all `#[spec_locked]` functions
- **Spec-derived Contracts**: Orange Paper parser + lexer extract parseable conditions (LaTeX, `\text{}`, `\geq`, etc.)
- **Contract Parsing**: Extracts `#[requires]` and `#[ensures]` attributes
- **Static Checking**: Fast Rust-based checks for simple properties
- **Z3 Verification**: Full SMT solving for complex properties (requires `--features z3`)
- **Named formula registry:** **Formula** headings + **`$$…$$`** blocks fill **`SpecParser::formulas()`**; **`#[spec_locked]`** may anchor **`F_*`** or **`C_*`** ([**SPEC_WORDING.md**](SPEC_WORDING.md), [**docs/LOCKING_MECHANISM.md**](docs/LOCKING_MECHANISM.md)).
- **Flexible Filtering**: By file, subsystem, name, or Orange Paper section
- **Multiple Output Formats**: Human-readable, JSON, JUnit XML, Markdown

## Z3 Support

Z3 verification requires the `z3` feature and system dependencies:

### Arch Linux

```bash
# Install Z3, LLVM, LLVM libs, and clang (required for bindgen)
sudo pacman -S z3 llvm llvm-libs clang

# Build with Z3 feature
cargo build --features z3 --bin cargo-spec-lock

# Run verification
cargo run --features z3 --bin cargo-spec-lock -- verify
```

**Important:** You need **both** `llvm` and `llvm-libs` packages. The `llvm` package provides static libraries, while `llvm-libs` provides the shared libraries (`.so` files) that bindgen needs.

**Note:** Ensure LLVM and llvm-libs versions match your clang version. If you have clang 21.x, you need llvm 21.x and llvm-libs 21.x. If versions don't match:
```bash
sudo pacman -Syu llvm llvm-libs clang  # Update all to matching versions
```

### Other Linux Distributions

For Debian/Ubuntu:
```bash
sudo apt-get install libz3-dev libclang-dev
cargo build --features z3 --bin cargo-spec-lock
```

For other distributions, install:
- Z3 development libraries
- LLVM and clang (matching versions)
- libclang development headers

