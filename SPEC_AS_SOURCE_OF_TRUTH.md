# Spec as Single Source of Truth

The Orange Paper (`THE_ORANGE_PAPER.md`) is the **single source of truth** for contracts. Rust `#[requires]`/`#[ensures]` attributes are **not** used when `--spec-path` is provided—all contracts come from the spec.

**See also**: [docs/LOCKING_MECHANISM.md](docs/LOCKING_MECHANISM.md) for the full locking lifecycle, attribute syntax, and verification modes.

## Architecture

## Flow

1. **Discover** functions with `#[spec_locked("section")]`
2. **Parse** Orange Paper, extract **FunctionName** + **Properties** and **Implementation Invariants**
3. **Enrich** each function with spec-derived contracts (replacing any manual ones)
4. **Verify** using the enriched contracts

## Spec Formats Supported

### 1. **FunctionName** + **Properties**
```
**GetBlockSubsidy**: $\mathbb{N} \rightarrow \mathbb{Z}$

**Properties**:
- Non-negative: $\text{GetBlockSubsidy}(h) \geq 0$
- Bounded: $\text{GetBlockSubsidy}(h) \leq \text{INITIAL\_SUBSIDY}$
```

### 2. Implementation Invariants (e.g. 10.6 Dandelion)

Also recognized: **Invariants** (same format as Implementation Invariants).

```
**Implementation Invariants (BLVM Specification Lock Verified)**:
1. **No Premature Broadcast**: $\forall tx, \text{phase}: \text{phase} = \text{Stem} \implies \text{broadcast\_count}(tx) = 0$
2. **Bounded Stem Length**: $\forall tx: \text{stem\_hops}(tx) \leq \text{max\_stem\_hops}$
...
```

When a section has Implementation Invariants but no **FunctionName**, a synthetic `*` function is created. Any `#[spec_locked("section")]` in that section receives those contracts.

## Section Alignment

`#[spec_locked("X.Y")]` must point to an Orange Paper section that has content:

| Section | Content |
|---------|---------|
| 2.2.2 | SafeAdd, SafeSub (overflow-safe arithmetic) |
| 10.6 | Implementation Invariants (Dandelion) |
| 5.x, 6.x, 7.x, etc. | **FunctionName** + **Properties** (consensus-critical math) |

Hash primitives (SHA256, Hash256) are implied by the spec's use in formulas (e.g. ComputeMerkleRoot, block hashing)—no explicit specification needed.

## Current Status

- **blvm-consensus**: 162 passed, 0 failed, 0 partial (all functions fully verified)
- **blvm-node**: 8 passed (Dandelion 10.6, protocol 10.1.1, handshake 10.2.1)
- **Spec scope**: Consensus only. RPC, rate limiters out of scope.

## Contract Matching (Elegant Fallbacks)

When enriching a function, the parser tries in order:
1. **Exact name** in section (e.g. `VerifyScript` ↔ `verify_script`)
2. **Name anywhere** in spec
3. **First function** in section (one spec function per section applies to all impls)
4. **Parent sections** (5.4.1 → 5.4 → 5) when section granularity differs
5. **Implementation Invariants** (`*`) when a named function has no parseable contracts

## Reaching 0 No-Contracts

1. **Add spec content** for every section with `#[spec_locked]`:
   - Add **FunctionName** + **Properties** for each function
   - Or add **Implementation Invariants** for algorithm sections

2. **Fix section numbers** in code when they point to wrong spec sections (e.g. crypto was 2.1, now 8.3.1)

3. **Run with `--spec-path`** always—verification without it cannot use spec-derived contracts

4. **Use `--strict`** to fail on any no-contracts or partial (CI enforcement)

## Commands

```bash
# Verify with spec (required for spec-derived contracts)
cargo run -p blvm-spec-lock --bin cargo-spec-lock -- verify \
  --spec-path ../blvm-spec/THE_ORANGE_PAPER.md \
  --crate-path ../blvm-consensus

# Strict mode (fails on no-contracts)
cargo run -p blvm-spec-lock --bin cargo-spec-lock -- verify \
  --spec-path ../blvm-spec/THE_ORANGE_PAPER.md \
  --crate-path ../blvm-consensus \
  --strict
```
