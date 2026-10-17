# Translator Patterns: Hashes, Iterators, Control Flow

Design doc for how blvm-spec-lock's Z3 translator handles complex Rust patterns. The goal: **elegant, extensible translation** that preserves determinism and enables verification.

## Philosophy

- **Implementation IS the formula**: We translate the actual Rust body to Z3 and prove `requires && implementation => ensures`.
- **Uninterpreted over concrete**: For hashes, digests, and opaque operations, we use uninterpreted functions + fresh vars rather than modeling full semantics.
- **Path splitting**: Control flow (if/else, match, if let) splits paths; each path contributes constraints to the overall formula.

---

## 1. Hashes and Digests

### Current approach

| Pattern | Translation |
|---------|-------------|
| `hash256(data)` | Uninterpreted `hash256(Int) -> Int` |
| `implied_hash(root, nonce)` | Uninterpreted `hash256_pair(Int, Int) -> Int` (both halves are inputs; the compression function stays uninterpreted) |
| `sha256(data)` | Uninterpreted (via digest) |
| `digest()` / `finalize()` | Fresh var `{receiver}_digest` |
| `[0u8; 32]` (zero hash) | Literal `0` |

**Why uninterpreted?** Full SHA-256 in Z3 is expensive and rarely needed for consensus verification. We care that:
- Same input → same output (determinism)
- Output is some Int (type constraint)

### Extensions (future)

- **Axioms**: Add `∀x. hash256(x) ≠ hash256(y) when x ≠ y` (injectivity) if needed for proofs.
- **Known hashes**: For constants like `ZERO_HASH`, resolve to literal `0`.
- **Composition**: `hash256(hash256(x))` → `hash256` applied twice; Z3 treats as distinct uninterpreted calls.

---

## 2. Iterators

### Current approach

| Pattern | Translation |
|---------|-------------|
| `x.iter()` / `into_iter()` | Pass-through to receiver (same var) |
| `iter.map(\|w\| w.len())` | Fresh var `{receiver}_map` (closure body not fully translated) |
| `iter.collect()` | Fresh var `{receiver}_collect` |
| `iter.sum()` | Fresh var `{receiver}_sum` |
| `iter.fold(init, \|acc, x\| body)` | Fresh var `{receiver}_fold` |
| `iter.reduce(\|a, b\| body)` | Fresh var `{receiver}_reduce` |
| `iter.next()` | Fresh var `{receiver}_next` |
| `iter.enumerate()` | Pass-through |
| `(0..n).step_by(2)` | Pass-through |

**Key insight**: We don't model iteration semantics. We model *result*: the final value after the loop/iterator chain. For `witness_data.iter().map(|w| w.len()).sum()`:
- `witness_data` is bound by `if let Some(witness_data) = witness`
- `iter()` → pass-through
- `map(...)` → fresh `witness_data_map`
- `sum()` → fresh `{receiver}_sum`

### Bounded iteration (future)

For `for i in 0..n { ... }` where we need to prove loop invariants:

1. **Unroll** for small constant `n` (e.g. `n ≤ 4`).
2. **Induction**: Add `P(0)` and `∀k. P(k) => P(k+1)` for loop invariant `P`.
3. **Summarization**: Replace loop with `result = f(n, init)` where `f` is an uninterpreted function with axioms.

---

## 3. Control Flow

### Supported patterns

| Pattern | Translation |
|---------|-------------|
| `if cond { a } else { b }` | `(cond => result == a) && (!cond => result == b)` |
| `if let Some(x) = opt { a } else { b }` | Same, with `cond = opt_is_some`, `x` bound in then-branch |
| `if let Err(e) = res { a } else { b }` | Same, with `cond = !res_is_ok`, `e` bound in then-branch |
| `if let None = opt { a } else { b }` | Same, with `cond = !opt_is_some` |
| `match opt { Some(x) => a, None => b }` | `ite(opt_is_some, a, b)` |
| `match res { Ok(x) => a, Err(_) => b }` | Same as Option |

### Expr::Let (`if let`)

```
if let Some(witness_data) = witness {
    let witness_size = witness_data.iter().map(|w| w.len()).sum();
    base_size + witness_size
} else {
    base_size
}
```

**Translation**:
1. Parse `let Some(witness_data) = witness` → inner var `witness_data`, expr `witness`.
2. Translate `witness` → ensure var exists.
3. Create/use `witness_is_some : Bool` (Option) or `witness_is_ok : Bool` (Result).
4. Create/use `witness_data : Int` (unwrapped value when Some/Ok).
5. Insert `witness_data` into `vars` so then-branch can use it.
6. Return the condition Bool for the if (is_some/is_ok for Some/Ok, negated for Err/None).

**Supported let patterns**:

| Pattern | Binds | Condition |
|---------|-------|-----------|
| `Some(x)` | `x` | `opt_is_some` |
| `None` | — | `!opt_is_some` |
| `Ok(x)` | `x` | `res_is_ok` |
| `Err(e)` | `e` | `!res_is_ok` |
| `Err(_)` | — | `!res_is_ok` |

Extensible to `Some((a,b))` etc. via `parse_let_option_result_pat`.

### Path splitting

Each branch contributes a conjunct:
- `cond => then_formula`
- `!cond => else_formula`

The solver sees: *if cond holds, then-branch must satisfy result; else else-branch must.*

---

## 4. Stmt::Local and Block Bindings

### Current

- `let x = expr` (Pat::Ident) → translate `expr`, insert `x` into vars.
- `let Some(x) = opt` in **standalone** form → not in Stmt::Local; appears as `Expr::Let` in `if let` condition.

### Gap (resolved)

- `Expr::Let` was previously unsupported → **fixed**: now handled in `translate_expr_with_vars`, returns Bool, binds inner var.

---

## 5. Summary: Elegant Patterns

| Concern | Pattern | Notes |
|---------|---------|-------|
| **Hashes** | Uninterpreted `hash(data) -> Int` | Determinism, no crypto semantics |
| **Iterators** | Fresh vars for `map`/`collect`/`sum`/`fold`/`reduce` | Result-focused, not step-by-step |
| **Loops** | Fresh var for loop result | Bounded unroll/induction for future |
| **if/else** | Path splitting `(cond => then) && (!cond => else)` | Standard |
| **if let** | `Expr::Let` → Bool + bind inner var | `Some(x)`, `Ok(x)`, `Err(e)`, `Err(_)`, `None` |
| **match** | `ite(cond, arm1, arm2)` | 2-arm Option/Result only |

---

## 6. Adding New Patterns

1. **New expression type**: Add match arm in `translate_expr_with_vars` (z3_translator.rs).
2. **New method**: Add case in `Expr::MethodCall` handler (e.g. `"max"`, `"min"`).
3. **New let pattern**: Extend `parse_let_option_result_pat` for `Some((a,b))`, ref patterns, etc.
4. **New uninterpreted fn**: Add to `known_int_returning_function` or `known_bool_uninterpreted_function`.

When in doubt: **fresh var + uninterpreted** is the conservative, extensible choice.
