# Coverage JSON shapes

**`cargo spec-lock coverage`** prints different top-level JSON depending on whether **`--spec-path`** is set. Pass/fail is always exit **0** for successful report generation (this command does not run Z3).

## Without `--spec-path` (implementation inventory)

Machine-oriented listing of **`#[spec_locked]`** functions: **`total_spec_locked`**, **`with_contracts`**, **`without_contracts`**, **`contract_coverage_percent`**, **`by_section`**, **`without_section`**.

Formula-related keys: **`formulas_bound_to_rust`** counts Rust **`formula_anchor`** fields; **`constants_bound_to_rust`** counts **`constant_anchor`**. With no **`--spec-path`**, **`formulas_defined`**, **`formulas_parseable_body`**, **`constants_defined`**, and the **`formula_anchor_*`** anchor-resolution counts are **0** (no merged spec / registry load), but rollup fields (**`formulas_verify_rollup`**, **`constants_verify_rollup`**) still parse when **`--rollup-from-verify-json`** is set (counts come only from **`verify`** JSON **`results[]`** rows with the respective **`formula_anchor` / `constant_anchor`** strings).

Optional **`coverage --rollup-from-verify-json PATH`**: **`PATH`** is **`cargo spec-lock verify`** JSON at **`report_format` 1 or 2** (**`results`** array required). Rows with a non-empty **`formula_anchor`** or **`constant_anchor`** accumulate **`passed`/`failed`/`partial`/`not_implemented`** into **`formulas_verify_rollup`/`constants_verify_rollup`** (JSON **`null`** when no qualifying rows existed in the file). Evidence fields on a format 2 row are ignored by this rollup.

| Key | Meaning |
|-----|---------|
| `formulas_defined` | Count of **`F_*`** in merged spec (**0** without **`--spec-path`**) |
| `formulas_parseable_body` | Registry bodies passing verify/enrich parse gate (**0** without registry load) |
| `formulas_bound_to_rust` | Rust functions with **`formula_anchor`** (may be nonzero without **`--spec-path`**) |
| `formula_anchor_parse_gate_ok` | Anchor id resolves + body passes gate (**0** without registry load) |
| `formula_anchor_spec_missing_id` | Anchor id missing from registry (**0** without registry load) |
| `formula_anchor_unparseable_body` | Id resolves but body fails gate (**0** without registry load) |
| `constants_defined` | Count of **`C_*`** constants from merged spec §4 excerpts (**0** without **`--spec-path`**) |
| `constants_bound_to_rust` | Rust functions carrying **`constant_anchor`** |
| `formulas_verify_rollup` | **`null`** or counts object (**`passed`/`failed`/…**) from **`verify`** JSON rows that set **`formula_anchor`** (**`--rollup-from-verify-json`** only — otherwise **`null`**) |
| `constants_verify_rollup` | Same for **`constant_anchor`** rows |

## With `--spec-path` (spec + impl rollup)

**Spec coverage** JSON: theorem/contract metrics (**`total_spec_functions`**, **`total_contracts`**, **`parseable_contracts`**, **`parseable_percent`**, **`impl_with_contracts`**, **`by_section`**, …) **plus** the same **`formulas_*`**, **`constants_*`**, **`formula_anchor_*`**, **`formulas_verify_rollup`**, and **`constants_verify_rollup`** keys as the inventory formatter (registry-filled when **`--spec-path`** is set; rollup still filled from **`verify`** JSON when **`--rollup-from-verify-json`** is passed).

**Environment:** paths default from **`--spec-path`** or **`SPEC_LOCK_SPEC_PATH`**. **`SPEC_LOCK_FORMULAS=0`** empties the formula registry (anchors count as missing id). **`--rollup-from-verify-json`** is independent of **`--spec-path`** (parses **`verify`** JSON only).

## JSON Schema (draft 2020-12)

| Mode | Schema file |
|------|--------------|
| No **`--spec-path`** (inventory) | [`schemas/coverage_inventory_v1.json`](../schemas/coverage_inventory_v1.json) |
| With **`--spec-path`** (spec rollup) | [`schemas/coverage_spec_rollup_v1.json`](../schemas/coverage_spec_rollup_v1.json) |

Schemas use **`additionalProperties: true`** on the document root (extra keys remain allowed unless we document a **`report_format`**-style freeze later).

## See also

- **[VERIFY_JSON.md](VERIFY_JSON.md)** — **`verify`** **`report_format` 2** (older files at **1** still roll up)
- **[LOCKING_MECHANISM.md](LOCKING_MECHANISM.md)** — exit semantics for **`verify`** / strict mode
