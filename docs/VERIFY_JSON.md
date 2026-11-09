# Verify JSON report (`report_format` 2)

Machine-readable output from **`cargo spec-lock verify`**.

- **`--format json`** prints this document on **stdout** (no human banner).
- **`--json-out <PATH>`** writes the **same document** to a UTF-8 file **in addition** to whatever `--format` prints on stdout — e.g. **`--format human --json-out spec_lock_verify.json`** gives one solver pass, human logs + a JSON sidecar for CI.

**Pass/fail** for automation remains the process **exit code** (and optional **`SPEC_LOCK_STRICT`** / **`--strict`** — see [Status and exit codes](LOCKING_MECHANISM.md#status-semantics)). This JSON is a **stable, versioned artifact** for counts, dashboards, and attestation hashing; human output is not versioned.

**Environment:** Orange Paper paths default from **`--spec-path`** or **`SPEC_LOCK_SPEC_PATH`** (comma- or colon-separated; used by `verify` and other subcommands that take `--spec-path`). The scanned crate defaults from **`--crate-path`** or **`SPEC_LOCK_CRATE_PATH`** (current directory if unset).

**Formula registry:** **`SPEC_LOCK_FORMULAS=0`** (or **`false`**, **`no`**, **`off`**) skips parsing **`Formula` (`F_*`)** blocks (**`SpecParser::formulas()`** empty — formula anchors resolve as missing). Otherwise formulas are indexed (default when unset). Consensus constants (**`C_*`**) derive from merged **§4** excerpts when **`--spec-path`** is used by **`coverage`/`spec_enrich`/`verify` discovery** tooling; **`constant_anchor`** rows in JSON come from **`C_*`** in **`#[spec_locked]`**.

**`coverage` JSON:** When **`--spec-path`** is set, **`cargo spec-lock coverage --format json`** includes **`formulas_*`**, **`formula_anchor_*`**, **`constants_defined`**, **`constants_bound_to_rust`**, and optional **`formulas_verify_rollup`** / **`constants_verify_rollup`** when **`--rollup-from-verify-json`** is used (same **`F_*`** parse gate as **`check-drift`**). See **[COVERAGE_JSON.md](COVERAGE_JSON.md)** (**`schemas/coverage_inventory_v1.json`**, **`schemas/coverage_spec_rollup_v1.json`**).

## Top-level fields

| Field | Type | Description |
|-------|------|-------------|
| `report_format` | `number` | **2** for `verify`. Version 1 keys remain. `verify-formulas` and the nested `formula_registry` stay **1**. Schema: `schemas/verify_report_v2.json`. The v1 schema file remains for readers of older documents. |
| `command` | `string` | Always **`"verify"`** for this report. |
| `tool` | object | **`name`**: `"blvm-spec-lock"`; **`version`**: semver of the `cargo-spec-lock` binary (same as `cargo-spec-lock --version`). |
| `summary` | object | Aggregate counts — see below. |
| `results` | array | One object per scanned/verified Rust **`#[spec_locked]`** row. |
| `formula_registry` | object \| absent | Present when **`--spec-path`** is set, **`SPEC_LOCK_FORMULAS`** is **on**, and **`F_*`** blocks exist — full **`report_format` 1** document shaped like standalone **`cargo spec-lock verify-formulas`** output (**nested `command`** is **`"verify-formulas"`**, **`tool`/`summary`/`results`** are formula rows only). Omitted entirely when formulas are disabled or absent. Validates with the same **`schemas/formula_verify_report_v1.json`** shape (**see schema** — root vs nested use the same row keys).

### Nested `formula_registry` (merged **`F_*`** gate)

Consumers gate **`verify`** primarily on **`summary`/`results`** for Rust witnesses; **`formula_registry`** mirrors the **`verify-formulas`** subtree for dashboards and **`jq`**.

- **`formula_registry.command`** — always **`verify-formulas`** inside the subtree.
- **`formula_registry.summary`** — counts such as **`static_pass`**, **`static_fail`**, **`z3_sat_pass`**, … (see **`verify-formulas`** standalone output — same keys).
- **`formula_registry.results[]`** — each row includes **`formula_id`**, **`section`**, **`static.status`** (**`passed` \| `failed`**) and **`z3_sat`** (object or **`null`** when **`--skip-z3`**) with **`status`** (**`sat`**, **`unsat`**, **`unknown`**, …).

```bash
# Formula registry aggregates (omit when `.formula_registry` absent)
jq '.formula_registry.summary // empty' spec_lock_verify.json

# Count formulas that passed static parse + Z3 SAT smoke (requires Z3-linked build / no skip)
jq '[.formula_registry.results[]? | select(.static.status == "passed" and .z3_sat != null and .z3_sat.status == "sat")] | length' \
  spec_lock_verify.json

# Rows where SAT smoke rejected the formula (possible contradiction — see nested detail)
jq '.formula_registry.results[]? | select(.z3_sat != null and .z3_sat.status == "unsat")' \
  spec_lock_verify.json
```

### `summary`

| Field | Type | Description |
|-------|------|-------------|
| `total` | `number` | Rows in `results` (filtered set). |
| `passed` | `number` | `VerificationResult::Passed`. |
| `failed` | `number` | Hard failures (`Failed` variant), **excluding** rows counted in `no_contracts`. |
| `partial` | `number` | Partial / unknown-heavy outcomes. |
| `no_contracts` | `number` | Failed because no obligations were derived (distinct from Z3/refutation failures). |
| `evidence` | object | Exclusive slot counts. The keys are `none`, `z3_contract`, `lean_formula`, `lean_model`, `differential`, and `z3_contract+lean_formula`. They sum to `total`. |

### `results[]`

Common keys:

| Field | Type | Description |
|-------|------|-------------|
| `file` | `string` | Path to Rust source file. |
| `function` | `string` | Function name. |
| `section` | `string` | Optional Orange Paper section from `#[spec_locked]`. |
| `anchor_kind` | `string` | Always set: **`function`** (normative **CamelCase** / section lock), **`formula`** (**`F_*`** anchor), or **`constant`** (**`C_*`** anchor). Mirrors resolver precedence: **`formula`** if **`formula_anchor`** is present, else **`constant`** if **`constant_anchor`** is set, else **`function`**. |
| `formula_anchor` | `string` | Present when **`#[spec_locked]`** named **`F_*`** (dual literal, **`§::…`**, or **`function = "F_…"`**). |
| `constant_anchor` | `string` | Present when the second anchor is **`C_*`** (stable id **`SpecParser::constants_stable_id_map`**) instead of **`F_*`**. |
| `status` | `string` | One of: `passed`, `failed`, `partial`, `not_implemented`. The Z3 verdict. Evidence does not change it. |
| `evidence` | array of string | Statuses that apply. `z3_contract` means Z3 discharged an ensures clause from the function body. `lean_formula` means a Lean theorem is the same proposition as the Orange Paper formula and the Lean gate passed. `lean_model` means a Lean theorem about the btc-lean model passed the gate; it says nothing about the Rust. `differential` means the Rust and the btc-lean executable agreed on the same inputs. `none` means no status above applies. |
| `evidence_slot` | string | The one summary bucket for this anchor. `z3_contract+lean_formula` is the pair, counted once. |
| `lean_row_id` | string or null | Census row id when a verified link exists. |
| `lean_declaration` | string or null | Lean declaration name for that row. |
| `lean_classification` | string | `unmapped` when no verified link exists. |
| `lean_covered` | boolean | True only when every Lean check for that link passed. |

Additional keys by status:

- **`failed`**: `reason` always; **`contract`** when the failure is a named contract obligation (omit or use reasoning string for “no contracts” style rows — see implementation). Optional **`detail`** object with **`failure_kind`**: stable string (`counterexample`, `parse_error`, `solver_unknown`, `solver_error`, `tooling`, `other`) — same taxonomy as the **`FailureKind`** enum in **`verify.rs`**. When **`failure_kind`** is **`solver_unknown`**, optional **`detail.partial_reason`** refines wording: **`z3_timeout`** (timeout-style message) vs **`z3_unknown`** (other unknown).
- **`partial`**: `verified`, `total`; optional `reason`. Optional **`detail`** object with **`partial_reason`**: stable string when the tool can classify the gap (`z3_unknown`, **`z3_timeout`**, `unsupported_translation`, `missing_z3_build`, `incomplete_coverage`, `other`).

## Examples

Empty filtered run:

```json
{
  "report_format": 2,
  "command": "verify",
  "tool": {
    "name": "blvm-spec-lock",
    "version": "0.1.10"
  },
  "summary": {
    "total": 0,
    "passed": 0,
    "failed": 0,
    "partial": 0,
    "no_contracts": 0
  },
  "results": []
}
```

## CI: single run (human log + JSON)

```bash
cargo-spec-lock verify $SPEC_ARGS --timeout 120 \
  --format human --json-out spec_lock_verify.json 2>&1 | tee spec_lock_output.txt
```

Prefer **hashing **`spec_lock_verify.json`** for attestation**; keep hashing `spec_lock_output.txt` only during migration.

### `jq` recipes

Assuming **`jq`** is installed:

```bash
# Passed rows (aligned with verification outcomes, not "PASSED" substring counts)
jq -r '.summary.passed // 0' spec_lock_verify.json

# Fail if any failures or missing-contract outcomes (belt-and-suspenders with exit code)
jq -e '(.summary.failed + .summary.no_contracts) == 0' spec_lock_verify.json >/dev/null

# Partial exits 0 with or without `--strict`.
# Gate on JSON when CI must reject Partial:
# jq -e '.summary.partial == 0' spec_lock_verify.json >/dev/null

# Tool identity in logs / metadata
jq -r '.tool | "\(.name) \(.version)"' spec_lock_verify.json

# Count rows by #[spec_locked] anchor kind (function vs F_* vs C_*)
jq '[.results[] | .anchor_kind] | group_by(.) | map({kind: .[0], n: length})' spec_lock_verify.json

# Rows where Z3 stopped with solver unknown (inspect detail.partial_reason: z3_timeout vs z3_unknown)
jq '[.results[] | select(.status == "failed" and .detail.failure_kind == "solver_unknown")] | length' \
  spec_lock_verify.json

# Rows with timeout-style solver unknown only (determinism failures use same codes when prefixed "Determinism: Z3 unknown: …")
jq '[.results[] | select(.status == "failed" and .detail.partial_reason == "z3_timeout")] | length' \
  spec_lock_verify.json
```

**Legacy:** Counting **`grep -c "Status: PASSED"`** on human text is brittle (formatting can change without a semver bump). Prefer **`jq` on `.summary`** once your installed **`cargo-spec-lock`** supports **`--json-out`**.

## `verify-formulas` JSON (`report_format` 1)

**`cargo spec-lock verify-formulas`** emits a **distinct** **`report_format` 1** document for the merged **`F_*`** **`Formula`** registry — **no** Rust **`#[spec_locked]`** rows. Discriminate with top-level **`command`**: **`verify-formulas`**. This command stays at **1** when **`verify`** is **2**.

- **Static gate:** **`formula_latex_parseable_for_verify`**, **`extract_parseable_condition`**, then **`syn::Expr`** (same **`F_*`** path as **`check-formulas`/`verify`/enrich).
- **Z3 SAT smoke:** per formula unless **`--skip-z3`**; requires **`cargo-spec-lock`** built with **`--features z3`**. Without Z3 (**and** **`F_*`** rows exist **and** static gates pass **and** **`--skip-z3`** omitted), **`verify-formulas` exits **`1`**.
- **`--json-out`:** writes this JSON document in addition to human stdout (**`--format human --json-out …`** mirrors **`verify`**).

```bash
cargo spec-lock verify-formulas \
  --spec-path path/to/PROTOCOL.md \
  --format human --json-out spec_lock_verify_formulas.json
```

**Schema:** **`schemas/formula_verify_report_v1.json`**.

## Schema files

Optional JSON Schema validators at the **`blvm-spec-lock`** repo root (**Draft** 2020-12):

- **`schemas/verify_report_v1.json`** — **`cargo spec-lock verify`**
- **`schemas/formula_verify_report_v1.json`** — **`cargo spec-lock verify-formulas`**
