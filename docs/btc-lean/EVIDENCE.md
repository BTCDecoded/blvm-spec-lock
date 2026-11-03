# Evidence on an Orange Paper anchor

The Orange Paper stays the spec. btc-lean is a separate Lean model. A verify row's `status` is the Z3 verdict. `evidence` is a set beside that verdict. The summary counts each anchor in one slot, so the slot totals add up to the number of anchors.

Pin: `d390f7932e64a134aec3cca1614bed3276539f2d`. The checkout is `BTC_LEAN_ROOT`, or a sibling directory named `btc-lean`. It is not vendored. `docs/btc-lean/anchor-map.json` is the only verified link from a Rust function to a census row. It is empty. An empty map covers nothing.

## Statuses

| Status | What it shows | What it does not show |
|---|---|---|
| `z3_contract` | Z3 discharged an ensures clause from the Rust function body | That a Lean theorem exists, or that the body matches the Lean model |
| `lean_formula` | A Lean theorem is definitionally the proposition emitted from the same formula AST Z3 checked, and the Lean gate passed | Agreement on test vectors |
| `lean_model` | A Lean theorem about the btc-lean model passed the gate | Anything about the Rust |
| `differential` | The Rust output and the btc-lean executable output matched on the same inputs, after the release archive hash matched | A proof. A mismatch is not this status |
| `none` | No status above applies | A failure of the Z3 verdict. Read `status` for that |

`z3_contract` together with `lean_formula` is the only pair that supports "the Rust satisfies the property." That pair is one summary slot, `z3_contract+lean_formula`. `lean_model` and `differential` are never that claim.

`lean_covered` is true only when the pin matches, `make gates` passes, the cited module builds by name, the cited source has no `sorry` or `admit`, the declaration's axioms are inside the allowlist, and a `lean_formula` link is definitionally equal to the emitted statement. The default `lake build BitcoinProofs` is not that check. The elaborator is not wired, so a `lean_formula` link stays uncovered.

## Allowlist

`docs/btc-lean/axiom-allowlist.txt`:

- `propext`
- `Classical.choice`
- `Quot.sound`

Anything else fails the gate. The static manifest at the pin names only these three. That manifest is not a fresh `#print axioms` of every cited declaration. A cited declaration missing from the manifest is not covered.

## Trust base

Trusted when a Lean check is actually run: the Lean 4 kernel at `v4.35.0`, the pinned mathlib revision `cfc55fc58714a59dc06e6e79edc6d1d95140d3c2`, and the elaborator that prints axioms. The formula emitter trusts the spec-lock parser. Z3 is trusted for `z3_contract`. The cryptographic layer in btc-lean is a port checked by conformance vectors. It is not a proof of equality with `libsecp256k1`. That is an assumption, and it is not an extra axiom on the allowlist.

`lake update` is not part of the gate.

## Census

The unit is a row of `spec/db/rules.yaml`. The wallet census is not included. With the empty anchor map, no anchor is `lean_formula`, `lean_model`, or `differential`.

| Class | Rows | Covered |
|---|---:|---|
| obsolete | 50 | no |
| residual | 18 | no |
| out_of_ledger | 6 | no |
| consensus_false | 59 | no |
| unmapped | 593 | no |
| differs | 0 | no |
| lean_formula | 0 | no |

The 18 residual ids stay excluded even though the pinned `docs/RESIDUALS.md` calls that ledger closed. No row is `differs`: a difference is recorded only after the Lean statement and the Orange Paper formula were both compared, and that comparison is not done for the unmapped rows.

## Commands

`cargo spec-lock lean-gate` requires the checkout and fails if the pin or the static gates fail. `cargo spec-lock verify` runs the same gate when the checkout is present. A missing checkout does not mark Lean coverage and does not change the Z3 verdict.

`cargo spec-lock lean-differential --archive <file>` hashes the file against `1ac846bdc24740cfdcf599c3ccf357e48bed50d7fd32071efae605d2a84168b8` before reading rows. `--vectors` is a JSON array of `{anchor, rust, lean}`.
