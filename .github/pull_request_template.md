<!--
GitHub hides this comment on the rendered pull request.

Replace each `_`. `none` and `no` are real answers. Delete a line only when it does not apply, and say why on that line.

- Class: `specification`, `validation`, `serialization`, `crypto`, `protocol`, `node`, `verification`, `release`, `docs`, or `other`.
- Consensus behavior: `yes` only when this change can accept a block or transaction the network would reject, or reject one the network would accept. Name the rule. A refactor that must not do that is `no`.
- What a wrong merge does: one sentence. Name the bad outcome.
- Spec: Orange Paper clause, BIP, or `none`.
- Regression test: path and test name. `none` needs a reason. Consensus behavior `yes` with regression test `none` is the line to stop on.
- Sibling repositories: other BTCDecoded repositories this forces a change in, or `none`.
- Public claim: `yes` if the diff edits a homepage, white paper, README status line, `.github/SYSTEM_STATUS.md`, or a sentence that says governance is enforced or solved. Name the file.
- Emergency: `no`, or `tier_1_critical`, `tier_2_urgent`, or `tier_3_elevated` from `BTCDecoded/governance` `config/emergency-tiers.yml`, plus the activation record. There is no one-maintainer timeout.

Enforcement is off. The written signature count and review period are not collected here.
-->

## Governance

- **Layer:** Verification tool, unassigned. `repository-layers.yml` does not give `blvm-spec-lock` a layer. This repository is the `cargo spec-lock verify` check named inside layer 2.
- **Class:** _
- **Consensus behavior:** _
- **What a wrong merge does:** _
- **Spec:** _
- **Regression test:** _
- **Sibling repositories:** _
- **Public claim:** _
- **Emergency:** _

## This repository

- **Check strength:** _
- **If weaker, the predicate:** _

<!-- Check strength: `stricter`, `unchanged`, or `weaker`. If weaker, name the predicate that was removed, skipped, or muted. Otherwise `n/a`. A weaker check can let a later consensus change pass verify and still diverge from the spec. -->

## Reviewer focus

- _
- _

Enforcement is off. This record does not block the merge.
