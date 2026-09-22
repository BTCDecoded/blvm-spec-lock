# Spec-lock mutation coverage

Phase 1. Obligations are the ones CI proves today. UNSAT means the mutant contradicts the obligation (caught). SAT means the obligation still holds of the mutant (not caught).

| mutant | function | change | obligation | Z3 | verdict |
|---|---|---|---|---|---|
| M1 | check_transaction | delete the duplicate-input HashSet check | F_CheckTransactionTotality: result == true || result == false | SAT | not caught |
| M2 | check_transaction | duplicate check compares txid only, ignores vout | F_CheckTransactionTotality: result == true || result == false | SAT | not caught |
| M3 | check_transaction | wrapping_add instead of checked_add on the output sum | F_CheckTransactionTotality: result == true || result == false | SAT | not caught |
| M4 | check_transaction | MAX_MONEY comparison changed from > to >= | F_CheckTransactionTotality: result == true || result == false | SAT | not caught |
| M5 | check_transaction | allow a single negative output value | F_CheckTransactionTotality: result == true || result == false | SAT | not caught |
| M6 | is_strict_der | accept signature length 74 | F_BIP66PreActivationPass: bip66_active == 0 => result == 1 | SAT | not caught |
| M7 | is_strict_der | drop the unnecessary-leading-zero check | F_BIP66PreActivationPass: bip66_active == 0 => result == 1 | SAT | not caught |
| M8 | is_strict_der | drop the high-bit check on R | F_BIP66PreActivationPass: bip66_active == 0 => result == 1 | SAT | not caught |
| M9 | is_strict_der | accept tag 0x31 as well as 0x30 | F_BIP66PreActivationPass: bip66_active == 0 => result == 1 | SAT | not caught |
| M10 | merkle_tree_from_hashes | remove the equal-adjacent-hash check before odd-padding | F_MerkleRootDeterminism: result(H1) == result(H2) | SAT | not caught |
| M11 | merkle_tree_from_hashes | compare adjacent hashes after padding instead of before | F_MerkleRootDeterminism: result(H1) == result(H2) | SAT | not caught |

Control (`false`): Z3 UNSAT — caught.

Consensus mutants caught: 0 / 11.

This count replaces a coverage percentage. A function whose only obligation is a tautology is not formally verified.
