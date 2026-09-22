# Spec-lock mutation coverage

Phase 3. Functional obligations. UNSAT means the mutant contradicts the obligation (caught). Encoding of the output sum is signed 64-bit. Lengths are 32-bit. Signature tag and R's first byte are 8-bit.

| mutant | function | change | obligation | Z3 | verdict |
|---|---|---|---|---|---|
| M1 | check_transaction | delete the duplicate-input HashSet check | F_NoDuplicateInputs: equal prevout (txid and vout) iff duplicate reject | UNSAT | caught |
| M2 | check_transaction | duplicate check compares txid only, ignores vout | F_NoDuplicateInputs: equal prevout (txid and vout) iff duplicate reject | UNSAT | caught |
| M3 | check_transaction | wrapping_add instead of checked_add on the output sum | F_OutputSumBounded: Err iff i64 bvadd overflows (width 64) | UNSAT | caught |
| M4 | check_transaction | MAX_MONEY comparison changed from > to >= | F_OutputSumBounded: value == MAX_MONEY is in range, so Ok | UNSAT | caught |
| M5 | check_transaction | allow a single negative output value | F_OutputSumBounded: Ok implies every output is non-negative | UNSAT | caught |
| M6 | is_strict_der | accept signature length 74 | F_StrictDERSoundness: length in 9..=73 | UNSAT | caught |
| M7 | is_strict_der | drop the unnecessary-leading-zero check | F_StrictDERSoundness: no unnecessary leading zero | UNSAT | caught |
| M8 | is_strict_der | drop the high-bit check on R | F_StrictDERSoundness: no high bit on R | UNSAT | caught |
| M9 | is_strict_der | accept tag 0x31 as well as 0x30 | F_StrictDERSoundness: tag byte is 0x30 | UNSAT | caught |
| M10 | merkle_tree_from_hashes | remove the equal-adjacent-hash check before odd-padding | F_MerkleMutationRejected: unpadded equal pair iff mutation; pad is not one | UNSAT | caught |
| M11 | merkle_tree_from_hashes | compare adjacent hashes after padding instead of before | F_MerkleMutationRejected: unpadded equal pair iff mutation; pad is not one | UNSAT | caught |

Control (`false`): Z3 UNSAT — caught.

Consensus mutants caught: 11 / 11.

This count replaces a coverage percentage. A function whose only obligation is a tautology is not formally verified.
