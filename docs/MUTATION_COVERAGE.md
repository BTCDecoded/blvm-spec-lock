# Spec-lock mutation coverage

Query is `body ∧ ¬clause` on the production arm after a source patch and a re-parse. Unpatched UNSAT means the body meets the clause. Patched SAT means the patch breaks it. A patched query that stays UNSAT is not a lock.

| mutant | function | change | shape | patched |
|---|---|---|---|---|
| M1 | check_transaction | delete the duplicate-input HashSet check | pointwise | SAT |
| M2 | check_transaction | insert txid only | pointwise | SAT |
| M3 | check_transaction | wrapping_add on the production output sum | inductive step | SAT |
| M4 | check_transaction | every production MAX_MONEY compare is >= | pointwise | SAT |
| M5 | check_transaction | drop sign and u64-cast rejects so a negative i64 is Ok | pointwise | SAT |
| M6 | is_strict_der | DER length bound 74 | pointwise | SAT |
| M7 | is_strict_der | drop the leading-zero check on R | pointwise | SAT |
| M8 | is_strict_der | drop the high bit check on R | pointwise | SAT |
| M9 | is_strict_der | accept tag 0x31 | pointwise | SAT |
| M10 | merkle_tree_from_hashes | drop the unpadded equal-hash check | inductive step | SAT |
| M11 | merkle_tree_from_hashes | compare adjacent hashes after the odd pad | inductive step | SAT |
| M12 | check_transaction | later production value_u64 compare is >=; fast path stays > | pointwise | SAT |
| M13 | check_transaction | insert txid only | pointwise | SAT |
| M14 | is_strict_der | DER length bound 74 | pointwise | SAT |
| M15 | merkle_tree_from_hashes | compare adjacent hashes after the odd pad | inductive step | SAT |

Unpatched production arms:

- output at MAX_MONEY: UNSAT
- negative output: UNSAT
- duplicate prevout: UNSAT
- output-sum step: UNSAT
- DER length 74: UNSAT
- DER high bit: UNSAT
- DER leading zero: UNSAT
- DER tag 0x31: UNSAT
- merkle mutation: UNSAT

## Consensus set

| function | shape | unpatched | boundary | predicate |
|---|---|---|---|---|
| check_bip147 | threshold | UNSAT | SAT | SAT |
| checkmultisig_window | multisig | UNSAT | SAT | SAT |
| deserialize_transaction_with_witness | tx-version | UNSAT | SAT | SAT |
| calculate_block_hash | reorg-undo | UNSAT | SAT | SAT |
| find_common_ancestor | reorg-window | UNSAT | SAT | SAT |
| genesis_header_hash | genesis-coinbase | UNSAT | SAT | SAT |
| OP_2DROP | opcode | UNSAT | SAT | SAT |
| OP_2OVER | opcode | UNSAT | SAT | SAT |
| OP_ABS | opcode | UNSAT | SAT | SAT |
| OP_CHECKSIGFROMSTACK | opcode | UNSAT | SAT | SAT |
| OP_CHECKTEMPLATEVERIFY | opcode | UNSAT | SAT | SAT |
| OP_CODESEPARATOR | opcode | UNSAT | SAT | SAT |
| OP_DEPTH | opcode | UNSAT | SAT | SAT |
| OP_DROP | opcode | UNSAT | SAT | SAT |
| OP_ELSE | opcode | UNSAT | SAT | SAT |
| OP_ENDIF | opcode | UNSAT | SAT | SAT |
| OP_FROMALTSTACK | opcode | UNSAT | SAT | SAT |
| OP_HASH256 | opcode | UNSAT | SAT | SAT |
| OP_NEGATE | opcode | UNSAT | SAT | SAT |
| OP_NOP | opcode | UNSAT | SAT | SAT |
| OP_NOTIF | opcode | UNSAT | SAT | SAT |
| OP_NUMNOTEQUAL | opcode | UNSAT | SAT | SAT |
| OP_OVER | opcode | UNSAT | SAT | SAT |
| OP_RETURN | opcode | UNSAT | SAT | SAT |
| OP_RIPEMD160 | opcode | UNSAT | SAT | SAT |
| OP_SHA1 | opcode | UNSAT | SAT | SAT |
| OP_SHA256 | opcode | UNSAT | SAT | SAT |
| OP_SIZE | opcode | UNSAT | SAT | SAT |
| OP_TOALTSTACK | opcode | UNSAT | SAT | SAT |
| p2sh_push_only_check | script | UNSAT | SAT | SAT |
| validate_supply_limit | supply | UNSAT | SAT | SAT |
| connect_block | pipeline | UNSAT | SAT | SAT |
| eval_script_pipeline | pipeline | UNSAT | SAT | SAT |
| block_fee_induction | inductive | UNSAT | SAT | SAT |

## Boundaries

`verify_signature` and the Schnorr wrappers lock the gates and the bytes passed to an uninterpreted verifier. They do not lock secp256k1. `OP_CHECKSIG`, `OP_CHECKSIGVERIFY`, `OP_CHECKMULTISIG`, `OP_CHECKMULTISIGVERIFY`, and `OP_CHECKSIGADD` lock the stack rule and that the opcode result equals that bit. Hash compression stays uninterpreted. `get_next_work_required_corrected` diverges from Bitcoin and is excluded. The block-weight `* 2` check is a denial-of-service guard and is excluded. `spec_witnesses`, one-call wrappers, mempool policy, and mining templates are excluded.

`count_sigops_in_script`, `calculate_block_weight`, and `calculate_chain_work` each set the accumulator to 0 before the loop and return it when the input is empty. That base is a conjunct of the fold query: the unpatched initializer is 0, and a non-zero initializer makes the query SAT. The inductive rows also require that the function returns that accumulator, and that block fees start at 0 and add each transaction fee before the coinbase check. `total_supply` sums all 64 subsidy epochs. `apply_transaction_with_id` is one update of a UTXO set the caller supplies. It has no zero-supply base. An empty output list is an error, so the successful path is never the empty step.

## Coverage

locked / (locked + unlocked) = 34 / 34

Spec-sourced clauses: 25 locked rows take every clause value from the spec parse (opcode table, section 4 constants, header equations, inclusive ranges, the subsidy shift, and the numeric atoms and concatenations the paper already writes).
`validate_block_header_fields` still proves the null merkle root from the prover. Section 5.3.1 says the merkle root is not part of `ValidBlockHeader`. Timestamp ≠ 0 and bits ≠ 0 are the parsed header equations.
ConnectBlock keeps every gate. The header-call patch leaves the weight comparison in place, so that gate stays. No gate was replaced.
Hash compression stays uninterpreted.
Residual, still locked: the verifier-call rows (`try_verify_p2pk_fast_path`, `try_verify_p2pkh_fast_path`, `try_verify_p2sh_fast_path`, `try_verify_p2wpkh_fast_path`, `OP_CHECKSIG_verifier`, and the result-equals-verifier conjunct on `verify_signature`, `verify_tapscript_schnorr_signature`, `verify_signature_from_stack`); ConnectBlock gates the existing patches do not break; the two pipelines; the five inductive rows; the median index; the program-counter and control-stack steps; `if_body_endif`; the script cache; reorg; block proof; and any row whose parsed sentence is weaker than the existing patch.
- check_bip147
- checkmultisig_window
- deserialize_transaction_with_witness
- calculate_block_hash
- find_common_ancestor
- genesis_header_hash
- connect_block
- eval_script_pipeline
- block_fee_induction

### Unlocked


### Excluded

These names are not in the ratio.

- SHA-256 and RIPEMD-160 compression
- secp256k1 curve arithmetic
- `get_next_work_required_corrected`
- `spec_witnesses` and one-call wrappers
- mempool policy and mining templates
- the block-weight `* 2` denial-of-service guard

