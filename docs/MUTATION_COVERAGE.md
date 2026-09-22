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
| check_transaction | pointwise | UNSAT | SAT | SAT |
| is_strict_der | pointwise | UNSAT | SAT | SAT |
| merkle_tree_from_hashes | inductive | UNSAT | SAT | SAT |
| is_sequence_disabled | threshold | UNSAT | SAT | SAT |
| extract_sequence_type_flag | threshold | UNSAT | SAT | SAT |
| extract_sequence_locktime_value | threshold | UNSAT | SAT | SAT |
| get_locktime_type | threshold | UNSAT | SAT | SAT |
| check_bip65 | threshold | UNSAT | SAT | SAT |
| check_proof_of_work | threshold | UNSAT | SAT | SAT |
| validate_witness_program_length | threshold | UNSAT | SAT | SAT |
| validate_block_header | threshold | UNSAT | SAT | SAT |
| validate_block_header_mtp | threshold | UNSAT | SAT | SAT |
| try_verify_p2pk_fast_path | opcode | UNSAT | SAT | SAT |
| try_verify_p2pkh_fast_path | opcode | UNSAT | SAT | SAT |
| try_verify_p2sh_fast_path | opcode | UNSAT | SAT | SAT |
| try_verify_p2wpkh_fast_path | opcode | UNSAT | SAT | SAT |
| compute_script_cache_key | pointwise | UNSAT | SAT | SAT |
| verify_script_cache_hit | pointwise | UNSAT | SAT | SAT |
| sighash_single_quirk | preimage | UNSAT | SAT | SAT |
| eval_script_pc | opcode | UNSAT | SAT | SAT |
| eval_script_control | opcode | UNSAT | SAT | SAT |
| get_block_subsidy | arith | UNSAT | SAT | SAT |
| calculate_transaction_weight_segwit | arith | UNSAT | SAT | SAT |
| weight_to_vsize | arith | UNSAT | SAT | SAT |
| check_coinbase_subsidy | arith | UNSAT | SAT | SAT |
| expand_target | arith | UNSAT | SAT | SAT |
| get_block_proof | arith | UNSAT | SAT | SAT |
| is_coinbase | threshold | UNSAT | SAT | SAT |
| taproot_activation_height | threshold | UNSAT | SAT | SAT |
| check_bip30 | threshold | UNSAT | SAT | SAT |
| check_bip34 | threshold | UNSAT | SAT | SAT |
| check_bip90 | threshold | UNSAT | SAT | SAT |
| check_bip147 | threshold | UNSAT | SAT | SAT |
| is_bip54_active_at | threshold | UNSAT | SAT | SAT |
| check_coinbase_maturity | threshold | UNSAT | SAT | SAT |
| get_median_time_past | threshold | UNSAT | SAT | SAT |
| activation_height_from_headers | threshold | UNSAT | SAT | SAT |
| compute_legacy_sighash_nocache | preimage | UNSAT | SAT | SAT |
| build_bip143_preimage | preimage | UNSAT | SAT | SAT |
| compute_taproot_signature_hash | preimage | UNSAT | SAT | SAT |
| serialize_block_header | preimage | UNSAT | SAT | SAT |
| push_advance | opcode | UNSAT | SAT | SAT |
| OP_0 | opcode | UNSAT | SAT | SAT |
| OP_0NOTEQUAL | opcode | UNSAT | SAT | SAT |
| OP_1 | opcode | UNSAT | SAT | SAT |
| OP_10 | opcode | UNSAT | SAT | SAT |
| OP_11 | opcode | UNSAT | SAT | SAT |
| OP_12 | opcode | UNSAT | SAT | SAT |
| OP_13 | opcode | UNSAT | SAT | SAT |
| OP_14 | opcode | UNSAT | SAT | SAT |
| OP_15 | opcode | UNSAT | SAT | SAT |
| OP_16 | opcode | UNSAT | SAT | SAT |
| OP_1ADD | opcode | UNSAT | SAT | SAT |
| OP_1NEGATE | opcode | UNSAT | SAT | SAT |
| OP_1SUB | opcode | UNSAT | SAT | SAT |
| OP_2 | opcode | UNSAT | SAT | SAT |
| OP_2DIV | opcode | UNSAT | SAT | SAT |
| OP_2DROP | opcode | UNSAT | SAT | SAT |
| OP_2DUP | opcode | UNSAT | SAT | SAT |
| OP_2MUL | opcode | UNSAT | SAT | SAT |
| OP_2OVER | opcode | UNSAT | SAT | SAT |
| OP_2ROT | opcode | UNSAT | SAT | SAT |
| OP_2SWAP | opcode | UNSAT | SAT | SAT |
| OP_3 | opcode | UNSAT | SAT | SAT |
| OP_3DUP | opcode | UNSAT | SAT | SAT |
| OP_4 | opcode | UNSAT | SAT | SAT |
| OP_5 | opcode | UNSAT | SAT | SAT |
| OP_6 | opcode | UNSAT | SAT | SAT |
| OP_7 | opcode | UNSAT | SAT | SAT |
| OP_8 | opcode | UNSAT | SAT | SAT |
| OP_9 | opcode | UNSAT | SAT | SAT |
| OP_ABS | opcode | UNSAT | SAT | SAT |
| OP_ADD | opcode | UNSAT | SAT | SAT |
| OP_BOOLAND | opcode | UNSAT | SAT | SAT |
| OP_BOOLOR | opcode | UNSAT | SAT | SAT |
| OP_CHECKLOCKTIMEVERIFY | opcode | UNSAT | SAT | SAT |
| OP_CHECKMULTISIG | opcode | UNSAT | SAT | SAT |
| OP_CHECKMULTISIGVERIFY | opcode | UNSAT | SAT | SAT |
| OP_CHECKSEQUENCEVERIFY | opcode | UNSAT | SAT | SAT |
| OP_CHECKSIG | opcode | UNSAT | SAT | SAT |
| OP_CHECKSIGADD | opcode | UNSAT | SAT | SAT |
| OP_CHECKSIGFROMSTACK | opcode | UNSAT | SAT | SAT |
| OP_CHECKSIGVERIFY | opcode | UNSAT | SAT | SAT |
| OP_CHECKTEMPLATEVERIFY | opcode | UNSAT | SAT | SAT |
| OP_CODESEPARATOR | opcode | UNSAT | SAT | SAT |
| OP_DEPTH | opcode | UNSAT | SAT | SAT |
| OP_DIV | opcode | UNSAT | SAT | SAT |
| OP_DROP | opcode | UNSAT | SAT | SAT |
| OP_DUP | opcode | UNSAT | SAT | SAT |
| OP_ELSE | opcode | UNSAT | SAT | SAT |
| OP_ENDIF | opcode | UNSAT | SAT | SAT |
| OP_EQUAL | opcode | UNSAT | SAT | SAT |
| OP_EQUALVERIFY | opcode | UNSAT | SAT | SAT |
| OP_FROMALTSTACK | opcode | UNSAT | SAT | SAT |
| OP_GREATERTHAN | opcode | UNSAT | SAT | SAT |
| OP_GREATERTHANOREQUAL | opcode | UNSAT | SAT | SAT |
| OP_HASH160 | opcode | UNSAT | SAT | SAT |
| OP_HASH256 | opcode | UNSAT | SAT | SAT |
| OP_IF | opcode | UNSAT | SAT | SAT |
| OP_IFDUP | opcode | UNSAT | SAT | SAT |
| OP_LESSTHAN | opcode | UNSAT | SAT | SAT |
| OP_LESSTHANOREQUAL | opcode | UNSAT | SAT | SAT |
| OP_LSHIFT | opcode | UNSAT | SAT | SAT |
| OP_MAX | opcode | UNSAT | SAT | SAT |
| OP_MIN | opcode | UNSAT | SAT | SAT |
| OP_MOD | opcode | UNSAT | SAT | SAT |
| OP_MUL | opcode | UNSAT | SAT | SAT |
| OP_NEGATE | opcode | UNSAT | SAT | SAT |
| OP_NIP | opcode | UNSAT | SAT | SAT |
| OP_NOP | opcode | UNSAT | SAT | SAT |
| OP_NOT | opcode | UNSAT | SAT | SAT |
| OP_NOTIF | opcode | UNSAT | SAT | SAT |
| OP_NUMEQUAL | opcode | UNSAT | SAT | SAT |
| OP_NUMEQUALVERIFY | opcode | UNSAT | SAT | SAT |
| OP_NUMNOTEQUAL | opcode | UNSAT | SAT | SAT |
| OP_OVER | opcode | UNSAT | SAT | SAT |
| OP_PICK | opcode | UNSAT | SAT | SAT |
| OP_RETURN | opcode | UNSAT | SAT | SAT |
| OP_RIPEMD160 | opcode | UNSAT | SAT | SAT |
| OP_ROLL | opcode | UNSAT | SAT | SAT |
| OP_ROT | opcode | UNSAT | SAT | SAT |
| OP_RSHIFT | opcode | UNSAT | SAT | SAT |
| OP_SHA1 | opcode | UNSAT | SAT | SAT |
| OP_SHA256 | opcode | UNSAT | SAT | SAT |
| OP_SIZE | opcode | UNSAT | SAT | SAT |
| OP_SUB | opcode | UNSAT | SAT | SAT |
| OP_SWAP | opcode | UNSAT | SAT | SAT |
| OP_TOALTSTACK | opcode | UNSAT | SAT | SAT |
| OP_TUCK | opcode | UNSAT | SAT | SAT |
| OP_VER | opcode | UNSAT | SAT | SAT |
| OP_VERIFY | opcode | UNSAT | SAT | SAT |
| OP_WITHIN | opcode | UNSAT | SAT | SAT |
| OP_CHECKSIG_verifier | opcode | UNSAT | SAT | SAT |
| count_sigops_in_script | fold | UNSAT | SAT | SAT |
| calculate_block_weight | fold | UNSAT | SAT | SAT |
| calculate_chain_work | fold | UNSAT | SAT | SAT |
| apply_transaction_with_id | fold | UNSAT | SAT | SAT |
| verify_signature | signature | UNSAT | SAT | SAT |
| verify_tapscript_schnorr_signature | signature | UNSAT | SAT | SAT |
| verify_signature_from_stack | signature | UNSAT | SAT | SAT |
| calculate_sequence_locks | sequence | UNSAT | SAT | SAT |
| evaluate_sequence_locks | sequence | UNSAT | SAT | SAT |
| get_next_work_required | retarget | UNSAT | SAT | SAT |
| total_supply | supply | UNSAT | SAT | SAT |
| verify_utxo_supply | supply | UNSAT | SAT | SAT |
| get_block_script_verify_flags_core | flags | UNSAT | SAT | SAT |
| check_bip66 | activation | UNSAT | SAT | SAT |
| check_bip54_timewarp | activation | UNSAT | SAT | SAT |
| check_bip54_tx_stripped_size | activation | UNSAT | SAT | SAT |
| check_bip54_sigop_limit | activation | UNSAT | SAT | SAT |
| check_bip54_coinbase | activation | UNSAT | SAT | SAT |
| script_num_decode | scriptnum | UNSAT | SAT | SAT |
| eval_script_limits | limit | UNSAT | SAT | SAT |
| cast_to_bool | script | UNSAT | SAT | SAT |
| is_minimal_if_condition | script | UNSAT | SAT | SAT |
| p2sh_push_only_check | script | UNSAT | SAT | SAT |
| find_and_delete | script | UNSAT | SAT | SAT |
| extract_witness_commitment | witness | UNSAT | SAT | SAT |
| compute_taproot_signature_hash | sighash | UNSAT | SAT | SAT |
| should_reorganize | chain | UNSAT | SAT | SAT |
| get_transaction_sigop_cost_with_utxos | sigop | UNSAT | SAT | SAT |
| check_tx_inputs | tx | UNSAT | SAT | SAT |
| block_weight_limit | limit | UNSAT | SAT | SAT |
| block_sigop_limit | limit | UNSAT | SAT | SAT |
| coinbase_scriptsig_len | limit | UNSAT | SAT | SAT |
| is_final_tx | limit | UNSAT | SAT | SAT |
| opcode_dispatch | dispatch | UNSAT | SAT | SAT |
| if_body_endif | dispatch | UNSAT | SAT | SAT |
| enforce_tx_finality | finality | UNSAT | SAT | SAT |
| retarget_mul_div | retarget | UNSAT | SAT | SAT |
| compress_target | retarget | UNSAT | SAT | SAT |
| opcode_bytes | dispatch | UNSAT | SAT | SAT |
| validate_supply_limit | supply | UNSAT | SAT | SAT |
| calculate_fee | supply | UNSAT | SAT | SAT |
| validate_witness_commitment | witness | UNSAT | SAT | SAT |
| strip_taproot_annex | taproot | UNSAT | SAT | SAT |
| count_witness_sigops | sigop | UNSAT | SAT | SAT |
| connect_block | pipeline | UNSAT | SAT | SAT |
| eval_script_pipeline | pipeline | UNSAT | SAT | SAT |
| get_next_work_pipeline | pipeline | UNSAT | SAT | SAT |
| count_sigops_induction | inductive | UNSAT | SAT | SAT |
| block_weight_induction | inductive | UNSAT | SAT | SAT |
| chain_work_induction | inductive | UNSAT | SAT | SAT |
| block_fee_induction | inductive | UNSAT | SAT | SAT |
| validate_block_header_fields | threshold | UNSAT | SAT | SAT |
| validate_prev_block_hash | threshold | UNSAT | SAT | SAT |
| is_op_success | dispatch | UNSAT | SAT | SAT |
| is_push_opcode | dispatch | UNSAT | SAT | SAT |
| block_weight_from_nested | inductive | UNSAT | SAT | SAT |

## Boundaries

`verify_signature` and the Schnorr wrappers lock the gates and the bytes passed to an uninterpreted verifier. They do not lock secp256k1. `OP_CHECKSIG`, `OP_CHECKSIGVERIFY`, `OP_CHECKMULTISIG`, `OP_CHECKMULTISIGVERIFY`, and `OP_CHECKSIGADD` lock the stack rule and that the opcode result equals that bit. Hash compression stays uninterpreted. `get_next_work_required_corrected` diverges from Bitcoin and is excluded. The block-weight `* 2` check is a denial-of-service guard and is excluded. `spec_witnesses`, one-call wrappers, mempool policy, and mining templates are excluded.

`count_sigops_in_script`, `calculate_block_weight`, and `calculate_chain_work` each set the accumulator to 0 before the loop and return it when the input is empty. That base is a conjunct of the fold query: the unpatched initializer is 0, and a non-zero initializer makes the query SAT. The inductive rows also require that the function returns that accumulator, and that block fees start at 0 and add each transaction fee before the coinbase check. `total_supply` sums all 64 subsidy epochs. `apply_transaction_with_id` is one update of a UTXO set the caller supplies. It has no zero-supply base. An empty output list is an error, so the successful path is never the empty step.

## Coverage

locked / (locked + unlocked) = 189 / 189

Spec-sourced clauses: 136 locked rows take every clause value from the spec parse (opcode table, section 4 constants, header equations, inclusive ranges, the subsidy shift, and the numeric atoms and concatenations the paper already writes).
`validate_block_header_fields` still proves the null merkle root from the prover. Section 5.3.1 says the merkle root is not part of `ValidBlockHeader`. Timestamp ≠ 0 and bits ≠ 0 are the parsed header equations.
ConnectBlock keeps every gate. The header-call patch leaves the weight comparison in place, so that gate stays. No gate was replaced.
Hash compression stays uninterpreted.
Residual, still locked: the verifier-call rows (`try_verify_p2pk_fast_path`, `try_verify_p2pkh_fast_path`, `try_verify_p2sh_fast_path`, `try_verify_p2wpkh_fast_path`, `OP_CHECKSIG_verifier`, and the result-equals-verifier conjunct on `verify_signature`, `verify_tapscript_schnorr_signature`, `verify_signature_from_stack`); ConnectBlock gates the existing patches do not break; the two pipelines; the five inductive rows; the median index; the program-counter and control-stack steps; `if_body_endif`; the script cache; reorg; block proof; and any row whose parsed sentence is weaker than the existing patch.
- try_verify_p2pk_fast_path
- try_verify_p2pkh_fast_path
- try_verify_p2sh_fast_path
- try_verify_p2wpkh_fast_path
- compute_script_cache_key
- verify_script_cache_hit
- eval_script_pc
- eval_script_control
- check_coinbase_subsidy
- get_block_proof
- taproot_activation_height
- check_bip30
- check_bip34
- check_bip147
- get_median_time_past
- compute_legacy_sighash_nocache
- compute_taproot_signature_hash
- serialize_block_header
- OP_CHECKSIG_verifier
- count_sigops_in_script
- calculate_block_weight
- calculate_chain_work
- apply_transaction_with_id
- verify_signature
- verify_tapscript_schnorr_signature
- verify_signature_from_stack
- calculate_sequence_locks
- evaluate_sequence_locks
- verify_utxo_supply
- get_block_script_verify_flags_core
- check_bip66
- script_num_decode
- cast_to_bool
- is_minimal_if_condition
- compute_taproot_signature_hash
- should_reorganize
- check_tx_inputs
- is_final_tx
- if_body_endif
- enforce_tx_finality
- retarget_mul_div
- compress_target
- calculate_fee
- validate_witness_commitment
- count_witness_sigops
- connect_block
- eval_script_pipeline
- get_next_work_pipeline
- count_sigops_induction
- block_weight_induction
- chain_work_induction
- block_fee_induction
- block_weight_from_nested

### Unlocked


### Excluded

These names are not in the ratio.

- SHA-256 and RIPEMD-160 compression
- secp256k1 curve arithmetic
- `get_next_work_required_corrected`
- `spec_witnesses` and one-call wrappers
- mempool policy and mining templates
- the block-weight `* 2` denial-of-service guard

