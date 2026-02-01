# Kani Proof Coverage Analysis

This document maps Kani proofs to their properties for Creusot migration.

## Economic Functions

### get_block_subsidy (11 proofs)

**Properties to verify:**
1. **Non-negative**: `subsidy >= 0` for all heights
2. **Halving schedule**: `subsidy = INITIAL_SUBSIDY >> halving_period` when `halving_period < 64`
3. **Zero after 64 halvings**: `subsidy = 0` when `height >= 64 * HALVING_INTERVAL`
4. **Boundary correctness**: Specific values at heights 0, 1, HALVING_INTERVAL, etc.
5. **Halving invariant**: `get_block_subsidy(h + HALVING_INTERVAL) = get_block_subsidy(h) / 2`

**Orange Paper Section**: 6.1

### total_supply (4 proofs)

**Properties to verify:**
1. **Monotonicity**: `total_supply(h2) >= total_supply(h1)` when `h2 >= h1`
2. **Non-negative**: `total_supply(h) >= 0` for all heights
3. **Supply limit**: `total_supply(h) <= MAX_MONEY` for all heights
4. **Convergence**: `lim(h→∞) total_supply(h) = 21 × 10⁶ × C`

**Orange Paper Section**: 6.2

### validate_supply_limit (1 proof)

**Properties to verify:**
1. **Correctness**: `validate_supply_limit(h) = true ⟺ total_supply(h) <= MAX_MONEY`

**Orange Paper Section**: 6.3

### calculate_fee (3 proofs)

**Properties to verify:**
1. **Non-negative**: `fee >= 0` for valid transactions
2. **Correctness**: `fee = sum(inputs.value) - sum(outputs.value)`
3. **Coinbase**: `fee = 0` for coinbase transactions
4. **Overflow safety**: Handles overflow correctly

**Orange Paper Section**: 6.3

## Required Orange Paper Format

To extract these properties, the Orange Paper should include:

1. **Function definitions** with signatures:
   ```
   **FunctionName**: $\mathbb{N} \rightarrow \mathbb{Z}$
   ```

2. **Mathematical formulas**:
   ```
   $$\text{FunctionName}(h) = \text{formula}$$
   ```

3. **Theorems** with properties:
   ```
   **Theorem X.Y.Z** (Property Name): statement
   
   $$\text{formula}$$
   ```

4. **Invariants** as numbered lists or theorems


