# BLVM Spec Lock

Purpose-built formal verification tool for Bitcoin Commons.

## Overview

BLVM Spec Lock provides formal verification for Bitcoin consensus code by:
- Linking Rust functions to Orange Paper specifications via `#[spec_locked]` attributes
- Verifying contracts (`#[requires]` and `#[ensures]`) using static analysis and Z3
- Providing a `cargo test`-like CLI experience

## Installation

```bash
cd blvm-spec-lock
cargo build --release --bin cargo-spec-lock
```

The binary will be at `target/release/cargo-spec-lock`.

To use as a cargo subcommand, create a symlink:
```bash
ln -s target/release/cargo-spec-lock ~/.cargo/bin/cargo-spec-lock
```

## Usage

### Basic Verification

```bash
# Verify all functions with #[spec_locked]
cargo spec-lock verify

# Verify specific file
cargo spec-lock verify src/economic.rs

# Verify by subsystem
cargo spec-lock verify --subsystem economic

# Verify by function name
cargo spec-lock verify --name get_block_subsidy

# Verify by Orange Paper section
cargo spec-lock verify --section 6.1
```

### Output Formats

```bash
# Human-readable (default)
cargo spec-lock verify

# JSON
cargo spec-lock verify --format json

# JUnit XML (for CI)
cargo spec-lock verify --format junit
```

## Writing Contracts

```rust
use blvm_spec_lock::spec_locked;

#[spec_locked("6.1")]
#[requires(height >= 0)]
#[ensures(result >= 0)]
#[ensures(result <= MAX_SUBSIDY)]
pub fn get_block_subsidy(height: u64) -> i64 {
    // Implementation...
}
```

## Features

- **Function Discovery**: Automatically finds all `#[spec_locked]` functions
- **Contract Parsing**: Extracts `#[requires]` and `#[ensures]` attributes
- **Static Checking**: Fast Rust-based checks for simple properties
- **Z3 Verification**: Full SMT solving for complex properties (requires `--features z3`)
- **Flexible Filtering**: By file, subsystem, name, or Orange Paper section
- **Multiple Output Formats**: Human-readable, JSON, JUnit XML, Markdown

## Z3 Support

Z3 verification requires the `z3` feature and system dependencies:

### Arch Linux

```bash
# Install Z3, LLVM, LLVM libs, and clang (required for bindgen)
sudo pacman -S z3 llvm llvm-libs clang

# Build with Z3 feature
cargo build --features z3 --bin cargo-spec-lock

# Run verification
cargo run --features z3 --bin cargo-spec-lock -- verify
```

**Important:** You need **both** `llvm` and `llvm-libs` packages. The `llvm` package provides static libraries, while `llvm-libs` provides the shared libraries (`.so` files) that bindgen needs.

**Note:** Ensure LLVM and llvm-libs versions match your clang version. If you have clang 21.x, you need llvm 21.x and llvm-libs 21.x. If versions don't match:
```bash
sudo pacman -Syu llvm llvm-libs clang  # Update all to matching versions
```

### Other Linux Distributions

For Debian/Ubuntu:
```bash
sudo apt-get install libz3-dev libclang-dev
cargo build --features z3 --bin cargo-spec-lock
```

For other distributions, install:
- Z3 development libraries
- LLVM and clang (matching versions)
- libclang development headers

