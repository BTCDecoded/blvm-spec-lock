//! # blvm-spec-lock
//!
//! BLVM Spec Lock: Purpose-built formal verification tool for Bitcoin Commons.
//!
//! This crate provides:
//! - `#[spec_locked]` attribute macro for linking Rust functions to Orange Paper specifications
//! - Direct Rust → Z3 translation for formal verification
//! - CLI tool (`cargo spec-lock`) for verification
//!
//! ## Usage
//!
//! ```rust,ignore
//! use blvm_spec_lock::{spec_locked, requires, ensures};
//!
//! /// GetBlockSubsidy: ℕ → ℤ
//! #[spec_locked("6.1")]
//! #[requires(height >= 0)]
//! #[ensures(result >= 0)]
//! pub fn get_block_subsidy(height: u64) -> i64 {
//!     0
//! }
//! ```
//!
//! (Examples are `ignore` for `cargo test` because `#[spec_locked]` needs `blvm-spec/` next to the
//! crate manifest or `../blvm-spec`. If **PROTOCOL.md** and **ARCHITECTURE.md** exist in either
//! place, they are preferred (merged); otherwise **THE_ORANGE_PAPER.md** is used as fallback.)
//!
//! The macro automatically:
//! 1. Reads the Orange Paper specification
//! 2. Parses the specified section
//! 3. Links function to spec (contracts come from manual annotations or Orange Paper)

#![allow(dead_code)]

#[path = "parser/mod.rs"]
mod parser;
#[path = "translator/mod.rs"]
mod translator;

mod macro_impl;
#[cfg(feature = "z3")]
mod mutation;
mod report;
// CLI module is only used by the binary, not the library

// Note: Proc-macro crates cannot export regular items.
// The binary accesses modules directly via path manipulation.

// Note: Proc-macro crates can only export proc macros, not regular items.
// Parser types are used internally by the macro only.

use proc_macro::TokenStream;

/// Spec-locked function attribute macro
///
/// Links a Rust function to its Orange Paper specification and generates
/// contracts automatically from Orange Paper properties.
///
/// # Parameters
///
/// - `section`: Section ID in Orange Paper (e.g., "6.1")
/// - `function`: Function name in specification (e.g., "GetBlockSubsidy")
/// - `spec_path`: Optional path to Orange Paper (defaults to workspace-relative)
///
/// # Examples
///
/// Simple positional syntax (recommended):
/// ```rust,ignore
/// use blvm_spec_lock::spec_locked;
///
/// #[spec_locked("6.1", "GetBlockSubsidy")]
/// pub fn get_block_subsidy(height: u64) -> i64 {
///     0
/// }
/// ```
///
/// Combined format:
/// ```rust,ignore
/// use blvm_spec_lock::spec_locked;
///
/// #[spec_locked("6.1::GetBlockSubsidy")]
/// pub fn get_block_subsidy(height: u64) -> i64 {
///     0
/// }
/// ```
///
/// Named parameters (also supported):
/// ```rust,ignore
/// use blvm_spec_lock::spec_locked;
///
/// #[spec_locked(section = "6.1", function = "GetBlockSubsidy")]
/// pub fn get_block_subsidy(height: u64) -> i64 {
///     0
/// }
/// ```
///
/// The macro links functions to Orange Paper specifications.
/// Contracts are provided via #[requires] and #[ensures] attributes.
#[proc_macro_attribute]
pub fn spec_locked(args: TokenStream, input: TokenStream) -> TokenStream {
    macro_impl::process_spec_locked(args, input)
}

/// Pass-through macro for #[requires] attributes
///
/// This is a placeholder that allows code to compile.
/// The actual verification will be done by the `cargo spec-lock` tool.
#[proc_macro_attribute]
pub fn requires(_args: TokenStream, input: TokenStream) -> TokenStream {
    // Pass through unchanged - verification tool will process these
    input
}

/// Pass-through macro for #[ensures] attributes
///
/// This is a placeholder that allows code to compile.
/// The actual verification will be done by the `cargo spec-lock` tool.
#[proc_macro_attribute]
pub fn ensures(_args: TokenStream, input: TokenStream) -> TokenStream {
    // Pass through unchanged - verification tool will process these
    input
}

/// Pass-through macro for #[axiom] attributes
///
/// An axiom is a *trusted* assertion about a function's return value.  Unlike
/// `#[ensures]`, an axiom is not verified from the body — it is asserted as a
/// hard constraint in the Z3 solver, enabling the corresponding `#[ensures]` to
/// be discharged.
///
/// Use sparingly: only for properties proven correct by human inspection where
/// the body contains constructs (loops, bitwise parsing) that the translator
/// cannot fully model.
#[proc_macro_attribute]
pub fn axiom(_args: TokenStream, input: TokenStream) -> TokenStream {
    input
}
