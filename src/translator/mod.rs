//! Translator module for BLVM Spec Lock
//!
//! This module contains:
//! - `static`: Fast Rust-based static checks (Tier 1)
//! - `z3_translator`: Rust AST → Z3 AST translation (Tier 2)
//! - `z3_verifier`: Z3 solving and counterexample extraction

pub mod static_checker;

#[cfg(feature = "z3")]
pub mod consensus_set;
#[cfg(feature = "z3")]
pub mod production_lock;
#[cfg(feature = "z3")]
pub mod z3_translator;

#[cfg(feature = "z3")]
pub mod z3_verifier;
