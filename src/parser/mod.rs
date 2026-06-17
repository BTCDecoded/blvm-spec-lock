//! Parser module for BLVM Spec Lock
//!
//! This module contains:
//! - `contracts`: Parses #[requires] and #[ensures] attributes from Rust functions
//! - `orange_paper`: Parses Orange Paper markdown to extract function specifications
//! - `lexer`: Tokenizes spec condition strings for translation to Rust expressions

pub mod condition;
pub mod contracts;
pub mod lexer;
pub mod orange_paper;

// Re-export Orange Paper types (used by macro_impl; binary uses via submodules)
#[allow(unused_imports)]
pub use orange_paper::{
    Contract, ContractType, FormulaSpec, FunctionSpec, PropertyType, SpecParser, SpecSection,
    section_id_subsumes_formula_section,
};

// Re-export Rust contract parsing (for future use in verification)
