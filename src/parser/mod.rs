//! Parser module for BLVM Spec Lock
//!
//! This module contains:
//! - `contracts`: Parses #[requires] and #[ensures] attributes from Rust functions
//! - `orange_paper`: Parses Orange Paper markdown to extract function specifications

pub mod contracts;
pub mod orange_paper;

// Re-export Orange Paper types (used by macro_impl)
// These are the primary types for Orange Paper parsing
pub use orange_paper::{
    SpecSection,
    FunctionSpec,
    Contract,
    ContractType,
    Theorem,
    SpecParser,
    Property,
    PropertyType,
};

// Re-export Rust contract parsing (for future use in verification)
pub use contracts::{Contract as RustContract, ContractType as RustContractType, extract_contracts};

