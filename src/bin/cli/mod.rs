//! CLI module for BLVM Spec Lock
//!
//! Handles command-line interface, file discovery, and verification orchestration

pub mod verify;
pub mod filters;
pub mod output;
pub mod coverage;
pub mod drift;

pub use verify::*;
pub use filters::*;
pub use output::*;
pub use coverage::*;
pub use drift::*;

