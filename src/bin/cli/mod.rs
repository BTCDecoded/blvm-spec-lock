//! CLI module for BLVM Spec Lock
//!
//! Handles command-line interface, file discovery, and verification orchestration

pub mod coverage;
pub mod drift;
pub mod filters;
pub mod formula_checks;
pub mod formula_dep_graph;
pub mod lean_census;
pub mod lean_evidence;
pub mod lean_gate;
pub mod output;
pub mod spec_enrich;
pub mod verify;
