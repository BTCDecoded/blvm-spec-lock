//! Z3 verifier: Z3 solving with counterexample extraction
//!
//! Uses Z3 to verify contracts and extract counterexamples when verification fails.
//!
//! ## Orange Paper = Single Source of Truth
//!
//! This verifier implements the core principle: the Orange Paper defines the math,
//! and we verify that the Rust implementation satisfies that math.
//!
//! For `ensures` contracts:
//! 1. Extract preconditions (requires) and postconditions (ensures) from Orange Paper
//! 2. Translate the Rust implementation to Z3 formula
//! 3. Prove: requires && implementation => ensures
//!
//! If Z3 proves this implication, the implementation is mathematically locked to the spec.

#[cfg(feature = "z3")]
use z3::{Context, Solver, SatResult, Sort};
#[cfg(feature = "z3")]
use z3::ast::{Ast, Int, Bool, forall_const};
use crate::parser::contracts::{Contract, ContractType};
#[cfg(feature = "z3")]
use crate::translator::z3_translator::Z3Translator;

#[cfg(feature = "z3")]
/// Result of Z3 verification
#[derive(Debug, Clone)]
pub enum VerificationResult {
    /// Property holds (unsatisfiable negation)
    Verified,
    /// Property fails (satisfiable - found counterexample)
    Failed {
        counterexample: Option<Counterexample>,
    },
    /// Verification timed out or was too complex
    Unknown {
        reason: String,
    },
    /// Error during verification
    Error {
        error: String,
    },
}

#[cfg(feature = "z3")]
/// Counterexample from Z3 model
#[derive(Debug, Clone)]
pub struct Counterexample {
    /// Variable assignments that violate the property
    pub assignments: std::collections::HashMap<String, String>,
}

#[cfg(feature = "z3")]
/// Z3 verifier for contracts
pub struct Z3Verifier {
    translator: Z3Translator,
}

#[cfg(feature = "z3")]
impl Z3Verifier {
    /// Create a new Z3 verifier
    pub fn new() -> Self {
        let translator = Z3Translator::new();
        
        Z3Verifier {
            translator,
        }
    }

    /// Verify a contract
    ///
    /// For requires: checks if precondition can be violated
    /// For ensures: checks if postcondition can be violated
    pub fn verify_contract(&mut self, contract: &Contract) -> VerificationResult {
        self.verify_contract_with_context(contract, None, &[])
    }
    
    /// Verify a contract with function signature context for type inference
    /// For ensures contracts, requires_contracts are used as additional constraints
    pub fn verify_contract_with_context(&mut self, contract: &Contract, func_sig: Option<&syn::ItemFn>, requires_contracts: &[Contract]) -> VerificationResult {
        // Extract parameter types and return type from function signature
        let (param_types, return_type) = if let Some(func) = func_sig {
            (extract_parameter_types(func), extract_return_type(func))
        } else {
            (std::collections::HashMap::new(), None)
        };
        
        // Translate contract to Z3 with type information
        let (z3_expr, type_constraints) = match self.translator.translate_contract_with_types(contract, &param_types, return_type.as_ref()) {
            Ok((expr, constraints)) => (expr, constraints),
            Err(e) => {
                return VerificationResult::Error {
                    error: format!("Translation error: {}", e),
                };
            }
        };

        // For verification, we check the negation
        // If negation is unsatisfiable, the property holds
        // If negation is satisfiable, we found a counterexample
        let negated_bool = match z3_expr.as_bool() {
            Some(b) => b.not(),
            None => {
                return VerificationResult::Error {
                    error: "Contract expression must be boolean".to_string(),
                };
            }
        };

        // Create solver for this verification
        let ctx = self.translator.context();
        let mut solver = Solver::new(ctx);
        
        // Add type constraints first (e.g., u64 >= 0)
        for constraint in &type_constraints {
            solver.assert(constraint);
        }
        
        // For ensures contracts:
        // 1. Add requires constraints (assume preconditions hold)
        // 2. Add implementation formula (translate function body to Z3)
        // 3. Check: requires && implementation => ensures
        //
        // This makes Orange Paper the single source of truth:
        // - Math (ensures contracts) comes from Orange Paper
        // - Implementation must satisfy the math
        if matches!(contract.contract_type, ContractType::Ensures) {
            // Add requires constraints
            for requires_contract in requires_contracts {
                match self.translator.translate_contract_with_types(requires_contract, &param_types, return_type.as_ref()) {
                    Ok((requires_expr, requires_constraints)) => {
                        for constraint in &requires_constraints {
                            solver.assert(constraint);
                        }
                        if let Some(requires_bool) = requires_expr.as_bool() {
                            solver.assert(&requires_bool);
                        }
                    }
                    Err(_) => {}
                }
            }
            
            // KEY: Translate function body to Z3 formula
            // This constrains 'result' to be the actual computed value
            if let Some(func) = func_sig {
                // Create fresh vars map for body translation
                let mut body_vars = std::collections::HashMap::new();
                
                // Initialize parameter variables
                for (name, _ty) in &param_types {
                    let symbol = z3::Symbol::String(name.clone());
                    let var = z3::ast::Int::new_const(ctx, symbol);
                    body_vars.insert(name.clone(), var);
                }
                
                // Initialize result variable
                let result_symbol = z3::Symbol::String("result".to_string());
                let result_var = z3::ast::Int::new_const(ctx, result_symbol);
                body_vars.insert("result".to_string(), result_var);
                
                // Add axioms for uninterpreted functions (shift operations)
                // This allows Z3 to reason about bit shifts mathematically
                add_shift_axioms(ctx, &mut solver);
                
                // Translate function body to Z3 formula
                // This constrains 'result' to match the actual computation
                if let Ok(Some(impl_formula)) = self.translator.translate_function_body(func, &mut body_vars) {
                    solver.assert(&impl_formula);
                }
                // If translation fails, we still verify based on type constraints and requires
                // This allows partial verification for complex functions
            }
        }
        
        // Add negated ensures contract to solver
        // We're checking: requires && implementation && !ensures is UNSAT
        // If UNSAT: requires && implementation => ensures (postcondition holds)
        // If SAT: Found counterexample where implementation doesn't satisfy postcondition
        solver.assert(&negated_bool);

        // Check satisfiability
        match solver.check() {
            SatResult::Unsat => {
                // Negation is unsatisfiable, so property holds
                VerificationResult::Verified
            }
            SatResult::Sat => {
                // Negation is satisfiable, so property fails
                let counterexample = self.extract_counterexample(&solver);
                VerificationResult::Failed {
                    counterexample,
                }
            }
            SatResult::Unknown => {
                VerificationResult::Unknown {
                    reason: "Z3 solver returned Unknown".to_string(),
                }
            }
        }
    }
    
    /// Extract counterexample from Z3 model
    fn extract_counterexample(&self, solver: &Solver<'_>) -> Option<Counterexample> {
        let _model = solver.get_model()?;
        // Model extraction is simplified - would iterate over variables in full impl
        Some(Counterexample {
            assignments: std::collections::HashMap::new(),
        })
    }

    /// Reset the solver (for verifying multiple contracts)
    /// Note: Since we create solvers on-demand, this is a no-op
    pub fn reset(&mut self) {
        // No-op: solvers are created on-demand
    }
}

/// Extract parameter types from function signature
fn extract_parameter_types(func: &syn::ItemFn) -> std::collections::HashMap<String, syn::Type> {
    let mut types = std::collections::HashMap::new();
    for input in &func.sig.inputs {
        if let syn::FnArg::Typed(pat_type) = input {
            if let syn::Pat::Ident(ident) = &*pat_type.pat {
                types.insert(ident.ident.to_string(), *pat_type.ty.clone());
            }
        }
    }
    types
}

/// Extract return type from function signature
fn extract_return_type(func: &syn::ItemFn) -> Option<syn::Type> {
    if let syn::ReturnType::Type(_, ty) = &func.sig.output {
        Some(*ty.clone())
    } else {
        None
    }
}

/// Add axioms for bit shift operations
/// 
/// Since we use uninterpreted functions for shifts (to avoid Real numbers),
/// we need to add axioms that capture the mathematical properties of shifts:
/// 
/// For right shift (>>): 
///   - shr(a, b) >= 0 when a >= 0 (non-negativity preserving)
///   - shr(a, b) <= a when a >= 0 and b >= 0 (monotonically decreasing)
///   - shr(a, 0) == a (identity)
/// 
/// For left shift (<<):
///   - shl(a, b) >= a when a >= 0 and b >= 0 (monotonically increasing)
///   - shl(a, 0) == a (identity)
#[cfg(feature = "z3")]
fn add_shift_axioms(ctx: &Context, solver: &mut Solver) {
    let int_sort = Sort::int(ctx);
    
    // Create bound variables for universal quantification
    let a = Int::new_const(ctx, "axiom_a");
    let b = Int::new_const(ctx, "axiom_b");
    let zero = Int::from_i64(ctx, 0);
    
    // Get the shr function declaration (must match what's used in translator)
    let shr_fn = z3::FuncDecl::new(ctx, "shr", &[&int_sort, &int_sort], &int_sort);
    let shl_fn = z3::FuncDecl::new(ctx, "shl", &[&int_sort, &int_sort], &int_sort);
    
    // Axiom 1: shr(a, b) >= 0 when a >= 0 and b >= 0
    // ∀a,b: (a >= 0 ∧ b >= 0) → shr(a,b) >= 0
    let shr_result = shr_fn.apply(&[&a, &b]);
    let shr_result_int = shr_result.as_int().unwrap();
    let premise1 = Bool::and(ctx, &[&a.ge(&zero), &b.ge(&zero)]);
    let conclusion1 = shr_result_int.ge(&zero);
    let axiom1 = premise1.implies(&conclusion1);
    
    // Use forall quantification
    let bound_a = a.clone();
    let bound_b = b.clone();
    let forall1 = forall_const(ctx, &[&bound_a, &bound_b], &[], &axiom1);
    solver.assert(&forall1);
    
    // Axiom 2: shr(a, b) <= a when a >= 0 and b >= 0
    // ∀a,b: (a >= 0 ∧ b >= 0) → shr(a,b) <= a
    let conclusion2 = shr_result_int.le(&a);
    let axiom2 = premise1.implies(&conclusion2);
    let forall2 = forall_const(ctx, &[&bound_a, &bound_b], &[], &axiom2);
    solver.assert(&forall2);
    
    // Axiom 3: shr(a, 0) == a (identity for shift by 0)
    // ∀a: shr(a, 0) == a
    let shr_by_zero = shr_fn.apply(&[&a, &zero]);
    let shr_by_zero_int = shr_by_zero.as_int().unwrap();
    let axiom3 = shr_by_zero_int._eq(&a);
    let forall3 = forall_const(ctx, &[&bound_a], &[], &axiom3);
    solver.assert(&forall3);
    
    // Axiom 4: shl(a, b) >= a when a >= 0 and b >= 0
    // ∀a,b: (a >= 0 ∧ b >= 0) → shl(a,b) >= a
    let shl_result = shl_fn.apply(&[&a, &b]);
    let shl_result_int = shl_result.as_int().unwrap();
    let conclusion4 = shl_result_int.ge(&a);
    let axiom4 = premise1.implies(&conclusion4);
    let forall4 = forall_const(ctx, &[&bound_a, &bound_b], &[], &axiom4);
    solver.assert(&forall4);
    
    // Axiom 5: shl(a, 0) == a (identity for shift by 0)
    let shl_by_zero = shl_fn.apply(&[&a, &zero]);
    let shl_by_zero_int = shl_by_zero.as_int().unwrap();
    let axiom5 = shl_by_zero_int._eq(&a);
    let forall5 = forall_const(ctx, &[&bound_a], &[], &axiom5);
    solver.assert(&forall5);
}

#[cfg(not(feature = "z3"))]
/// Stub implementation when Z3 feature is disabled
pub struct Z3Verifier;

#[cfg(not(feature = "z3"))]
impl Z3Verifier {
    pub fn new() -> Self {
        Z3Verifier
    }
    
    pub fn verify_contract(&mut self, _contract: &Contract) -> VerificationResult {
        VerificationResult::Error {
            error: "Z3 feature not enabled".to_string(),
        }
    }
}

#[cfg(not(feature = "z3"))]
#[derive(Debug, Clone)]
pub enum VerificationResult {
    Error {
        error: String,
    },
}



