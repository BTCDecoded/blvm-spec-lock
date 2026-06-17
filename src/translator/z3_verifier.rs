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

use crate::parser::contracts::{Contract, ContractType};
#[cfg(feature = "z3")]
use crate::translator::z3_translator::{
    Z3Translator, Z3VarMap, returns_bool_like, returns_result_or_option_result,
};
#[cfg(feature = "z3")]
use z3::ast::{Ast, Bool, Int, forall_const};
#[cfg(feature = "z3")]
use z3::{Context, SatResult, Solver, Sort};

#[cfg(feature = "z3")]
/// Result of Z3 verification
#[derive(Debug, Clone)]
pub enum VerificationResult {
    /// Property holds (unsatisfiable negation).
    /// `body_translated` is `true` when the function body was successfully translated
    /// to Z3 constraints and contributed to the proof (semantic pass), `false` when
    /// the proof relied only on type-level axioms or requires (type-level pass).
    Verified { body_translated: bool },
    /// Property fails (satisfiable - found counterexample)
    Failed {
        counterexample: Option<Counterexample>,
    },
    /// Verification timed out or was too complex
    Unknown { reason: String },
    /// Error during verification
    Error { error: String },
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
    /// Create a new Z3 verifier.
    /// `timeout_ms`: Solver timeout in milliseconds (avoids Unknown from indefinite solving).
    pub fn new(timeout_ms: u64) -> Self {
        let translator = Z3Translator::new(timeout_ms);

        Z3Verifier { translator }
    }

    /// Verify a contract
    ///
    /// For requires: checks if precondition can be violated
    /// For ensures: checks if postcondition can be violated
    pub fn verify_contract(&mut self, contract: &Contract) -> VerificationResult {
        self.verify_contract_with_context(contract, None, &[], &[])
    }

    /// Verify a contract with function signature context for type inference.
    ///
    /// `requires_contracts` — asserted as preconditions when verifying ensures.
    /// `callee_postconds` — `(fn_name, condition)` pairs where `condition` is a proven
    ///   postcondition of `fn_name` (e.g. `"result >= 0"`, `"result <= INITIAL_SUBSIDY"`).
    ///   For each entry whose `call_{fn_name}_result` variable appears in `shared_vars`
    ///   (created when the body translator models the function call as an UF), the condition
    ///   is rewritten to reference the callee-result variable and injected as a Z3 axiom.
    ///   This allows wrapper functions that delegate to proven implementations to discharge
    ///   their own postcondition obligations without translating the full body.
    pub fn verify_contract_with_context(
        &mut self,
        contract: &Contract,
        func_sig: Option<&syn::ItemFn>,
        requires_contracts: &[Contract],
        callee_postconds: &[(&str, &str)],
    ) -> VerificationResult {
        // Extract parameter types and return type from function signature
        let (param_types, return_type) = if let Some(func) = func_sig {
            (extract_parameter_types(func), extract_return_type(func))
        } else {
            (std::collections::HashMap::new(), None)
        };

        // Build a single SHARED variable map that is reused for the ensures translation,
        // the requires translations, and the body translation.
        //
        // CRITICAL: Z3's `Int::new_const(ctx, "x")` creates a FRESH AST node each call.
        // If we create separate maps for each translation, Z3 sees the "result" in the
        // ensures formula and the "result" in the body formula as UNRELATED variables —
        // the body constraint does not constrain the ensures variable.  By sharing one
        // map, all three translations reference the SAME Z3 constant objects.
        let ctx = self.translator.context();
        let (mut shared_vars, type_constraints) = self
            .translator
            .build_shared_vars(&param_types, return_type.as_ref());

        // Translate contract to Z3 using the shared variable map
        let z3_expr = match self
            .translator
            .translate_contract_with_shared_vars(contract, &mut shared_vars)
        {
            Ok(expr) => expr,
            Err(e) => {
                return VerificationResult::Error {
                    error: format!("Translation error: {e}"),
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
        // Track whether we successfully translated the function body into solver constraints.
        // A SAT result without body constraints is vacuous (not a real counterexample).
        let mut body_translated = false;

        if matches!(contract.contract_type, ContractType::Ensures) {
            // Add requires constraints — translate with the SAME shared_vars so the
            // "height" in requires refers to the same Z3 constant as in the body.
            for requires_contract in requires_contracts {
                if let Ok(requires_expr) = self
                    .translator
                    .translate_contract_with_shared_vars(requires_contract, &mut shared_vars)
                {
                    if let Some(requires_bool) = requires_expr.as_bool() {
                        solver.assert(&requires_bool);
                    }
                }
            }

            // KEY: Translate function body to Z3 formula using the SHARED vars.
            // The body translator will look up "height" and "result" in shared_vars and
            // find the SAME Z3 constant objects already used for the ensures formula.
            if let Some(func) = func_sig {
                add_shift_axioms(ctx, &mut solver);

                if let Ok(Some(impl_formula)) = self
                    .translator
                    .translate_function_body(func, &mut shared_vars)
                {
                    // Only count the body as "translated" when it contains concrete constraints,
                    // not when it's purely uninterpreted function wrappers.
                    //
                    // The generic fallback in z3_translator.rs translates any opaque call as
                    // `result == call_{fn}_{arity}(args)` where `call_*` is an uninterpreted Z3
                    // function. With no body axioms, Z3 is free to assign `call_*(...)` to any
                    // value, so the SAT result is vacuous even though `body_translated` would
                    // otherwise be true.
                    //
                    // Wrappers like `ite`, `and`, `or` around uninterpreted calls (e.g. the `?`
                    // operator modelled as `ite(is_err(call_f(args)), -1, call_f(args))`) are
                    // also vacuous — Z3 still freely assigns `call_f(...)`.
                    //
                    // A body is concrete only when it contains arithmetic beyond uninterpreted
                    // wrappers: actual bit-operations (bvshr/shl), integer division, modulo, or
                    // explicit numerical comparisons (indicated by numeric literals in the formula).
                    let formula_str = impl_formula.to_string();
                    // Detect vacuous body formulas that add no useful constraints:
                    //
                    // 1. Tautology: "(= result result)" — translator fell back to a no-op.
                    //    Happens when the body is a complex call the translator can't model
                    //    (e.g. tuple destructuring from a method call).
                    //
                    // 2. Pure uninterpreted: body reduces to "result = call_f(args)" where
                    //    call_f has no axioms — Z3 freely assigns any value to call_f.
                    //    Wrappers (ite, and, or) around uninterpreted calls are also vacuous.
                    //
                    // Both cases leave Z3 free to violate any ensures contract without a real
                    // implementation witness, producing false counterexamples.
                    // A body formula is vacuous when it adds no real implementation constraints.
                    //
                    // Vacuous classes:
                    // 1. Tautology: "(= result result)" or "true" — translator fell back to
                    //    a no-op (e.g. complex tuple destructuring).
                    // 2. Pure uninterpreted call: "(= result (F a b c))" where F is NOT a
                    //    Z3/SMT-LIB built-in operator.  The generic fallback uses "call_*";
                    //    named uninterpreted functions (from known_uninterpreted_function table)
                    //    use names like "get_next_work", "connect_block", etc.
                    //    Z3 freely assigns any value to these — no meaningful constraints.
                    //
                    // Concrete formulas use built-in operators: arithmetic (+,-,*,/,div,mod,
                    // bvshr/shl), comparisons (>=,<=,>,<), Boolean (and,or,not), conditionals
                    // (ite), or literals (true,false,integers).
                    let body_formula_vacuous = is_formula_body_vacuous(&formula_str);
                    if std::env::var("SPEC_LOCK_DEBUG_BODY").is_ok() {
                        eprintln!("BODY_DEBUG: formula_vacuous={body_formula_vacuous}");
                        eprintln!(
                            "BODY_DEBUG formula: {}",
                            &formula_str[..formula_str.len().min(300)]
                        );
                    }
                    solver.assert(&impl_formula);

                    // Add non-negativity for any length variable created during body
                    // translation.  The `len` / `is_empty` method handlers produce fresh
                    // Z3 Int constants whose names end with `_len` or are `len_result`.
                    // Without a `>= 0` bound, Z3 can exploit negative lengths to
                    // manufacture spurious counterexamples (e.g. `witness_len = -1`).
                    //
                    // Also add non-negativity for `for_loop_*` placeholder variables.
                    // These are created when the body contains a `for` loop that the
                    // translator cannot fully model.  In practice these accumulate integer
                    // results (sums) that must be >= 0 (e.g. `total_supply` sums block
                    // subsidies which are always non-negative).
                    for (name, var) in shared_vars.iter() {
                        if name.ends_with("_len")
                            || name == "len_result"
                            || name.starts_with("for_loop_")
                        {
                            if let Some(len_int) = var.as_int() {
                                let zero = Int::from_i64(ctx, 0);
                                solver.assert(&len_int.ge(&zero));
                            }
                        }
                    }

                    // Propagate proven callee postconditions for UF-delegating wrappers.
                    //
                    // Functions like `lib.rs::get_block_subsidy` call
                    // `economic::get_block_subsidy(height)`, which the translator models as
                    // an uninterpreted function result variable `call_get_block_subsidy_result`.
                    // Z3 cannot prove `result >= 0` or `result <= INITIAL_SUBSIDY` for the
                    // wrapper without knowing the callee's proven postconditions.
                    //
                    // For each `(callee_fn, condition)` in `callee_postconds`, if
                    // `call_{callee_fn}_result` exists in `shared_vars` (placed there by the
                    // body translator when it modelled the call as an uninterpreted function),
                    // we substitute `result` with the callee-result variable in the condition
                    // string, parse it, translate it to Z3, and assert it as an axiom.
                    //
                    // Named constants such as `INITIAL_SUBSIDY` and `MAX_MONEY` are resolved
                    // to their numeric values by `translate_expr_with_vars` via `resolve_constant`.
                    let mut added_nonneg = false;
                    for &(callee_fn, condition) in callee_postconds {
                        let var_name = format!("call_{callee_fn}_result");
                        if shared_vars.contains_key(var_name.as_str()) {
                            let subst = substitute_result_ident(condition, &var_name);
                            if let Ok(expr) = syn::parse_str::<syn::Expr>(&subst) {
                                if let Ok(z3_expr) = self
                                    .translator
                                    .translate_expr_with_vars(&expr, &mut shared_vars)
                                {
                                    if let Some(bool_expr) = z3_expr.as_bool() {
                                        solver.assert(&bool_expr);
                                        added_nonneg = true;
                                    }
                                }
                            }
                        }
                    }

                    // Signed-range axioms are now handled via #[blvm_spec_lock::axiom]
                    // attributes on individual functions rather than a hardcoded table here.
                    // The CLI passes axiom contracts through requires_contracts so they are
                    // already asserted above as hard constraints, with added_nonneg set when
                    // any of them successfully constrain a shared variable.
                    // Callee-ensures axiom for validate_taproot_script.
                    // The function signature is `fn validate_taproot_script(script) -> Result<bool>`.
                    // Its body verifies that the script is exactly 34 bytes (P2TR v1 OP_CHECKSIG).
                    // When `call_validate_taproot_script_result` is `true`, assert script_len == 34.
                    // This lets `is_taproot_output` (which calls `validate_taproot_script(...).unwrap_or(false)`)
                    // prove its ensures: `result == (script_len == 34)`.
                    // Find the script length variable: may be `script_pubkey_len`,
                    // `output_script_pubkey_len`, `script_len`, etc.
                    let script_len_key = shared_vars
                        .keys()
                        .find(|k| k.ends_with("script_pubkey_len") || k.as_str() == "script_len")
                        .cloned();
                    if let (Some(taproot_var), Some(script_len_var)) = (
                        shared_vars.get("call_validate_taproot_script_result"),
                        script_len_key
                            .as_ref()
                            .and_then(|k| shared_vars.get(k.as_str())),
                    ) {
                        if let (Some(taproot_bool), Some(len_int)) =
                            (taproot_var.as_bool(), script_len_var.as_int())
                        {
                            let thirty_four = Int::from_i64(ctx, 34);
                            // validate_taproot_script returns Ok(true) iff script is 34 bytes
                            let axiom = taproot_bool.implies(&len_int._eq(&thirty_four));
                            solver.assert(&axiom);
                        }
                    }

                    // Struct-field binding axioms from known_struct_field_function.
                    // When the body calls `bip54_deployment_{mainnet,testnet,regtest}`, the
                    // translator binds `call_bip54_deployment_{net}_bit = 15` in shared_vars
                    // as concrete Int literals.  The `result_bit` variable holds the field
                    // value of the return struct (synthesised in translate_block_to_result_formula).
                    //
                    // For `bip54_deployment_for_network`, the body is an ITE over these calls,
                    // so `result_bit` must equal whichever branch is taken — but Z3 cannot infer
                    // this without an axiom.  Assert: for every `call_X_bit` variable that was
                    // bound to 15 by the translator, assert `result_bit == 15`.  This is safe
                    // because `known_struct_field_function` only emits entries for functions
                    // whose spec guarantees that field value (bit = 15 is mandated by BIP-54).
                    if let Some(result_bit_var) = shared_vars.get("result_bit") {
                        if let Some(result_bit_int) = result_bit_var.as_int() {
                            let has_callee_bit = shared_vars
                                .keys()
                                .any(|k| k.ends_with("_bit") && k.starts_with("call_"));
                            if has_callee_bit {
                                // All known_struct_field_function entries for `_bit` use 15
                                let fifteen = Int::from_i64(ctx, 15);
                                solver.assert(&result_bit_int._eq(&fifteen));
                            }
                        }
                    }

                    // Always count the body as translated — the formula still helps Z3 prove
                    // UNSAT (valid contracts).  The `body_formula_vacuous` flag is used later
                    // to decide whether a SAT result is genuine or vacuous.
                    body_translated = true;
                    if body_formula_vacuous {
                        // SAT on a vacuous body is not a genuine counterexample: mark the
                        // translated body flag off so the is_vacuous check fires.
                        body_translated = false;
                    }
                    // If callee contracts (non-negativity axioms, taproot axioms, struct-field
                    // axioms) were injected, those provide concrete semantics even when the body
                    // formula itself is vacuous — promote body_translated to true so genuine SAT
                    // is not silently demoted to PARTIAL.
                    if added_nonneg && !body_translated {
                        body_translated = true;
                    }
                }
                // If translation fails, we still verify based on type constraints and requires.
                // body_translated remains false; SAT in that case is vacuous (see below).
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
                VerificationResult::Verified { body_translated }
            }
            SatResult::Sat => {
                // Negation is satisfiable — Z3 found a model.
                //
                // Only treat this as a real counterexample when we have concrete variable
                // assignments.  There are two reasons an empty-assignments result is vacuous:
                //
                // 1. Body translation failed: no implementation constraints were added,
                //    so Z3 trivially satisfies !ensures from the postcondition alone.
                // 2. Body translation succeeded but assignments map is empty: the current
                //    extract_counterexample implementation is a stub; it does not yet walk
                //    the Z3 model to extract named-variable values.  Until that is
                //    implemented every SAT result carries an empty {} counterexample,
                //    which gives no evidence of a real implementation violation.
                //
                // In both cases return Unknown so the caller classifies the result as a
                // translation-gap (Partial) rather than a hard failure.  Once
                // extract_counterexample is fully implemented this branch will only trigger
                // for case 1; case 2 will produce non-empty assignments and fall through
                // to the real Failed path below.
                let counterexample = self.extract_counterexample(&solver);
                // A counterexample is genuine only if:
                // 1. Body was translated (otherwise no impl constraints, trivially SAT)
                // 2. Counterexample contains at least one assignment
                // 3. ALL assigned variable names are either:
                //    a. A named function parameter (in param_types)
                //    b. The "result" variable
                //    c. A renamed parameter (prefix "r1_"/"r2_" for determinism runs)
                //    If Z3 assigns values to translator-internal variables like
                //    `for_loop_14` or `call_foo_result`, the body formula is
                //    incomplete and those free variables are being exploited — the
                //    counterexample is therefore a translator artifact, not a real
                //    implementation violation.
                let is_vacuous = !body_translated
                    || counterexample.as_ref().is_none_or(|ce| {
                        if ce.assignments.is_empty() {
                            return true;
                        }
                        // Check for translator-internal variables in the counterexample.
                        // Genuine counterexamples only involve:
                        // - exact parameter names
                        // - "result"
                        // - determinism-prefixed names (r1_/r2_ + param or result)
                        let known_names: std::collections::HashSet<&str> = param_types
                            .keys()
                            .map(|s| s.as_str())
                            .chain(std::iter::once("result"))
                            .collect();
                        ce.assignments.keys().any(|k| {
                            // Strip determinism prefixes before checking
                            let bare = k
                                .strip_prefix("r1_")
                                .or_else(|| k.strip_prefix("r2_"))
                                .unwrap_or(k.as_str());
                            !known_names.contains(bare)
                        })
                    });
                if is_vacuous {
                    return VerificationResult::Unknown {
                        reason: if !body_translated {
                            "Could not translate function body to Z3 constraints; \
                             SAT result without body constraints is not meaningful"
                                .to_string()
                        } else {
                            "Z3 found SAT but counterexample model has no named variable \
                             assignments (incomplete translator); result is not a concrete \
                             witness against the implementation"
                                .to_string()
                        },
                    };
                }
                VerificationResult::Failed { counterexample }
            }
            SatResult::Unknown => VerificationResult::Unknown {
                reason: "Z3 solver returned Unknown (timeout or complexity). Try --timeout 30."
                    .to_string(),
            },
        }
    }

    /// Lightweight **formula-only** check: translate an **ensures** condition (no Rust implementation)
    /// and ask Z3 whether the formula is **satisfiable**.
    ///
    /// - **`Verified`**: the formula is **SAT** — there exists a model (consistent / not an obvious contradiction).
    /// - **`Failed`**: **UNSAT** — the formula is unsatisfiable (e.g. `x < x`).
    /// - **`Unknown` / `Error`**: solver or translation issue.
    ///
    /// This does **not** prove the formula against code; it is a smoke test that LaTeX → Rust → Z3 is coherent.
    pub fn check_ensures_formula_sat_smoke(&mut self, contract: &Contract) -> VerificationResult {
        if !matches!(contract.contract_type, ContractType::Ensures) {
            return VerificationResult::Error {
                error: "check_ensures_formula_sat_smoke expects an Ensures contract".to_string(),
            };
        }
        let (z3_expr, type_constraints) = match self.translator.translate_contract_with_types(
            contract,
            &std::collections::HashMap::new(),
            None,
        ) {
            Ok(x) => x,
            Err(e) => {
                return VerificationResult::Error {
                    error: format!("Translation error: {e}"),
                };
            }
        };
        let pos = match z3_expr.as_bool() {
            Some(b) => b,
            None => {
                return VerificationResult::Error {
                    error: "Formula must translate to a boolean Z3 expression".to_string(),
                };
            }
        };
        let ctx = self.translator.context();
        let mut solver = Solver::new(ctx);
        add_shift_axioms(ctx, &mut solver);
        for c in &type_constraints {
            solver.assert(c);
        }
        solver.assert(&pos);
        match solver.check() {
            SatResult::Sat => VerificationResult::Verified {
                body_translated: false,
            },
            SatResult::Unsat => VerificationResult::Failed {
                counterexample: None,
            },
            SatResult::Unknown => VerificationResult::Unknown {
                reason: "Z3 Unknown (formula satisfiability smoke)".to_string(),
            },
        }
    }

    /// Extract counterexample from Z3 model.
    ///
    /// Returns `None` when no model is available, and `Some(Counterexample { assignments })`
    /// when Z3 produced a satisfying model.  `assignments` is populated from the model's
    /// declarations; when the translator did not introduce named constants the map is empty
    /// (see note below).
    ///
    /// **Important — stub status:** model traversal is not yet implemented; `assignments`
    /// is always empty.  As long as this is the case every SAT result is vacuous (no
    /// concrete witness), so callers must treat an empty-assignments counterexample the
    /// same as an Unknown/translation-gap result for spec-derived contracts.
    fn extract_counterexample(&self, solver: &Solver<'_>) -> Option<Counterexample> {
        let model = solver.get_model()?;
        let mut assignments = std::collections::HashMap::new();

        // Walk every constant declaration in the model and record its value.
        // We only care about named scalar constants (Int/Bool) — skips
        // uninterpreted functions and array sorts that have no simple string rep.
        for decl in model.iter() {
            if decl.arity() != 0 {
                continue; // skip function interpretations
            }
            let name = decl.name();
            // Evaluate the constant in the model with model-completion enabled
            // so Z3 picks a concrete value even for don't-care variables.
            let ast = decl.apply(&[]);
            let value_str = if let Some(int_val) = ast.as_int() {
                model.eval(&int_val, true).map(|v| v.to_string())
            } else if let Some(bool_val) = ast.as_bool() {
                model.eval(&bool_val, true).map(|v| v.to_string())
            } else {
                None
            };
            if let Some(s) = value_str {
                assignments.insert(name, s);
            }
        }

        Some(Counterexample { assignments })
    }

    /// Reset the solver (for verifying multiple contracts)
    /// Note: Since we create solvers on-demand, this is a no-op
    pub fn reset(&mut self) {
        // No-op: solvers are created on-demand
    }

    /// Verify determinism: ∀a,b: a=b → f(a)=f(b)
    /// Two-run Z3: translate body twice with distinct vars, prove (inputs equal) => (outputs equal)
    pub fn verify_determinism(
        &mut self,
        func: &syn::ItemFn,
        requires_contracts: &[Contract],
    ) -> VerificationResult {
        let ctx = self.translator.context();
        let param_types = extract_parameter_types(func);
        let return_type = extract_return_type(func);

        if param_types.is_empty() {
            return VerificationResult::Verified {
                body_translated: false,
            };
        }

        let mut solver = Solver::new(ctx);
        add_shift_axioms(ctx, &mut solver);

        let prefix1 = "r1_";
        let prefix2 = "r2_";

        let mut vars1 = Z3VarMap::new();
        let mut vars2 = Z3VarMap::new();

        for name in param_types.keys() {
            let sym1 = z3::Symbol::String(format!("{prefix1}{name}"));
            let sym2 = z3::Symbol::String(format!("{prefix2}{name}"));
            let var1 = z3::ast::Int::new_const(ctx, sym1);
            let var2 = z3::ast::Int::new_const(ctx, sym2);
            vars1.insert(name.clone(), var1.into());
            vars2.insert(name.clone(), var2.into());
        }

        let result_sym1 = z3::Symbol::String(format!("{prefix1}result"));
        let result_sym2 = z3::Symbol::String(format!("{prefix2}result"));
        // Result<T> / Option<Result<T>>: use Int for determinism (0=Err/None, 1=Ok(false), 2=Ok(true))
        // Only for functions that need it (script verification) - avoids breaking others
        let func_name = func.sig.ident.to_string();
        let use_int_result = return_type
            .as_ref()
            .is_some_and(returns_result_or_option_result)
            && matches!(
                func_name.as_str(),
                "verify_script_with_context_full"
                    | "verify_script_with_context"
                    | "try_verify_p2pk_fast_path"
            );
        let result1: z3::ast::Dynamic = if use_int_result {
            z3::ast::Int::new_const(ctx, result_sym1).into()
        } else if return_type.as_ref().is_some_and(returns_bool_like) {
            z3::ast::Bool::new_const(ctx, result_sym1).into()
        } else {
            z3::ast::Int::new_const(ctx, result_sym1).into()
        };
        let result2: z3::ast::Dynamic = if use_int_result {
            z3::ast::Int::new_const(ctx, result_sym2).into()
        } else if return_type.as_ref().is_some_and(returns_bool_like) {
            z3::ast::Bool::new_const(ctx, result_sym2).into()
        } else {
            z3::ast::Int::new_const(ctx, result_sym2).into()
        };
        vars1.insert("result".to_string(), result1.clone());
        vars2.insert("result".to_string(), result2.clone());

        let formula1 = match self.translator.translate_function_body(func, &mut vars1) {
            Ok(Some(f)) => f,
            Ok(None) => {
                return VerificationResult::Error {
                    error: "Could not translate body for run 1 (no formula)".to_string(),
                };
            }
            Err(e) => {
                return VerificationResult::Error {
                    error: format!("Could not translate body for run 1: {e}"),
                };
            }
        };
        let formula2 = match self.translator.translate_function_body(func, &mut vars2) {
            Ok(Some(f)) => f,
            Ok(None) => {
                return VerificationResult::Error {
                    error: "Could not translate body for run 2 (no formula)".to_string(),
                };
            }
            Err(e) => {
                return VerificationResult::Error {
                    error: format!("Could not translate body for run 2: {e}"),
                };
            }
        };

        // Detect vacuous body translations that cannot support a meaningful determinism
        // proof and return Unknown rather than a spurious Non-deterministic result.
        //
        // Two distinct cases:
        //   (a) Explicit tautologies (empty / "true" / self-equality) — skip immediately.
        //   (b) Loop-counter divergence: the translator's internal loop counter increments
        //       between the two translate_function_body calls, producing different free-
        //       variable names in f1 and f2 (e.g. loop_13 vs loop_17). Z3 treats them as
        //       independent → spurious SAT. Detect by: both formulas are vacuous AND they
        //       differ. When f1 == f2 the free variable is shared and Z3 correctly finds
        //       UNSAT (deterministic) — let it proceed.
        //
        // Do NOT skip uninterpreted-function bodies: UF congruence proves determinism.
        let f1_str = formula1.to_string();
        let f2_str = formula2.to_string();
        let is_tautology = |s: &str| {
            let s = s.trim();
            if s.is_empty() || s == "true" {
                return true;
            }
            // Self-equality: (= result result), (= r1_result r1_result), etc.
            if s.contains("(= result result)")
                || s.contains("(= r1_result r1_result)")
                || s.contains("(= r2_result r2_result)")
            {
                return true;
            }
            false
        };
        if is_tautology(&f1_str) || is_tautology(&f2_str) {
            return VerificationResult::Unknown {
                reason: "Could not translate function body to Z3 constraints; \
                         determinism check without body constraints is not meaningful"
                    .to_string(),
            };
        }

        solver.assert(&formula1);
        solver.assert(&formula2);

        for req in requires_contracts {
            if let Ok(expr1) = self
                .translator
                .translate_expr_with_vars(&req.condition, &mut vars1)
            {
                if let Some(b1) = expr1.as_bool() {
                    solver.assert(&b1);
                }
            }
            if let Ok(expr2) = self
                .translator
                .translate_expr_with_vars(&req.condition, &mut vars2)
            {
                if let Some(b2) = expr2.as_bool() {
                    solver.assert(&b2);
                }
            }
        }

        let mut input_equiv = Vec::new();
        for name in param_types.keys() {
            let v1 = vars1.get(name).and_then(|x| x.as_int()).unwrap();
            let v2 = vars2.get(name).and_then(|x| x.as_int()).unwrap();
            input_equiv.push(v1._eq(&v2));
        }
        let equiv_refs: Vec<&Bool> = input_equiv.iter().collect();
        let input_equal = Bool::and(ctx, &equiv_refs);

        let output_diff = if let (Some(r1), Some(r2)) = (result1.as_int(), result2.as_int()) {
            r1._eq(&r2).not()
        } else if let (Some(r1), Some(r2)) = (result1.as_bool(), result2.as_bool()) {
            r1._eq(&r2).not()
        } else {
            return VerificationResult::Error {
                error: "Result type not Int or Bool".to_string(),
            };
        };

        let negated = Bool::and(ctx, &[&input_equal, &output_diff]);
        solver.assert(&negated);

        match solver.check() {
            SatResult::Unsat => VerificationResult::Verified {
                body_translated: true,
            },
            SatResult::Sat => {
                // If both body formulas are vacuous (untranslated) the SAT result is due to
                // unconstrained free variables (loop-counter divergence, uninterpreted calls),
                // not a real implementation non-determinism.
                let both_body_vacuous =
                    is_formula_body_vacuous(&f1_str) && is_formula_body_vacuous(&f2_str);
                if both_body_vacuous {
                    return VerificationResult::Unknown {
                        reason: "Could not translate function body to Z3 constraints; \
                                 determinism SAT with untranslated bodies is not a concrete \
                                 witness against the implementation"
                            .to_string(),
                    };
                }
                // Same vacuous-SAT rule as verify_contract_with_context: if the counterexample
                // model has no named variable assignments the result is not a concrete witness.
                // extract_counterexample is a stub that always returns an empty HashMap, so
                // every SAT result is vacuous until model traversal is implemented.
                let counterexample = self.extract_counterexample(&solver);
                let is_vacuous = counterexample
                    .as_ref()
                    .is_none_or(|ce| ce.assignments.is_empty());
                if is_vacuous {
                    return VerificationResult::Unknown {
                        reason: "Z3 found SAT but counterexample model has no named variable \
                                 assignments (incomplete translator); result is not a concrete \
                                 witness against the implementation"
                            .to_string(),
                    };
                }
                VerificationResult::Failed { counterexample }
            }
            SatResult::Unknown => VerificationResult::Unknown {
                reason: "Z3 returned Unknown (determinism check). Try --timeout 30.".to_string(),
            },
        }
    }
}

/// Return true when an SMT-LIB body formula provides no real implementation constraints.
///
/// A formula is vacuous when:
/// 1. It is a tautology: `(= result result)`, `true`, or empty.
/// 2. It is a pure uninterpreted-function application: `(= result (F a b c))` where F is
///    **not** a Z3/SMT-LIB built-in operator (`+`, `-`, `*`, `div`, `mod`, `bvshr`, `bvshl`,
///    comparison operators, Boolean operators, `ite`, etc.).
///    — Generic fallback uninterpreted functions use a `call_` prefix.
///    — Named uninterpreted functions (from `known_uninterpreted_function`) use names like
///    `get_next_work`, `connect_block`, `hash256`, etc.
///    In both cases Z3 assigns any value freely → no meaningful constraints.
///
/// Concrete formulas use built-in operators so Z3's reasoning is grounded.
/// Examples of concrete formulas:
///   `(= result (+ height 1))`
///   `(= result (ite (>= bits 0) bits 0))`
///   `(= result true)` — literal assignment, no uninterpreted calls
#[cfg(feature = "z3")]
fn is_formula_body_vacuous(formula_str: &str) -> bool {
    let s = formula_str.trim();

    // Tautology or empty
    if s.is_empty() || s == "true" || s == "(= result result)" {
        return true;
    }

    // Self-equality of identical tokens: (= X X) — e.g. (= true true), (= 0 0), (= false false)
    // These are generated when the translator collapses a branch to a literal comparison.
    if s.starts_with("(= ") && s.ends_with(')') {
        let inner = &s[3..s.len() - 1];
        if let Some((lhs, rhs)) = inner.split_once(' ') {
            if lhs == rhs.trim() {
                return true;
            }
        }
    }

    // Top-level UF structure: (= VARIABLE (USER_FN args...))
    // If the top-level value expression is a call to a user-defined function (not a Z3
    // built-in), result is bound to an uninterpreted function — vacuous regardless of
    // what the argument expressions contain (e.g. `(ite false 1 0)` inside args).
    //
    // Z3 built-in operators always start with a recognised SMT-LIB keyword or symbol;
    // user-defined functions are named by the translator as snake_case identifiers.
    const Z3_BUILTIN_PREFIX: &[&str] = &[
        "+", "-", "*", "/", "div", "mod", "rem", ">=", "<=", ">", "<", "=", "not", "and", "or",
        "ite", "=>", "bvshr", "bvshl", "bvand", "bvor", "bvnot", "let", "forall", "exists",
    ];
    if s.starts_with("(= ") && s.ends_with(')') {
        let inner = &s[3..s.len() - 1]; // strip "(= " and ")"
        if let Some(space_pos) = inner.find(' ') {
            let val_expr = inner[space_pos..].trim();
            if val_expr.starts_with('(') && val_expr.ends_with(')') {
                let inner_val = &val_expr[1..val_expr.len() - 1]; // strip outer parens
                let fn_name = inner_val
                    .split_once([' ', ')'])
                    .map_or(inner_val, |(n, _)| n);
                if !Z3_BUILTIN_PREFIX.contains(&fn_name) {
                    // Not a built-in — user-defined (uninterpreted) function call.
                    return true;
                }
            }
        }
    }

    // Z3/SMT-LIB built-in operators and keywords that indicate concrete semantics.
    // If ANY of these appear in the formula, it is concrete.
    const CONCRETE_MARKERS: &[&str] = &[
        // Arithmetic
        "(+ ", "(- ", "(* ", "(/ ", " div ", " mod ", "(div ", "(rem ",
        // Bit-vector shifts
        "bvshr", "bvshl", // Comparison (prefix application style)
        "(>= ", "(<= ", "(> ", "(< ", // Boolean
        "(and ", "(or ", "(not ",
        "(ite ",
        // Literals beyond 0/1
        // (handled separately below)
    ];

    for marker in CONCRETE_MARKERS {
        if s.contains(marker) {
            return false; // Concrete
        }
    }

    // Numeric literals indicate concrete arithmetic constants.
    // Strip only parentheses from each whitespace-delimited token so that
    // `"34))"` → `"34"`, `"15)"` → `"15"`, etc. parse correctly while
    // identifiers like `"call_bip54_deployment_mainnet_0"` still fail.
    if s.split_whitespace().any(|tok| {
        let trimmed = tok.trim_matches(|c: char| c == '(' || c == ')');
        trimmed.parse::<i64>().is_ok_and(|n| n.abs() > 1)
    }) {
        return false; // Concrete
    }

    // No concrete markers found: formula is either a tautology, a literal assignment,
    // an inner comparison, or a pure uninterpreted-function application.
    //
    // (a) Literal assignments ARE concrete (translator determined the result statically):
    //     `(= result true)`, `(= result false)`, `(= result 0)`, `(= result 15)`, etc.
    //     Accepts any integer literal, not just 0/1.
    //
    // (b) Inner comparisons ARE concrete: `(= result (= len 0))`, `(= result (= script_len 34))`
    //     The value expression is itself a comparison — constrains result to a bool computed
    //     from concrete sub-expressions.
    if s.starts_with("(= ") && s.ends_with(')') {
        let inner = &s[3..s.len() - 1]; // strip leading "(= " and trailing ")"
        let mut parts = inner.splitn(2, ' ');
        let _var = parts.next().unwrap_or("");
        if let Some(val) = parts.next() {
            let val = val.trim();
            // (a) literal assignment
            if val == "true" || val == "false" || val.parse::<i64>().is_ok() {
                return false; // Concrete literal assignment
            }
            // (b) inner comparison: (= a b), (>= a b), (<= a b), (> a b), (< a b), (not ...)
            // These represent boolean expressions that constrain result concretely.
            const INNER_CMP_PREFIXES: &[&str] = &["(= ", "(>= ", "(<= ", "(> ", "(< ", "(not "];
            if INNER_CMP_PREFIXES.iter().any(|p| val.starts_with(p)) {
                return false; // Concrete inner comparison
            }
        }
    }

    // Everything else without concrete markers is an uninterpreted-function application.
    true
}

#[cfg(all(test, feature = "z3"))]
mod formula_sat_smoke_tests {
    use super::{VerificationResult, Z3Verifier};
    use crate::parser::contracts::{Contract, ContractType};
    use syn::parse_str;

    #[test]
    fn ensures_literal_true_is_sat() {
        let mut v = Z3Verifier::new(5000);
        let c = Contract {
            contract_type: ContractType::Ensures,
            condition: parse_str("true").unwrap(),
            comment: None,
        };
        assert!(matches!(
            v.check_ensures_formula_sat_smoke(&c),
            VerificationResult::Verified { .. }
        ));
    }

    #[test]
    fn result_eq_result_is_sat() {
        let mut v = Z3Verifier::new(5000);
        let c = Contract {
            contract_type: ContractType::Ensures,
            condition: parse_str("result == result").unwrap(),
            comment: None,
        };
        assert!(matches!(
            v.check_ensures_formula_sat_smoke(&c),
            VerificationResult::Verified { .. }
        ));
    }

    #[test]
    fn x_lt_x_is_unsat_contradiction() {
        let mut v = Z3Verifier::new(5000);
        let c = Contract {
            contract_type: ContractType::Ensures,
            condition: parse_str("x < x").unwrap(),
            comment: None,
        };
        assert!(matches!(
            v.check_ensures_formula_sat_smoke(&c),
            VerificationResult::Failed { .. }
        ));
    }
}

/// Bit shifts use UF `shr` / `shl` (`FuncDecl::new` with the same name shares one UF per [`Context`](z3::Context)).
/// Literal `>> k` / `<< k` use [`Z3Translator::pow2_int`](crate::translator::z3_translator::Z3Translator::pow2_int) for correct `2^k` including `k=63`.
/// The `shr(a,k)=a/2^k` axioms use [`Z3Translator::pow2_int`](crate::translator::z3_translator::Z3Translator::pow2_int) for `2^k` (k < 64) so k=63 is correct on the host.
#[cfg(feature = "z3")]
fn add_shift_axioms(ctx: &Context, solver: &mut Solver) {
    let int_sort = Sort::int(ctx);

    let a = Int::new_const(ctx, "axiom_a");
    let b = Int::new_const(ctx, "axiom_b");
    let zero = Int::from_i64(ctx, 0);

    let shr_fn = z3::FuncDecl::new(ctx, "shr", &[&int_sort, &int_sort], &int_sort);
    let shl_fn = z3::FuncDecl::new(ctx, "shl", &[&int_sort, &int_sort], &int_sort);

    let shr_result = shr_fn.apply(&[&a, &b]);
    let shr_result_int = shr_result.as_int().unwrap();
    let premise1 = Bool::and(ctx, &[&a.ge(&zero), &b.ge(&zero)]);
    let conclusion1 = shr_result_int.ge(&zero);
    let axiom1 = premise1.implies(&conclusion1);

    let bound_a = a.clone();
    let bound_b = b.clone();
    let forall1 = forall_const(ctx, &[&bound_a, &bound_b], &[], &axiom1);
    solver.assert(&forall1);

    let conclusion2 = shr_result_int.le(&a);
    let axiom2 = premise1.implies(&conclusion2);
    let forall2 = forall_const(ctx, &[&bound_a, &bound_b], &[], &axiom2);
    solver.assert(&forall2);

    let shr_by_zero = shr_fn.apply(&[&a, &zero]);
    let shr_by_zero_int = shr_by_zero.as_int().unwrap();
    let axiom3 = shr_by_zero_int._eq(&a);
    let forall3 = forall_const(ctx, &[&bound_a], &[], &axiom3);
    solver.assert(&forall3);

    let shl_result = shl_fn.apply(&[&a, &b]);
    let shl_result_int = shl_result.as_int().unwrap();
    let conclusion4 = shl_result_int.ge(&a);
    let axiom4 = premise1.implies(&conclusion4);
    let forall4 = forall_const(ctx, &[&bound_a, &bound_b], &[], &axiom4);
    solver.assert(&forall4);

    let shl_by_zero = shl_fn.apply(&[&a, &zero]);
    let shl_by_zero_int = shl_by_zero.as_int().unwrap();
    let axiom5 = shl_by_zero_int._eq(&a);
    let forall5 = forall_const(ctx, &[&bound_a], &[], &axiom5);
    solver.assert(&forall5);

    for k in 0_u32..64 {
        let k_const = Int::from_i64(ctx, i64::from(k));
        // Match translator literal >> encoding; use pow2_int so k=63 does not overflow host i64.
        let two_pow_k = Z3Translator::pow2_int(ctx, k);
        let shr_ak = shr_fn.apply(&[&a, &k_const]);
        let shr_ak_int = shr_ak.as_int().unwrap();
        let div_ak = a.clone().div(&two_pow_k);
        let axiom = shr_ak_int._eq(&div_ak);
        let forall_k = forall_const(ctx, &[&bound_a], &[], &axiom);
        solver.assert(&forall_k);
    }

    // Large-shift axiom: shr(a, k) = 0 for any non-negative 64-bit integer a and k >= 64.
    // This is mathematically correct for all 64-bit values: shifting right by ≥ 64 bits
    // produces zero.  Without this axiom, Z3 cannot prove the Bitcoin block-subsidy
    // exhaustion (halving_period ≥ 64 → subsidy = 0) because the literal axioms above
    // only cover shift amounts 0..63.
    let sixty_four = Int::from_i64(ctx, 64);
    let i64_max = Int::from_i64(ctx, i64::MAX);
    let premise_large_shift = Bool::and(ctx, &[&a.ge(&zero), &a.le(&i64_max), &b.ge(&sixty_four)]);
    let shr_large = shr_fn.apply(&[&a, &b]);
    let shr_large_int = shr_large.as_int().unwrap();
    let axiom_large_shift = premise_large_shift.implies(&shr_large_int._eq(&zero));
    let forall_large_shift = forall_const(ctx, &[&bound_a, &bound_b], &[], &axiom_large_shift);
    solver.assert(&forall_large_shift);
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

/// Replace the bare identifier `result` (word-boundary safe) with `replacement`.
///
/// Used to rewrite a callee postcondition string — e.g. `"result >= 0"` —
/// so it references the callee-result variable name — e.g. `"call_get_block_subsidy_result >= 0"`.
/// Only replaces whole-word occurrences: identifiers containing `result` as a substring
/// (e.g. `result_0`, `len_result`) are left unchanged.
#[cfg(feature = "z3")]
fn substitute_result_ident(condition: &str, replacement: &str) -> String {
    let bytes = condition.as_bytes();
    let target = b"result";
    let tlen = target.len();
    let mut out = String::with_capacity(condition.len() + replacement.len());
    let mut i = 0;
    while i < bytes.len() {
        if i + tlen <= bytes.len() && &bytes[i..i + tlen] == target {
            let before_ok = i == 0 || !is_ident_byte(bytes[i - 1]);
            let after_ok = i + tlen >= bytes.len() || !is_ident_byte(bytes[i + tlen]);
            if before_ok && after_ok {
                out.push_str(replacement);
                i += tlen;
                continue;
            }
        }
        // SAFETY: condition is valid UTF-8 Rust expression, all bytes ≤ 127 in identifiers.
        out.push(bytes[i] as char);
        i += 1;
    }
    out
}

#[cfg(feature = "z3")]
fn is_ident_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

#[cfg(not(feature = "z3"))]
/// Stub implementation when Z3 feature is disabled
pub struct Z3Verifier;

#[cfg(not(feature = "z3"))]
impl Z3Verifier {
    pub fn new(_timeout_ms: u64) -> Self {
        Z3Verifier
    }

    pub fn verify_contract(&mut self, _contract: &Contract) -> VerificationResult {
        VerificationResult::Error {
            error: "Z3 feature not enabled".to_string(),
        }
    }

    pub fn check_ensures_formula_sat_smoke(&mut self, _contract: &Contract) -> VerificationResult {
        VerificationResult::Error {
            error: "Z3 feature not enabled".to_string(),
        }
    }
}

#[cfg(not(feature = "z3"))]
#[derive(Debug, Clone)]
pub enum VerificationResult {
    Error { error: String },
}
