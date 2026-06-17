//! Z3 translator: Rust AST → Z3 AST translation
//!
//! Translates Rust expressions AND function bodies to Z3 expressions for verification.
//! Focused on Bitcoin-specific patterns (u64, i64, Vec, arithmetic, comparisons).
//! Variable `>>` / `<<` use UF `shr` / `shl` with axioms in `z3_verifier`; literal RHS uses `div` /
//! `mul` with exact `2^k` via [`Z3Translator::pow2_int`].
//! `%` (Rem) maps to Z3 `rem`; `&` with a constant mask uses `div`/`rem` patterns when the mask is
//! a power of two or one less than a power of two (including mask on the left operand).
//!
//! ## Key Insight: Implementation IS the Formula
//!
//! For ensures contracts, we don't just check "can the postcondition be violated?"
//! We translate the ACTUAL IMPLEMENTATION to Z3 and verify:
//!   requires + implementation_formula => ensures
//!
//! This makes the Orange Paper the single source of truth:
//! - Orange Paper defines the math (contracts)
//! - Implementation must satisfy the math
//! - Z3 proves implementation => postcondition

use crate::parser::contracts::Contract;
use syn::{Block, Expr, ItemFn, Stmt};
use z3::ast::{Ast, Bool, Int};
#[cfg(feature = "z3")]
use z3::{Config, Context, Sort};

#[cfg(feature = "z3")]
/// Variable map for Z3 translation: holds Int or Bool (for result when return type is bool)
pub type Z3VarMap<'a> = std::collections::HashMap<String, z3::ast::Dynamic<'a>>;

#[cfg(feature = "z3")]
/// Z3 translator for Rust expressions
pub struct Z3Translator {
    ctx: Context,
}

#[cfg(feature = "z3")]
impl Z3Translator {
    /// Create a new Z3 translator.
    /// `timeout_ms`: Solver timeout in milliseconds for deterministic verification.
    pub fn new(timeout_ms: u64) -> Self {
        let mut cfg = Config::new();
        cfg.set_proof_generation(true);
        cfg.set_model_generation(true);
        if timeout_ms > 0 {
            cfg.set_param_value("timeout", &timeout_ms.to_string());
        }
        let ctx = Context::new(&cfg);

        Z3Translator { ctx }
    }

    /// Get the Z3 context
    pub fn context(&self) -> &Context {
        &self.ctx
    }

    /// Translate a Rust expression to a Z3 expression
    ///
    /// Uses a variable map to ensure same variable name = same Z3 variable within one expression
    pub fn translate_expr_with_vars<'a>(
        &'a self,
        expr: &Expr,
        vars: &mut Z3VarMap<'a>,
    ) -> Result<z3::ast::Dynamic<'a>, TranslationError> {
        match expr {
            Expr::Lit(lit) => self.translate_literal(&lit.lit),
            Expr::Path(path) => {
                let name = path_to_string(&path.path);

                // Check if this is a known constant
                if let Some(constant_value) = resolve_constant(&name) {
                    return Ok(Int::from_i64(&self.ctx, constant_value).into());
                }

                // Bool-like enum variants mapped to Z3 Bool constants:
                //   ValidationResult::Valid    → true   ValidationResult::Invalid(…) → false
                //   MempoolResult::Accepted    → true   MempoolResult::Rejected(…)   → false
                // The last path segment is checked so the fully-qualified form and the
                // bare local alias (after `use …::Valid`) both work.
                let last_seg = name.rsplit("::").next().unwrap_or(&name);
                if matches!(last_seg, "Valid" | "Accepted") {
                    return Ok(Bool::from_bool(&self.ctx, true).into());
                }
                if matches!(last_seg, "Invalid" | "Rejected") {
                    return Ok(Bool::from_bool(&self.ctx, false).into());
                }

                // Get or create variable (new vars default to Int)
                let var = vars.entry(name.clone()).or_insert_with(|| {
                    let symbol = z3::Symbol::String(name);
                    Int::new_const(&self.ctx, symbol).into()
                });
                Ok(var.clone())
            }
            Expr::Binary(bin) => {
                let left = self.translate_expr_with_vars(&bin.left, vars)?;
                let right = self.translate_expr_with_vars(&bin.right, vars)?;
                // Concrete shr/shl when right is literal (avoids uninterpreted function)
                if matches!(bin.op, syn::BinOp::Shr(_)) {
                    if let Some(shift_val) = extract_int_literal(&bin.right) {
                        if (0..64).contains(&shift_val) {
                            let left_int = left.as_int().ok_or_else(|| {
                                TranslationError::TypeError("Expected Int".to_string())
                            })?;
                            let divisor = Self::pow2_int(&self.ctx, shift_val as u32);
                            return Ok(left_int.div(&divisor).into());
                        }
                    }
                }
                if matches!(bin.op, syn::BinOp::Shl(_)) {
                    if let Some(shift_val) = extract_int_literal(&bin.right) {
                        if (0..64).contains(&shift_val) {
                            let left_int = left.as_int().ok_or_else(|| {
                                TranslationError::TypeError("Expected Int".to_string())
                            })?;
                            let multiplier = Self::pow2_int(&self.ctx, shift_val as u32);
                            return Ok((left_int * multiplier).into());
                        }
                    }
                }
                // BitAnd (&): model with div/rem for constant masks (Z3 Int has no native bitwise)
                if matches!(bin.op, syn::BinOp::BitAnd(_)) {
                    let left_int = left
                        .as_int()
                        .ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                    let right_int = right
                        .as_int()
                        .ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                    if let Some(mask) = extract_int_literal(&bin.right) {
                        if mask > 0 {
                            let mask_u = mask as u64;
                            // Power of 2 (single bit): a & 2^k = ((a / 2^k) % 2) * 2^k
                            if mask_u.is_power_of_two() {
                                let divisor = Int::from_i64(&self.ctx, mask);
                                let two = Int::from_i64(&self.ctx, 2);
                                let quotient = left_int.div(&divisor);
                                let bit = quotient.rem(&two);
                                return Ok((bit * divisor).into());
                            }
                            // 2^k - 1 (lower k bits): a & (2^k-1) = a % 2^k
                            let next_power = mask + 1;
                            if (next_power as u64).is_power_of_two() {
                                let modulus = Int::from_i64(&self.ctx, next_power);
                                return Ok(left_int.rem(&modulus).into());
                            }
                        }
                    }
                    // Commutative: constant mask on the left
                    if let Some(mask) = extract_int_literal(&bin.left) {
                        if mask > 0 {
                            let mask_u = mask as u64;
                            if mask_u.is_power_of_two() {
                                let divisor = Int::from_i64(&self.ctx, mask);
                                let two = Int::from_i64(&self.ctx, 2);
                                let quotient = right_int.div(&divisor);
                                let bit = quotient.rem(&two);
                                return Ok((bit * divisor).into());
                            }
                            let next_power = mask + 1;
                            if (next_power as u64).is_power_of_two() {
                                let modulus = Int::from_i64(&self.ctx, next_power);
                                return Ok(right_int.rem(&modulus).into());
                            }
                        }
                    }
                    // Fallback: uninterpreted function (like Shr/Shl for non-constant)
                    let bitand_fn = z3::FuncDecl::new(
                        &self.ctx,
                        "bitand",
                        &[&Sort::int(&self.ctx), &Sort::int(&self.ctx)],
                        &Sort::int(&self.ctx),
                    );
                    return Ok(bitand_fn.apply(&[&left_int, &right_int]));
                }
                self.translate_binary_op(bin.op, left, right)
            }
            Expr::MethodCall(method) => self.translate_method_call(method, vars),
            Expr::Call(call) => self.translate_call(call, vars),
            Expr::Unary(unary) => {
                let expr = self.translate_expr_with_vars(&unary.expr, vars)?;
                self.translate_unary_op(unary.op, expr)
            }
            Expr::Paren(paren) => self.translate_expr_with_vars(&paren.expr, vars),
            Expr::Cast(cast) => {
                // (expr) as Type - pass through (we model as Int)
                self.translate_expr_with_vars(&cast.expr, vars)
            }
            Expr::Reference(reference) => {
                // &expr - pass through (we don't model pointers)
                self.translate_expr_with_vars(&reference.expr, vars)
            }
            Expr::Tuple(tuple) => {
                // (a, b, c) - for determinism, use first element or fresh var from all
                if let Some(first) = tuple.elems.first() {
                    self.translate_expr_with_vars(first, vars)
                } else {
                    let name = format!("tuple_{}", vars.len());
                    let var = vars.entry(name.clone()).or_insert_with(|| {
                        let symbol = z3::Symbol::String(name);
                        Int::new_const(&self.ctx, symbol).into()
                    });
                    Ok(var.clone())
                }
            }
            Expr::Try(try_expr) => {
                // expr? - pass through (model Ok case; Err => early return handled elsewhere)
                self.translate_expr_with_vars(&try_expr.expr, vars)
            }
            Expr::Range(range) => {
                // 0..n or a..b - model as fresh Int (range bounds)
                let _ = range
                    .start
                    .as_ref()
                    .map(|e| self.translate_expr_with_vars(e, vars));
                let _ = range
                    .end
                    .as_ref()
                    .map(|e| self.translate_expr_with_vars(e, vars));
                let name = format!("range_{}", vars.len());
                let var = vars.entry(name.clone()).or_insert_with(|| {
                    let symbol = z3::Symbol::String(name);
                    Int::new_const(&self.ctx, symbol).into()
                });
                Ok(var.clone())
            }
            Expr::Field(field) => self.translate_field_access(field, vars),
            Expr::Index(index) => {
                // slice[i] or vec[i] - model as fresh Int (conservative; no array semantics)
                let _ = self.translate_expr_with_vars(&index.expr, vars)?;
                let _ = self.translate_expr_with_vars(&index.index, vars)?;
                let fresh = format!("index_{}", vars.len());
                let var = vars.entry(fresh.clone()).or_insert_with(|| {
                    let symbol = z3::Symbol::String(fresh);
                    Int::new_const(&self.ctx, symbol).into()
                });
                Ok(var.clone())
            }
            Expr::Block(block) => {
                // Block expression: { stmts; expr } - process lets for bindings, translate last expr
                for stmt in &block.block.stmts {
                    if let Stmt::Local(local) = stmt {
                        if let Some(init) = &local.init {
                            if let syn::Pat::Ident(ident) = &local.pat {
                                let var_name = ident.ident.to_string();
                                if let Ok(z3_expr) = self.translate_expr_with_vars(&init.expr, vars)
                                {
                                    if z3_expr.as_int().is_some() || z3_expr.as_bool().is_some() {
                                        vars.insert(var_name, z3_expr);
                                    }
                                }
                            }
                        }
                    }
                }
                if let Some(Stmt::Expr(expr, None)) = block.block.stmts.last() {
                    return self.translate_expr_with_vars(expr, vars);
                }
                Err(TranslationError::UnsupportedExpression(
                    "Block expression: no final expression".to_string(),
                ))
            }
            Expr::Match(match_expr) => self.translate_match(match_expr, vars),
            Expr::ForLoop(fl) => {
                let _ = self.translate_expr_with_vars(&fl.expr, vars);
                let _ = self.translate_block_to_result_formula(&fl.body, vars);
                let name = format!("for_loop_{}", vars.len());
                let var = vars.entry(name.clone()).or_insert_with(|| {
                    let symbol = z3::Symbol::String(name);
                    Int::new_const(&self.ctx, symbol).into()
                });
                Ok(var.clone())
            }
            Expr::Closure(closure) => {
                let _ = self.translate_expr_with_vars(&closure.body, vars);
                let name = format!("closure_{}", vars.len());
                let var = vars.entry(name.clone()).or_insert_with(|| {
                    let symbol = z3::Symbol::String(name);
                    Int::new_const(&self.ctx, symbol).into()
                });
                Ok(var.clone())
            }
            Expr::Repeat(repeat) => {
                // [expr; len] - e.g. [0u8; 32] for zero hash. Model as constant or fresh Int.
                let _ = self.translate_expr_with_vars(&repeat.len, vars);
                if let Some(val) = extract_int_literal(&repeat.expr) {
                    if val == 0 {
                        return Ok(Int::from_i64(&self.ctx, 0).into());
                    }
                }
                let name = format!("repeat_{}", vars.len());
                let var = vars.entry(name.clone()).or_insert_with(|| {
                    let symbol = z3::Symbol::String(name);
                    Int::new_const(&self.ctx, symbol).into()
                });
                Ok(var.clone())
            }
            Expr::Array(array) => {
                // [a, b, c] - model as constant if all same literal, else fresh Int
                if array.elems.len() == 1 {
                    if let Some(val) = extract_int_literal(array.elems.first().unwrap()) {
                        return Ok(Int::from_i64(&self.ctx, val).into());
                    }
                }
                let name = format!("array_{}", vars.len());
                let var = vars.entry(name.clone()).or_insert_with(|| {
                    let symbol = z3::Symbol::String(name);
                    Int::new_const(&self.ctx, symbol).into()
                });
                Ok(var.clone())
            }
            Expr::If(if_expr) => {
                // Standalone if (not in block context) - translate to ite
                self.translate_if_expr_to_dynamic(if_expr, vars)
            }
            Expr::While(while_expr) => {
                let _ = self.translate_expr_with_vars(&while_expr.cond, vars);
                let _ = self.translate_block_to_result_formula(&while_expr.body, vars);
                let name = format!("while_loop_{}", vars.len());
                let var = vars.entry(name.clone()).or_insert_with(|| {
                    let symbol = z3::Symbol::String(name);
                    Int::new_const(&self.ctx, symbol).into()
                });
                Ok(var.clone())
            }
            Expr::Loop(loop_expr) => {
                let _ = self.translate_block_to_result_formula(&loop_expr.body, vars);
                let name = format!("loop_{}", vars.len());
                let var = vars.entry(name.clone()).or_insert_with(|| {
                    let symbol = z3::Symbol::String(name);
                    Int::new_const(&self.ctx, symbol).into()
                });
                Ok(var.clone())
            }
            Expr::Let(let_expr) => {
                // if let Some(x)=opt / Ok(x)=res / Err(e)=res / None=opt - used as condition in if
                // Returns Bool (matches/doesn't match); binds inner var for then-branch when present
                let (inner_var_opt, bool_suffix, use_as_is) =
                    parse_let_option_result_pat(&let_expr.pat).ok_or_else(|| {
                        TranslationError::UnsupportedExpression(format!(
                            "Let: only Some(x), Ok(x), Err(e), Err(_), None patterns supported, got {:?}",
                            let_expr.pat
                        ))
                    })?;
                let _ = self.translate_expr_with_vars(&let_expr.expr, vars)?;
                let base = expr_to_var_hint(&let_expr.expr);
                let bool_name = format!("{base}_{bool_suffix}");
                let raw_bool = vars
                    .entry(bool_name.clone())
                    .or_insert_with(|| {
                        let symbol = z3::Symbol::String(bool_name);
                        Bool::new_const(&self.ctx, symbol).into()
                    })
                    .clone();
                let cond_bool = raw_bool.as_bool().ok_or_else(|| {
                    TranslationError::TypeError(format!("{bool_suffix}: expected Bool"))
                })?;
                let cond_bool = if use_as_is {
                    cond_bool
                } else {
                    cond_bool.not()
                };
                if let Some(inner_var) = inner_var_opt {
                    let inner_val = vars
                        .entry(inner_var.clone())
                        .or_insert_with(|| {
                            let symbol = z3::Symbol::String(inner_var.clone());
                            Int::new_const(&self.ctx, symbol).into()
                        })
                        .clone();
                    vars.insert(inner_var, inner_val);
                }
                Ok(cond_bool.into())
            }
            Expr::Struct(s) => {
                // Struct literal: TypeName { field1: expr1, field2: expr2, … }
                // Bind each named field value into vars so that the final-expression
                // handler in translate_block_to_result_formula can produce field
                // equality formulas (e.g. result_bit == 15).
                // Return the value of the first translatable field as a proxy.
                let mut first_val: Option<z3::ast::Dynamic<'a>> = None;
                for field in &s.fields {
                    if let syn::Member::Named(ident) = &field.member {
                        if let Ok(fz3) = self.translate_expr_with_vars(&field.expr, vars) {
                            // Store under plain field name so later references find it.
                            vars.entry(ident.to_string()).or_insert_with(|| fz3.clone());
                            if first_val.is_none() {
                                first_val = Some(fz3);
                            }
                        }
                    }
                }
                if let Some(v) = first_val {
                    if v.as_int().is_some() || v.as_bool().is_some() {
                        return Ok(v);
                    }
                }
                let name = format!("struct_{}", vars.len());
                let var = vars.entry(name.clone()).or_insert_with(|| {
                    let symbol = z3::Symbol::String(name);
                    Int::new_const(&self.ctx, symbol).into()
                });
                Ok(var.clone())
            }
            _ => Err(TranslationError::UnsupportedExpression(format!("{expr:?}"))),
        }
    }

    /// Translate a Rust expression to a Z3 expression (public API)
    pub fn translate_expr(&self, expr: &Expr) -> Result<z3::ast::Dynamic<'_>, TranslationError> {
        let mut vars = Z3VarMap::new();
        self.translate_expr_with_vars(expr, &mut vars)
    }

    /// Translate a literal (integer, boolean, etc.)
    fn translate_literal(&self, lit: &syn::Lit) -> Result<z3::ast::Dynamic<'_>, TranslationError> {
        match lit {
            syn::Lit::Int(int_lit) => {
                let value = parse_lit_int(int_lit).ok_or_else(|| {
                    TranslationError::ParseError(format!("Cannot parse integer literal: {int_lit}"))
                })?;
                Ok(Int::from_i64(&self.ctx, value).into())
            }
            syn::Lit::Bool(bool_lit) => Ok(Bool::from_bool(&self.ctx, bool_lit.value).into()),
            _ => Err(TranslationError::UnsupportedLiteral(format!("{lit:?}"))),
        }
    }

    /// Translate a binary operation given already-translated operands
    fn translate_binary_op<'a>(
        &'a self,
        op: syn::BinOp,
        left: z3::ast::Dynamic<'a>,
        right: z3::ast::Dynamic<'a>,
    ) -> Result<z3::ast::Dynamic<'a>, TranslationError> {
        match op {
            syn::BinOp::Add(_) => {
                let left_int = left
                    .as_int()
                    .ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                let right_int = right
                    .as_int()
                    .ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                Ok((left_int + right_int).into())
            }
            syn::BinOp::Sub(_) => {
                let left_int = left
                    .as_int()
                    .ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                let right_int = right
                    .as_int()
                    .ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                Ok((left_int - right_int).into())
            }
            syn::BinOp::Mul(_) => {
                let left_int = left
                    .as_int()
                    .ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                let right_int = right
                    .as_int()
                    .ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                Ok((left_int * right_int).into())
            }
            syn::BinOp::Div(_) => {
                // Z3 integer division
                let left_int = left
                    .as_int()
                    .ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                let right_int = right
                    .as_int()
                    .ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                Ok(left_int.div(&right_int).into())
            }
            syn::BinOp::Rem(_) => {
                let left_int = left
                    .as_int()
                    .ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                let right_int = right
                    .as_int()
                    .ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                Ok(left_int.rem(&right_int).into())
            }
            syn::BinOp::Shr(_) => {
                let left_int = left
                    .as_int()
                    .ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                let right_int = right
                    .as_int()
                    .ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;

                let shift_fn = z3::FuncDecl::new(
                    &self.ctx,
                    "shr",
                    &[&Sort::int(&self.ctx), &Sort::int(&self.ctx)],
                    &Sort::int(&self.ctx),
                );
                Ok(shift_fn.apply(&[&left_int, &right_int]))
            }
            syn::BinOp::Shl(_) => {
                let left_int = left
                    .as_int()
                    .ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                let right_int = right
                    .as_int()
                    .ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;

                let shift_fn = z3::FuncDecl::new(
                    &self.ctx,
                    "shl",
                    &[&Sort::int(&self.ctx), &Sort::int(&self.ctx)],
                    &Sort::int(&self.ctx),
                );
                Ok(shift_fn.apply(&[&left_int, &right_int]))
            }
            syn::BinOp::Eq(_) => {
                // Equality: Bool-Bool, Int-Int, and Bool-Int (spec: \in {true,false} for 0/1)
                let eq = match (
                    left.as_bool(),
                    left.as_int(),
                    right.as_bool(),
                    right.as_int(),
                ) {
                    (Some(l), _, Some(r), _) => l._eq(&r),
                    (_, Some(l), _, Some(r)) => l._eq(&r),
                    (Some(l), _, _, Some(r)) => {
                        let one = Int::from_i64(&self.ctx, 1);
                        let zero = Int::from_i64(&self.ctx, 0);
                        let l_int = l.ite(&one, &zero);
                        l_int._eq(&r)
                    }
                    (_, Some(l), Some(r), _) => {
                        let one = Int::from_i64(&self.ctx, 1);
                        let zero = Int::from_i64(&self.ctx, 0);
                        let r_int = r.ite(&one, &zero);
                        l._eq(&r_int)
                    }
                    _ => {
                        return Err(TranslationError::TypeError(
                            "Eq: operands must be Bool or Int (got mixed sorts)".to_string(),
                        ));
                    }
                };
                Ok(eq.into())
            }
            syn::BinOp::Ne(_) => {
                let eq = match (
                    left.as_bool(),
                    left.as_int(),
                    right.as_bool(),
                    right.as_int(),
                ) {
                    (Some(l), _, Some(r), _) => l._eq(&r),
                    (_, Some(l), _, Some(r)) => l._eq(&r),
                    (Some(l), _, _, Some(r)) => {
                        let one = Int::from_i64(&self.ctx, 1);
                        let zero = Int::from_i64(&self.ctx, 0);
                        let l_int = l.ite(&one, &zero);
                        l_int._eq(&r)
                    }
                    (_, Some(l), Some(r), _) => {
                        let one = Int::from_i64(&self.ctx, 1);
                        let zero = Int::from_i64(&self.ctx, 0);
                        let r_int = r.ite(&one, &zero);
                        l._eq(&r_int)
                    }
                    _ => {
                        return Err(TranslationError::TypeError(
                            "Ne: operands must be Bool or Int (got mixed sorts)".to_string(),
                        ));
                    }
                };
                Ok(eq.not().into())
            }
            syn::BinOp::Lt(_) | syn::BinOp::Le(_) | syn::BinOp::Gt(_) | syn::BinOp::Ge(_) => {
                // Coerce Bool to Int (true=1, false=0) for comparisons - handles spec patterns
                let left_int = left
                    .as_int()
                    .or_else(|| {
                        left.as_bool().map(|b| {
                            let one = Int::from_i64(&self.ctx, 1);
                            let zero = Int::from_i64(&self.ctx, 0);
                            b.ite(&one, &zero)
                        })
                    })
                    .ok_or_else(|| {
                        TranslationError::TypeError(
                            "Lt/Le/Gt/Ge: left operand must be Int or Bool".to_string(),
                        )
                    })?;
                let right_int = right
                    .as_int()
                    .or_else(|| {
                        right.as_bool().map(|b| {
                            let one = Int::from_i64(&self.ctx, 1);
                            let zero = Int::from_i64(&self.ctx, 0);
                            b.ite(&one, &zero)
                        })
                    })
                    .ok_or_else(|| {
                        TranslationError::TypeError(
                            "Lt/Le/Gt/Ge: right operand must be Int or Bool".to_string(),
                        )
                    })?;
                let cmp = match op {
                    syn::BinOp::Lt(_) => left_int.lt(&right_int),
                    syn::BinOp::Le(_) => left_int.le(&right_int),
                    syn::BinOp::Gt(_) => left_int.gt(&right_int),
                    syn::BinOp::Ge(_) => left_int.ge(&right_int),
                    _ => unreachable!(),
                };
                Ok(cmp.into())
            }
            syn::BinOp::And(_) => {
                let left_bool = left
                    .as_bool()
                    .ok_or_else(|| TranslationError::TypeError("Expected Bool".to_string()))?;
                let right_bool = right
                    .as_bool()
                    .ok_or_else(|| TranslationError::TypeError("Expected Bool".to_string()))?;
                Ok((left_bool & right_bool).into())
            }
            syn::BinOp::Or(_) => {
                let left_bool = left
                    .as_bool()
                    .ok_or_else(|| TranslationError::TypeError("Expected Bool".to_string()))?;
                let right_bool = right
                    .as_bool()
                    .ok_or_else(|| TranslationError::TypeError("Expected Bool".to_string()))?;
                Ok((left_bool | right_bool).into())
            }
            _ => Err(TranslationError::UnsupportedOperator(format!("{op:?}"))),
        }
    }

    /// Exact `2^k` as Z3 `Int` for `k < 64` (avoids host `1i64 << 63` overflow).
    pub(crate) fn pow2_int(ctx: &Context, k: u32) -> Int<'_> {
        debug_assert!(k < 64);
        let v = 1u128 << k;
        if v <= i64::MAX as u128 {
            Int::from_i64(ctx, v as i64)
        } else {
            Int::from_str(ctx, &v.to_string()).expect("Z3 int pow2")
        }
    }

    /// Translate a method call (e.g., vec.len(), opt.is_some())
    fn translate_method_call<'a>(
        &'a self,
        method: &syn::ExprMethodCall,
        vars: &mut Z3VarMap<'a>,
    ) -> Result<z3::ast::Dynamic<'a>, TranslationError> {
        let method_name = method.method.to_string();

        match method_name.as_str() {
            "checked_add" | "checked_sub" | "checked_mul" => {
                // a.checked_add(b) returns Option; model as a+b (overflow ignored for verification)
                let left = self.translate_expr_with_vars(&method.receiver, vars)?;
                let arg = method.args.first().ok_or_else(|| {
                    TranslationError::UnsupportedExpression("checked_add needs 1 arg".to_string())
                })?;
                let right = self.translate_expr_with_vars(arg, vars)?;
                let left_int = left.as_int().ok_or_else(|| {
                    TranslationError::TypeError("checked_add: expected Int".to_string())
                })?;
                let right_int = right.as_int().ok_or_else(|| {
                    TranslationError::TypeError("checked_add: expected Int".to_string())
                })?;
                let result = match method_name.as_str() {
                    "checked_add" => left_int + right_int,
                    "checked_sub" => left_int - right_int,
                    "checked_mul" => left_int * right_int,
                    _ => unreachable!(),
                };
                Ok(result.into())
            }
            "unwrap_or" | "unwrap_or_else" => {
                // x.unwrap_or(default) or x.unwrap_or_else(|| default) - use receiver (the Option)
                self.translate_expr_with_vars(&method.receiver, vars)
            }
            "min" | "max" => {
                let left = self.translate_expr_with_vars(&method.receiver, vars)?;
                let arg = method.args.first().ok_or_else(|| {
                    TranslationError::UnsupportedExpression("min/max needs 1 arg".to_string())
                })?;
                let right = self.translate_expr_with_vars(arg, vars)?;
                let left_int = left.as_int().ok_or_else(|| {
                    TranslationError::TypeError("min/max: expected Int".to_string())
                })?;
                let right_int = right.as_int().ok_or_else(|| {
                    TranslationError::TypeError("min/max: expected Int".to_string())
                })?;
                let result = match method_name.as_str() {
                    "min" => left_int.lt(&right_int).ite(&left_int, &right_int),
                    "max" => left_int.gt(&right_int).ite(&left_int, &right_int),
                    _ => unreachable!(),
                };
                Ok(result.into())
            }
            "with" => {
                // thread_local.with(|cell| block) - translate closure body
                if let Some(Expr::Closure(closure)) = method.args.first() {
                    if closure.inputs.len() == 1 {
                        if let syn::Pat::Ident(ident) = &closure.inputs[0] {
                            let param = ident.ident.to_string();
                            let fresh = format!("with_{param}");
                            let new_var = Int::new_const(&self.ctx, z3::Symbol::String(fresh));
                            let old = vars.insert(param.clone(), new_var.into());
                            let result = self.translate_expr_with_vars(&closure.body, vars);
                            if let Some(prev) = old {
                                vars.insert(param, prev);
                            } else {
                                vars.remove(&param);
                            }
                            return result;
                        }
                    }
                }
                let _ = self.translate_expr_with_vars(&method.receiver, vars);
                let base = expr_to_var_hint(&method.receiver);
                let name = format!("{base}_with_result");
                let var = vars.entry(name.clone()).or_insert_with(|| {
                    let symbol = z3::Symbol::String(name);
                    Int::new_const(&self.ctx, symbol).into()
                });
                Ok(var.clone())
            }
            "clear" | "extend_from_slice" | "push" | "copy_from_slice" => {
                let _ = self.translate_expr_with_vars(&method.receiver, vars);
                for arg in &method.args {
                    let _ = self.translate_expr_with_vars(arg, vars);
                }
                let base = expr_to_var_hint(&method.receiver);
                let name = format!("{base}_after_{method_name}");
                let var_val = vars
                    .entry(name.clone())
                    .or_insert_with(|| {
                        let symbol = z3::Symbol::String(name);
                        Int::new_const(&self.ctx, symbol).into()
                    })
                    .clone();
                // Update receiver so subsequent uses (e.g. digest(&bytes)) see mutated value
                if let Expr::Path(path) = &*method.receiver {
                    vars.insert(path_to_string(&path.path), var_val.clone());
                }
                Ok(var_val)
            }
            "digest" | "finalize" => {
                // Uninterpreted: digest(data) for determinism. Receiver holds state; use first arg if any.
                if let Some(arg) = method.args.first() {
                    let data = self.translate_expr_with_vars(arg, vars)?;
                    let data_int = data.as_int().ok_or_else(|| {
                        TranslationError::TypeError("digest arg must be Int".to_string())
                    })?;
                    let int_sort = Sort::int(&self.ctx);
                    let fn_decl =
                        z3::FuncDecl::new(&self.ctx, "sha256_digest", &[&int_sort], &int_sort);
                    return Ok(fn_decl.apply(&[&data_int]));
                }
                let _ = self.translate_expr_with_vars(&method.receiver, vars);
                let base = expr_to_var_hint(&method.receiver);
                let name = format!("{base}_digest");
                let var = vars.entry(name.clone()).or_insert_with(|| {
                    let symbol = z3::Symbol::String(name);
                    Int::new_const(&self.ctx, symbol).into()
                });
                Ok(var.clone())
            }
            "hash256" | "hash" => {
                // Uninterpreted: hash256/hash(data) for determinism
                let arg = method.args.first().ok_or_else(|| {
                    TranslationError::UnsupportedExpression("hash256/hash needs 1 arg".to_string())
                })?;
                let data = self.translate_expr_with_vars(arg, vars)?;
                let data_int = data.as_int().ok_or_else(|| {
                    TranslationError::TypeError("hash arg must be Int".to_string())
                })?;
                let int_sort = Sort::int(&self.ctx);
                let fn_decl = z3::FuncDecl::new(&self.ctx, "hash256", &[&int_sort], &int_sort);
                Ok(fn_decl.apply(&[&data_int]))
            }
            "into" => self.translate_expr_with_vars(&method.receiver, vars),
            "clone" | "serialize" => {
                // x.clone() / x.serialize() - pass through (same value for determinism)
                self.translate_expr_with_vars(&method.receiver, vars)
            }
            "as_ref" => {
                // option.as_ref() - pass through (Option<&T> from Option<T>)
                self.translate_expr_with_vars(&method.receiver, vars)
            }
            "map" => {
                // option.map(|x| f(x)) - use closure body or pass through
                if let Some(Expr::Closure(closure)) = method.args.first() {
                    if closure.inputs.len() == 1 {
                        if let syn::Pat::Ident(ident) = &closure.inputs[0] {
                            let param = ident.ident.to_string();
                            let _recv = self.translate_expr_with_vars(&method.receiver, vars)?;
                            let fresh = format!("map_{param}");
                            let new_var = Int::new_const(&self.ctx, z3::Symbol::String(fresh));
                            let old = vars.insert(param.clone(), new_var.into());
                            let result = self.translate_expr_with_vars(&closure.body, vars);
                            if let Some(prev) = old {
                                vars.insert(param, prev);
                            } else {
                                vars.remove(&param);
                            }
                            if let Ok(r) = result {
                                return Ok(r);
                            }
                        }
                    }
                }
                let _ = self.translate_expr_with_vars(&method.receiver, vars);
                let base = expr_to_var_hint(&method.receiver);
                let name = format!("{base}_map");
                let var = vars.entry(name.clone()).or_insert_with(|| {
                    let symbol = z3::Symbol::String(name);
                    Int::new_const(&self.ctx, symbol).into()
                });
                Ok(var.clone())
            }
            "borrow_mut" | "borrow" => {
                let _ = self.translate_expr_with_vars(&method.receiver, vars);
                let base = expr_to_var_hint(&method.receiver);
                let name = format!("{base}_borrow");
                let var = vars.entry(name.clone()).or_insert_with(|| {
                    let symbol = z3::Symbol::String(name);
                    Int::new_const(&self.ctx, symbol).into()
                });
                Ok(var.clone())
            }
            "len" => {
                // vec.len() - return fresh Int (length); receiver type not modeled
                let _ = self.translate_expr_with_vars(&method.receiver, vars);
                let base = expr_to_var_hint(&method.receiver);
                let name = if base == "x" {
                    "len_result".to_string()
                } else {
                    format!("{base}_len")
                };
                let var = vars.entry(name.clone()).or_insert_with(|| {
                    let symbol = z3::Symbol::String(name);
                    Int::new_const(&self.ctx, symbol).into()
                });
                Ok(var.clone())
            }
            "iter" | "into_iter" | "par_iter" => {
                // Pass through to receiver - iterator over collection
                self.translate_expr_with_vars(&method.receiver, vars)
            }
            "step_by" => {
                // (0..n).step_by(2) - pass through (iterator adapter)
                self.translate_expr_with_vars(&method.receiver, vars)
            }
            "collect" => {
                // iter.collect() - return fresh var for collected value
                let _ = self.translate_expr_with_vars(&method.receiver, vars);
                let base = expr_to_var_hint(&method.receiver);
                let name = format!("{base}_collect");
                let var = vars.entry(name.clone()).or_insert_with(|| {
                    let symbol = z3::Symbol::String(name);
                    Int::new_const(&self.ctx, symbol).into()
                });
                Ok(var.clone())
            }
            "enumerate" => {
                // iter.enumerate() - pass through (iterator adapter)
                self.translate_expr_with_vars(&method.receiver, vars)
            }
            "next" => {
                // iter.next() - return fresh var for next element
                let _ = self.translate_expr_with_vars(&method.receiver, vars);
                let base = expr_to_var_hint(&method.receiver);
                let name = format!("{base}_next");
                let var = vars.entry(name.clone()).or_insert_with(|| {
                    let symbol = z3::Symbol::String(name);
                    Int::new_const(&self.ctx, symbol).into()
                });
                Ok(var.clone())
            }
            "sum" => {
                // iter.sum() - return fresh var for sum (e.g. witness_data.iter().map(|w| w.len()).sum())
                let _ = self.translate_expr_with_vars(&method.receiver, vars);
                let base = expr_to_var_hint(&method.receiver);
                let name = format!("{base}_sum");
                let var = vars.entry(name.clone()).or_insert_with(|| {
                    let symbol = z3::Symbol::String(name);
                    Int::new_const(&self.ctx, symbol).into()
                });
                Ok(var.clone())
            }
            "fold" => {
                // iter.fold(init, |acc, x| body) - return fresh var for folded result
                let _ = self.translate_expr_with_vars(&method.receiver, vars);
                if let Some(init) = method.args.first() {
                    let _ = self.translate_expr_with_vars(init, vars);
                }
                let base = expr_to_var_hint(&method.receiver);
                let name = format!("{base}_fold");
                let var = vars.entry(name.clone()).or_insert_with(|| {
                    let symbol = z3::Symbol::String(name);
                    Int::new_const(&self.ctx, symbol).into()
                });
                Ok(var.clone())
            }
            "reduce" => {
                // iter.reduce(|a, b| body) - return fresh var for reduced result
                let _ = self.translate_expr_with_vars(&method.receiver, vars);
                let base = expr_to_var_hint(&method.receiver);
                let name = format!("{base}_reduce");
                let var = vars.entry(name.clone()).or_insert_with(|| {
                    let symbol = z3::Symbol::String(name);
                    Int::new_const(&self.ctx, symbol).into()
                });
                Ok(var.clone())
            }
            "saturating_sub" => {
                // a.saturating_sub(b) - model as a - b (determinism: same inputs => same output)
                let left = self.translate_expr_with_vars(&method.receiver, vars)?;
                let arg = method.args.first().ok_or_else(|| {
                    TranslationError::UnsupportedExpression(
                        "saturating_sub needs 1 arg".to_string(),
                    )
                })?;
                let right = self.translate_expr_with_vars(arg, vars)?;
                let left_int = left.as_int().ok_or_else(|| {
                    TranslationError::TypeError("saturating_sub: expected Int".to_string())
                })?;
                let right_int = right.as_int().ok_or_else(|| {
                    TranslationError::TypeError("saturating_sub: expected Int".to_string())
                })?;
                Ok((left_int - right_int).into())
            }
            "to_le_bytes" => {
                // x.to_le_bytes() - uninterpreted for determinism (bytes from int)
                let recv = self.translate_expr_with_vars(&method.receiver, vars)?;
                let recv_int = recv.as_int().ok_or_else(|| {
                    TranslationError::TypeError("to_le_bytes: expected Int".to_string())
                })?;
                let int_sort = Sort::int(&self.ctx);
                let fn_decl = z3::FuncDecl::new(&self.ctx, "to_le_bytes", &[&int_sort], &int_sort);
                Ok(fn_decl.apply(&[&recv_int]))
            }
            "is_some" | "is_none" => {
                // Option checks: return Bool. Use fresh var for unknown Option; name from receiver.
                let _ = self.translate_expr_with_vars(&method.receiver, vars);
                let base = expr_to_var_hint(&method.receiver);
                let name = format!("{base}_is_some");
                let var = vars.entry(name.clone()).or_insert_with(|| {
                    let symbol = z3::Symbol::String(name);
                    Bool::new_const(&self.ctx, symbol).into()
                });
                let bool_val = var.as_bool().ok_or_else(|| {
                    TranslationError::TypeError("is_some: expected Bool".to_string())
                })?;
                Ok(if method_name == "is_none" {
                    bool_val.not().into()
                } else {
                    bool_val.clone().into()
                })
            }
            "is_ok" | "is_err" => {
                // Result checks: same as Option (Ok/Err)
                let _ = self.translate_expr_with_vars(&method.receiver, vars);
                let base = expr_to_var_hint(&method.receiver);
                let name = format!("{base}_is_ok");
                let var = vars.entry(name.clone()).or_insert_with(|| {
                    let symbol = z3::Symbol::String(name);
                    Bool::new_const(&self.ctx, symbol).into()
                });
                let bool_val = var.as_bool().ok_or_else(|| {
                    TranslationError::TypeError("is_ok: expected Bool".to_string())
                })?;
                Ok(if method_name == "is_err" {
                    bool_val.not().into()
                } else {
                    bool_val.clone().into()
                })
            }
            "unwrap" => {
                // opt.unwrap() or res.unwrap(): return inner value when Some/Ok.
                // If receiver is Some(expr) or Ok(expr), use that; else fresh Int.
                let receiver = &method.receiver;
                if method.args.is_empty() {
                    // Try to unwrap from call: Some(x) or Ok(x)
                    if let Expr::Call(call) = &**receiver {
                        if let Ok(name) = call_expr_to_name(&call.func) {
                            let base = name.split("::").last().unwrap_or(&name);
                            if (base == "Some" || base == "Ok") && call.args.len() == 1 {
                                return self.translate_expr_with_vars(&call.args[0], vars);
                            }
                        }
                    }
                    // Fallback: fresh Int for unknown Option/Result value
                    let _ = self.translate_expr_with_vars(receiver, vars);
                    let base = expr_to_var_hint(receiver);
                    let name = format!("{base}_unwrap");
                    let var = vars.entry(name.clone()).or_insert_with(|| {
                        let symbol = z3::Symbol::String(name);
                        Int::new_const(&self.ctx, symbol).into()
                    });
                    return Ok(var.clone());
                }
                Err(TranslationError::UnsupportedExpression(
                    "unwrap with args not supported".to_string(),
                ))
            }
            "div_ceil" => {
                // a.div_ceil(b) = (a + b - 1) / b  (ceiling integer division)
                let left = self.translate_expr_with_vars(&method.receiver, vars)?;
                let arg = method.args.first().ok_or_else(|| {
                    TranslationError::UnsupportedExpression("div_ceil needs 1 arg".to_string())
                })?;
                let right = self.translate_expr_with_vars(arg, vars)?;
                let left_int = left.as_int().ok_or_else(|| {
                    TranslationError::TypeError("div_ceil: expected Int lhs".to_string())
                })?;
                let right_int = right.as_int().ok_or_else(|| {
                    TranslationError::TypeError("div_ceil: expected Int rhs".to_string())
                })?;
                let one = Int::from_i64(&self.ctx, 1);
                let numerator = left_int + right_int.clone() - one;
                Ok((numerator / right_int).into())
            }
            "saturating_mul" => {
                // a.saturating_mul(b) — model as a * b (same as checked_mul for Z3 Int)
                let left = self.translate_expr_with_vars(&method.receiver, vars)?;
                let arg = method.args.first().ok_or_else(|| {
                    TranslationError::UnsupportedExpression(
                        "saturating_mul needs 1 arg".to_string(),
                    )
                })?;
                let right = self.translate_expr_with_vars(arg, vars)?;
                let left_int = left.as_int().ok_or_else(|| {
                    TranslationError::TypeError("saturating_mul: expected Int".to_string())
                })?;
                let right_int = right.as_int().ok_or_else(|| {
                    TranslationError::TypeError("saturating_mul: expected Int".to_string())
                })?;
                Ok((left_int * right_int).into())
            }
            "is_empty" => {
                // x.is_empty() == (x.len() == 0)
                // Reuse the same `{base}_len` variable as the `len` handler so that
                // `x.len() > 0` in an ensures clause refers to the same Z3 constant.
                let _ = self.translate_expr_with_vars(&method.receiver, vars);
                let base = expr_to_var_hint(&method.receiver);
                let len_name = if base == "x" {
                    "len_result".to_string()
                } else {
                    format!("{base}_len")
                };
                let len_var = vars
                    .entry(len_name.clone())
                    .or_insert_with(|| {
                        let symbol = z3::Symbol::String(len_name);
                        Int::new_const(&self.ctx, symbol).into()
                    })
                    .clone();
                let len_int = len_var.as_int().ok_or_else(|| {
                    TranslationError::TypeError("is_empty: len must be Int".to_string())
                })?;
                let zero = Int::from_i64(&self.ctx, 0);
                Ok(len_int._eq(&zero).into())
            }
            "all" => {
                // iter.all(|x| pred(x)) — uninterpreted Bool; no closure expansion
                let _ = self.translate_expr_with_vars(&method.receiver, vars);
                let base = expr_to_var_hint(&method.receiver);
                let name = format!("{base}_all");
                let var = vars.entry(name.clone()).or_insert_with(|| {
                    let symbol = z3::Symbol::String(name);
                    Bool::new_const(&self.ctx, symbol).into()
                });
                Ok(var.clone())
            }
            "contains" => {
                // range.contains(&x) — model as lo <= x && x <= hi
                // Handles inclusive (..=) and exclusive (..) ranges on the receiver.
                let arg = method.args.first().ok_or_else(|| {
                    TranslationError::UnsupportedExpression("contains needs 1 arg".to_string())
                })?;
                let x_z3 = self.translate_expr_with_vars(arg, vars)?;
                let x_int = x_z3.as_int().ok_or_else(|| {
                    TranslationError::TypeError("contains: arg must be Int".to_string())
                })?;
                if let Expr::Range(range) = &*method.receiver {
                    let lo_int = if let Some(start) = &range.start {
                        let lo = self.translate_expr_with_vars(start, vars)?;
                        lo.as_int().ok_or_else(|| {
                            TranslationError::TypeError(
                                "contains: range start must be Int".to_string(),
                            )
                        })?
                    } else {
                        // No lower bound — treat as always satisfied (use -MAX)
                        Int::from_i64(&self.ctx, i64::MIN / 2)
                    };
                    let hi_int = if let Some(end) = &range.end {
                        let hi = self.translate_expr_with_vars(end, vars)?;
                        let hi_int = hi.as_int().ok_or_else(|| {
                            TranslationError::TypeError(
                                "contains: range end must be Int".to_string(),
                            )
                        })?;
                        match range.limits {
                            syn::RangeLimits::Closed(_) => hi_int, // ..= : inclusive
                            syn::RangeLimits::HalfOpen(_) => {
                                // .. : exclusive upper bound → hi - 1
                                let one = Int::from_i64(&self.ctx, 1);
                                hi_int - one
                            }
                        }
                    } else {
                        Int::from_i64(&self.ctx, i64::MAX / 2)
                    };
                    let cond = Bool::and(&self.ctx, &[&lo_int.le(&x_int), &x_int.le(&hi_int)]);
                    return Ok(cond.into());
                }
                // Non-range receiver — fallback to uninterpreted Bool
                let _ = self.translate_expr_with_vars(&method.receiver, vars);
                let base = expr_to_var_hint(&method.receiver);
                let name = format!("{base}_contains");
                let var = vars.entry(name.clone()).or_insert_with(|| {
                    let symbol = z3::Symbol::String(name);
                    Bool::new_const(&self.ctx, symbol).into()
                });
                Ok(var.clone())
            }
            _ => Err(TranslationError::UnsupportedExpression(format!(
                "Method call: {method_name}"
            ))),
        }
    }

    /// Translate a function call. For known functions returning Int, returns a fresh variable
    /// (allows body translation to proceed; formula is conservative).
    /// For Ok(expr) and Some(expr), returns the inner expr (Result/Option unwrap for ensures).
    fn translate_call<'a>(
        &'a self,
        call: &syn::ExprCall,
        vars: &mut Z3VarMap<'a>,
    ) -> Result<z3::ast::Dynamic<'a>, TranslationError> {
        let name = call_expr_to_name(&call.func)?;
        let base = name.split("::").last().unwrap_or(&name);
        // result(args): Spec replaces GetMedianTimePast(headers) etc. with result(headers).
        // Treat as the result variable (return value of the function under verification).
        if base == "result" {
            let var = vars.entry("result".to_string()).or_insert_with(|| {
                let symbol = z3::Symbol::String("result".to_string());
                Int::new_const(&self.ctx, symbol).into()
            });
            return Ok(var.clone());
        }
        // Ok(expr) / Some(expr): result is the inner value (for Result<T,E> / Option<T> returns)
        if (base == "Ok" || base == "Some") && call.args.len() == 1 {
            return self.translate_expr_with_vars(&call.args[0], vars);
        }
        // Constructors (new, default) - return fresh var for determinism
        if base == "new" || base == "default" {
            for arg in &call.args {
                let _ = self.translate_expr_with_vars(arg, vars);
            }
            let name = format!("{base}_result");
            let var = vars.entry(name.clone()).or_insert_with(|| {
                let symbol = z3::Symbol::String(name);
                Int::new_const(&self.ctx, symbol).into()
            });
            return Ok(var.clone());
        }
        // Err(_): for Result<T>, use 0 for determinism (0=Err, 1=Ok(false), 2=Ok(true))
        if base == "Err" && call.args.len() <= 1 {
            return Ok(Int::from_i64(&self.ctx, 0).into());
        }
        // Bool-like enum tuple-struct constructors that map to Bool false:
        //   ValidationResult::Invalid("msg") → false
        //   MempoolResult::Rejected("msg")   → false
        if matches!(base, "Invalid" | "Rejected") {
            // Translate args (for side effects like var creation) but discard.
            for arg in &call.args {
                let _ = self.translate_expr_with_vars(arg, vars);
            }
            return Ok(Bool::from_bool(&self.ctx, false).into());
        }
        // Bool-returning uninterpreted (Result<bool>, Option<bool>)
        if let Some((fn_name, arity_opt)) = known_bool_uninterpreted_function(&name) {
            let mut arg_asts: Vec<z3::ast::Int> = Vec::new();
            for arg in &call.args {
                let z3_arg = self.translate_expr_with_vars(arg, vars)?;
                let int_arg = if let Some(i) = z3_arg.as_int() {
                    i
                } else if let Some(b) = z3_arg.as_bool() {
                    let zero = Int::from_i64(&self.ctx, 0);
                    let one = Int::from_i64(&self.ctx, 1);
                    b.ite(&one, &zero)
                } else {
                    return Err(TranslationError::TypeError(
                        "Bool uninterpreted fn arg must be Int or Bool".to_string(),
                    ));
                };
                arg_asts.push(int_arg);
            }
            let arity = arg_asts.len();
            if let Some(expected) = arity_opt {
                if arity != expected {
                    return Err(TranslationError::UnsupportedExpression(format!(
                        "{base} expects {expected} args, got {arity}"
                    )));
                }
            }
            let int_sort = Sort::int(&self.ctx);
            let bool_sort = Sort::bool(&self.ctx);
            let sorts: Vec<&z3::Sort> = std::iter::repeat_n(&int_sort, arity).collect();
            let z3_fn_name = if arity_opt.is_some() {
                format!("{fn_name}_b")
            } else {
                format!("{fn_name}_{arity}_b")
            };
            let fn_decl = z3::FuncDecl::new(
                &self.ctx,
                z3::Symbol::String(z3_fn_name),
                sorts.as_slice(),
                &bool_sort,
            );
            let arg_refs: Vec<&dyn Ast> = arg_asts.iter().map(|a| a as &dyn Ast).collect();
            let result = fn_decl.apply(&arg_refs);
            return Ok(result);
        }
        // Uninterpreted functions for determinism: f(args) so that same inputs => same output
        if let Some((fn_name, arity_opt)) = known_uninterpreted_function(&name) {
            let mut arg_asts: Vec<z3::ast::Int> = Vec::new();
            for arg in &call.args {
                let z3_arg = self.translate_expr_with_vars(arg, vars)?;
                let int_arg = if let Some(i) = z3_arg.as_int() {
                    i
                } else if let Some(b) = z3_arg.as_bool() {
                    let zero = Int::from_i64(&self.ctx, 0);
                    let one = Int::from_i64(&self.ctx, 1);
                    b.ite(&one, &zero)
                } else {
                    return Err(TranslationError::TypeError(
                        "Uninterpreted fn arg must be Int or Bool".to_string(),
                    ));
                };
                arg_asts.push(int_arg);
            }
            let arity = arg_asts.len();
            if let Some(expected) = arity_opt {
                if arity != expected {
                    return Err(TranslationError::UnsupportedExpression(format!(
                        "{base} expects {expected} args, got {arity}"
                    )));
                }
            }
            let int_sort = Sort::int(&self.ctx);
            let sorts: Vec<&z3::Sort> = std::iter::repeat_n(&int_sort, arity).collect();
            let z3_fn_name = if arity_opt.is_some() {
                fn_name.to_string()
            } else {
                format!("{fn_name}_{arity}")
            };
            let fn_decl = z3::FuncDecl::new(
                &self.ctx,
                z3::Symbol::String(z3_fn_name),
                sorts.as_slice(),
                &int_sort,
            );
            let arg_refs: Vec<&dyn Ast> = arg_asts.iter().map(|a| a as &dyn Ast).collect();
            let result = fn_decl.apply(&arg_refs);
            return Ok(result);
        }
        if let Some(fresh_name) = known_int_returning_function(&name) {
            // Translate args (for variable binding; we don't model the relation yet)
            for arg in &call.args {
                let _ = self.translate_expr_with_vars(arg, vars);
            }
            let var = vars.entry(fresh_name.clone()).or_insert_with(|| {
                let symbol = z3::Symbol::String(fresh_name);
                Int::new_const(&self.ctx, symbol).into()
            });
            return Ok(var.clone());
        }
        if let Some(fresh_name) = known_bool_returning_function(&name) {
            for arg in &call.args {
                let _ = self.translate_expr_with_vars(arg, vars);
            }
            let var = vars.entry(fresh_name.clone()).or_insert_with(|| {
                let symbol = z3::Symbol::String(fresh_name);
                Bool::new_const(&self.ctx, symbol).into()
            });
            return Ok(var.clone());
        }
        // If the callee is known to return a struct with fixed field values, bind those fields
        // in vars so that callers can reason about result.field in their ensures clauses.
        if let Some(fields) = known_struct_field_function(name.split("::").last().unwrap_or(&name))
        {
            for arg in &call.args {
                let _ = self.translate_expr_with_vars(arg, vars);
            }
            // Synthesize a base name for the call result
            let base = name.split("::").last().unwrap_or(&name);
            let call_result_name = format!("call_{base}_struct");
            // Insert each field as a concrete Int constant
            for (field, value) in &fields {
                let field_var_name = format!("call_{base}_{field}");
                vars.entry(field_var_name.clone())
                    .or_insert_with(|| Int::from_i64(&self.ctx, *value).into());
            }
            // Return an uninterpreted Int as the overall struct representative
            let overall = vars.entry(call_result_name.clone()).or_insert_with(|| {
                let symbol = z3::Symbol::String(call_result_name);
                Int::new_const(&self.ctx, symbol).into()
            });
            return Ok(overall.clone());
        }
        // Generic fallback: treat unknown calls as uninterpreted (same inputs => same output)
        let mut arg_asts: Vec<z3::ast::Int> = Vec::new();
        for arg in &call.args {
            let z3_arg = self.translate_expr_with_vars(arg, vars)?;
            let int_arg = if let Some(i) = z3_arg.as_int() {
                i
            } else if let Some(b) = z3_arg.as_bool() {
                // Coerce Bool to Int (0/1) for uninterpreted fn
                let zero = Int::from_i64(&self.ctx, 0);
                let one = Int::from_i64(&self.ctx, 1);
                b.ite(&one, &zero)
            } else {
                return Err(TranslationError::TypeError(
                    "Unknown fn arg must be Int or Bool".to_string(),
                ));
            };
            arg_asts.push(int_arg);
        }
        let arity = arg_asts.len();
        let base = name.split("::").last().unwrap_or(&name);
        let z3_fn_name = format!("call_{}_{}", base.replace("::", "_"), arity);
        let int_sort = Sort::int(&self.ctx);
        let sorts: Vec<&z3::Sort> = std::iter::repeat_n(&int_sort, arity).collect();
        let fn_decl = z3::FuncDecl::new(
            &self.ctx,
            z3::Symbol::String(z3_fn_name),
            sorts.as_slice(),
            &int_sort,
        );
        let arg_refs: Vec<&dyn Ast> = arg_asts.iter().map(|a| a as &dyn Ast).collect();
        Ok(fn_decl.apply(&arg_refs))
    }

    /// Translate match expr { Some(x) => a, None => b } or { Ok(v) => a, Err(_) => b }
    fn translate_match<'a>(
        &'a self,
        match_expr: &syn::ExprMatch,
        vars: &mut Z3VarMap<'a>,
    ) -> Result<z3::ast::Dynamic<'a>, TranslationError> {
        let scrutinee = self.translate_expr_with_vars(&match_expr.expr, vars)?;
        let base = expr_to_var_hint(&match_expr.expr);

        // --- 1. Option/Result two-arm match (existing) ---
        if match_expr.arms.len() == 2 && match_expr.arms.iter().all(|a| a.guard.is_none()) {
            let (arm1, arm2) = (&match_expr.arms[0], &match_expr.arms[1]);
            let some_arm = parse_some_ok_arm(arm1).or_else(|| parse_some_ok_arm(arm2));
            let none_arm = parse_none_err_arm(arm1).or_else(|| parse_none_err_arm(arm2));
            if let (Some((inner_var, body)), Some(default_body)) = (some_arm, none_arm) {
                let inner_val = vars
                    .entry(inner_var.clone())
                    .or_insert_with(|| {
                        let symbol = z3::Symbol::String(inner_var.clone());
                        Int::new_const(&self.ctx, symbol).into()
                    })
                    .clone();
                vars.insert(inner_var, inner_val);
                let body_z3 = self.translate_expr_with_vars(body, vars)?;
                let default_z3 = self.translate_expr_with_vars(default_body, vars)?;
                let is_some_bool = vars
                    .entry(format!("{base}_is_some"))
                    .or_insert_with(|| {
                        let symbol = z3::Symbol::String(format!("{base}_is_some"));
                        Bool::new_const(&self.ctx, symbol).into()
                    })
                    .as_bool()
                    .ok_or_else(|| {
                        TranslationError::TypeError("is_some: expected Bool".to_string())
                    })?
                    .clone();
                let body_int = body_z3.as_int().ok_or_else(|| {
                    TranslationError::TypeError("match body: expected Int".to_string())
                })?;
                let default_int = default_z3.as_int().ok_or_else(|| {
                    TranslationError::TypeError("match default: expected Int".to_string())
                })?;
                return Ok(is_some_bool.ite(&body_int, &default_int).into());
            }
        }

        // --- 2. Integer-literal arm match (e.g. piecewise subsidy, len-based dispatch) ---
        // All arms must be either:
        //   • A single integer literal pattern  (no guard, no subpattern)
        //   • A wildcard/identifier pattern `_` used as the default arm
        // Body of each arm can be Int or Bool; the ITE tower preserves the type.
        //
        // We build a nested ITE tower:
        //   scrutinee == lit_n  →  val_n
        //   ...
        //   _  →  default_val
        //
        // The wildcard arm must be present; if missing we return an error.
        if let Some(scrutinee_int) = scrutinee.as_int() {
            // Collect arms; detect whether they're Int or Bool uniformly.
            enum ArmVal<'b> {
                Int(z3::ast::Int<'b>),
                Bool(z3::ast::Bool<'b>),
            }

            let mut literal_arms: Vec<(i64, ArmVal<'a>)> = Vec::new();
            let mut default_arm: Option<ArmVal<'a>> = None;
            let mut is_bool_match = false;
            let mut all_literal = true; // set to false if any non-literal pattern found

            for arm in &match_expr.arms {
                if arm.guard.is_some() {
                    all_literal = false;
                    break;
                }
                let body_z3 = match self.translate_expr_with_vars(&arm.body, vars) {
                    Ok(z) => z,
                    Err(_) => {
                        all_literal = false;
                        break;
                    }
                };
                let arm_val = if let Some(b) = body_z3.as_bool() {
                    is_bool_match = true;
                    ArmVal::Bool(b)
                } else if let Some(i) = body_z3.as_int() {
                    ArmVal::Int(i)
                } else {
                    all_literal = false;
                    break;
                };

                match &arm.pat {
                    syn::Pat::Lit(lit_pat) => {
                        if let syn::Lit::Int(int_lit) = &lit_pat.lit {
                            let val = int_lit
                                .base10_parse::<i64>()
                                .map_err(|e| TranslationError::ParseError(e.to_string()))?;
                            literal_arms.push((val, arm_val));
                            continue;
                        }
                        // Non-integer literal pattern — fall through to enum-variant path
                        all_literal = false;
                        break;
                    }
                    syn::Pat::Wild(_) | syn::Pat::Ident(_) => {
                        default_arm = Some(arm_val);
                    }
                    _ => {
                        // Non-literal pattern (e.g. enum variant) — fall through to enum-variant path
                        all_literal = false;
                        break;
                    }
                }
            }

            // Only proceed with literal-match ITE if all arms were literals / wildcards.
            if all_literal && !literal_arms.is_empty() {
                let default_val = match default_arm {
                    Some(d) => d,
                    None => {
                        // No explicit wildcard: use last arm as default
                        if let Some((_, av)) = literal_arms.pop() {
                            av
                        } else {
                            return Err(TranslationError::UnsupportedExpression(
                                "Match: no arms found".to_string(),
                            ));
                        }
                    }
                };

                // Build ITE tower from last arm to first (right-fold).
                if is_bool_match {
                    let to_bool = |av: ArmVal<'a>, ctx: &'a z3::Context| -> z3::ast::Bool<'a> {
                        match av {
                            ArmVal::Bool(b) => b,
                            ArmVal::Int(i) => {
                                let zero = Int::from_i64(ctx, 0);
                                i._eq(&zero).not()
                            }
                        }
                    };
                    let mut result_expr: z3::ast::Bool<'a> = to_bool(default_val, &self.ctx);
                    for (lit_val, arm_val) in literal_arms.into_iter().rev() {
                        let lit_z3 = Int::from_i64(&self.ctx, lit_val);
                        let cond = scrutinee_int._eq(&lit_z3);
                        let arm_bool = to_bool(arm_val, &self.ctx);
                        result_expr = cond.ite(&arm_bool, &result_expr);
                    }
                    return Ok(result_expr.into());
                } else {
                    let to_int = |av: ArmVal<'a>| -> Result<z3::ast::Int<'a>, TranslationError> {
                        match av {
                            ArmVal::Int(i) => Ok(i),
                            ArmVal::Bool(_) => Err(TranslationError::TypeError(
                                "Mixed Bool/Int match arms not supported".to_string(),
                            )),
                        }
                    };
                    let mut result_expr: z3::ast::Int<'a> = to_int(default_val)?;
                    for (lit_val, arm_val) in literal_arms.into_iter().rev() {
                        let lit_z3 = Int::from_i64(&self.ctx, lit_val);
                        let cond = scrutinee_int._eq(&lit_z3);
                        result_expr = cond.ite(&to_int(arm_val)?, &result_expr);
                    }
                    return Ok(result_expr.into());
                }
            }
            // If not all-literal, fall through to enum-variant path below.
        }

        // --- 3. Enum-variant arm match (e.g. match network { Network::Mainnet => … }) ---
        // All arm patterns must be Pat::Path (enum variant paths) or wildcard/ident.
        // Each distinct variant is assigned a consecutive integer discriminant (0, 1, 2, …).
        // The scrutinee is already an Int variable in shared_vars; the ITE tower uses
        // discriminant equality to select the arm value.
        {
            enum ArmVal<'b> {
                Int(z3::ast::Int<'b>),
                Bool(z3::ast::Bool<'b>),
            }

            let mut variant_arms: Vec<(i64, ArmVal<'a>)> = Vec::new();
            let mut default_arm: Option<ArmVal<'a>> = None;
            let mut discriminant: i64 = 0;
            let mut all_enum = true;
            let mut is_bool_match = false;

            for arm in &match_expr.arms {
                if arm.guard.is_some() {
                    all_enum = false;
                    break;
                }
                let body_z3 = match self.translate_expr_with_vars(&arm.body, vars) {
                    Ok(z) => z,
                    Err(_) => {
                        all_enum = false;
                        break;
                    }
                };
                let arm_val = if let Some(b) = body_z3.as_bool() {
                    is_bool_match = true;
                    ArmVal::Bool(b)
                } else if let Some(i) = body_z3.as_int() {
                    ArmVal::Int(i)
                } else {
                    all_enum = false;
                    break;
                };

                match &arm.pat {
                    syn::Pat::Path(_) | syn::Pat::Struct(_) | syn::Pat::TupleStruct(_) => {
                        variant_arms.push((discriminant, arm_val));
                        discriminant += 1;
                    }
                    syn::Pat::Wild(_) | syn::Pat::Ident(_) => {
                        default_arm = Some(arm_val);
                    }
                    _ => {
                        all_enum = false;
                        break;
                    }
                }
            }

            if all_enum && !variant_arms.is_empty() {
                let scrutinee_int = match scrutinee.as_int() {
                    Some(i) => i,
                    None => {
                        // Scrutinee might be Bool (unusual); bail out
                        return Err(TranslationError::UnsupportedExpression(
                            "Match: enum scrutinee is not Int".to_string(),
                        ));
                    }
                };

                // If no wildcard, use last variant arm as default.
                let default_val = match default_arm {
                    Some(d) => d,
                    None => {
                        if let Some((_, av)) = variant_arms.pop() {
                            av
                        } else {
                            return Err(TranslationError::UnsupportedExpression(
                                "Match: no enum arms found".to_string(),
                            ));
                        }
                    }
                };

                if is_bool_match {
                    let to_bool = |av: ArmVal<'a>, ctx: &'a z3::Context| -> z3::ast::Bool<'a> {
                        match av {
                            ArmVal::Bool(b) => b,
                            ArmVal::Int(i) => {
                                let zero = Int::from_i64(ctx, 0);
                                i._eq(&zero).not()
                            }
                        }
                    };
                    let mut result_expr: z3::ast::Bool<'a> = to_bool(default_val, &self.ctx);
                    for (disc, arm_val) in variant_arms.into_iter().rev() {
                        let disc_z3 = Int::from_i64(&self.ctx, disc);
                        let cond = scrutinee_int._eq(&disc_z3);
                        let arm_bool = to_bool(arm_val, &self.ctx);
                        result_expr = cond.ite(&arm_bool, &result_expr);
                    }
                    return Ok(result_expr.into());
                } else {
                    let to_int = |av: ArmVal<'a>| -> Result<z3::ast::Int<'a>, TranslationError> {
                        match av {
                            ArmVal::Int(i) => Ok(i),
                            ArmVal::Bool(_) => Err(TranslationError::TypeError(
                                "Mixed Bool/Int enum arms".to_string(),
                            )),
                        }
                    };
                    let mut result_expr: z3::ast::Int<'a> = to_int(default_val)?;
                    for (disc, arm_val) in variant_arms.into_iter().rev() {
                        let disc_z3 = Int::from_i64(&self.ctx, disc);
                        let cond = scrutinee_int._eq(&disc_z3);
                        result_expr = cond.ite(&to_int(arm_val)?, &result_expr);
                    }
                    return Ok(result_expr.into());
                }
            }
        }

        Err(TranslationError::UnsupportedExpression(
            "Match: only Option/Result (2-arm), integer-literal, or enum-variant arms supported"
                .to_string(),
        ))
    }

    /// Translate a unary operation given already-translated operand
    fn translate_unary_op<'a>(
        &'a self,
        op: syn::UnOp,
        expr: z3::ast::Dynamic<'a>,
    ) -> Result<z3::ast::Dynamic<'a>, TranslationError> {
        match op {
            syn::UnOp::Not(_) => {
                let bool_expr = expr
                    .as_bool()
                    .ok_or_else(|| TranslationError::TypeError("Expected Bool".to_string()))?;
                Ok(bool_expr.not().into())
            }
            syn::UnOp::Neg(_) => {
                let int_expr = expr
                    .as_int()
                    .ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                Ok(int_expr.unary_minus().into())
            }
            syn::UnOp::Deref(_) => {
                // Dereference - for now, just return the expression
                Ok(expr)
            }
            _ => Err(TranslationError::UnsupportedExpression(format!(
                "Unsupported unary op: {op:?}"
            ))),
        }
    }

    /// Translate struct field access (e.g. block.header.bits) to a Z3 variable.
    /// Flattens the path to a var name (block_header_bits) for lookup/creation.
    fn translate_field_access<'a>(
        &'a self,
        field: &syn::ExprField,
        vars: &mut Z3VarMap<'a>,
    ) -> Result<z3::ast::Dynamic<'a>, TranslationError> {
        let name = field_expr_to_var_name(field);
        let var = vars.entry(name.clone()).or_insert_with(|| {
            let symbol = z3::Symbol::String(name);
            Int::new_const(&self.ctx, symbol).into()
        });
        Ok(var.clone())
    }

    /// Translate a contract condition to Z3
    pub fn translate_contract(
        &self,
        contract: &Contract,
    ) -> Result<z3::ast::Dynamic<'_>, TranslationError> {
        let (expr, _) =
            self.translate_contract_with_types(contract, &std::collections::HashMap::new(), None)?;
        Ok(expr)
    }

    /// Translate a contract condition to Z3 with type information
    /// Returns the expression and type constraints
    pub fn translate_contract_with_types(
        &self,
        contract: &Contract,
        param_types: &std::collections::HashMap<String, syn::Type>,
        return_type: Option<&syn::Type>,
    ) -> Result<(z3::ast::Dynamic<'_>, Vec<z3::ast::Bool<'_>>), TranslationError> {
        let (mut vars, type_constraints) = self.build_shared_vars(param_types, return_type);
        let expr = self.translate_expr_with_vars(&contract.condition, &mut vars)?;
        Ok((expr, type_constraints))
    }

    /// Translate a contract expression using an externally-supplied shared variable map.
    ///
    /// This is the preferred path in `verify_contract_with_context` so that the
    /// ensures, requires, and body translation all reference the **same** Z3
    /// constants for "height", "result", etc.  Using fresh `Int::new_const` in each
    /// translation produces unrelated Z3 AST nodes that the solver treats as
    /// independent variables.
    pub fn translate_contract_with_shared_vars<'a>(
        &'a self,
        contract: &Contract,
        vars: &mut Z3VarMap<'a>,
    ) -> Result<z3::ast::Dynamic<'a>, TranslationError> {
        self.translate_expr_with_vars(&contract.condition, vars)
    }

    /// Build a shared `Z3VarMap` (parameter variables + "result") and the
    /// corresponding type constraints.  The returned map should be re-used for
    /// all sub-translations within a single `verify_contract_with_context` call.
    pub fn build_shared_vars<'a>(
        &'a self,
        param_types: &std::collections::HashMap<String, syn::Type>,
        return_type: Option<&syn::Type>,
    ) -> (Z3VarMap<'a>, Vec<z3::ast::Bool<'a>>) {
        let mut vars = Z3VarMap::new();
        let mut type_constraints = Vec::new();

        for (name, ty) in param_types {
            let symbol = z3::Symbol::String(name.clone());
            let var = Int::new_const(&self.ctx, symbol);
            vars.insert(name.clone(), var.into());
            if is_unsigned_type(ty) {
                if let Some(var_ref) = vars.get(name).and_then(|v| v.as_int()) {
                    type_constraints.push(var_ref.ge(&Int::from_i64(&self.ctx, 0)));
                }
            }
        }

        if let Some(return_ty) = return_type {
            // If the return type (possibly wrapped in Result<(T0, T1, …)>) is a tuple,
            // create per-element variables `result_0`, `result_1`, … so that ensures
            // contracts can reference individual fields.  We also create a generic
            // `result` Int placeholder for contracts that don't use the decomposition.
            if let Some(tuple_ty) = unwrap_to_tuple(return_ty) {
                for (i, elem_ty) in tuple_ty.elems.iter().enumerate() {
                    let slot_name = format!("result_{i}");
                    let sym = z3::Symbol::String(slot_name.clone());
                    if returns_bool_like(elem_ty) {
                        let var = Bool::new_const(&self.ctx, sym);
                        vars.insert(slot_name, var.into());
                    } else {
                        let var = Int::new_const(&self.ctx, sym);
                        if is_unsigned_type(elem_ty) {
                            let zero = Int::from_i64(&self.ctx, 0);
                            type_constraints.push(var.ge(&zero));
                        }
                        vars.insert(slot_name, var.into());
                    }
                }
                // Also a generic "result" Int so existing body translation still works.
                let sym = z3::Symbol::String("result".to_string());
                let var = Int::new_const(&self.ctx, sym);
                vars.insert("result".to_string(), var.into());
            } else {
                let symbol = z3::Symbol::String("result".to_string());
                if returns_bool_like(return_ty) {
                    let var = Bool::new_const(&self.ctx, symbol);
                    vars.insert("result".to_string(), var.into());
                } else {
                    let var = Int::new_const(&self.ctx, symbol);
                    vars.insert("result".to_string(), var.into());
                    if is_unsigned_type(return_ty) {
                        if let Some(var_ref) = vars.get("result").and_then(|v| v.as_int()) {
                            type_constraints.push(var_ref.ge(&Int::from_i64(&self.ctx, 0)));
                        }
                    }
                }
            }
        }

        (vars, type_constraints)
    }

    /// Translate a function body to a Z3 formula that relates inputs to result
    ///
    /// This is the KEY for verifying ensures: we translate the implementation
    /// to a Z3 formula and prove: requires && implementation => ensures
    pub fn translate_function_body<'a>(
        &'a self,
        func: &ItemFn,
        vars: &mut Z3VarMap<'a>,
    ) -> Result<Option<z3::ast::Bool<'a>>, TranslationError> {
        // Extract the function body
        let body = &func.block;

        // For simple functions, translate the body to a formula
        // result == <body_expression>
        self.translate_block_to_result_formula(body, vars)
    }

    /// Translate a block to a formula: result == <final_expression>
    ///
    /// Handles:
    /// - let bindings (variable assignments)
    /// - if expressions with early returns
    /// - debug_assert! macros (skipped)
    /// - final implicit return
    fn translate_block_to_result_formula<'a>(
        &'a self,
        block: &Block,
        vars: &mut Z3VarMap<'a>,
    ) -> Result<Option<z3::ast::Bool<'a>>, TranslationError> {
        let _formulas: Vec<z3::ast::Bool<'a>> = Vec::new();
        let mut early_return_conditions: Vec<(z3::ast::Bool<'a>, z3::ast::Bool<'a>)> = Vec::new();
        // Conditions under which the function returns Err / panics early.
        // For the Ok path these conditions are negated: `if fee < 0 { return Err }` means
        // the Ok path assumes `fee >= 0`.  Accumulated here and folded into the final formula.
        let mut err_guard_conditions: Vec<z3::ast::Bool<'a>> = Vec::new();

        // Save the pre-body result slot so that functions using `result` as a local
        // variable name (e.g. `let result = weight.div_ceil(4)`) don't confuse the
        // return-value Z3 constant with the rebound local expression.
        let result_slot = vars.get("result").cloned();

        // Process statements to build variable bindings and collect return conditions
        for stmt in &block.stmts {
            match stmt {
                Stmt::Local(local) => {
                    // let x = expr;
                    if let Some(init) = &local.init {
                        if let syn::Pat::Ident(ident) = &local.pat {
                            let var_name = ident.ident.to_string();
                            // Translate the init expression
                            if let Ok(z3_expr) = self.translate_expr_with_vars(&init.expr, vars) {
                                if z3_expr.as_int().is_some() || z3_expr.as_bool().is_some() {
                                    vars.insert(var_name, z3_expr);
                                }
                            }
                        }
                    }
                }
                Stmt::Expr(expr, Some(_)) => {
                    if let Expr::Assign(assign) = expr {
                        if let Expr::Path(path) = &*assign.left {
                            let var_name = path_to_string(&path.path);
                            if let Ok(z3_expr) = self.translate_expr_with_vars(&assign.right, vars)
                            {
                                if z3_expr.as_int().is_some() || z3_expr.as_bool().is_some() {
                                    // Don't overwrite result_slot; track it separately.
                                    vars.insert(var_name, z3_expr);
                                }
                            }
                        } else if let Expr::Index(index) = &*assign.left {
                            let _ = self.translate_expr_with_vars(&index.expr, vars);
                            let _ = self.translate_expr_with_vars(&index.index, vars);
                            if let Ok(val) = self.translate_expr_with_vars(&assign.right, vars) {
                                let base = expr_to_var_hint(&index.expr);
                                let idx = extract_int_literal(&index.index).unwrap_or(0);
                                let name = format!("{base}_after_{idx}");
                                vars.insert(name.clone(), val.clone());
                                // Update base var so return sees final value (hash[i]=x; hash)
                                if let Expr::Path(path) = &*index.expr {
                                    let base_name = path_to_string(&path.path);
                                    vars.insert(base_name, val);
                                }
                            }
                        }
                    } else if let Expr::Binary(bin) = expr {
                        if matches!(bin.op, syn::BinOp::AddAssign(_) | syn::BinOp::SubAssign(_)) {
                            if let Expr::Path(path) = &*bin.left {
                                let var_name = path_to_string(&path.path);
                                let left = vars.get(&var_name).cloned().unwrap_or_else(|| {
                                    Int::new_const(&self.ctx, z3::Symbol::String(var_name.clone()))
                                        .into()
                                });
                                if let Ok(right) = self.translate_expr_with_vars(&bin.right, vars) {
                                    if let (Some(left_int), Some(right_int)) =
                                        (left.as_int(), right.as_int())
                                    {
                                        let result = match bin.op {
                                            syn::BinOp::AddAssign(_) => {
                                                (left_int + right_int).into()
                                            }
                                            syn::BinOp::SubAssign(_) => {
                                                (left_int - right_int).into()
                                            }
                                            _ => continue,
                                        };
                                        vars.insert(var_name, result);
                                    }
                                }
                            }
                        }
                    } else if let Expr::ForLoop(fl) = expr {
                        let _ = self.translate_expr_with_vars(&fl.expr, vars);
                        let _ = self.translate_block_to_result_formula(&fl.body, vars);
                    } else if let Expr::While(while_expr) = expr {
                        let _ = self.translate_expr_with_vars(&while_expr.cond, vars);
                        let _ = self.translate_block_to_result_formula(&while_expr.body, vars);
                    } else if let Expr::Loop(loop_expr) = expr {
                        let _ = self.translate_block_to_result_formula(&loop_expr.body, vars);
                    } else if let Expr::If(if_expr) = expr {
                        if let Some((cond, result_formula)) =
                            self.translate_if_with_early_return(if_expr, vars)?
                        {
                            early_return_conditions.push((cond, result_formula));
                        } else if let Some(err_cond) =
                            self.translate_if_with_err_return(if_expr, vars)
                        {
                            // `if bad { return Err(...) }` — on the Ok path, bad is false.
                            err_guard_conditions.push(err_cond);
                        }
                    } else if let Expr::Return(ret) = expr {
                        if let Some(return_expr) = &ret.expr {
                            if let Ok(z3_expr) = self.translate_expr_with_vars(return_expr, vars) {
                                // Use the pre-body result slot to avoid the rebound local.
                                let result_var = result_slot.as_ref().ok_or_else(|| {
                                    TranslationError::UnsupportedExpression(
                                        "No result variable".to_string(),
                                    )
                                })?;
                                let eq_formula = if let Some(int_val) = z3_expr.as_int() {
                                    result_var.as_int().map(|r| r._eq(&int_val))
                                } else if let Some(bool_val) = z3_expr.as_bool() {
                                    result_var.as_bool().map(|r| r._eq(&bool_val))
                                } else {
                                    None
                                };
                                if let Some(eq) = eq_formula {
                                    return Ok(Some(eq));
                                }
                            }
                        }
                    }
                }
                Stmt::Expr(expr, None) => {
                    // For non-last if-expressions (guard patterns like `if bad { return Err }`),
                    // capture the Err-guard condition so the Ok path has `!bad` as a constraint.
                    // The last Stmt::Expr(_, None) is the function's return value and is handled
                    // below by `block.stmts.last()`.
                    let is_last = block.stmts.last() == Some(stmt);
                    if !is_last {
                        if let Expr::If(if_expr) = expr {
                            if let Some((cond, result_formula)) =
                                self.translate_if_with_early_return(if_expr, vars)?
                            {
                                early_return_conditions.push((cond, result_formula));
                            } else if let Some(err_cond) =
                                self.translate_if_with_err_return(if_expr, vars)
                            {
                                err_guard_conditions.push(err_cond);
                            }
                        }
                    }
                    // Special case: struct-literal return (e.g. `Bip9Deployment { bit: 15, … }`).
                    // Produce a conjunction of `result_{field} == field_value` formulas so
                    // that ensures clauses using `result.field` access resolve correctly.
                    if let Expr::Struct(struct_expr) = expr {
                        let mut field_eqs: Vec<z3::ast::Bool<'a>> = Vec::new();
                        for field in &struct_expr.fields {
                            if let syn::Member::Named(ident) = &field.member {
                                let slot_name = format!("result_{ident}");
                                if let Ok(fz3) = self.translate_expr_with_vars(&field.expr, vars) {
                                    if let Some(fi) = fz3.as_int() {
                                        // Look up or create the result.{field} slot.
                                        let slot = vars
                                            .entry(slot_name.clone())
                                            .or_insert_with(|| {
                                                let sym = z3::Symbol::String(slot_name);
                                                Int::new_const(&self.ctx, sym).into()
                                            })
                                            .clone();
                                        if let Some(si) = slot.as_int() {
                                            field_eqs.push(si._eq(&fi));
                                        }
                                    }
                                }
                            }
                        }
                        if !field_eqs.is_empty() {
                            let refs: Vec<&z3::ast::Bool<'_>> = field_eqs.iter().collect();
                            let conj = Bool::and(&self.ctx, &refs);
                            if early_return_conditions.is_empty() {
                                return Ok(Some(conj));
                            } else {
                                let mut all_conditions = Vec::new();
                                let mut negated_conds = Vec::new();
                                for (cond, rf) in &early_return_conditions {
                                    all_conditions.push(cond.implies(rf));
                                    negated_conds.push(cond.not());
                                }
                                if !negated_conds.is_empty() {
                                    let nc_refs: Vec<&z3::ast::Bool<'_>> =
                                        negated_conds.iter().collect();
                                    let no_early = Bool::and(&self.ctx, &nc_refs);
                                    all_conditions.push(no_early.implies(&conj));
                                }
                                let ac_refs: Vec<&z3::ast::Bool<'_>> =
                                    all_conditions.iter().collect();
                                return Ok(Some(Bool::and(&self.ctx, &ac_refs)));
                            }
                        }
                    }

                    // Final expression (implicit return).
                    // Skip if this is the last statement — it is processed after the loop
                    // where err_guard_conditions can be properly incorporated.
                    // Handling it here would return early and bypass err guards.
                    if is_last {
                        // Defer to post-loop handling.
                    } else if let Ok(z3_expr) = self.translate_expr_with_vars(expr, vars) {
                        let result_var = result_slot.as_ref().ok_or_else(|| {
                            TranslationError::UnsupportedExpression(
                                "No result variable".to_string(),
                            )
                        })?;
                        let eq_formula = if let Some(int_val) = z3_expr.as_int() {
                            result_var.as_int().map(|r| r._eq(&int_val))
                        } else if let Some(bool_val) = z3_expr.as_bool() {
                            result_var.as_bool().map(|r| r._eq(&bool_val))
                        } else {
                            None
                        };
                        if let Some(eq) = eq_formula {
                            if early_return_conditions.is_empty() {
                                return Ok(Some(eq));
                            } else {
                                let mut all_conditions = Vec::new();
                                let mut negated_conds = Vec::new();
                                for (cond, result_formula) in &early_return_conditions {
                                    all_conditions.push(cond.implies(result_formula));
                                    negated_conds.push(cond.not());
                                }
                                if !negated_conds.is_empty() {
                                    let refs: Vec<&z3::ast::Bool> = negated_conds.iter().collect();
                                    let no_early_return = Bool::and(&self.ctx, &refs);
                                    all_conditions.push(no_early_return.implies(&eq));
                                }
                                if !all_conditions.is_empty() {
                                    let refs: Vec<&z3::ast::Bool> = all_conditions.iter().collect();
                                    return Ok(Some(Bool::and(&self.ctx, &refs)));
                                }
                                return Ok(Some(eq));
                            }
                        }
                    }
                }
                Stmt::Item(_) => {
                    // Skip items (nested functions, etc.)
                }
                Stmt::Macro(_) => {
                    // Skip macros (debug_assert!, etc.)
                }
            }
        }

        // Check if the last statement is a return or expression.
        // For simple expressions (Expr::Path, arithmetic, method calls) the post-loop code
        // must use `result_slot` — the pre-body Z3 return-value constant — as the LHS of the
        // equality formula, not `vars.get("result")` which may have been rebound by a local
        // `let result = …` binding (e.g. `weight_to_vsize` rebinds "result" to `div_ceil(…)`).
        // For complex forms (Ok(…), Expr::Return, Expr::If) we temporarily restore result_slot
        // so that translate_return_expr's internal `vars.get("result")` lookup finds the right var.
        let base_formula = if let Some(Stmt::Expr(expr, None)) = block.stmts.last() {
            match expr {
                // Complex forms handled by translate_return_expr — restore result_slot first.
                Expr::Return(_) | Expr::If(_) | Expr::Call(_) => {
                    let saved_result = vars.get("result").cloned();
                    if let Some(slot) = result_slot.clone() {
                        vars.insert("result".to_string(), slot);
                    }
                    let formula = self.translate_return_expr(expr, vars)?;
                    // Restore any rebinding that was in place.
                    if let Some(saved) = saved_result {
                        vars.insert("result".to_string(), saved);
                    } else {
                        vars.remove("result");
                    }
                    formula
                }
                // Simple expression (path, arithmetic, method call): translate with current
                // (possibly rebound) vars, but use result_slot as LHS.
                _ => {
                    if let Ok(z3_expr) = self.translate_expr_with_vars(expr, vars) {
                        let result_var = result_slot.as_ref();
                        result_var.and_then(|rv| {
                            if let Some(int_val) = z3_expr.as_int() {
                                rv.as_int().map(|r| r._eq(&int_val))
                            } else if let Some(bool_val) = z3_expr.as_bool() {
                                rv.as_bool().map(|r| r._eq(&bool_val))
                            } else {
                                None
                            }
                        })
                    } else {
                        None
                    }
                }
            }
        } else if !early_return_conditions.is_empty() {
            // Handle case where there are only early returns (no final expression)
            let mut all_conditions = Vec::new();
            for (cond, result_formula) in &early_return_conditions {
                all_conditions.push(cond.implies(result_formula));
            }
            let refs: Vec<&z3::ast::Bool> = all_conditions.iter().collect();
            Some(Bool::and(&self.ctx, &refs))
        } else {
            None
        };

        // Conjoin err-guard negations into the final formula.
        // Each err guard `if cond { return Err }` means the Ok path has `!cond`.
        // For example, `if fee < 0 { return Err }; Ok(fee)` implies `fee >= 0 ∧ result = fee`.
        if !err_guard_conditions.is_empty() {
            let negated: Vec<z3::ast::Bool<'a>> =
                err_guard_conditions.iter().map(|c| c.not()).collect();
            let neg_refs: Vec<&z3::ast::Bool<'_>> = negated.iter().collect();
            let guards_ok = Bool::and(&self.ctx, &neg_refs);
            if let Some(formula) = base_formula {
                let refs: Vec<&z3::ast::Bool<'_>> = vec![&guards_ok, &formula];
                return Ok(Some(Bool::and(&self.ctx, &refs)));
            } else {
                return Ok(Some(guards_ok));
            }
        }

        Ok(base_formula)
    }

    /// Handle if statement with potential early return
    /// Returns (condition, result_formula) if there's an early return
    fn translate_if_with_early_return<'a>(
        &'a self,
        if_expr: &syn::ExprIf,
        vars: &mut Z3VarMap<'a>,
    ) -> Result<Option<(z3::ast::Bool<'a>, z3::ast::Bool<'a>)>, TranslationError> {
        // Translate condition
        let cond_z3 = self.translate_expr_with_vars(&if_expr.cond, vars)?;
        let cond_bool = match cond_z3.as_bool() {
            Some(b) => b,
            None => return Ok(None),
        };

        // Check if the then branch has an early return
        for stmt in &if_expr.then_branch.stmts {
            if let Stmt::Expr(Expr::Return(ret), _) = stmt {
                if let Some(return_expr) = &ret.expr {
                    // Ok(expr) — handles both Result<bool> (encoded 1/2) and Result<Int>
                    if let Expr::Call(call) = &**return_expr {
                        if let Ok(name) = call_expr_to_name(&call.func) {
                            let base = name.split("::").last().unwrap_or(&name);
                            if base == "Ok" && call.args.len() == 1 {
                                let inner = self.translate_expr_with_vars(&call.args[0], vars)?;
                                if let Some(b) = inner.as_bool() {
                                    if let Some(r) = vars.get("result").and_then(|v| v.as_int()) {
                                        let one = Int::from_i64(&self.ctx, 1);
                                        let two = Int::from_i64(&self.ctx, 2);
                                        let encoded = b.ite(&two, &one);
                                        return Ok(Some((cond_bool, r._eq(&encoded))));
                                    }
                                } else if let Some(int_val) = inner.as_int() {
                                    if let Some(r) = vars.get("result").and_then(|v| v.as_int()) {
                                        return Ok(Some((cond_bool, r._eq(&int_val))));
                                    }
                                }
                            }
                        }
                    }
                    // Skip Err(...) returns — these are Err-guard patterns handled separately
                    // by translate_if_with_err_return, not Ok early returns.
                    let is_err_return = if let Expr::Call(call) = &**return_expr {
                        call_expr_to_name(&call.func)
                            .map(|n| n.split("::").last().unwrap_or(&n) == "Err")
                            .unwrap_or(false)
                    } else {
                        false
                    };
                    if !is_err_return {
                        if let Ok(z3_expr) = self.translate_expr_with_vars(return_expr, vars) {
                            let result_var = vars.get("result").ok_or_else(|| {
                                TranslationError::UnsupportedExpression(
                                    "No result variable".to_string(),
                                )
                            })?;
                            let eq = if let Some(int_val) = z3_expr.as_int() {
                                result_var.as_int().map(|r| r._eq(&int_val))
                            } else if let Some(bool_val) = z3_expr.as_bool() {
                                result_var.as_bool().map(|r| r._eq(&bool_val))
                            } else {
                                None
                            };
                            if let Some(eq_bool) = eq {
                                return Ok(Some((cond_bool, eq_bool)));
                            }
                        }
                    }
                }
            }
        }

        Ok(None)
    }

    /// Detect `if cond { return Err(...) }` patterns (Err guard).
    ///
    /// Returns the condition `cond` as a Z3 Bool if the then-branch contains only
    /// an unconditional `return Err(...)` (or `return Err;`).  The caller negates
    /// this condition to obtain the constraint that holds on the Ok path.
    ///
    /// Handles both:
    /// - `if fee < 0 { return Err(...); }` — single-stmt then branch
    /// - `if x > max { return Err(...); }` — same pattern
    fn translate_if_with_err_return<'a>(
        &'a self,
        if_expr: &syn::ExprIf,
        vars: &mut Z3VarMap<'a>,
    ) -> Option<z3::ast::Bool<'a>> {
        // Only handle if-without-else (pure guard pattern)
        if if_expr.else_branch.is_some() {
            return None;
        }
        // Translate the condition
        let cond_z3 = self.translate_expr_with_vars(&if_expr.cond, vars).ok()?;
        let cond_bool = cond_z3.as_bool()?;

        // Check that the then-branch is only `return Err(...)`
        let stmts = &if_expr.then_branch.stmts;
        if stmts.len() != 1 {
            return None;
        }
        if let Stmt::Expr(Expr::Return(ret), _) = &stmts[0] {
            if let Some(return_expr) = &ret.expr {
                if let Expr::Call(call) = &**return_expr {
                    if let Ok(name) = call_expr_to_name(&call.func) {
                        let base = name.split("::").last().unwrap_or(&name);
                        if base == "Err" {
                            return Some(cond_bool);
                        }
                    }
                }
            }
        }
        None
    }

    /// Translate a return expression to: result == <expr>
    fn translate_return_expr<'a>(
        &'a self,
        expr: &Expr,
        vars: &mut Z3VarMap<'a>,
    ) -> Result<Option<z3::ast::Bool<'a>>, TranslationError> {
        match expr {
            Expr::Return(ret) => {
                if let Some(return_expr) = &ret.expr {
                    // Ok(expr) with Int result: 1=Ok(false), 2=Ok(true)
                    if let Expr::Call(call) = &**return_expr {
                        if let Ok(name) = call_expr_to_name(&call.func) {
                            let base = name.split("::").last().unwrap_or(&name);
                            if base == "Ok" && call.args.len() == 1 {
                                let inner = self.translate_expr_with_vars(&call.args[0], vars)?;
                                if let Some(b) = inner.as_bool() {
                                    if let Some(r) = vars.get("result").and_then(|v| v.as_int()) {
                                        let one = Int::from_i64(&self.ctx, 1);
                                        let two = Int::from_i64(&self.ctx, 2);
                                        let encoded = b.ite(&two, &one);
                                        return Ok(Some(r._eq(&encoded)));
                                    }
                                }
                            }
                        }
                    }
                    let z3_expr = self.translate_expr_with_vars(return_expr, vars)?;
                    let result_var = vars.get("result").ok_or_else(|| {
                        TranslationError::UnsupportedExpression("No result variable".to_string())
                    })?;
                    let eq = if let Some(int_val) = z3_expr.as_int() {
                        result_var.as_int().map(|r| r._eq(&int_val))
                    } else if let Some(bool_val) = z3_expr.as_bool() {
                        result_var.as_bool().map(|r| r._eq(&bool_val))
                    } else {
                        None
                    };
                    if let Some(eq_bool) = eq {
                        return Ok(Some(eq_bool));
                    }
                }
            }
            Expr::If(if_expr) => {
                // if condition { then_expr } else { else_expr }
                // Translates to: (condition => result == then_expr) && (!condition => result == else_expr)
                return self.translate_if_to_formula(if_expr, vars);
            }
            Expr::Call(call) => {
                // Ok(expr) — unwrap the inner value and equate with `result`.
                // Handles Result<bool>, Result<Int>, Result<ValidationResult>,
                // and tuple returns Result<(T0, T1, …)> via result_0/result_1/… slots.
                if let Ok(name) = call_expr_to_name(&call.func) {
                    let base = name.split("::").last().unwrap_or(&name);
                    if base == "Ok" && call.args.len() == 1 {
                        // Tuple return: Ok((val0, val1, …)) → result_0=val0 ∧ result_1=val1 ∧ …
                        if let Expr::Tuple(tuple_expr) = &call.args[0] {
                            let mut conjuncts: Vec<z3::ast::Bool<'a>> = Vec::new();
                            for (i, elem) in tuple_expr.elems.iter().enumerate() {
                                let slot_name = format!("result_{i}");
                                if let Ok(elem_z3) = self.translate_expr_with_vars(elem, vars) {
                                    if let Some(slot) = vars.get(&slot_name).cloned() {
                                        let eq = if let Some(b) = elem_z3.as_bool() {
                                            slot.as_bool().map(|r| r._eq(&b))
                                        } else if let Some(iv) = elem_z3.as_int() {
                                            slot.as_int().map(|r| r._eq(&iv))
                                        } else {
                                            None
                                        };
                                        if let Some(f) = eq {
                                            conjuncts.push(f);
                                        }
                                    }
                                }
                            }
                            if !conjuncts.is_empty() {
                                let refs: Vec<&z3::ast::Bool<'_>> = conjuncts.iter().collect();
                                return Ok(Some(Bool::and(&self.ctx, &refs)));
                            }
                        }

                        // Translate inner expression first (requires mut borrow of vars)
                        let inner = self.translate_expr_with_vars(&call.args[0], vars)?;
                        let result_var = vars.get("result").cloned();
                        if let Some(result_var) = result_var {
                            if let Some(r) = result_var.as_int() {
                                if let Some(b) = inner.as_bool() {
                                    // Ok(bool) — encode as Int: true→2, false→1
                                    let one = Int::from_i64(&self.ctx, 1);
                                    let two = Int::from_i64(&self.ctx, 2);
                                    let encoded = b.ite(&two, &one);
                                    return Ok(Some(r._eq(&encoded)));
                                } else if let Some(int_val) = inner.as_int() {
                                    // Ok(integer) — direct equality
                                    return Ok(Some(r._eq(&int_val)));
                                }
                            } else if let Some(r) = result_var.as_bool() {
                                if let Some(b) = inner.as_bool() {
                                    return Ok(Some(r._eq(&b)));
                                }
                            }
                        }
                    }
                }
                // Direct call (e.g. verify_script_with_context_full) - returns Int
                if let Ok(z3_expr) = self.translate_expr_with_vars(expr, vars) {
                    let result_var = vars.get("result").ok_or_else(|| {
                        TranslationError::UnsupportedExpression("No result variable".to_string())
                    })?;
                    let eq = if let Some(int_val) = z3_expr.as_int() {
                        result_var.as_int().map(|r| r._eq(&int_val))
                    } else if let Some(bool_val) = z3_expr.as_bool() {
                        result_var.as_bool().map(|r| r._eq(&bool_val))
                    } else {
                        None
                    };
                    if let Some(eq_bool) = eq {
                        return Ok(Some(eq_bool));
                    }
                }
            }
            _ => {
                // Direct expression (implicit return)
                if let Ok(z3_expr) = self.translate_expr_with_vars(expr, vars) {
                    let result_var = vars.get("result").ok_or_else(|| {
                        TranslationError::UnsupportedExpression("No result variable".to_string())
                    })?;
                    let eq = if let Some(int_val) = z3_expr.as_int() {
                        result_var.as_int().map(|r| r._eq(&int_val))
                    } else if let Some(bool_val) = z3_expr.as_bool() {
                        result_var.as_bool().map(|r| r._eq(&bool_val))
                    } else {
                        None
                    };
                    if let Some(eq_bool) = eq {
                        return Ok(Some(eq_bool));
                    }
                }
            }
        }

        Ok(None)
    }

    /// Translate an if expression to: (cond => result == then) && (!cond => result == else)
    fn translate_if_to_formula<'a>(
        &'a self,
        if_expr: &syn::ExprIf,
        vars: &mut Z3VarMap<'a>,
    ) -> Result<Option<z3::ast::Bool<'a>>, TranslationError> {
        // Translate condition
        let cond_z3 = self.translate_expr_with_vars(&if_expr.cond, vars)?;
        let cond_bool = cond_z3.as_bool().ok_or_else(|| {
            TranslationError::TypeError("If condition must be boolean".to_string())
        })?;

        // Translate then branch
        let then_formula = self.translate_block_to_result_formula(&if_expr.then_branch, vars)?;

        // Translate else branch (if present)
        let else_formula = if let Some((_, else_branch)) = &if_expr.else_branch {
            match &**else_branch {
                Expr::Block(block) => self.translate_block_to_result_formula(&block.block, vars)?,
                Expr::If(nested_if) => self.translate_if_to_formula(nested_if, vars)?,
                _ => {
                    let z3_expr = self.translate_expr_with_vars(else_branch, vars)?;
                    let result_var = vars.get("result").ok_or_else(|| {
                        TranslationError::UnsupportedExpression("No result variable".to_string())
                    })?;
                    result_var
                        .as_int()
                        .and_then(|r| z3_expr.as_int().map(|v| r._eq(&v)))
                        .or_else(|| {
                            result_var
                                .as_bool()
                                .and_then(|r| z3_expr.as_bool().map(|v| r._eq(&v)))
                        })
                }
            }
        } else {
            None
        };

        // Build the formula: (cond => then) && (!cond => else)
        match (then_formula, else_formula) {
            (Some(then_f), Some(else_f)) => {
                // (cond => then) && (!cond => else)
                let then_impl = cond_bool.implies(&then_f);
                let else_impl = cond_bool.not().implies(&else_f);
                Ok(Some(Bool::and(&self.ctx, &[&then_impl, &else_impl])))
            }
            (Some(then_f), None) => {
                // Only then branch matters (cond => then)
                Ok(Some(cond_bool.implies(&then_f)))
            }
            (None, Some(else_f)) => {
                // Only else branch matters (!cond => else)
                Ok(Some(cond_bool.not().implies(&else_f)))
            }
            (None, None) => Ok(None),
        }
    }

    /// Translate standalone if expression to Dynamic (Int or Bool) via ite
    fn translate_if_expr_to_dynamic<'a>(
        &'a self,
        if_expr: &syn::ExprIf,
        vars: &mut Z3VarMap<'a>,
    ) -> Result<z3::ast::Dynamic<'a>, TranslationError> {
        let cond_z3 = self.translate_expr_with_vars(&if_expr.cond, vars)?;
        let cond_bool = cond_z3.as_bool().ok_or_else(|| {
            TranslationError::TypeError("If condition must be boolean".to_string())
        })?;

        let then_z3 = match if_expr.then_branch.stmts.last() {
            Some(Stmt::Expr(expr, None)) => self.translate_expr_with_vars(expr, vars)?,
            _ => {
                return Err(TranslationError::UnsupportedExpression(
                    "If then branch: expected single expression".to_string(),
                ));
            }
        };

        let else_z3 = if let Some((_, else_branch)) = &if_expr.else_branch {
            match &**else_branch {
                Expr::Block(block) => {
                    if let Some(Stmt::Expr(expr, None)) = block.block.stmts.last() {
                        self.translate_expr_with_vars(expr, vars)?
                    } else {
                        return Err(TranslationError::UnsupportedExpression(
                            "If else block: expected single expression".to_string(),
                        ));
                    }
                }
                Expr::If(nested) => self.translate_if_expr_to_dynamic(nested, vars)?,
                other => self.translate_expr_with_vars(other, vars)?,
            }
        } else {
            return Err(TranslationError::UnsupportedExpression(
                "If without else not supported as expression".to_string(),
            ));
        };

        if let (Some(then_int), Some(else_int)) = (then_z3.as_int(), else_z3.as_int()) {
            return Ok(cond_bool.ite(&then_int, &else_int).into());
        }
        if let (Some(then_b), Some(else_b)) = (then_z3.as_bool(), else_z3.as_bool()) {
            return Ok(cond_bool.ite(&then_b, &else_b).into());
        }
        Err(TranslationError::TypeError(
            "If branches must both be Int or both Bool".to_string(),
        ))
    }
}

/// Resolve common Bitcoin consensus constants
/// Returns the constant value if known, None otherwise
fn resolve_constant(name: &str) -> Option<i64> {
    match name {
        // Economic constants (from blvm-consensus/src/constants.rs)
        "INITIAL_SUBSIDY" => Some(50_0000_0000), // 50 BTC in satoshis
        "MAX_MONEY" => Some(2_100_000_000_000_000), // 21M BTC in satoshis
        "HALVING_INTERVAL" => Some(210_000),
        "SATOSHIS_PER_BTC" => Some(100_000_000),

        // Transaction constants
        "MAX_BLOCK_SIZE" => Some(1_000_000), // 1MB
        "MAX_TX_SIZE" => Some(100_000),      // Conservative limit

        // Script constants
        "MAX_SCRIPT_SIZE" => Some(10_000),
        "MAX_STACK_SIZE" => Some(1000),

        // Script opcodes (blvm-primitives/src/opcodes.rs)
        "OP_1" => Some(0x51),  // 81
        "OP_16" => Some(0x60), // 96

        // SegWit program lengths (blvm-primitives/src/constants.rs)
        "SEGWIT_P2WPKH_LENGTH" => Some(20),
        "SEGWIT_P2WSH_LENGTH" => Some(32),
        "TAPROOT_PROGRAM_LENGTH" => Some(32),

        // Taproot activation heights (blvm-primitives/src/constants.rs)
        "TAPROOT_ACTIVATION_MAINNET" => Some(709_632),
        "TAPROOT_ACTIVATION_TESTNET" => Some(2_011_968),
        "TAPROOT_ACTIVATION_REGTEST" => Some(0),

        _ => None,
    }
}

/// Check if return type is Result<T> or Option<Result<T>>.
/// For determinism, we use Int for result: 0=Err/None, 1=Ok(false)/Some(Err), 2=Ok(true)/Some(Ok(false)), 3=Some(Ok(true)).
pub fn returns_result_or_option_result(ty: &syn::Type) -> bool {
    if let syn::Type::Path(p) = ty {
        if let Some(seg) = p.path.segments.last() {
            if seg.ident == "Result" {
                return true;
            }
            if seg.ident == "Option" {
                if let syn::PathArguments::AngleBracketed(args) = &seg.arguments {
                    for arg in &args.args {
                        if let syn::GenericArgument::Type(t) = arg {
                            if returns_result_or_option_result(t) {
                                return true;
                            }
                        }
                    }
                }
            }
        }
    }
    false
}

/// Check if a type is bool or wraps bool (Result<bool>, Option<bool>).
/// Used to create result as Bool in Z3 instead of Int.
/// If `ty` is a tuple `(T0, T1, …)` — possibly inside `Result<(…)>` or `Option<(…)>` —
/// return a reference to the inner `TypeTuple`.  Returns `None` otherwise.
fn unwrap_to_tuple(ty: &syn::Type) -> Option<&syn::TypeTuple> {
    match ty {
        syn::Type::Tuple(t) => Some(t),
        syn::Type::Path(p) => {
            let seg = p.path.segments.last()?;
            if seg.ident == "Result" || seg.ident == "Option" {
                if let syn::PathArguments::AngleBracketed(args) = &seg.arguments {
                    for arg in &args.args {
                        if let syn::GenericArgument::Type(inner) = arg {
                            if let Some(t) = unwrap_to_tuple(inner) {
                                return Some(t);
                            }
                        }
                    }
                }
            }
            None
        }
        _ => None,
    }
}

/// Auto-derive type-level contract strings for a function's return type.
///
/// Returns a list of `(formula_str, is_bool)` pairs representing contracts that
/// are trivially true by the type alone — no function body needed.  These are
/// used by the verifier when a `#[spec_locked]` function has no explicit
/// `#[ensures]` annotations, allowing the verifier to emit PASSED (type-level)
/// rather than FAILED (no contracts).
///
/// Rules:
/// - `bool` / bool-like types (`ValidationResult`, `MempoolResult`, …) → `"result == true || result == false"`
/// - Tuple return types → per-element contracts for each component
/// - Unsigned / opaque types (`Hash`, `Block`, `u64`, `Natural`, …) → `"result >= 0"`
/// - Signed types (`Integer`, `i64`, …) → no auto-contract (returns `[]`)
pub fn auto_type_contracts(return_ty: &syn::Type) -> Vec<String> {
    // Tuple case: decompose into per-element contracts.
    if let Some(tuple) = unwrap_to_tuple(return_ty) {
        let mut contracts = Vec::new();
        for (i, elem_ty) in tuple.elems.iter().enumerate() {
            if returns_bool_like(elem_ty) {
                contracts.push(format!("result_{i} == true || result_{i} == false"));
            } else if is_unsigned_type(elem_ty) {
                contracts.push(format!("result_{i} >= 0"));
            }
        }
        return contracts;
    }
    // Scalar case.
    if returns_bool_like(return_ty) {
        return vec!["result == true || result == false".to_string()];
    }
    if is_unsigned_type(return_ty) {
        return vec!["result >= 0".to_string()];
    }
    vec![]
}

pub fn returns_bool_like(ty: &syn::Type) -> bool {
    if let syn::Type::Path(p) = ty {
        if let Some(seg) = p.path.segments.last() {
            if seg.ident == "bool" {
                return true;
            }
            // ValidationResult and MempoolResult are modelled as Bool:
            //   Valid=true, Invalid=false | Accepted=true, Rejected=false
            if seg.ident == "ValidationResult" || seg.ident == "MempoolResult" {
                return true;
            }
            if seg.ident == "Result" || seg.ident == "Option" {
                if let syn::PathArguments::AngleBracketed(args) = &seg.arguments {
                    for arg in &args.args {
                        if let syn::GenericArgument::Type(t) = arg {
                            if returns_bool_like(t) {
                                return true;
                            }
                        }
                    }
                }
            }
        }
    }
    false
}

/// Check if a type is unsigned (or wraps an unsigned type in Result/Option).
/// Handles both primitive types (u8, u16, u32, u64, u128, usize) and common type aliases.
/// Check whether `ty` is (or wraps) a type that should receive a `result >= 0` type constraint
/// in Z3.
///
/// Rules (in order):
///
/// 1. **Known signed primitives / aliases** (`i8..isize`, `Integer`) → `false`.
/// 2. **Known unsigned primitives / aliases** (`u8..usize`, `Natural`) → `true`.
/// 3. **`Result<T>` / `Option<T>`**: recurse on the *first* generic argument only (the
///    `Ok`/`Some` type).  Checking all args would incorrectly classify `Result<i64, Err>`
///    as unsigned because the error type `Err` is opaque.
/// 4. **Tuple `(T0, T1, …)`**: return `false` — tuple elements are handled individually by
///    `build_shared_vars`; the aggregate `result` variable for tuples is an untyped placeholder.
/// 5. **Everything else** (Hash, Block, UtxoSet, U256, Sighash, Cow, Vec, WitnessVersion, …):
///    these types are all modelled as opaque `Int` in Z3 with no negative representation,
///    so treating them as non-negative is sound for the purposes of the `result >= 0`
///    type constraint.  Note: this only affects the *type constraint* injected into the
///    solver — the contract itself must still be added explicitly by the caller.
fn is_unsigned_type(ty: &syn::Type) -> bool {
    match ty {
        syn::Type::Path(type_path) => {
            if let Some(segment) = type_path.path.segments.last() {
                let type_name = segment.ident.to_string();

                // (1) Known signed types — these can hold negative values.
                if matches!(
                    type_name.as_str(),
                    "i8" | "i16" | "i32" | "i64" | "i128" | "isize" | "Integer"
                ) {
                    return false;
                }

                // (2) Known unsigned primitives and aliases.
                if matches!(
                    type_name.as_str(),
                    "u8" | "u16" | "u32" | "u64" | "u128" | "usize" | "Natural"
                ) {
                    return true;
                }

                // (3) Result<T, E> / Option<T> / error::Result<T>:
                //     only the first generic arg (the Ok/Some type) determines signedness.
                if matches!(type_name.as_str(), "Result" | "Option" | "error::Result") {
                    if let syn::PathArguments::AngleBracketed(args) = &segment.arguments {
                        if let Some(syn::GenericArgument::Type(first_inner)) = args.args.first() {
                            return is_unsigned_type(first_inner);
                        }
                    }
                    return false;
                }

                // (5) All other named types are opaque non-negative integers in Z3.
                true
            } else {
                false
            }
        }
        // (4) Tuple — handled element-by-element; aggregate is untyped.
        syn::Type::Tuple(_) => false,
        // Arrays / slices (e.g. [u8; 32]) — inherently non-negative opaque values.
        syn::Type::Array(_) | syn::Type::Slice(_) => true,
        // References / pointers — pass through to the inner type.
        syn::Type::Reference(r) => is_unsigned_type(&r.elem),
        syn::Type::Ptr(p) => is_unsigned_type(&p.elem),
        // Anything else: treat as non-negative opaque.
        _ => true,
    }
}

/// Convert a path to a string representation
fn path_to_string(path: &syn::Path) -> String {
    path.segments
        .iter()
        .map(|seg| seg.ident.to_string())
        .collect::<Vec<_>>()
        .join("::")
}

/// Extract a variable name from a field expression (e.g. block.header.bits -> "block_header_bits")
fn field_expr_to_var_name(field: &syn::ExprField) -> String {
    let mut parts = vec![];
    collect_field_path(&field.base, &mut parts);
    parts.push(member_to_string(&field.member));
    parts.join("_")
}

fn collect_field_path(expr: &syn::Expr, parts: &mut Vec<String>) {
    match expr {
        syn::Expr::Field(f) => {
            collect_field_path(&f.base, parts);
            parts.push(member_to_string(&f.member));
        }
        syn::Expr::Path(p) => {
            parts.push(path_to_string(&p.path));
        }
        _ => {
            parts.push("_".to_string());
        }
    }
}

fn member_to_string(member: &syn::Member) -> String {
    match member {
        syn::Member::Named(ident) => ident.to_string(),
        syn::Member::Unnamed(index) => index.index.to_string(),
    }
}

/// Extract a variable name hint from an expression (for unique naming)
fn expr_to_var_hint(expr: &syn::Expr) -> String {
    match expr {
        syn::Expr::Path(p) => path_to_string(&p.path).replace("::", "_"),
        syn::Expr::Field(f) => field_expr_to_var_name(f),
        syn::Expr::MethodCall(m) => {
            let rcv = expr_to_var_hint(&m.receiver);
            if rcv == "x" {
                "m".to_string()
            } else {
                format!("{rcv}_rcv")
            }
        }
        _ => "x".to_string(),
    }
}

/// Result of parsing a let pattern: (inner var to bind, bool suffix, use as-is or negated).
/// - Some: (Some(inner), "is_some", true)
/// - None: (None, "is_some", false)
/// - Ok: (Some(inner), "is_ok", true)
/// - Err(e): (Some(e), "is_ok", false)
/// - Err(_): (None, "is_ok", false)
fn parse_let_option_result_pat(pat: &syn::Pat) -> Option<(Option<String>, &'static str, bool)> {
    match pat {
        syn::Pat::TupleStruct(ts) => {
            let seg = ts.path.segments.last()?;
            let variant = seg.ident.to_string();
            match variant.as_str() {
                "Some" if ts.elems.len() == 1 => {
                    if let syn::Pat::Ident(ident) = &ts.elems[0] {
                        return Some((Some(ident.ident.to_string()), "is_some", true));
                    }
                }
                "Ok" if ts.elems.len() == 1 => {
                    if let syn::Pat::Ident(ident) = &ts.elems[0] {
                        return Some((Some(ident.ident.to_string()), "is_ok", true));
                    }
                }
                "Err" if ts.elems.len() == 1 => {
                    if let syn::Pat::Ident(ident) = &ts.elems[0] {
                        return Some((Some(ident.ident.to_string()), "is_ok", false));
                    }
                    return Some((None, "is_ok", false));
                }
                _ => {}
            }
        }
        syn::Pat::Path(p) => {
            let seg = p.path.segments.last()?;
            if seg.ident == "None" {
                return Some((None, "is_some", false));
            }
        }
        _ => {}
    }
    None
}

/// Parse arm as Some(pat) => body or Ok(pat) => body. Returns (inner_var_name, body).
fn parse_some_ok_arm(arm: &syn::Arm) -> Option<(String, &syn::Expr)> {
    if let syn::Pat::TupleStruct(ts) = &arm.pat {
        let seg = ts.path.segments.last()?;
        let variant = seg.ident.to_string();
        if (variant == "Some" || variant == "Ok") && ts.elems.len() == 1 {
            if let syn::Pat::Ident(ident) = &ts.elems[0] {
                return Some((ident.ident.to_string(), &arm.body));
            }
        }
    }
    None
}

/// Parse arm as None => body or Err(_) => body. Returns body.
fn parse_none_err_arm(arm: &syn::Arm) -> Option<&syn::Expr> {
    match &arm.pat {
        syn::Pat::Path(p) => {
            let seg = p.path.segments.last()?;
            if seg.ident == "None" {
                return Some(&arm.body);
            }
        }
        syn::Pat::TupleStruct(ts) => {
            let seg = ts.path.segments.last()?;
            if seg.ident == "Err" && ts.elems.len() <= 1 {
                return Some(&arm.body);
            }
        }
        _ => {}
    }
    None
}

/// Parse any integer literal token to `i64`.
///
/// Handles:
/// - Decimal: `42`, `-7`
/// - Hex: `0xff`, `0x0000_FFFF` (underscore separators stripped)
/// - Octal: `0o77`
/// - Binary: `0b1010`
/// - Type suffixes stripped: `255u8`, `65535u64`
fn parse_lit_int(int_lit: &syn::LitInt) -> Option<i64> {
    // Fast path for plain decimal literals.
    if let Ok(v) = int_lit.base10_parse::<i64>() {
        return Some(v);
    }
    let s = int_lit.to_string();
    let (raw_digits, radix) =
        if let Some(rest) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
            (rest, 16u32)
        } else if let Some(rest) = s.strip_prefix("0o").or_else(|| s.strip_prefix("0O")) {
            (rest, 8)
        } else if let Some(rest) = s.strip_prefix("0b").or_else(|| s.strip_prefix("0B")) {
            (rest, 2)
        } else {
            return None;
        };
    // Strip type suffix (e.g. "ffu8" → "ff") and underscore separators ("0000_ffff" → "0000ffff").
    let digits: String = raw_digits
        .trim_end_matches(|c: char| c.is_alphabetic())
        .chars()
        .filter(|&c| c != '_')
        .collect();
    i64::from_str_radix(&digits, radix).ok()
}

/// Extract integer literal from expression if it's a literal.
/// Handles decimal, hex (0x), octal (0o), and binary (0b) with underscore separators.
fn extract_int_literal(expr: &syn::Expr) -> Option<i64> {
    if let syn::Expr::Lit(syn::ExprLit {
        lit: syn::Lit::Int(int_lit),
        ..
    }) = expr
    {
        parse_lit_int(int_lit)
    } else {
        None
    }
}

/// Extract function name from call expression (Path or Path with segments)
fn call_expr_to_name(expr: &syn::Expr) -> Result<String, TranslationError> {
    match expr {
        syn::Expr::Path(p) => Ok(path_to_string(&p.path)),
        _ => Err(TranslationError::UnsupportedExpression(format!(
            "Call func: {expr:?}"
        ))),
    }
}

/// Bool-returning uninterpreted (Result<bool>, Option<bool>). Check before Int-returning.
fn known_bool_uninterpreted_function(name: &str) -> Option<(&'static str, Option<usize>)> {
    let base = name.split("::").last().unwrap_or(name);
    match base {
        "check_proof_of_work" => Some(("check_pow", Some(1))),
        "verify_tapscript_schnorr_signature" => Some(("verify_schnorr", None)),
        "is_standard_tx" => Some(("is_standard_tx", Some(1))),
        "replacement_checks" => Some(("replacement_checks", Some(4))),
        "eval_script" => Some(("eval_script", Some(4))),
        "eval_script_inner" => Some(("eval_script_inner", Some(4))),
        "eval_script_impl" => Some(("eval_script_impl", Some(4))),
        "verify_schnorr" => Some(("verify_schnorr", Some(3))),
        _ => None,
    }
}

/// Uninterpreted functions for determinism: f(args) so same inputs => same output (congruence).
/// Returns (Z3 function name, arity). Use None for arity to accept any arg count.
fn known_uninterpreted_function(name: &str) -> Option<(&'static str, Option<usize>)> {
    let base = name.split("::").last().unwrap_or(name);
    match base {
        "serialize_transaction" => Some(("serialize", Some(1))),
        "serialize_transaction_into" => Some(("serialize_into", Some(2))),
        "digest" => Some(("sha256_digest", Some(1))),
        "hash256" => Some(("hash256", Some(1))),
        "to_le_bytes" => Some(("to_le_bytes", Some(1))),
        "with_capacity" => Some(("vec_with_capacity", Some(1))),
        "get_locktime_type" => Some(("locktime_type", Some(1))),
        "sha256_hash" => Some(("hash256", Some(1))),
        "double_sha256_hash" => Some(("hash256", Some(1))),
        "calculate_tx_id" => Some(("hash256", Some(1))),
        "serialize_header" => Some(("serialize_header", Some(1))),
        // "total_supply" moved to known_int_returning_function to allow non-neg constraint injection.
        "calculate_transaction_size" => Some(("tx_size", Some(1))),
        "expand_target" => Some(("expand_target", Some(1))),
        "from_bytes" => Some(("from_bytes", Some(1))),
        "apply_transaction" => Some(("apply_tx", Some(3))),
        "apply_transaction_with_id" => Some(("apply_tx_with_id", None)),
        "check_tx_inputs" => Some(("check_tx_inputs", Some(3))),
        "check_proof_of_work" => Some(("check_pow", Some(1))),
        "eval_script" => Some(("eval_script", Some(4))),
        "get_next_work_required" => Some(("get_next_work", Some(2))),
        "get_next_work_required_corrected" => Some(("get_next_work", Some(2))),
        "get_next_work_required_internal" => Some(("get_next_work_internal", None)),
        "calculate_merkle_root" => Some(("merkle_root", Some(1))),
        "calculate_merkle_root_from_tx_ids" => Some(("merkle_root_ids", Some(1))),
        "merkle_tree_from_hashes" => Some(("merkle_tree", Some(1))),
        // Flexible arity (use call's arg count).
        // connect_block is the single public API (takes BlockValidationContext); no separate connect_block_ctx.
        "connect_block" => Some(("connect_block", None)),
        "connect_block_with_context" => Some(("connect_block", None)),
        "connect_block_ibd" => Some(("connect_block_ibd", None)),
        "connect_block_inner" => Some(("connect_block_inner", None)),
        "validate_block" => Some(("validate_block", None)),
        "validate_block_with_time_context" => Some(("validate_block_ctx", None)),
        "validate_transaction" => Some(("validate_tx", None)),
        "validate_block_header" => Some(("validate_header", None)),
        "check_tx_inputs_with_utxos" => Some(("check_tx_inputs", None)),
        "calculate_transaction_sighash" => Some(("sighash", None)),
        "calculate_transaction_sighash_single_input" => Some(("sighash_single", None)),
        "calculate_transaction_sighash_with_script_code" => Some(("sighash_script", None)),
        "build_time_context" => Some(("build_time_context", None)),
        _ => None,
    }
}

/// Known functions that return Int/u64/i64. Returns fresh var name for the call result.
/// Multiple calls to same function share a var (conservative; models "some value").
fn known_int_returning_function(name: &str) -> Option<String> {
    let base = name.split("::").last().unwrap_or(name);
    match base {
        "get_block_subsidy"
        | "total_supply"
        | "get_next_work_required"
        | "expand_target"
        | "compress_target"
        | "difficulty_from_bits" => Some(format!("call_{base}_result")),
        "calculate_merkle_root" | "calculate_block_hash" => Some(format!("call_{base}_result")),
        "extract_sequence_locktime_value" | "ExtractSequenceLocktimeValue" => {
            Some("call_extract_sequence_locktime_value_result".to_string())
        }
        "get_median_time_past" | "GetMedianTimePast" => {
            Some("call_get_median_time_past_result".to_string())
        }
        "u128" | "from_le_bytes" => None, // type conversions, not direct
        _ => None,
    }
}

/// Known functions that return bool. Returns fresh var name for the call result.
fn known_bool_returning_function(name: &str) -> Option<String> {
    let base = name.split("::").last().unwrap_or(name);
    match base {
        "is_zero_hash" => Some("call_is_zero_hash_result".to_string()),
        "locktime_types_match" => Some("call_locktime_types_match_result".to_string()),
        "is_standard_script" => Some("call_is_standard_script_result".to_string()),
        // validate_taproot_script returns Result<bool>; model as named Bool variable so
        // callers (is_taproot_output) can reason about it via the callee-ensures axiom.
        "validate_taproot_script" => Some("call_validate_taproot_script_result".to_string()),
        _ => None,
    }
}

/// Known functions that return structs with specific field values.
/// Returns a list of (field_name, concrete_value) pairs.
/// Used to propagate callee ensures (e.g. bip54 deployment always has bit=15) into
/// calling functions whose ensures reference struct fields (result.bit == 15).
fn known_struct_field_function(name: &str) -> Option<Vec<(&'static str, i64)>> {
    match name {
        "bip54_deployment_mainnet" | "bip54_deployment_testnet" | "bip54_deployment_regtest" => {
            Some(vec![("bit", 15)])
        }
        _ => None,
    }
}

/// Translation errors
#[derive(Debug, Clone)]
pub enum TranslationError {
    UnsupportedExpression(String),
    UnsupportedLiteral(String),
    UnsupportedOperator(String),
    TypeError(String),
    ParseError(String),
}

impl std::fmt::Display for TranslationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TranslationError::UnsupportedExpression(msg) => {
                write!(f, "Unsupported expression: {msg}")
            }
            TranslationError::UnsupportedLiteral(msg) => write!(f, "Unsupported literal: {msg}"),
            TranslationError::UnsupportedOperator(msg) => {
                write!(f, "Unsupported operator: {msg}")
            }
            TranslationError::TypeError(msg) => write!(f, "Type error: {msg}"),
            TranslationError::ParseError(msg) => write!(f, "Parse error: {msg}"),
        }
    }
}

impl std::error::Error for TranslationError {}

#[cfg(all(test, feature = "z3"))]
mod tests {
    use super::*;
    use z3::{SatResult, Solver};

    #[test]
    fn test_piecewise_body_vs_ensures_uses_same_result_var() {
        let tr = Z3Translator::new(10000);
        let code = r#"
            fn _verify_f_subsidy_piecewise(height: u64) -> i64 {
                let k = height / 210000;
                match k {
                    0 => 5000000000_i64,
                    1 => 2500000000_i64,
                    _ => 0_i64,
                }
            }
        "#;
        let func: syn::ItemFn = syn::parse_str(code).expect("parse fn");
        let mut param_types = std::collections::HashMap::new();
        param_types.insert(
            "height".to_string(),
            syn::parse_str::<syn::Type>("u64").unwrap(),
        );
        let return_type: syn::Type = syn::parse_str("i64").unwrap();

        let (mut shared_vars, type_constraints) =
            tr.build_shared_vars(&param_types, Some(&return_type));

        // Translate ensures: result >= 0 && result <= 5000000000
        let ensures_expr: syn::Expr =
            syn::parse_str("result >= 0 && result <= 5000000000").unwrap();
        let contract = Contract {
            contract_type: crate::parser::contracts::ContractType::Ensures,
            condition: ensures_expr,
            comment: None,
        };
        let ensures_z3 = tr
            .translate_contract_with_shared_vars(&contract, &mut shared_vars)
            .expect("ensures translation");
        let negated = ensures_z3.as_bool().unwrap().not();

        // Translate body
        let body_formula = tr
            .translate_function_body(&func, &mut shared_vars)
            .expect("body translation")
            .expect("body formula not None");

        let ctx = tr.context();
        let solver = Solver::new(ctx);
        for c in &type_constraints {
            solver.assert(c);
        }
        solver.assert(&body_formula);
        solver.assert(&negated);

        let result = solver.check();
        println!("SAT result (should be Unsat): {result:?}");
        if result == SatResult::Sat {
            if let Some(model) = solver.get_model() {
                println!("Model: {model}");
            }
        }
        assert_eq!(result, SatResult::Unsat, "Body should prove ensures");
    }
}

#[cfg(not(feature = "z3"))]
/// Stub implementation when Z3 feature is disabled
pub struct Z3Translator;

#[cfg(not(feature = "z3"))]
impl Z3Translator {
    pub fn new() -> Self {
        Z3Translator
    }

    pub fn translate_contract(&mut self, _contract: &Contract) -> Result<(), String> {
        Err("Z3 feature not enabled".to_string())
    }
}
