//! Z3 translator: Rust AST → Z3 AST translation
//!
//! Translates Rust expressions AND function bodies to Z3 expressions for verification.
//! Focused on Bitcoin-specific patterns (u64, i64, Vec, arithmetic, comparisons).
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

#[cfg(feature = "z3")]
use z3::{Config, Context, Sort};
use z3::ast::{Ast, Int, Bool};
use syn::{Expr, Stmt, Block, ItemFn};
use crate::parser::contracts::Contract;

#[cfg(feature = "z3")]
/// Z3 translator for Rust expressions
pub struct Z3Translator {
    ctx: Context,
}

#[cfg(feature = "z3")]
impl Z3Translator {
    /// Create a new Z3 translator
    pub fn new() -> Self {
        let mut cfg = Config::new();
        cfg.set_proof_generation(true);
        cfg.set_model_generation(true);
        let ctx = Context::new(&cfg);
        
        Z3Translator {
            ctx,
        }
    }

    /// Get the Z3 context
    pub fn context(&self) -> &Context {
        &self.ctx
    }

    /// Translate a Rust expression to a Z3 expression
    /// 
    /// Uses a variable map to ensure same variable name = same Z3 variable within one expression
    pub fn translate_expr_with_vars<'a>(&'a self, expr: &Expr, vars: &mut std::collections::HashMap<String, z3::ast::Int<'a>>) -> Result<z3::ast::Dynamic<'a>, TranslationError> {
        match expr {
            Expr::Lit(lit) => self.translate_literal(&lit.lit),
            Expr::Path(path) => {
                let name = path_to_string(&path.path);
                
                // Check if this is a known constant
                if let Some(constant_value) = resolve_constant(&name) {
                    return Ok(Int::from_i64(&self.ctx, constant_value).into());
                }
                
                // Get or create variable
                let var = vars.entry(name.clone()).or_insert_with(|| {
                    let symbol = z3::Symbol::String(name);
                    Int::new_const(&self.ctx, symbol)
                });
                Ok(var.clone().into())
            }
            Expr::Binary(bin) => {
                let left = self.translate_expr_with_vars(&bin.left, vars)?;
                let right = self.translate_expr_with_vars(&bin.right, vars)?;
                self.translate_binary_op(bin.op, left, right)
            }
            Expr::MethodCall(method) => self.translate_method_call(method),
            Expr::Call(call) => self.translate_call(call),
            Expr::Unary(unary) => {
                let expr = self.translate_expr_with_vars(&unary.expr, vars)?;
                self.translate_unary_op(unary.op, expr)
            }
            Expr::Paren(paren) => self.translate_expr_with_vars(&paren.expr, vars),
            _ => Err(TranslationError::UnsupportedExpression(format!("{:?}", expr))),
        }
    }
    
    /// Translate a Rust expression to a Z3 expression (public API)
    pub fn translate_expr(&self, expr: &Expr) -> Result<z3::ast::Dynamic<'_>, TranslationError> {
        let mut vars: std::collections::HashMap<String, z3::ast::Int<'_>> = std::collections::HashMap::new();
        self.translate_expr_with_vars(expr, &mut vars)
    }

    /// Translate a literal (integer, boolean, etc.)
    fn translate_literal(&self, lit: &syn::Lit) -> Result<z3::ast::Dynamic<'_>, TranslationError> {
        match lit {
            syn::Lit::Int(int_lit) => {
                let value = int_lit.base10_parse::<i64>()
                    .map_err(|e| TranslationError::ParseError(e.to_string()))?;
                Ok(Int::from_i64(&self.ctx, value).into())
            }
            syn::Lit::Bool(bool_lit) => {
                Ok(Bool::from_bool(&self.ctx, bool_lit.value).into())
            }
            _ => Err(TranslationError::UnsupportedLiteral(format!("{:?}", lit))),
        }
    }

    /// Translate a binary operation given already-translated operands
    fn translate_binary_op<'a>(&'a self, op: syn::BinOp, left: z3::ast::Dynamic<'a>, right: z3::ast::Dynamic<'a>) -> Result<z3::ast::Dynamic<'a>, TranslationError> {
        match op {
            syn::BinOp::Add(_) => {
                let left_int = left.as_int().ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                let right_int = right.as_int().ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                Ok((left_int + right_int).into())
            }
            syn::BinOp::Sub(_) => {
                let left_int = left.as_int().ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                let right_int = right.as_int().ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                Ok((left_int - right_int).into())
            }
            syn::BinOp::Mul(_) => {
                let left_int = left.as_int().ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                let right_int = right.as_int().ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                Ok((left_int * right_int).into())
            }
            syn::BinOp::Div(_) => {
                // Z3 integer division
                let left_int = left.as_int().ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                let right_int = right.as_int().ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                Ok(left_int.div(&right_int).into())
            }
            syn::BinOp::Shr(_) => {
                // Right shift: a >> b is equivalent to a / 2^b for non-negative values
                // For simplicity with Z3, we model this using uninterpreted function
                // or approximate for common cases
                let left_int = left.as_int().ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                let right_int = right.as_int().ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                
                // Create an uninterpreted shift function
                // This allows Z3 to reason about shift operations abstractly
                let shift_fn = z3::FuncDecl::new(
                    &self.ctx,
                    "shr",
                    &[&Sort::int(&self.ctx), &Sort::int(&self.ctx)],
                    &Sort::int(&self.ctx),
                );
                Ok(shift_fn.apply(&[&left_int, &right_int]).into())
            }
            syn::BinOp::Shl(_) => {
                // Left shift: a << b is equivalent to a * 2^b
                let left_int = left.as_int().ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                let right_int = right.as_int().ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                
                let shift_fn = z3::FuncDecl::new(
                    &self.ctx,
                    "shl",
                    &[&Sort::int(&self.ctx), &Sort::int(&self.ctx)],
                    &Sort::int(&self.ctx),
                );
                Ok(shift_fn.apply(&[&left_int, &right_int]).into())
            }
            syn::BinOp::Eq(_) => {
                // Equality comparison
                let eq = left._eq(&right);
                Ok(eq.into())
            }
            syn::BinOp::Ne(_) => {
                // Inequality
                let eq = left._eq(&right);
                Ok(eq.not().into())
            }
            syn::BinOp::Lt(_) => {
                let left_int = left.as_int().ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                let right_int = right.as_int().ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                Ok(left_int.lt(&right_int).into())
            }
            syn::BinOp::Le(_) => {
                let left_int = left.as_int().ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                let right_int = right.as_int().ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                Ok(left_int.le(&right_int).into())
            }
            syn::BinOp::Gt(_) => {
                let left_int = left.as_int().ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                let right_int = right.as_int().ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                Ok(left_int.gt(&right_int).into())
            }
            syn::BinOp::Ge(_) => {
                let left_int = left.as_int().ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                let right_int = right.as_int().ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                Ok(left_int.ge(&right_int).into())
            }
            syn::BinOp::And(_) => {
                let left_bool = left.as_bool().ok_or_else(|| TranslationError::TypeError("Expected Bool".to_string()))?;
                let right_bool = right.as_bool().ok_or_else(|| TranslationError::TypeError("Expected Bool".to_string()))?;
                Ok((left_bool & right_bool).into())
            }
            syn::BinOp::Or(_) => {
                let left_bool = left.as_bool().ok_or_else(|| TranslationError::TypeError("Expected Bool".to_string()))?;
                let right_bool = right.as_bool().ok_or_else(|| TranslationError::TypeError("Expected Bool".to_string()))?;
                Ok((left_bool | right_bool).into())
            }
            _ => Err(TranslationError::UnsupportedOperator(format!("{:?}", op))),
        }
    }

    /// Translate a method call (e.g., vec.len(), opt.is_some())
    fn translate_method_call(&self, method: &syn::ExprMethodCall) -> Result<z3::ast::Dynamic<'_>, TranslationError> {
        let method_name = method.method.to_string();
        
        match method_name.as_str() {
            "len" => {
                // vec.len() - for now, treat as integer variable
                // In full implementation, would track array/vector types
                let receiver = self.translate_expr(&method.receiver)?;
                // Return the length as an integer (simplified)
                Ok(receiver)
            }
            "is_some" | "is_none" => {
                // Option checks - would need Option type handling
                Err(TranslationError::UnsupportedExpression("Option methods not yet supported".to_string()))
            }
            _ => Err(TranslationError::UnsupportedExpression(format!("Method call: {}", method_name))),
        }
    }

    /// Translate a function call
    fn translate_call(&self, _call: &syn::ExprCall) -> Result<z3::ast::Dynamic<'_>, TranslationError> {
        // Function calls need more context - defer for now
        Err(TranslationError::UnsupportedExpression("Function calls not yet supported".to_string()))
    }

    /// Translate a unary operation given already-translated operand
    fn translate_unary_op<'a>(&'a self, op: syn::UnOp, expr: z3::ast::Dynamic<'a>) -> Result<z3::ast::Dynamic<'a>, TranslationError> {
        match op {
            syn::UnOp::Not(_) => {
                let bool_expr = expr.as_bool().ok_or_else(|| TranslationError::TypeError("Expected Bool".to_string()))?;
                Ok(bool_expr.not().into())
            }
            syn::UnOp::Neg(_) => {
                let int_expr = expr.as_int().ok_or_else(|| TranslationError::TypeError("Expected Int".to_string()))?;
                Ok(int_expr.unary_minus().into())
            }
            syn::UnOp::Deref(_) => {
                // Dereference - for now, just return the expression
                Ok(expr)
            }
            _ => Err(TranslationError::UnsupportedExpression(format!("Unsupported unary op: {:?}", op))),
        }
    }

    /// Translate a contract condition to Z3
    pub fn translate_contract(&self, contract: &Contract) -> Result<z3::ast::Dynamic<'_>, TranslationError> {
        let (expr, _) = self.translate_contract_with_types(contract, &std::collections::HashMap::new(), None)?;
        Ok(expr)
    }
    
    /// Translate a contract condition to Z3 with type information
    /// Returns the expression and type constraints
    pub fn translate_contract_with_types(&self, contract: &Contract, param_types: &std::collections::HashMap<String, syn::Type>, return_type: Option<&syn::Type>) -> Result<(z3::ast::Dynamic<'_>, Vec<z3::ast::Bool<'_>>), TranslationError> {
        let mut vars: std::collections::HashMap<String, z3::ast::Int<'_>> = std::collections::HashMap::new();
        let mut type_constraints = Vec::new();
        
        // Pre-create variables with type constraints for parameters
        for (name, ty) in param_types {
            let symbol = z3::Symbol::String(name.clone());
            let var = Int::new_const(&self.ctx, symbol);
            vars.insert(name.clone(), var);
            
            // Add type-based constraints
            if is_unsigned_type(ty) {
                // u8, u16, u32, u64, usize, Natural -> >= 0
                let var_ref = vars.get(name).unwrap();
                type_constraints.push(var_ref.ge(&Int::from_i64(&self.ctx, 0)));
            }
            // For signed types (i8, i16, i32, i64, isize, Integer), no constraint
            // For other types, we'd need more sophisticated handling
        }
        
        // Pre-create "result" variable if return type is known (for ensures contracts)
        if let Some(return_ty) = return_type {
            let symbol = z3::Symbol::String("result".to_string());
            let var = Int::new_const(&self.ctx, symbol);
            vars.insert("result".to_string(), var);
            
            // Add type-based constraints for return value
            if is_unsigned_type(return_ty) {
                let var_ref = vars.get("result").unwrap();
                type_constraints.push(var_ref.ge(&Int::from_i64(&self.ctx, 0)));
            }
        }
        
        let expr = self.translate_expr_with_vars(&contract.condition, &mut vars)?;
        Ok((expr, type_constraints))
    }
    
    /// Translate a function body to a Z3 formula that relates inputs to result
    /// 
    /// This is the KEY for verifying ensures: we translate the implementation
    /// to a Z3 formula and prove: requires && implementation => ensures
    pub fn translate_function_body<'a>(&'a self, func: &ItemFn, vars: &mut std::collections::HashMap<String, z3::ast::Int<'a>>) -> Result<Option<z3::ast::Bool<'a>>, TranslationError> {
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
    fn translate_block_to_result_formula<'a>(&'a self, block: &Block, vars: &mut std::collections::HashMap<String, z3::ast::Int<'a>>) -> Result<Option<z3::ast::Bool<'a>>, TranslationError> {
        let mut formulas: Vec<z3::ast::Bool<'a>> = Vec::new();
        let mut early_return_conditions: Vec<(z3::ast::Bool<'a>, z3::ast::Bool<'a>)> = Vec::new();
        
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
                                if let Some(int_val) = z3_expr.as_int() {
                                    vars.insert(var_name, int_val);
                                }
                            }
                        }
                    }
                }
                Stmt::Expr(expr, Some(_)) => {
                    // Statement expression with semicolon (e.g., if cond { return x; })
                    if let Expr::If(if_expr) = expr {
                        // Handle if statement with potential early return
                        if let Some((cond, result_formula)) = self.translate_if_with_early_return(if_expr, vars)? {
                            early_return_conditions.push((cond, result_formula));
                        }
                    }
                }
                Stmt::Expr(expr, None) => {
                    // Final expression (implicit return) - no semicolon
                    if let Ok(z3_expr) = self.translate_expr_with_vars(expr, vars) {
                        if let Some(int_val) = z3_expr.as_int() {
                            let result_var = vars.get("result").ok_or_else(|| {
                                TranslationError::UnsupportedExpression("No result variable".to_string())
                            })?;
                            
                            // This is the final return
                            // Build formula: (no early returns) => result == this_expr
                            if early_return_conditions.is_empty() {
                                return Ok(Some(result_var._eq(&int_val)));
                            } else {
                                // Combine all conditions:
                                // (cond1 => result == val1) && (cond2 => result == val2) && (!cond1 && !cond2 => result == final)
                                let mut all_conditions = Vec::new();
                                let mut negated_conds = Vec::new();
                                
                                for (cond, result_formula) in &early_return_conditions {
                                    // cond => result_formula
                                    all_conditions.push(cond.implies(result_formula));
                                    negated_conds.push(cond.not());
                                }
                                
                                // (!cond1 && !cond2 && ...) => result == final_expr
                                if !negated_conds.is_empty() {
                                    let refs: Vec<&z3::ast::Bool> = negated_conds.iter().collect();
                                    let no_early_return = Bool::and(&self.ctx, &refs);
                                    all_conditions.push(no_early_return.implies(&result_var._eq(&int_val)));
                                }
                                
                                if !all_conditions.is_empty() {
                                    let refs: Vec<&z3::ast::Bool> = all_conditions.iter().collect();
                                    return Ok(Some(Bool::and(&self.ctx, &refs)));
                                }
                                
                                return Ok(Some(result_var._eq(&int_val)));
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
        
        // Check if the last statement is a return or expression
        if let Some(Stmt::Expr(expr, None)) = block.stmts.last() {
            return self.translate_return_expr(expr, vars);
        }
        
        // Handle case where there are only early returns (no final expression)
        if !early_return_conditions.is_empty() {
            let mut all_conditions = Vec::new();
            for (cond, result_formula) in &early_return_conditions {
                all_conditions.push(cond.implies(result_formula));
            }
            let refs: Vec<&z3::ast::Bool> = all_conditions.iter().collect();
            return Ok(Some(Bool::and(&self.ctx, &refs)));
        }
        
        // No clear return expression found
        Ok(None)
    }
    
    /// Handle if statement with potential early return
    /// Returns (condition, result_formula) if there's an early return
    fn translate_if_with_early_return<'a>(&'a self, if_expr: &syn::ExprIf, vars: &mut std::collections::HashMap<String, z3::ast::Int<'a>>) -> Result<Option<(z3::ast::Bool<'a>, z3::ast::Bool<'a>)>, TranslationError> {
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
                    if let Ok(z3_expr) = self.translate_expr_with_vars(return_expr, vars) {
                        if let Some(int_val) = z3_expr.as_int() {
                            let result_var = vars.get("result").ok_or_else(|| {
                                TranslationError::UnsupportedExpression("No result variable".to_string())
                            })?;
                            return Ok(Some((cond_bool, result_var._eq(&int_val))));
                        }
                    }
                }
            }
        }
        
        Ok(None)
    }
    
    /// Translate a return expression to: result == <expr>
    fn translate_return_expr<'a>(&'a self, expr: &Expr, vars: &mut std::collections::HashMap<String, z3::ast::Int<'a>>) -> Result<Option<z3::ast::Bool<'a>>, TranslationError> {
        match expr {
            Expr::Return(ret) => {
                if let Some(return_expr) = &ret.expr {
                    let z3_expr = self.translate_expr_with_vars(return_expr, vars)?;
                    if let Some(int_val) = z3_expr.as_int() {
                        // result == return_expr
                        let result_var = vars.get("result").ok_or_else(|| {
                            TranslationError::UnsupportedExpression("No result variable".to_string())
                        })?;
                        return Ok(Some(result_var._eq(&int_val)));
                    }
                }
            }
            Expr::If(if_expr) => {
                // if condition { then_expr } else { else_expr }
                // Translates to: (condition => result == then_expr) && (!condition => result == else_expr)
                return self.translate_if_to_formula(if_expr, vars);
            }
            _ => {
                // Direct expression (implicit return)
                if let Ok(z3_expr) = self.translate_expr_with_vars(expr, vars) {
                    if let Some(int_val) = z3_expr.as_int() {
                        let result_var = vars.get("result").ok_or_else(|| {
                            TranslationError::UnsupportedExpression("No result variable".to_string())
                        })?;
                        return Ok(Some(result_var._eq(&int_val)));
                    }
                }
            }
        }
        
        Ok(None)
    }
    
    /// Translate an if expression to: (cond => result == then) && (!cond => result == else)
    fn translate_if_to_formula<'a>(&'a self, if_expr: &syn::ExprIf, vars: &mut std::collections::HashMap<String, z3::ast::Int<'a>>) -> Result<Option<z3::ast::Bool<'a>>, TranslationError> {
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
                    if let Some(int_val) = z3_expr.as_int() {
                        let result_var = vars.get("result").ok_or_else(|| {
                            TranslationError::UnsupportedExpression("No result variable".to_string())
                        })?;
                        Some(result_var._eq(&int_val))
                    } else {
                        None
                    }
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
}

/// Resolve common Bitcoin consensus constants
/// Returns the constant value if known, None otherwise
fn resolve_constant(name: &str) -> Option<i64> {
    match name {
        // Economic constants (from blvm-consensus/src/constants.rs)
        "INITIAL_SUBSIDY" => Some(50_0000_0000), // 50 BTC in satoshis
        "MAX_MONEY" => Some(21_000_000_0000_0000), // 21M BTC in satoshis
        "HALVING_INTERVAL" => Some(210_000),
        "SATOSHIS_PER_BTC" => Some(100_000_000),
        
        // Transaction constants
        "MAX_BLOCK_SIZE" => Some(1_000_000), // 1MB
        "MAX_TX_SIZE" => Some(100_000), // Conservative limit
        
        // Script constants
        "MAX_SCRIPT_SIZE" => Some(10_000),
        "MAX_STACK_SIZE" => Some(1000),
        
        _ => None,
    }
}

/// Check if a type is unsigned
/// Handles both primitive types (u8, u16, u32, u64, u128, usize) and common type aliases
fn is_unsigned_type(ty: &syn::Type) -> bool {
    if let syn::Type::Path(type_path) = ty {
        if let Some(segment) = type_path.path.segments.last() {
            let type_name = segment.ident.to_string();
            
            // Check primitive unsigned types
            if type_name.starts_with('u') && (type_name == "u8" || type_name == "u16" || 
                type_name == "u32" || type_name == "u64" || type_name == "u128" || type_name == "usize") {
                return true;
            }
            
            // Check common type aliases used in Bitcoin consensus code
            // Natural = u64, Integer = i64 (from blvm-consensus/src/types.rs)
            if type_name == "Natural" {
                return true; // Natural is u64
            }
        }
    }
    false
}

/// Convert a path to a string representation
fn path_to_string(path: &syn::Path) -> String {
    path.segments
        .iter()
        .map(|seg| seg.ident.to_string())
        .collect::<Vec<_>>()
        .join("::")
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
            TranslationError::UnsupportedExpression(msg) => write!(f, "Unsupported expression: {}", msg),
            TranslationError::UnsupportedLiteral(msg) => write!(f, "Unsupported literal: {}", msg),
            TranslationError::UnsupportedOperator(msg) => write!(f, "Unsupported operator: {}", msg),
            TranslationError::TypeError(msg) => write!(f, "Type error: {}", msg),
            TranslationError::ParseError(msg) => write!(f, "Parse error: {}", msg),
        }
    }
}

impl std::error::Error for TranslationError {}

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



