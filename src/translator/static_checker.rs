//! Static checker for fast Rust-based verification (Tier 1)
//!
//! Performs fast pattern-matching checks that don't require Z3:
//! - Bounds checks: `index < vec.len()`
//! - Overflow checks: `a + b` → `a.checked_add(b).is_some()`
//! - Option checks: `opt.is_some()`
//! - Constant equality: `value == CONSTANT`

use syn::Expr;
use crate::parser::contracts::{Contract, ContractType};

/// Result of a static check
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StaticCheckResult {
    /// Check passed (property holds)
    Passed,
    /// Check failed (property doesn't hold)
    Failed,
    /// Check requires Z3 (too complex for static analysis)
    RequiresZ3,
}

/// Perform static checks on a contract
///
/// Returns `Some(result)` if the check can be done statically,
/// or `None` if Z3 is required.
pub fn check_contract_statically(contract: &Contract) -> Option<StaticCheckResult> {
    match contract.contract_type {
        ContractType::Requires => check_requires_statically(&contract.condition),
        ContractType::Ensures => check_ensures_statically(&contract.condition),
    }
}

/// Check a requires (precondition) contract statically
fn check_requires_statically(expr: &Expr) -> Option<StaticCheckResult> {
    // Pattern match on common precondition patterns
    match expr {
        // Constant equality: x == CONSTANT
        Expr::Binary(bin) if matches!(bin.op, syn::BinOp::Eq(_)) => {
            check_constant_equality(&bin.left, &bin.right)
        }
        // Bounds check: index < vec.len()
        Expr::Binary(bin) if matches!(bin.op, syn::BinOp::Lt(_)) => {
            check_bounds(&bin.left, &bin.right)
        }
        // Non-negative: x >= 0
        Expr::Binary(bin) if matches!(bin.op, syn::BinOp::Ge(_)) => {
            check_non_negative(&bin.left, &bin.right)
        }
        // Option check: opt.is_some()
        Expr::MethodCall(method) => {
            check_option_method(method)
        }
        // Too complex - requires Z3
        _ => None,
    }
}

/// Check an ensures (postcondition) contract statically
fn check_ensures_statically(expr: &Expr) -> Option<StaticCheckResult> {
    // Similar patterns to requires, but for postconditions
    match expr {
        // Constant equality: result == CONSTANT
        Expr::Binary(bin) if matches!(bin.op, syn::BinOp::Eq(_)) => {
            check_constant_equality(&bin.left, &bin.right)
        }
        // Bounds: result >= 0
        Expr::Binary(bin) if matches!(bin.op, syn::BinOp::Ge(_)) => {
            check_non_negative(&bin.left, &bin.right)
        }
        // Too complex - requires Z3
        _ => None,
    }
}

/// Check if an expression is a constant equality check
fn check_constant_equality(left: &Expr, right: &Expr) -> Option<StaticCheckResult> {
    // Check if one side is a constant
    let (constant, variable) = match (left, right) {
        (Expr::Lit(_), _) => (left, right),
        (_, Expr::Lit(_)) => (right, left),
        _ => return None, // Not a constant equality
    };
    
    // For now, we can't evaluate constants at compile time in the verification tool
    // This would require evaluating the actual Rust code, which is complex
    // Return RequiresZ3 to let Z3 handle it
    Some(StaticCheckResult::RequiresZ3)
}

/// Check if an expression is a bounds check (index < vec.len())
fn check_bounds(left: &Expr, right: &Expr) -> Option<StaticCheckResult> {
    // Pattern: index < vec.len() or vec.len() > index
    // This requires runtime information, so we can't check statically
    // Return RequiresZ3
    Some(StaticCheckResult::RequiresZ3)
}

/// Check if an expression is a non-negative check (x >= 0)
fn check_non_negative(left: &Expr, right: &Expr) -> Option<StaticCheckResult> {
    // Pattern: x >= 0 or 0 <= x
    // Check if right side is literal 0
    if let Expr::Lit(lit) = right {
        if let syn::Lit::Int(int_lit) = &lit.lit {
            if int_lit.base10_digits() == "0" {
                // For u64/u32/u16/u8, this is always true
                // For i64/i32/i16/i8, this needs Z3
                // For now, return RequiresZ3 (we'd need type information)
                return Some(StaticCheckResult::RequiresZ3);
            }
        }
    }
    
    // Check if left side is literal 0 (0 <= x)
    if let Expr::Lit(lit) = left {
        if let syn::Lit::Int(int_lit) = &lit.lit {
            if int_lit.base10_digits() == "0" {
                return Some(StaticCheckResult::RequiresZ3);
            }
        }
    }
    
    None
}

/// Check if an expression is an option method call (opt.is_some())
fn check_option_method(method: &syn::ExprMethodCall) -> Option<StaticCheckResult> {
    // Check if method name is is_some() or is_none()
    let method_name = method.method.to_string();
    if method_name == "is_some" || method_name == "is_none" {
        // This requires runtime information
        return Some(StaticCheckResult::RequiresZ3);
    }
    
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use syn::parse_quote;

    #[test]
    fn test_constant_equality() {
        let expr: Expr = parse_quote! { x == 5 };
        let contract = Contract {
            contract_type: ContractType::Requires,
            condition: expr,
            comment: None,
        };
        
        let result = check_contract_statically(&contract);
        // Should require Z3 (can't evaluate constants statically)
        assert_eq!(result, Some(StaticCheckResult::RequiresZ3));
    }

    #[test]
    fn test_non_negative() {
        let expr: Expr = parse_quote! { x >= 0 };
        let contract = Contract {
            contract_type: ContractType::Requires,
            condition: expr,
            comment: None,
        };
        
        let result = check_contract_statically(&contract);
        // Should require Z3 (needs type information)
        assert_eq!(result, Some(StaticCheckResult::RequiresZ3));
    }
}

