//! Contract AST and parsing
//!
//! Defines the structure for verification contracts (requires/ensures)

use syn::{Attribute, Expr, ItemFn};

/// A verification contract (precondition or postcondition)
#[derive(Debug, Clone)]
pub struct Contract {
    /// Type of contract (requires or ensures)
    pub contract_type: ContractType,
    /// The condition expression
    pub condition: Expr,
    /// Optional comment/documentation
    pub comment: Option<String>,
}

/// Type of verification contract
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ContractType {
    /// Precondition: #[requires(condition)]
    Requires,
    /// Postcondition: #[ensures(condition)]
    Ensures,
}

/// Extract contracts from a function's attributes
pub fn extract_contracts(func: &ItemFn) -> Vec<Contract> {
    let mut contracts = Vec::new();

    for attr in &func.attrs {
        if let Some(contract) = parse_contract_attribute(attr) {
            contracts.push(contract);
        }
    }

    contracts
}

/// Parse a single attribute to see if it's a contract
fn parse_contract_attribute(attr: &Attribute) -> Option<Contract> {
    let path = attr.path();
    
    // Check if it's #[requires(...)] or #[ensures(...)]
    // Handle both bare attributes and crate-prefixed: #[blvm_spec_lock::requires]
    let is_requires = path.is_ident("requires") || 
        (path.segments.len() == 2 && 
         path.segments[0].ident == "blvm_spec_lock" && 
         path.segments[1].ident == "requires");
    
    let is_ensures = path.is_ident("ensures") || 
        (path.segments.len() == 2 && 
         path.segments[0].ident == "blvm_spec_lock" && 
         path.segments[1].ident == "ensures");
    
    if is_requires {
        // Parse the condition from the attribute
        if let Ok(expr) = attr.parse_args::<Expr>() {
            return Some(Contract {
                contract_type: ContractType::Requires,
                condition: expr,
                comment: extract_comment(attr),
            });
        }
    } else if is_ensures {
        if let Ok(expr) = attr.parse_args::<Expr>() {
            return Some(Contract {
                contract_type: ContractType::Ensures,
                condition: expr,
                comment: extract_comment(attr),
            });
        }
    }

    None
}

/// Extract comment from attribute if present
fn extract_comment(_attr: &Attribute) -> Option<String> {
    // Comments in contracts are handled by the verification tool when it processes the contracts
    None
}

