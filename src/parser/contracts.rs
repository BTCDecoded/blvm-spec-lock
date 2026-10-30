//! Contract AST and parsing
//!
//! Defines the structure for verification contracts (requires/ensures/axiom)

use syn::{Attribute, Expr, ItemFn};

/// A verification contract (precondition, postcondition, or trusted axiom)
#[derive(Debug, Clone)]
pub struct Contract {
    /// Type of contract (requires, ensures, or axiom)
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
    /// Trusted axiom: #[axiom(condition)]
    ///
    /// An axiom is asserted as a *hard constraint* in the solver rather than
    /// verified from the body.  Use this sparingly for properties that are
    /// provably correct by human inspection but whose bodies contain constructs
    /// (loops, bitwise arithmetic) the Z3 translator cannot fully model.
    ///
    /// An axiom is assumed while checking a different `ensures`. An `ensures`
    /// whose condition is the same text as an axiom is not discharged by that
    /// axiom. The body has to prove it, or the result stays partial.
    Axiom,
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

    let is_requires = path.is_ident("requires")
        || (path.segments.len() == 2
            && path.segments[0].ident == "blvm_spec_lock"
            && path.segments[1].ident == "requires");

    let is_ensures = path.is_ident("ensures")
        || (path.segments.len() == 2
            && path.segments[0].ident == "blvm_spec_lock"
            && path.segments[1].ident == "ensures");

    let is_axiom = path.is_ident("axiom")
        || (path.segments.len() == 2
            && path.segments[0].ident == "blvm_spec_lock"
            && path.segments[1].ident == "axiom");

    if is_requires {
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
    } else if is_axiom {
        if let Ok(expr) = attr.parse_args::<Expr>() {
            return Some(Contract {
                contract_type: ContractType::Axiom,
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
