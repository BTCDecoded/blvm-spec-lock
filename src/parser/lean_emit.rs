//! Lean proposition emitted from the `syn::Expr` that Z3 already verifies.
//!
//! The string is the proposition, not a hand-written theorem. An expression
//! this module does not know returns [`LeanEmitError`] with marker
//! `unsupported`. It does not become `True`, a hole, or an uninterpreted
//! function.

use syn::Expr;

pub const UNSUPPORTED: &str = "unsupported";

#[derive(Debug, PartialEq, Eq)]
pub struct LeanEmitError {
    pub marker: &'static str,
    pub detail: String,
}

impl LeanEmitError {
    fn unsupported(detail: impl Into<String>) -> Self {
        Self {
            marker: UNSUPPORTED,
            detail: detail.into(),
        }
    }
}

/// Emit the Lean proposition for `expr`.
pub fn emit_lean_statement(expr: &Expr) -> Result<String, LeanEmitError> {
    emit_expr(expr)
}

fn emit_expr(expr: &Expr) -> Result<String, LeanEmitError> {
    match expr {
        Expr::Paren(inner) => emit_expr(&inner.expr),
        Expr::Group(inner) => emit_expr(&inner.expr),
        Expr::Lit(lit) => emit_lit(&lit.lit),
        Expr::Path(path) => emit_path(path),
        Expr::Unary(unary) => emit_unary(unary),
        Expr::Binary(binary) => emit_binary(binary),
        Expr::Field(field) => {
            let base = emit_expr(&field.base)?;
            let member = match &field.member {
                syn::Member::Named(ident) => ident.to_string(),
                syn::Member::Unnamed(_) => {
                    return Err(LeanEmitError::unsupported("tuple field index"));
                }
            };
            Ok(format!("{base}.{member}"))
        }
        other => Err(LeanEmitError::unsupported(format!(
            "expression form {}",
            expr_kind(other)
        ))),
    }
}

fn emit_lit(lit: &syn::Lit) -> Result<String, LeanEmitError> {
    match lit {
        syn::Lit::Int(value) => Ok(value.base10_digits().to_string()),
        syn::Lit::Bool(value) => Ok(if value.value() { "true" } else { "false" }.to_string()),
        _ => Err(LeanEmitError::unsupported("non-integer literal")),
    }
}

fn emit_path(path: &syn::ExprPath) -> Result<String, LeanEmitError> {
    if path.qself.is_some() || path.path.segments.len() != 1 {
        return Err(LeanEmitError::unsupported("qualified path"));
    }
    let segment = &path.path.segments[0];
    if !segment.arguments.is_none() {
        return Err(LeanEmitError::unsupported("generic arguments"));
    }
    Ok(segment.ident.to_string())
}

fn emit_unary(unary: &syn::ExprUnary) -> Result<String, LeanEmitError> {
    if !matches!(unary.op, syn::UnOp::Not(_)) {
        return Err(LeanEmitError::unsupported("unary operator"));
    }
    let inner = emit_expr(&unary.expr)?;
    Ok(format!("¬ ({inner})"))
}

fn emit_binary(binary: &syn::ExprBinary) -> Result<String, LeanEmitError> {
    let op = match binary.op {
        syn::BinOp::And(_) => "∧",
        syn::BinOp::Or(_) => "∨",
        syn::BinOp::Eq(_) => "=",
        syn::BinOp::Ne(_) => "≠",
        syn::BinOp::Lt(_) => "<",
        syn::BinOp::Le(_) => "≤",
        syn::BinOp::Gt(_) => ">",
        syn::BinOp::Ge(_) => "≥",
        syn::BinOp::Add(_) => "+",
        syn::BinOp::Sub(_) => "-",
        syn::BinOp::Mul(_) => "*",
        syn::BinOp::Div(_) => "/",
        syn::BinOp::Rem(_) => "%",
        syn::BinOp::Shl(_) => "<<<",
        syn::BinOp::Shr(_) => ">>>",
        syn::BinOp::BitAnd(_) => "&&&",
        syn::BinOp::BitOr(_) => "|||",
        syn::BinOp::BitXor(_) => "^^^",
        _ => return Err(LeanEmitError::unsupported("binary operator")),
    };
    let left = emit_expr(&binary.left)?;
    let right = emit_expr(&binary.right)?;
    Ok(format!("({left} {op} {right})"))
}

fn expr_kind(expr: &Expr) -> &'static str {
    match expr {
        Expr::Array(_) => "array",
        Expr::Assign(_) => "assign",
        Expr::Async(_) => "async",
        Expr::Await(_) => "await",
        Expr::Block(_) => "block",
        Expr::Break(_) => "break",
        Expr::Call(_) => "call",
        Expr::Cast(_) => "cast",
        Expr::Closure(_) => "closure",
        Expr::Const(_) => "const",
        Expr::Continue(_) => "continue",
        Expr::ForLoop(_) => "for",
        Expr::If(_) => "if",
        Expr::Index(_) => "index",
        Expr::Infer(_) => "infer",
        Expr::Let(_) => "let",
        Expr::Loop(_) => "loop",
        Expr::Macro(_) => "macro",
        Expr::Match(_) => "match",
        Expr::MethodCall(_) => "method call",
        Expr::Range(_) => "range",
        Expr::Reference(_) => "reference",
        Expr::Repeat(_) => "repeat",
        Expr::Return(_) => "return",
        Expr::Struct(_) => "struct",
        Expr::Try(_) => "try",
        Expr::TryBlock(_) => "try block",
        Expr::Tuple(_) => "tuple",
        Expr::Unsafe(_) => "unsafe",
        Expr::Verbatim(_) => "verbatim",
        Expr::While(_) => "while",
        Expr::Yield(_) => "yield",
        _ => "other",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn parse(src: &str) -> syn::Expr {
        syn::parse_str(src).unwrap_or_else(|err| panic!("parse {src}: {err}"))
    }

    fn golden(name: &str) -> String {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/golden/lean_emit")
            .join(name);
        std::fs::read_to_string(&path).unwrap_or_else(|err| panic!("read {}: {err}", path.display()))
    }

    #[test]
    fn subsidy_bounds_match_golden() {
        let expr = parse("result >= 0 && result <= INITIAL_SUBSIDY");
        let got = emit_lean_statement(&expr).expect("bounds");
        assert_eq!(got, golden("subsidy_bounds.lean").trim_end());
    }

    #[test]
    fn vsize_identity_matches_golden() {
        let expr = parse("result == (weight + 3) / 4");
        let got = emit_lean_statement(&expr).expect("vsize");
        assert_eq!(got, golden("vsize_identity.lean").trim_end());
    }

    #[test]
    fn call_is_unsupported() {
        let expr = parse("foo(1)");
        let err = emit_lean_statement(&expr).expect_err("call");
        assert_eq!(err.marker, UNSUPPORTED);
        assert!(err.detail.contains("call"));
    }

    #[test]
    fn method_call_is_unsupported() {
        let expr = parse("weight.div_ceil(4)");
        let err = emit_lean_statement(&expr).expect_err("method");
        assert_eq!(err.marker, UNSUPPORTED);
        assert!(err.detail.contains("method call"));
    }
}
