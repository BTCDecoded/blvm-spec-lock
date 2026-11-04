//! One edit of the call a function returns.
//!
//! The call is the initializer of the local the body returns. The function's
//! name is not consulted. One edit doubles the integer literal argument.
//! The other replaces that call with binary division by the same argument.

use syn::{Expr, ItemFn, Lit, LocalInit, Pat, Stmt};

fn returned_init(func: &mut ItemFn) -> Option<&mut Expr> {
    let name = match func.block.stmts.last() {
        Some(Stmt::Expr(Expr::Path(path), _)) => path.path.get_ident().cloned(),
        _ => None,
    }?;
    for stmt in &mut func.block.stmts {
        let Stmt::Local(local) = stmt else {
            continue;
        };
        let Pat::Ident(pat) = &local.pat else {
            continue;
        };
        if pat.ident != name {
            continue;
        }
        let LocalInit { expr, .. } = local.init.as_mut()?;
        return Some(expr);
    }
    None
}

/// The expression the function returns: a local's initializer, or the tail
/// expression when the function returns that expression directly.
fn returned_expr(func: &mut ItemFn) -> Option<&mut Expr> {
    if func.block.stmts.last().is_some_and(
        |stmt| matches!(stmt, Stmt::Expr(Expr::Path(path), _) if path.path.get_ident().is_some()),
    ) {
        return returned_init(func);
    }
    match func.block.stmts.last_mut() {
        Some(Stmt::Expr(expr, _)) => Some(expr),
        _ => None,
    }
}

/// Decrement one integer literal that is an operand of `*` in the returned expression.
pub fn decrement_mul_literal(func: &mut ItemFn) -> bool {
    let Some(expr) = returned_expr(func) else {
        return false;
    };
    decrement_mul_in(expr)
}

fn decrement_mul_in(expr: &mut Expr) -> bool {
    match expr {
        Expr::Binary(bin) => {
            if matches!(bin.op, syn::BinOp::Mul(_))
                && (decrement_lit(&mut bin.left) || decrement_lit(&mut bin.right))
            {
                return true;
            }
            decrement_mul_in(&mut bin.left) || decrement_mul_in(&mut bin.right)
        }
        Expr::Paren(paren) => decrement_mul_in(&mut paren.expr),
        _ => false,
    }
}

fn increment_lit(expr: &mut Expr) -> bool {
    let Expr::Lit(lit_expr) = expr else {
        return false;
    };
    let Lit::Int(lit) = &lit_expr.lit else {
        return false;
    };
    let Ok(n) = lit.base10_parse::<u128>() else {
        return false;
    };
    *expr = syn::parse_str(&(n + 1).to_string()).unwrap_or_else(|_| unreachable!("decimal"));
    true
}

fn decrement_lit(expr: &mut Expr) -> bool {
    let Expr::Lit(lit_expr) = expr else {
        return false;
    };
    let Lit::Int(lit) = &lit_expr.lit else {
        return false;
    };
    let Ok(n) = lit.base10_parse::<u128>() else {
        return false;
    };
    if n < 1 {
        return false;
    }
    *expr = syn::parse_str(&(n - 1).to_string()).unwrap_or_else(|_| unreachable!("decimal"));
    true
}

fn peel_cast(expr: &mut Expr) -> &mut Expr {
    match expr {
        Expr::Cast(cast) => peel_cast(&mut cast.expr),
        Expr::Paren(paren) => peel_cast(&mut paren.expr),
        _ => expr,
    }
}

/// Make the two sides of a returned `||` of equalities compare against the same value.
pub fn collapse_returned_or_eq(func: &mut ItemFn) -> bool {
    let Some(expr) = returned_expr(func) else {
        return false;
    };
    collapse_or_eq(expr)
}

fn collapse_or_eq(expr: &mut Expr) -> bool {
    match expr {
        Expr::Binary(bin) if matches!(bin.op, syn::BinOp::Or(_)) => {
            let same = matches!(
                (&*bin.left, &*bin.right),
                (Expr::Binary(left), Expr::Binary(right))
                    if matches!(left.op, syn::BinOp::Eq(_))
                        && matches!(right.op, syn::BinOp::Eq(_))
            );
            if same {
                let rhs = if let Expr::Binary(right) = &*bin.right {
                    right.right.clone()
                } else {
                    return false;
                };
                if let Expr::Binary(left) = &mut *bin.left {
                    left.right = rhs;
                    return true;
                }
            }
            collapse_or_eq(&mut bin.left) || collapse_or_eq(&mut bin.right)
        }
        Expr::Binary(bin) => collapse_or_eq(&mut bin.left) || collapse_or_eq(&mut bin.right),
        Expr::Paren(paren) => collapse_or_eq(&mut paren.expr),
        Expr::Block(block) => block.block.stmts.iter_mut().any(|stmt| match stmt {
            syn::Stmt::Expr(expr, _) => collapse_or_eq(expr),
            _ => false,
        }),
        Expr::Match(match_expr) => match_expr
            .arms
            .iter_mut()
            .any(|arm| collapse_or_eq(&mut arm.body)),
        _ => false,
    }
}

/// Set the right-hand side of the last returned equality to `0`.
pub fn zero_last_returned_eq(func: &mut ItemFn) -> bool {
    let Some(expr) = returned_expr(func) else {
        return false;
    };
    zero_last_eq(expr)
}

fn zero_last_eq(expr: &mut Expr) -> bool {
    match expr {
        Expr::Match(match_expr) => match_expr
            .arms
            .iter_mut()
            .rev()
            .any(|arm| zero_last_eq(&mut arm.body)),
        Expr::Binary(bin) => {
            if zero_last_eq(&mut bin.right) || zero_last_eq(&mut bin.left) {
                return true;
            }
            if matches!(bin.op, syn::BinOp::Eq(_)) {
                bin.right = syn::parse_quote!(0);
                return true;
            }
            false
        }
        Expr::Paren(paren) => zero_last_eq(&mut paren.expr),
        Expr::Block(block) => block.block.stmts.iter_mut().rev().any(|stmt| match stmt {
            syn::Stmt::Expr(expr, _) => zero_last_eq(expr),
            _ => false,
        }),
        _ => false,
    }
}

/// Drop the first `if … { return true; }` in the body.
/// Replace the first `return Ok(true)` with `return Ok(false)`.
pub fn flip_early_ok_true(func: &mut ItemFn) -> bool {
    for stmt in &mut func.block.stmts {
        let Stmt::Expr(Expr::If(if_expr), _) = stmt else {
            continue;
        };
        if if_expr.else_branch.is_some() {
            continue;
        }
        let [Stmt::Expr(Expr::Return(ret), _)] = if_expr.then_branch.stmts.as_slice() else {
            continue;
        };
        let Some(expr) = ret.expr.as_deref() else {
            continue;
        };
        let Expr::Call(call) = expr else {
            continue;
        };
        let Ok(name) = call_base(&call.func) else {
            continue;
        };
        if name != "Ok" || call.args.len() != 1 || !is_true_lit(&call.args[0]) {
            continue;
        }
        if_expr.then_branch.stmts[0] = syn::parse_quote!(return Ok(false););
        return true;
    }
    false
}

/// Drop the first `if … { return Ok(true); }` with no else.
pub fn drop_early_ok_true(func: &mut ItemFn) -> bool {
    let Some(index) = func.block.stmts.iter().position(is_early_ok_true) else {
        return false;
    };
    func.block.stmts.remove(index);
    true
}

fn is_early_ok_true(stmt: &Stmt) -> bool {
    let Stmt::Expr(Expr::If(if_expr), _) = stmt else {
        return false;
    };
    if if_expr.else_branch.is_some() {
        return false;
    }
    let [Stmt::Expr(Expr::Return(ret), _)] = if_expr.then_branch.stmts.as_slice() else {
        return false;
    };
    let Some(expr) = ret.expr.as_deref() else {
        return false;
    };
    let Expr::Call(call) = expr else {
        return false;
    };
    let Ok(name) = call_base(&call.func) else {
        return false;
    };
    name == "Ok" && call.args.len() == 1 && is_true_lit(&call.args[0])
}

fn is_true_lit(expr: &Expr) -> bool {
    matches!(expr, Expr::Lit(lit) if matches!(&lit.lit, Lit::Bool(bit) if bit.value))
}

fn call_base(func: &Expr) -> Result<String, ()> {
    let Expr::Path(path) = func else {
        return Err(());
    };
    path.path
        .segments
        .last()
        .map(|seg| seg.ident.to_string())
        .ok_or(())
}

pub fn drop_early_true_return(func: &mut ItemFn) -> bool {
    let Some(index) = func.block.stmts.iter().position(is_early_true_return) else {
        return false;
    };
    func.block.stmts.remove(index);
    true
}

fn is_early_true_return(stmt: &Stmt) -> bool {
    let Stmt::Expr(Expr::If(if_expr), _) = stmt else {
        return false;
    };
    if if_expr.else_branch.is_some() {
        return false;
    }
    let [Stmt::Expr(Expr::Return(ret), _)] = if_expr.then_branch.stmts.as_slice() else {
        return false;
    };
    let Some(expr) = ret.expr.as_deref() else {
        return false;
    };
    matches!(expr, Expr::Lit(lit) if matches!(&lit.lit, Lit::Bool(bit) if bit.value))
}

/// Replace a returned `>=` with `>`.
pub fn tighten_returned_ge(func: &mut ItemFn) -> bool {
    let Some(expr) = returned_expr(func) else {
        return false;
    };
    tighten_ge(expr)
}

fn tighten_ge(expr: &mut Expr) -> bool {
    match expr {
        Expr::Binary(bin) if matches!(bin.op, syn::BinOp::Ge(_)) => {
            let left = bin.left.clone();
            let right = bin.right.clone();
            *expr = syn::parse_quote!(#left > #right);
            true
        }
        Expr::Binary(bin) => tighten_ge(&mut bin.left) || tighten_ge(&mut bin.right),
        Expr::Paren(paren) => tighten_ge(&mut paren.expr),
        _ => false,
    }
}

/// Replace a returned `<=` with `<`.
pub fn tighten_returned_le(func: &mut ItemFn) -> bool {
    let Some(expr) = returned_expr(func) else {
        return false;
    };
    let Expr::Binary(bin) = expr else {
        return false;
    };
    if !matches!(bin.op, syn::BinOp::Le(_)) {
        return false;
    }
    let left = bin.left.clone();
    let right = bin.right.clone();
    *expr = syn::parse_quote!(#left < #right);
    true
}

/// Increment the integer literal in a returned comparison.
pub fn increment_returned_cmp_literal(func: &mut ItemFn) -> bool {
    let Some(expr) = returned_expr(func) else {
        return false;
    };
    increment_cmp_in(expr)
}

fn increment_cmp_in(expr: &mut Expr) -> bool {
    if let Expr::Binary(bin) = expr {
        if matches!(
            bin.op,
            syn::BinOp::Le(_)
                | syn::BinOp::Lt(_)
                | syn::BinOp::Ge(_)
                | syn::BinOp::Gt(_)
                | syn::BinOp::Eq(_)
                | syn::BinOp::Ne(_)
        ) && (increment_cmp_lit(&mut bin.right) || increment_cmp_lit(&mut bin.left))
        {
            return true;
        }
        return increment_cmp_in(&mut bin.left) || increment_cmp_in(&mut bin.right);
    }
    match expr {
        Expr::Match(match_expr) => match_expr
            .arms
            .iter_mut()
            .any(|arm| increment_cmp_in(&mut arm.body)),
        Expr::Paren(paren) => increment_cmp_in(&mut paren.expr),
        _ => false,
    }
}

/// Flip the first boolean literal in a returned match arm.
pub fn flip_returned_match_bool(func: &mut ItemFn) -> bool {
    let Some(expr) = returned_expr(func) else {
        return false;
    };
    let Expr::Match(match_expr) = expr else {
        return false;
    };
    match_expr
        .arms
        .iter_mut()
        .any(|arm| flip_bool_lit(&mut arm.body))
}

/// Increment the first integer literal in a returned `matches!` pattern.
pub fn increment_returned_matches_lit(func: &mut ItemFn) -> bool {
    edit_returned_matches(func, increment_first_pat_lit)
}

/// Increment the start of the last inclusive range in a returned `matches!` pattern.
pub fn increment_returned_matches_range_start(func: &mut ItemFn) -> bool {
    edit_returned_matches(func, increment_last_range_start)
}

fn edit_returned_matches(func: &mut ItemFn, edit: fn(&mut Pat) -> bool) -> bool {
    let Some(expr) = returned_expr(func) else {
        return false;
    };
    let tokens = match &*expr {
        Expr::Macro(mac) if mac.mac.path.is_ident("matches") => mac.mac.tokens.clone(),
        _ => return false,
    };
    let Ok(mut parsed) = syn::parse2::<MatchesEdit>(tokens) else {
        return false;
    };
    if !edit(&mut parsed.pat) {
        return false;
    }
    let scrutinee = parsed.expr;
    let pat = parsed.pat;
    *expr = syn::parse_quote!(matches!(#scrutinee, #pat));
    true
}

struct MatchesEdit {
    expr: Expr,
    pat: Pat,
}

impl syn::parse::Parse for MatchesEdit {
    fn parse(input: syn::parse::ParseStream<'_>) -> syn::Result<Self> {
        let expr = input.parse()?;
        input.parse::<syn::Token![,]>()?;
        let pat = Pat::parse_multi(input)?;
        Ok(Self { expr, pat })
    }
}

fn increment_first_pat_lit(pat: &mut Pat) -> bool {
    match pat {
        Pat::Lit(lit) => increment_pat_int(&mut lit.lit),
        Pat::Or(or_pat) => or_pat.cases.iter_mut().any(increment_first_pat_lit),
        Pat::Paren(paren) => increment_first_pat_lit(&mut paren.pat),
        _ => false,
    }
}

fn increment_pat_int(lit: &mut syn::Lit) -> bool {
    let syn::Lit::Int(int_lit) = lit else {
        return false;
    };
    let Ok(n) = int_lit.base10_parse::<u128>() else {
        return false;
    };
    let next = n.saturating_add(1);
    if next == n {
        return false;
    }
    *lit = syn::parse_str(&next.to_string()).unwrap_or_else(|_| unreachable!("decimal"));
    true
}

fn increment_last_range_start(pat: &mut Pat) -> bool {
    match pat {
        Pat::Or(or_pat) => {
            let last = or_pat
                .cases
                .iter()
                .enumerate()
                .rev()
                .find(|(_, case)| matches!(case, Pat::Range(_)))
                .map(|(index, _)| index);
            let Some(index) = last else {
                return false;
            };
            increment_last_range_start(&mut or_pat.cases[index])
        }
        Pat::Range(range) => range
            .start
            .as_mut()
            .is_some_and(|start| increment_cmp_lit(start)),
        Pat::Paren(paren) => increment_last_range_start(&mut paren.pat),
        _ => false,
    }
}

fn flip_bool_lit(expr: &mut Expr) -> bool {
    let Expr::Lit(lit_expr) = expr else {
        return false;
    };
    let Lit::Bool(bit) = &mut lit_expr.lit else {
        return false;
    };
    bit.value = !bit.value;
    true
}

fn increment_cmp_lit(expr: &mut Expr) -> bool {
    let Expr::Lit(lit_expr) = expr else {
        return false;
    };
    let Lit::Int(lit) = &lit_expr.lit else {
        return false;
    };
    let Ok(n) = lit.base10_parse::<u128>() else {
        return false;
    };
    let next = n.saturating_add(1);
    if next == n {
        return false;
    }
    *expr = syn::parse_str(&next.to_string()).unwrap_or_else(|_| unreachable!("decimal"));
    true
}

/// Drop the left operand of a returned `||`.
pub fn drop_returned_or_left(func: &mut ItemFn) -> bool {
    let Some(expr) = returned_expr(func) else {
        return false;
    };
    let Expr::Binary(bin) = expr else {
        return false;
    };
    if !matches!(bin.op, syn::BinOp::Or(_)) {
        return false;
    }
    let right = bin.right.clone();
    *expr = *right;
    true
}

/// Replace the first `!=` in the returned expression with `==`.
pub fn flip_nested_neq(func: &mut ItemFn) -> bool {
    let Some(expr) = returned_expr(func) else {
        return false;
    };
    flip_neq(expr)
}

fn flip_neq(expr: &mut Expr) -> bool {
    match expr {
        Expr::Binary(bin) if matches!(bin.op, syn::BinOp::Ne(_)) => {
            let left = bin.left.clone();
            let right = bin.right.clone();
            *expr = syn::parse_quote!(#left == #right);
            true
        }
        Expr::Binary(bin) => flip_neq(&mut bin.left) || flip_neq(&mut bin.right),
        Expr::Paren(paren) => flip_neq(&mut paren.expr),
        Expr::Call(call) => call.args.iter_mut().any(flip_neq),
        _ => false,
    }
}

/// Drop the left operand of a returned `&&`.
pub fn drop_returned_and_left(func: &mut ItemFn) -> bool {
    let Some(expr) = returned_expr(func) else {
        return false;
    };
    let Expr::Binary(bin) = expr else {
        return false;
    };
    if !matches!(bin.op, syn::BinOp::And(_)) {
        return false;
    }
    let right = bin.right.clone();
    *expr = *right;
    true
}

/// Replace the `<` that guards the returned `if` with `<=`.
pub fn relax_returned_lt(func: &mut ItemFn) -> bool {
    let Some(expr) = returned_expr(func) else {
        return false;
    };
    let Expr::If(if_expr) = expr else {
        return false;
    };
    let Expr::Binary(bin) = &mut *if_expr.cond else {
        return false;
    };
    if !matches!(bin.op, syn::BinOp::Lt(_)) {
        return false;
    }
    let left = bin.left.clone();
    let right = bin.right.clone();
    if_expr.cond = syn::parse_quote!(#left <= #right);
    true
}

/// Replace the `<` that guards the returned `if` with `>`.
pub fn reverse_returned_lt(func: &mut ItemFn) -> bool {
    let Some(expr) = returned_expr(func) else {
        return false;
    };
    let Expr::If(if_expr) = expr else {
        return false;
    };
    let Expr::Binary(bin) = &mut *if_expr.cond else {
        return false;
    };
    if !matches!(bin.op, syn::BinOp::Lt(_)) {
        return false;
    }
    let left = bin.left.clone();
    let right = bin.right.clone();
    if_expr.cond = syn::parse_quote!(#left > #right);
    true
}

/// Replace a returned `>` with `>=`.
pub fn relax_returned_gt(func: &mut ItemFn) -> bool {
    let Some(expr) = returned_expr(func) else {
        return false;
    };
    relax_gt(expr)
}

fn relax_gt(expr: &mut Expr) -> bool {
    match expr {
        Expr::Binary(bin) if matches!(bin.op, syn::BinOp::Gt(_)) => {
            let left = bin.left.clone();
            let right = bin.right.clone();
            *expr = syn::parse_quote!(#left >= #right);
            true
        }
        Expr::Call(call) => call.args.iter_mut().any(relax_gt),
        Expr::Binary(bin) => relax_gt(&mut bin.left) || relax_gt(&mut bin.right),
        Expr::Paren(paren) => relax_gt(&mut paren.expr),
        Expr::Try(try_expr) => relax_gt(&mut try_expr.expr),
        _ => false,
    }
}

/// Replace a returned `>` with `<`.
pub fn reverse_returned_gt(func: &mut ItemFn) -> bool {
    let Some(expr) = returned_expr(func) else {
        return false;
    };
    reverse_gt(expr)
}

fn reverse_gt(expr: &mut Expr) -> bool {
    match expr {
        Expr::Binary(bin) if matches!(bin.op, syn::BinOp::Gt(_)) => {
            let left = bin.left.clone();
            let right = bin.right.clone();
            *expr = syn::parse_quote!(#left < #right);
            true
        }
        Expr::Call(call) => call.args.iter_mut().any(reverse_gt),
        Expr::Binary(bin) => reverse_gt(&mut bin.left) || reverse_gt(&mut bin.right),
        Expr::Paren(paren) => reverse_gt(&mut paren.expr),
        Expr::Try(try_expr) => reverse_gt(&mut try_expr.expr),
        _ => false,
    }
}

/// Decrement one integer literal that is an operand of `&` in the returned expression.
pub fn decrement_and_literal(func: &mut ItemFn) -> bool {
    let Some(expr) = returned_expr(func) else {
        return false;
    };
    let expr = peel_cast(expr);
    let Expr::Binary(bin) = expr else {
        return false;
    };
    if !matches!(bin.op, syn::BinOp::BitAnd(_)) {
        return false;
    }
    decrement_lit(&mut bin.left) || decrement_lit(&mut bin.right)
}

/// Replace a returned `&` with `|`.
pub fn replace_returned_and_with_or(func: &mut ItemFn) -> bool {
    let Some(expr) = returned_expr(func) else {
        return false;
    };
    let expr = peel_cast(expr);
    let Expr::Binary(bin) = expr else {
        return false;
    };
    if !matches!(bin.op, syn::BinOp::BitAnd(_)) {
        return false;
    }
    let left = bin.left.clone();
    let right = bin.right.clone();
    *expr = syn::parse_quote!(#left | #right);
    true
}

/// Halve one integer literal that is an operand of `&` in the returned expression.
pub fn halve_and_literal(func: &mut ItemFn) -> bool {
    let Some(expr) = returned_expr(func) else {
        return false;
    };
    halve_and_in(expr)
}

fn halve_and_in(expr: &mut Expr) -> bool {
    match expr {
        Expr::Binary(bin) => {
            if matches!(bin.op, syn::BinOp::BitAnd(_))
                && (halve_lit(&mut bin.left) || halve_lit(&mut bin.right))
            {
                return true;
            }
            halve_and_in(&mut bin.left) || halve_and_in(&mut bin.right)
        }
        Expr::Paren(paren) => halve_and_in(&mut paren.expr),
        _ => false,
    }
}

/// Replace a returned `==` with `!=`.
pub fn flip_returned_eq(func: &mut ItemFn) -> bool {
    let Some(expr) = returned_expr(func) else {
        return false;
    };
    let Expr::Binary(bin) = expr else {
        return false;
    };
    if !matches!(bin.op, syn::BinOp::Eq(_)) {
        return false;
    }
    let left = bin.left.clone();
    let right = bin.right.clone();
    *expr = syn::parse_quote!(#left != #right);
    true
}

/// Raise the first `==` integer literal in the body by one.
pub fn increment_first_eq_lit(func: &mut ItemFn) -> bool {
    increment_eq_in_block(&mut func.block)
}

fn increment_eq_in_block(block: &mut syn::Block) -> bool {
    for stmt in &mut block.stmts {
        match stmt {
            Stmt::Local(local) => {
                if let Some(init) = &mut local.init {
                    if increment_eq_lit(&mut init.expr) {
                        return true;
                    }
                }
            }
            Stmt::Expr(expr, _) => {
                if increment_eq_lit(expr) {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

fn increment_eq_lit(expr: &mut Expr) -> bool {
    match expr {
        Expr::Binary(bin) if matches!(bin.op, syn::BinOp::Eq(_)) => {
            if increment_lit(&mut bin.left) || increment_lit(&mut bin.right) {
                return true;
            }
            increment_eq_lit(&mut bin.left) || increment_eq_lit(&mut bin.right)
        }
        Expr::Binary(bin) => increment_eq_lit(&mut bin.left) || increment_eq_lit(&mut bin.right),
        Expr::Paren(paren) => increment_eq_lit(&mut paren.expr),
        Expr::Cast(cast) => increment_eq_lit(&mut cast.expr),
        Expr::If(if_expr) => {
            increment_eq_lit(&mut if_expr.cond) || increment_eq_in_block(&mut if_expr.then_branch)
        }
        Expr::Block(block) => increment_eq_in_block(&mut block.block),
        _ => false,
    }
}

/// Turn the first `<=` in the body into `<`.
pub fn tighten_first_le(func: &mut ItemFn) -> bool {
    tighten_le_in_block(&mut func.block)
}

fn tighten_le_in_block(block: &mut syn::Block) -> bool {
    for stmt in &mut block.stmts {
        match stmt {
            Stmt::Local(local) => {
                if let Some(init) = &mut local.init {
                    if tighten_any_le(&mut init.expr) {
                        return true;
                    }
                }
            }
            Stmt::Expr(expr, _) => {
                if tighten_any_le(expr) {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

fn tighten_any_le(expr: &mut Expr) -> bool {
    match expr {
        Expr::Binary(bin) if matches!(bin.op, syn::BinOp::Le(_)) => {
            let left = bin.left.clone();
            let right = bin.right.clone();
            *expr = syn::parse_quote!(#left < #right);
            true
        }
        Expr::Binary(bin) => tighten_any_le(&mut bin.left) || tighten_any_le(&mut bin.right),
        Expr::Paren(paren) => tighten_any_le(&mut paren.expr),
        Expr::If(if_expr) => {
            tighten_any_le(&mut if_expr.cond)
                || tighten_le_in_block(&mut if_expr.then_branch)
                || if_expr
                    .else_branch
                    .as_mut()
                    .is_some_and(|(_, branch)| tighten_any_le(branch))
        }
        Expr::Block(block) => tighten_le_in_block(&mut block.block),
        Expr::Let(let_expr) => tighten_any_le(&mut let_expr.expr),
        _ => false,
    }
}

/// Replace the first `<=` comparison in the body with `false`.
pub fn false_first_le(func: &mut ItemFn) -> bool {
    false_le_in_block(&mut func.block)
}

fn false_le_in_block(block: &mut syn::Block) -> bool {
    for stmt in &mut block.stmts {
        match stmt {
            Stmt::Local(local) => {
                if let Some(init) = &mut local.init {
                    if false_any_le(&mut init.expr) {
                        return true;
                    }
                }
            }
            Stmt::Expr(expr, _) => {
                if false_any_le(expr) {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

fn false_any_le(expr: &mut Expr) -> bool {
    match expr {
        Expr::Binary(bin) if matches!(bin.op, syn::BinOp::Le(_)) => {
            *expr = syn::parse_quote!(false);
            true
        }
        Expr::Binary(bin) => false_any_le(&mut bin.left) || false_any_le(&mut bin.right),
        Expr::Paren(paren) => false_any_le(&mut paren.expr),
        Expr::If(if_expr) => {
            false_any_le(&mut if_expr.cond)
                || false_le_in_block(&mut if_expr.then_branch)
                || if_expr
                    .else_branch
                    .as_mut()
                    .is_some_and(|(_, branch)| false_any_le(branch))
        }
        Expr::Block(block) => false_le_in_block(&mut block.block),
        Expr::Let(let_expr) => false_any_le(&mut let_expr.expr),
        _ => false,
    }
}

/// Turn the first `>=` in the body into `>`.
pub fn tighten_first_ge(func: &mut ItemFn) -> bool {
    tighten_ge_in_block(&mut func.block)
}

fn tighten_ge_in_block(block: &mut syn::Block) -> bool {
    for stmt in &mut block.stmts {
        match stmt {
            Stmt::Local(local) => {
                if let Some(init) = &mut local.init {
                    if tighten_any_ge(&mut init.expr) {
                        return true;
                    }
                }
            }
            Stmt::Expr(expr, _) => {
                if tighten_any_ge(expr) {
                    return true;
                }
            }
            Stmt::Item(syn::Item::Const(item)) => {
                if tighten_any_ge(&mut item.expr) {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

fn tighten_any_ge(expr: &mut Expr) -> bool {
    match expr {
        Expr::Binary(bin) if matches!(bin.op, syn::BinOp::Ge(_)) => {
            let left = bin.left.clone();
            let right = bin.right.clone();
            *expr = syn::parse_quote!(#left > #right);
            true
        }
        Expr::Binary(bin) => tighten_any_ge(&mut bin.left) || tighten_any_ge(&mut bin.right),
        Expr::Paren(paren) => tighten_any_ge(&mut paren.expr),
        Expr::If(if_expr) => {
            tighten_any_ge(&mut if_expr.cond)
                || tighten_ge_in_block(&mut if_expr.then_branch)
                || if_expr
                    .else_branch
                    .as_mut()
                    .is_some_and(|(_, branch)| tighten_any_ge(branch))
        }
        Expr::Block(block) => tighten_ge_in_block(&mut block.block),
        _ => false,
    }
}

/// Halve the literal in the first const item.
pub fn halve_const_item(func: &mut ItemFn) -> bool {
    halve_const_in_block(&mut func.block)
}

fn halve_const_in_block(block: &mut syn::Block) -> bool {
    for stmt in &mut block.stmts {
        match stmt {
            Stmt::Item(syn::Item::Const(item)) => {
                if halve_int_lit(&mut item.expr) {
                    return true;
                }
            }
            Stmt::Expr(Expr::If(if_expr), _) => {
                if halve_const_in_block(&mut if_expr.then_branch) {
                    return true;
                }
                if let Some((_, branch)) = if_expr.else_branch.as_mut() {
                    match branch.as_mut() {
                        Expr::If(nested) => {
                            if halve_const_in_block(&mut nested.then_branch) {
                                return true;
                            }
                        }
                        Expr::Block(block) => {
                            if halve_const_in_block(&mut block.block) {
                                return true;
                            }
                        }
                        _ => {}
                    }
                }
            }
            Stmt::Expr(Expr::Block(block), _) => {
                if halve_const_in_block(&mut block.block) {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

fn halve_int_lit(expr: &mut Expr) -> bool {
    let Expr::Lit(lit) = expr else {
        return false;
    };
    let syn::Lit::Int(value) = &lit.lit else {
        return false;
    };
    let Ok(number) = value.base10_parse::<u64>() else {
        return false;
    };
    let half = number / 2;
    *expr = syn::parse_quote!(#half);
    true
}

/// Turn the first `<` in the body into `<=`.
pub fn relax_first_lt(func: &mut ItemFn) -> bool {
    relax_lt_in_block(&mut func.block)
}

fn relax_lt_in_block(block: &mut syn::Block) -> bool {
    for stmt in &mut block.stmts {
        match stmt {
            Stmt::Local(local) => {
                if let Some(init) = &mut local.init {
                    if relax_any_lt(&mut init.expr) {
                        return true;
                    }
                }
            }
            Stmt::Expr(expr, _) => {
                if relax_any_lt(expr) {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

fn relax_any_lt(expr: &mut Expr) -> bool {
    match expr {
        Expr::Binary(bin) if matches!(bin.op, syn::BinOp::Lt(_)) => {
            let left = bin.left.clone();
            let right = bin.right.clone();
            *expr = syn::parse_quote!(#left <= #right);
            true
        }
        Expr::Binary(bin) => relax_any_lt(&mut bin.left) || relax_any_lt(&mut bin.right),
        Expr::Paren(paren) => relax_any_lt(&mut paren.expr),
        Expr::Cast(cast) => relax_any_lt(&mut cast.expr),
        Expr::If(if_expr) => {
            relax_any_lt(&mut if_expr.cond)
                || relax_lt_in_block(&mut if_expr.then_branch)
                || if_expr
                    .else_branch
                    .as_mut()
                    .is_some_and(|(_, branch)| relax_any_lt(branch))
        }
        Expr::Block(block) => relax_lt_in_block(&mut block.block),
        _ => false,
    }
}

/// Point the returned call at the other parameter.
pub fn swap_returned_call_param(func: &mut ItemFn) -> bool {
    let params = param_names(func);
    let Some(expr) = returned_expr(func) else {
        return false;
    };
    swap_call_param(expr, &params)
}

fn param_names(func: &ItemFn) -> Vec<String> {
    func.sig
        .inputs
        .iter()
        .filter_map(|arg| match arg {
            syn::FnArg::Typed(pat) => match &*pat.pat {
                Pat::Ident(id) => Some(id.ident.to_string()),
                _ => None,
            },
            _ => None,
        })
        .collect()
}

fn swap_call_param(expr: &mut Expr, params: &[String]) -> bool {
    match expr {
        Expr::Call(call) => call.args.iter_mut().any(|arg| retarget_path(arg, params)),
        Expr::Binary(bin) => {
            swap_call_param(&mut bin.left, params) || swap_call_param(&mut bin.right, params)
        }
        Expr::Paren(paren) => swap_call_param(&mut paren.expr, params),
        _ => false,
    }
}

fn retarget_path(expr: &mut Expr, params: &[String]) -> bool {
    let Expr::Path(path) = expr else {
        return false;
    };
    let Some(name) = path.path.get_ident() else {
        return false;
    };
    let name = name.to_string();
    let Some(other) = params.iter().find(|param| *param != &name) else {
        return false;
    };
    let ident = syn::Ident::new(other, proc_macro2::Span::call_site());
    *expr = syn::parse_quote!(#ident);
    true
}

/// Replace a returned `!=` with `==`.
pub fn flip_returned_neq(func: &mut ItemFn) -> bool {
    let Some(expr) = returned_expr(func) else {
        return false;
    };
    let Expr::Binary(bin) = expr else {
        return false;
    };
    if !matches!(bin.op, syn::BinOp::Ne(_)) {
        return false;
    }
    let left = bin.left.clone();
    let right = bin.right.clone();
    *expr = syn::parse_quote!(#left == #right);
    true
}

/// Turn a returned sum into that sum minus one.
pub fn subtract_one_from_returned_sum(func: &mut ItemFn) -> bool {
    let Some(expr) = returned_expr(func) else {
        return false;
    };
    let is_add = matches!(
        expr,
        Expr::Binary(bin) if matches!(bin.op, syn::BinOp::Add(_))
    );
    if !is_add {
        return false;
    }
    let inner = expr.clone();
    *expr = syn::parse_quote!((#inner) - 1);
    true
}

/// Double the integer literal passed to the call whose result is returned.
pub fn replace_returned_call_literal(func: &mut ItemFn) -> bool {
    let Some(init) = returned_init(func) else {
        return false;
    };
    let Expr::MethodCall(call) = init else {
        return false;
    };
    let Some(arg) = call.args.first_mut() else {
        return false;
    };
    let Expr::Lit(lit_expr) = arg else {
        return false;
    };
    let Lit::Int(lit) = &lit_expr.lit else {
        return false;
    };
    let Ok(n) = lit.base10_parse::<u128>() else {
        return false;
    };
    let next = n.saturating_mul(2);
    if next == n {
        return false;
    }
    *arg = syn::parse_str(&next.to_string()).unwrap_or_else(|_| unreachable!("decimal literal"));
    true
}

/// Halve the integer literal in a comparison that guards an early return.
pub fn halve_guard_literal(func: &mut ItemFn) -> bool {
    for stmt in &mut func.block.stmts {
        let Stmt::Expr(expr, _) = stmt else {
            continue;
        };
        if halve_if_guard(expr) {
            return true;
        }
    }
    false
}

fn halve_if_guard(expr: &mut Expr) -> bool {
    let Expr::If(if_expr) = expr else {
        return false;
    };
    let returns = if_expr
        .then_branch
        .stmts
        .iter()
        .any(|stmt| matches!(stmt, Stmt::Expr(Expr::Return(_), _)));
    if !returns {
        return false;
    }
    let Expr::Binary(bin) = &mut *if_expr.cond else {
        return false;
    };
    if !matches!(
        bin.op,
        syn::BinOp::Ge(_) | syn::BinOp::Gt(_) | syn::BinOp::Le(_) | syn::BinOp::Lt(_)
    ) {
        return false;
    }
    halve_lit(&mut bin.right) || halve_lit(&mut bin.left)
}

fn halve_lit(expr: &mut Expr) -> bool {
    let Expr::Lit(lit_expr) = expr else {
        return false;
    };
    let syn::Lit::Int(lit) = &lit_expr.lit else {
        return false;
    };
    let Ok(n) = lit.base10_parse::<u128>() else {
        return false;
    };
    if n < 2 || n % 2 != 0 {
        return false;
    }
    *expr = syn::parse_str(&(n / 2).to_string()).unwrap_or_else(|_| unreachable!("decimal"));
    true
}

/// Replace a returned `x >> y` with `x >> (y + 1)`.
pub fn increment_returned_shift(func: &mut ItemFn) -> bool {
    let Some(init) = returned_init(func) else {
        return false;
    };
    let Expr::Binary(bin) = &mut *init else {
        return false;
    };
    if !matches!(bin.op, syn::BinOp::Shr(_)) {
        return false;
    }
    let right = bin.right.clone();
    bin.right = syn::parse_quote!((#right + 1));
    true
}

/// Copy the next `else if` arm onto the first arm of the returned `if`.
pub fn copy_next_if_arm(func: &mut ItemFn) -> bool {
    let Some(expr) = returned_expr(func) else {
        return false;
    };
    let Expr::If(outer) = expr else {
        return false;
    };
    let Some((_, else_branch)) = &outer.else_branch else {
        return false;
    };
    let Expr::If(next) = &**else_branch else {
        return false;
    };
    let Some(Stmt::Expr(next_body, _)) = next.then_branch.stmts.last() else {
        return false;
    };
    let next_body = next_body.clone();
    let Some(Stmt::Expr(first, _)) = outer.then_branch.stmts.last_mut() else {
        return false;
    };
    *first = next_body;
    true
}

/// Increment the first integer literal in a returned `if` arm.
pub fn increment_returned_if_literal(func: &mut ItemFn) -> bool {
    let Some(expr) = returned_expr(func) else {
        return false;
    };
    increment_first_literal(expr)
}

fn increment_first_literal(expr: &mut Expr) -> bool {
    match expr {
        Expr::Lit(lit_expr) => {
            let Lit::Int(lit) = &lit_expr.lit else {
                return false;
            };
            let Ok(n) = lit.base10_parse::<u128>() else {
                return false;
            };
            let next = n.saturating_add(1);
            if next == n {
                return false;
            }
            *expr = syn::parse_str(&next.to_string()).unwrap_or_else(|_| unreachable!("decimal"));
            true
        }
        Expr::If(if_expr) => {
            let found = if_expr.then_branch.stmts.iter_mut().any(|stmt| match stmt {
                Stmt::Expr(inner, _) => increment_first_literal(inner),
                _ => false,
            });
            if found {
                return true;
            }
            if let Some((_, else_branch)) = &mut if_expr.else_branch {
                increment_first_literal(else_branch)
            } else {
                false
            }
        }
        Expr::Block(block) => block.block.stmts.iter_mut().any(|stmt| match stmt {
            Stmt::Expr(inner, _) => increment_first_literal(inner),
            _ => false,
        }),
        Expr::Paren(paren) => increment_first_literal(&mut paren.expr),
        _ => false,
    }
}

/// Replace the returned call `recv.method(arg)` with `recv / arg`.
pub fn replace_returned_call_with_div(func: &mut ItemFn) -> bool {
    let Some(init) = returned_init(func) else {
        return false;
    };
    let (recv, arg) = {
        let Expr::MethodCall(call) = &*init else {
            return false;
        };
        if call.args.len() != 1 {
            return false;
        }
        (call.receiver.clone(), call.args[0].clone())
    };
    *init = syn::parse_quote!(#recv / #arg);
    true
}

/// Negate a returned `is_empty` call.
pub fn negate_returned_is_empty(func: &mut ItemFn) -> bool {
    let Some(expr) = returned_expr(func) else {
        return false;
    };
    let Expr::MethodCall(call) = expr else {
        return false;
    };
    if call.method != "is_empty" {
        return false;
    }
    let recv = call.receiver.clone();
    *expr = syn::parse_quote!(!#recv.is_empty());
    true
}

/// Replace a returned `is_empty` call with `len() == 1`.
pub fn returned_empty_becomes_len_one(func: &mut ItemFn) -> bool {
    let Some(expr) = returned_expr(func) else {
        return false;
    };
    let Expr::MethodCall(call) = expr else {
        return false;
    };
    if call.method != "is_empty" {
        return false;
    }
    let recv = call.receiver.clone();
    *expr = syn::parse_quote!(#recv.len() == 1);
    true
}

/// Replace the first `<=` in an `if` condition with `<`.
pub fn relax_first_guard_le(func: &mut ItemFn) -> bool {
    for stmt in &mut func.block.stmts {
        let Stmt::Expr(Expr::If(if_expr), _) = stmt else {
            continue;
        };
        if relax_le(&mut if_expr.cond) {
            return true;
        }
    }
    false
}

fn relax_le(expr: &mut Expr) -> bool {
    match expr {
        Expr::Binary(bin) if matches!(bin.op, syn::BinOp::Le(_)) => {
            let left = bin.left.clone();
            let right = bin.right.clone();
            *expr = syn::parse_quote!(#left < #right);
            true
        }
        Expr::Binary(bin) => relax_le(&mut bin.left) || relax_le(&mut bin.right),
        Expr::Paren(paren) => relax_le(&mut paren.expr),
        _ => false,
    }
}

/// Replace the first `<` in an `if` condition with `<=`.
pub fn relax_first_guard_lt(func: &mut ItemFn) -> bool {
    for stmt in &mut func.block.stmts {
        let Stmt::Expr(Expr::If(if_expr), _) = stmt else {
            continue;
        };
        if relax_lt(&mut if_expr.cond) {
            return true;
        }
    }
    false
}

fn relax_lt(expr: &mut Expr) -> bool {
    match expr {
        Expr::Binary(bin) if matches!(bin.op, syn::BinOp::Lt(_)) => {
            let left = bin.left.clone();
            let right = bin.right.clone();
            *expr = syn::parse_quote!(#left <= #right);
            true
        }
        Expr::Binary(bin) => relax_lt(&mut bin.left) || relax_lt(&mut bin.right),
        Expr::Paren(paren) => relax_lt(&mut paren.expr),
        _ => false,
    }
}

/// Increment the literal on the right of the first `>` in an `if` condition.
pub fn increment_first_guard_gt_literal(func: &mut ItemFn) -> bool {
    for stmt in &mut func.block.stmts {
        let Stmt::Expr(Expr::If(if_expr), _) = stmt else {
            continue;
        };
        if increment_gt_lit(&mut if_expr.cond) {
            return true;
        }
    }
    false
}

fn increment_gt_lit(expr: &mut Expr) -> bool {
    match expr {
        Expr::Binary(bin) if matches!(bin.op, syn::BinOp::Gt(_)) => increment_lit(&mut bin.right),
        Expr::Binary(bin) => increment_gt_lit(&mut bin.left) || increment_gt_lit(&mut bin.right),
        Expr::Paren(paren) => increment_gt_lit(&mut paren.expr),
        _ => false,
    }
}

/// Replace the first `!=` in an `if` condition with `==`.
pub fn flip_first_guard_neq(func: &mut ItemFn) -> bool {
    for stmt in &mut func.block.stmts {
        let Stmt::Expr(Expr::If(if_expr), _) = stmt else {
            continue;
        };
        if flip_neq(&mut if_expr.cond) {
            return true;
        }
    }
    false
}

/// Decrement the literal on the right of the first `<` in an `if` condition.
pub fn decrement_first_guard_lt_literal(func: &mut ItemFn) -> bool {
    for stmt in &mut func.block.stmts {
        let Stmt::Expr(Expr::If(if_expr), _) = stmt else {
            continue;
        };
        if decrement_lt_lit(&mut if_expr.cond) {
            return true;
        }
    }
    false
}

/// Raise the literal argument of the first `saturating_sub` by one.
pub fn increment_saturating_sub_lit(func: &mut ItemFn) -> bool {
    edit_saturating_sub(&mut func.block)
}

fn edit_saturating_sub(block: &mut syn::Block) -> bool {
    for stmt in &mut block.stmts {
        match stmt {
            syn::Stmt::Local(local) => {
                if let Some(init) = &mut local.init {
                    if increment_saturating_sub(&mut init.expr) {
                        return true;
                    }
                }
            }
            syn::Stmt::Expr(expr, _) => {
                if increment_saturating_sub(expr) {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

fn increment_saturating_sub(expr: &mut Expr) -> bool {
    match expr {
        Expr::MethodCall(call) if call.method == "saturating_sub" => {
            call.args.iter_mut().any(increment_lit)
        }
        Expr::Binary(bin) => {
            increment_saturating_sub(&mut bin.left) || increment_saturating_sub(&mut bin.right)
        }
        Expr::Call(call) => call.args.iter_mut().any(increment_saturating_sub),
        Expr::If(if_expr) => {
            increment_saturating_sub(&mut if_expr.cond)
                || if_expr.then_branch.stmts.iter_mut().any(|stmt| match stmt {
                    syn::Stmt::Expr(expr, _) => increment_saturating_sub(expr),
                    syn::Stmt::Local(local) => local
                        .init
                        .as_mut()
                        .is_some_and(|init| increment_saturating_sub(&mut init.expr)),
                    _ => false,
                })
        }
        _ => false,
    }
}

/// Set the first `==` integer literal to 0.
pub fn zero_eq_lit(func: &mut ItemFn) -> bool {
    zero_eq_in_block(&mut func.block)
}

fn zero_eq_in_block(block: &mut syn::Block) -> bool {
    for stmt in &mut block.stmts {
        let syn::Stmt::Expr(expr, _) = stmt else {
            continue;
        };
        if zero_eq_lit_expr(expr) {
            return true;
        }
    }
    false
}

fn zero_eq_lit_expr(expr: &mut Expr) -> bool {
    match expr {
        Expr::Binary(bin) if matches!(bin.op, syn::BinOp::Eq(_)) => {
            if zero_lit(&mut bin.left) || zero_lit(&mut bin.right) {
                return true;
            }
            zero_eq_lit_expr(&mut bin.left) || zero_eq_lit_expr(&mut bin.right)
        }
        Expr::Binary(bin) => zero_eq_lit_expr(&mut bin.left) || zero_eq_lit_expr(&mut bin.right),
        Expr::Paren(paren) => zero_eq_lit_expr(&mut paren.expr),
        Expr::If(if_expr) => {
            zero_eq_lit_expr(&mut if_expr.cond)
                || if_expr.then_branch.stmts.iter_mut().any(|stmt| match stmt {
                    syn::Stmt::Expr(inner, _) => zero_eq_lit_expr(inner),
                    _ => false,
                })
        }
        Expr::Index(index) => {
            zero_eq_lit_expr(&mut index.expr) || zero_eq_lit_expr(&mut index.index)
        }
        _ => false,
    }
}

fn zero_lit(expr: &mut Expr) -> bool {
    let Expr::Lit(lit_expr) = expr else {
        return false;
    };
    if !matches!(lit_expr.lit, Lit::Int(_)) {
        return false;
    }
    *expr = syn::parse_quote!(0);
    true
}

/// Raise the first `==` literal inside a `for` by one.
pub fn increment_eq_lit_in_for(func: &mut ItemFn) -> bool {
    edit_for_eq_lit(&mut func.block, true)
}

/// Replace the first `==` literal inside a `for` with `false`.
pub fn eq_lit_in_for_becomes_false(func: &mut ItemFn) -> bool {
    edit_for_eq_lit(&mut func.block, false)
}

fn edit_for_eq_lit(block: &mut syn::Block, increment: bool) -> bool {
    for stmt in &mut block.stmts {
        match stmt {
            syn::Stmt::Expr(Expr::ForLoop(fl), _) => {
                if edit_eq_lit_stmts(&mut fl.body.stmts, increment) {
                    return true;
                }
            }
            syn::Stmt::Expr(Expr::Block(inner), _) => {
                if edit_for_eq_lit(&mut inner.block, increment) {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

fn edit_eq_lit_stmts(stmts: &mut [syn::Stmt], increment: bool) -> bool {
    for stmt in stmts {
        let syn::Stmt::Expr(expr, _) = stmt else {
            continue;
        };
        if edit_eq_lit(expr, increment) {
            return true;
        }
    }
    false
}

fn edit_eq_lit(expr: &mut Expr, increment: bool) -> bool {
    match expr {
        Expr::Binary(bin) if matches!(bin.op, syn::BinOp::Eq(_)) => {
            if increment {
                if increment_lit(&mut bin.left) || increment_lit(&mut bin.right) {
                    return true;
                }
            } else if matches!(bin.left.as_ref(), Expr::Lit(_))
                || matches!(bin.right.as_ref(), Expr::Lit(_))
            {
                *expr = syn::parse_quote!(false);
                return true;
            }
            edit_eq_lit(&mut bin.left, increment) || edit_eq_lit(&mut bin.right, increment)
        }
        Expr::Binary(bin) => {
            edit_eq_lit(&mut bin.left, increment) || edit_eq_lit(&mut bin.right, increment)
        }
        Expr::Paren(paren) => edit_eq_lit(&mut paren.expr, increment),
        Expr::If(if_expr) => {
            edit_eq_lit(&mut if_expr.cond, increment)
                || edit_eq_lit_stmts(&mut if_expr.then_branch.stmts, increment)
        }
        Expr::Index(index) => edit_eq_lit(&mut index.expr, increment),
        _ => false,
    }
}

fn decrement_lt_lit(expr: &mut Expr) -> bool {
    match expr {
        Expr::Binary(bin) if matches!(bin.op, syn::BinOp::Lt(_)) => decrement_lit(&mut bin.right),
        Expr::Binary(bin) => decrement_lt_lit(&mut bin.left) || decrement_lt_lit(&mut bin.right),
        Expr::Paren(paren) => decrement_lt_lit(&mut paren.expr),
        Expr::Cast(cast) => decrement_lt_lit(&mut cast.expr),
        _ => false,
    }
}

/// Drop the left operand of the first `&&` in an `if` condition.
pub fn drop_first_guard_and_left(func: &mut ItemFn) -> bool {
    for stmt in &mut func.block.stmts {
        let Stmt::Expr(Expr::If(if_expr), _) = stmt else {
            continue;
        };
        let right = match if_expr.cond.as_ref() {
            Expr::Binary(bin) if matches!(bin.op, syn::BinOp::And(_)) => (*bin.right).clone(),
            _ => continue,
        };
        *if_expr.cond = right;
        return true;
    }
    false
}
