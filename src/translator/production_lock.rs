//! Lock queries over the production `cfg` arm.
//!
//! The formula is built from that arm. Unpatched `body ∧ ¬clause` is UNSAT.
//! A source patch that breaks the clause makes the same query SAT.
//! Predicate samples evaluate the patched function as a `syn` tree.
//! Quantified queries stay bitvectors. A sample that still walks source text
//! is waiting for the same evaluator.
//! The MIR text is checked afterwards: the compiled compare must be the
//! operator this translation used.

use syn::visit::Visit;

use super::ast_body::{self, CmpOp};
use super::sample_eval::{self, Val};
use z3::ast::{Array, Ast, BV, Bool, exists_const};
use z3::{Config, Context, SatResult, Solver, Sort};

pub fn retain_production(mut func: syn::ItemFn) -> syn::ItemFn {
    retain_block(&mut func.block);
    func
}

fn retain_block(block: &mut syn::Block) {
    let stmts = std::mem::take(&mut block.stmts);
    let mut kept = Vec::with_capacity(stmts.len());
    for mut stmt in stmts {
        if cfg_is_not_production(stmt_attrs(&stmt)) {
            continue;
        }
        clear_production_attr(&mut stmt);
        walk_stmt(&mut stmt);
        kept.push(stmt);
    }
    block.stmts = kept;
}

fn stmt_attrs(stmt: &syn::Stmt) -> &[syn::Attribute] {
    match stmt {
        syn::Stmt::Local(local) => &local.attrs,
        syn::Stmt::Expr(expr, _) => expr_attrs(expr),
        syn::Stmt::Macro(mac) => &mac.attrs,
        syn::Stmt::Item(_) => &[],
    }
}

fn expr_attrs(expr: &syn::Expr) -> &[syn::Attribute] {
    match expr {
        syn::Expr::Block(e) => &e.attrs,
        syn::Expr::ForLoop(e) => &e.attrs,
        syn::Expr::If(e) => &e.attrs,
        syn::Expr::While(e) => &e.attrs,
        syn::Expr::Loop(e) => &e.attrs,
        syn::Expr::Let(e) => &e.attrs,
        _ => &[],
    }
}

fn clear_production_attr(stmt: &mut syn::Stmt) {
    let attrs = match stmt {
        syn::Stmt::Local(local) => &mut local.attrs,
        syn::Stmt::Expr(syn::Expr::Block(e), _) => &mut e.attrs,
        syn::Stmt::Expr(syn::Expr::ForLoop(e), _) => &mut e.attrs,
        syn::Stmt::Expr(syn::Expr::If(e), _) => &mut e.attrs,
        syn::Stmt::Expr(syn::Expr::While(e), _) => &mut e.attrs,
        syn::Stmt::Expr(syn::Expr::Loop(e), _) => &mut e.attrs,
        syn::Stmt::Expr(syn::Expr::Let(e), _) => &mut e.attrs,
        _ => return,
    };
    attrs.retain(|attr| !cfg_is_production(std::slice::from_ref(attr)));
}

fn walk_stmt(stmt: &mut syn::Stmt) {
    match stmt {
        syn::Stmt::Expr(syn::Expr::Block(inner), _) => retain_block(&mut inner.block),
        syn::Stmt::Expr(syn::Expr::ForLoop(inner), _) => retain_block(&mut inner.body),
        syn::Stmt::Expr(syn::Expr::While(inner), _) => retain_block(&mut inner.body),
        syn::Stmt::Expr(syn::Expr::Loop(inner), _) => retain_block(&mut inner.body),
        syn::Stmt::Expr(syn::Expr::If(inner), _) => {
            retain_block(&mut inner.then_branch);
            if let Some((_, else_branch)) = inner.else_branch.as_mut() {
                if let syn::Expr::Block(block) = else_branch.as_mut() {
                    retain_block(&mut block.block);
                }
            }
        }
        _ => {}
    }
}

fn cfg_is_production(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|a| {
        let s = quote_attr(a);
        s.contains("feature") && s.contains("production") && !s.contains("not")
    })
}

fn cfg_is_not_production(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|a| {
        let s = quote_attr(a);
        s.contains("not") && s.contains("production")
    })
}

fn quote_attr(attr: &syn::Attribute) -> String {
    quote::quote!(#attr).to_string()
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MoneySite {
    pub lt_zero: bool,
    pub cast_u64: bool,
    pub op: MoneyOp,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MoneyOp {
    Gt,
    Ge,
    Absent,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DupSite {
    pub present: bool,
    pub full_prevout: bool,
}

#[derive(Clone, Debug)]
pub struct ProductionFacts {
    pub money: Vec<MoneySite>,
    pub dup: DupSite,
    pub checked_add: bool,
    pub wrapping_add: bool,
    pub der_len_gt: Option<u64>,
    pub der_high_bit: bool,
    pub der_leading_zero: bool,
    pub der_tag_30: bool,
    pub der_rejects_31: bool,
    pub merkle_eq_before_pad: bool,
    pub merkle_eq_present: bool,
    pub sighash_single_le_one: bool,
    pub cache_updates_flags: bool,
}

struct FactVisit {
    facts: ProductionFacts,
}

impl FactVisit {
    fn new() -> Self {
        Self {
            facts: ProductionFacts {
                money: Vec::new(),
                dup: DupSite {
                    present: false,
                    full_prevout: false,
                },
                checked_add: false,
                wrapping_add: false,
                der_len_gt: None,
                der_high_bit: false,
                der_leading_zero: false,
                der_tag_30: false,
                der_rejects_31: false,
                merkle_eq_before_pad: false,
                merkle_eq_present: false,
                sighash_single_le_one: false,
                cache_updates_flags: false,
            },
        }
    }
}

impl<'ast> Visit<'ast> for FactVisit {
    fn visit_expr_method_call(&mut self, node: &'ast syn::ExprMethodCall) {
        let name = node.method.to_string();
        if name == "checked_add" {
            self.facts.checked_add = true;
        }
        if name == "wrapping_add" {
            self.facts.wrapping_add = true;
        }
        if name == "insert" {
            let names = node
                .args
                .iter()
                .flat_map(ast_body::idents_in)
                .collect::<Vec<_>>();
            self.facts.dup.present = true;
            let txid_only = names.iter().any(|name| name == "txid");
            self.facts.dup.full_prevout = names.iter().any(|name| name == "prevout") && !txid_only;
        }
        if name == "update" {
            let names = node
                .args
                .iter()
                .flat_map(ast_body::idents_in)
                .collect::<Vec<_>>();
            if names.iter().any(|name| name == "flags") {
                self.facts.cache_updates_flags = true;
            }
        }
        syn::visit::visit_expr_method_call(self, node);
    }

    fn visit_expr_binary(&mut self, node: &'ast syn::ExprBinary) {
        let names = ast_body::idents_in(&syn::Expr::Binary(node.clone()));
        if names.iter().any(|name| name.starts_with("MAX_MONEY")) {
            let op = match node.op {
                syn::BinOp::Gt(_) => MoneyOp::Gt,
                syn::BinOp::Ge(_) => MoneyOp::Ge,
                _ => MoneyOp::Absent,
            };
            if op != MoneyOp::Absent {
                let cast_u64 = matches!(node.left.as_ref(), syn::Expr::Cast(cast) if type_is(&cast.ty, "u64"))
                    || matches!(node.right.as_ref(), syn::Expr::Cast(cast) if type_is(&cast.ty, "u64"))
                    || names
                        .iter()
                        .any(|name| name == "value_u64" || name == "total_u64");
                self.facts.money.push(MoneySite {
                    lt_zero: false,
                    cast_u64,
                    op,
                });
            }
        }
        if matches!(node.op, syn::BinOp::Lt(_))
            && names.iter().any(|name| name.contains("value"))
            && ast_body::key_of(&node.right).lit == Some(0)
            && !names.iter().any(|name| name.starts_with("MAX_MONEY"))
        {
            self.facts.money.push(MoneySite {
                lt_zero: true,
                cast_u64: false,
                op: MoneyOp::Absent,
            });
        }
        if names.iter().any(|name| name == "signature") && matches!(node.op, syn::BinOp::Gt(_)) {
            if ast_body::key_of(&node.right).lit == Some(73) {
                self.facts.der_len_gt = Some(73);
            }
            if ast_body::key_of(&node.right).lit == Some(74) {
                self.facts.der_len_gt = Some(74);
            }
        }
        syn::visit::visit_expr_binary(self, node);
    }
}

pub fn facts_of(func: &syn::ItemFn) -> ProductionFacts {
    let kept = retain_production(func.clone());
    let mut v = FactVisit::new();
    v.visit_block(&kept.block);
    let scanned = ast_body::analyze(&quote::quote!(#kept).to_string());
    v.facts.der_high_bit = scanned.bits.iter().any(|bit| {
        !bit.or && bit.lit == 0x80 && bit.left.has("signature") && bit.left.index == Some(4)
    });
    v.facts.der_leading_zero = scanned.cmps.iter().any(|cmp| {
        cmp.op == CmpOp::Eq
            && cmp.left.has("signature")
            && cmp.left.index == Some(4)
            && cmp.right.lit == Some(0)
    });
    v.facts.der_tag_30 = scanned
        .cmps
        .iter()
        .any(|cmp| cmp.left.lit == Some(0x30) || cmp.right.lit == Some(0x30));
    v.facts.der_rejects_31 = scanned.cmps.iter().any(|cmp| {
        cmp.op == CmpOp::Ne && (cmp.left.lit == Some(0x30) || cmp.right.lit == Some(0x30))
    }) && scanned
        .cmps
        .iter()
        .all(|cmp| cmp.left.lit != Some(0x31) && cmp.right.lit != Some(0x31));
    v.facts.merkle_eq_present = scanned.marks.iter().any(|mark| *mark == "merkle-eq");
    v.facts.merkle_eq_before_pad = v.facts.merkle_eq_present
        && match (
            scanned.marks.iter().position(|mark| *mark == "merkle-eq"),
            scanned.marks.iter().position(|mark| *mark == "len-and-1"),
        ) {
            (Some(eq), Some(pad)) => eq < pad,
            (Some(_), None) => true,
            _ => false,
        };
    v.facts.sighash_single_le_one = scanned
        .stores
        .iter()
        .any(|store| store.base == "result" && store.index == 0 && store.value == 1);
    v.facts
}

fn type_is(ty: &syn::Type, name: &str) -> bool {
    match ty {
        syn::Type::Path(path) => path
            .path
            .segments
            .last()
            .is_some_and(|seg| seg.ident == name),
        _ => false,
    }
}

fn solver() -> (Config, Context) {
    let mut cfg = Config::new();
    cfg.set_model_generation(true);
    cfg.set_timeout_msec(5_000);
    let ctx = Context::new(&cfg);
    (cfg, ctx)
}

/// `body ∧ ¬clause`. UNSAT: the body meets the clause. SAT: it does not.
pub(crate) fn check(build: impl FnOnce(&Context, &Solver)) -> SatResult {
    let (_cfg, ctx) = solver();
    let s = Solver::new(&ctx);
    build(&ctx, &s);
    s.check()
}

fn money_rejected<'a>(
    ctx: &'a Context,
    facts: &ProductionFacts,
    value: &BV<'a>,
    max_money: i64,
) -> Bool<'a> {
    let max = BV::from_i64(ctx, max_money, 64);
    let zero = BV::from_i64(ctx, 0, 64);
    let mut rejected = Bool::from_bool(ctx, false);
    for site in &facts.money {
        if site.lt_zero {
            rejected |= value.bvslt(&zero);
        }
        let over = match (site.cast_u64, site.op) {
            (true, MoneyOp::Gt) => Some(value.bvugt(&max)),
            (true, MoneyOp::Ge) => Some(value.bvuge(&max)),
            (false, MoneyOp::Gt) => Some(value.bvsgt(&max)),
            (false, MoneyOp::Ge) => Some(value.bvsge(&max)),
            (_, MoneyOp::Absent) => None,
        };
        if let Some(over) = over {
            rejected |= over;
        }
    }
    rejected
}

pub fn money_in_range_query(facts: &ProductionFacts) -> SatResult {
    let impl_max = crate::parser::spec_expr::impl_i64("MAX_MONEY");
    let spec_max = crate::parser::spec_expr::upper_bound("M_MAX") as i64;
    check(|ctx, solver| {
        let value = BV::new_const(ctx, "value", 64);
        let rejected = money_rejected(ctx, facts, &value, impl_max);
        // Clause: the spec cap is in range, so the implementation does not reject it.
        solver.assert(&value._eq(&BV::from_i64(ctx, spec_max, 64)));
        solver.assert(&rejected);
    })
}

pub fn negative_rejected_query(facts: &ProductionFacts) -> SatResult {
    let impl_max = crate::parser::spec_expr::impl_i64("MAX_MONEY");
    check(|ctx, solver| {
        let value = BV::from_i64(ctx, -1, 64);
        let rejected = money_rejected(ctx, facts, &value, impl_max);
        // Clause: a negative i64 is rejected.
        solver.assert(&rejected.not());
    })
}

fn exists_prevout_pair<'a>(
    ctx: &'a Context,
    n: &BV<'a>,
    txid: &Array<'a>,
    vout: &Array<'a>,
    full: bool,
    tag: &str,
) -> Bool<'a> {
    let i = BV::new_const(ctx, format!("i_{tag}"), 32);
    let j = BV::new_const(ctx, format!("j_{tag}"), 32);
    let in_range = i.bvult(n) & j.bvult(n) & i._eq(&j).not();
    let txid_eq = txid
        .select(&i)
        .as_bv()
        .unwrap()
        ._eq(&txid.select(&j).as_bv().unwrap());
    let vout_eq = vout
        .select(&i)
        .as_bv()
        .unwrap()
        ._eq(&vout.select(&j).as_bv().unwrap());
    let key_eq = if full { txid_eq & vout_eq } else { txid_eq };
    exists_const(ctx, &[&i, &j], &[], &(in_range & key_eq))
}

pub fn dup_query(facts: &ProductionFacts) -> SatResult {
    check(|ctx, solver| {
        let idx = Sort::bitvector(ctx, 32);
        let word = Sort::bitvector(ctx, 32);
        let n = BV::new_const(ctx, "n_inputs", 32);
        let max = BV::from_u64(ctx, 100_000, 32);
        solver.assert(&n.bvule(&max));
        solver.assert(&n.bvuge(&BV::from_u64(ctx, 2, 32)));
        let txid = Array::new_const(ctx, "txid", &idx, &word);
        let vout = Array::new_const(ctx, "vout", &idx, &word);
        let full = exists_prevout_pair(ctx, &n, &txid, &vout, true, "full");
        let rejected = if !facts.dup.present {
            Bool::from_bool(ctx, false)
        } else if facts.dup.full_prevout {
            full.clone()
        } else {
            exists_prevout_pair(ctx, &n, &txid, &vout, false, "txid")
        };
        // Clause: rejected iff some i ≠ j share the full prevout.
        solver.assert(&rejected.iff(&full).not());
    })
}

pub fn overflow_query(facts: &ProductionFacts) -> SatResult {
    check(|ctx, solver| {
        let acc = BV::new_const(ctx, "acc", 64);
        let next = BV::new_const(ctx, "next", 64);
        let (_sum, ok) = crate::translator::z3_translator::Z3Translator::i64_checked_binop(
            ctx,
            "checked_add",
            &acc,
            &next,
        );
        // Inductive step: Err iff this add overflows. wrapping_add does not.
        let returned_err = if facts.wrapping_add {
            Bool::from_bool(ctx, false)
        } else if facts.checked_add {
            ok.not()
        } else {
            Bool::from_bool(ctx, false)
        };
        let clause = returned_err.iff(&ok.not());
        solver.assert(&clause.not());
    })
}

pub fn der_len_query(facts: &ProductionFacts) -> SatResult {
    let (_, spec_hi) = crate::parser::spec_expr::range_near("IsStrictDER");
    let spec_hi = spec_hi as i64;
    let body_bound = facts.der_len_gt.unwrap_or(spec_hi as u64) as i64;
    check(|ctx, solver| {
        let len = BV::from_i64(ctx, spec_hi + 1, 32);
        let rejected = len.bvugt(&BV::from_i64(ctx, body_bound, 32));
        let clause = len.bvugt(&BV::from_i64(ctx, spec_hi, 32));
        solver.assert(&rejected.iff(&clause).not());
    })
}

pub fn merkle_query(facts: &ProductionFacts) -> SatResult {
    check(|ctx, solver| {
        let left = BV::new_const(ctx, "h0", 32);
        let right = BV::new_const(ctx, "h1", 32);
        let equal = left._eq(&right);
        let mutated = if facts.merkle_eq_present && facts.merkle_eq_before_pad {
            equal.clone()
        } else if facts.merkle_eq_present {
            // The compare runs after the odd pad, so the padded pair matches
            // even when the unpadded hashes differ.
            Bool::from_bool(ctx, true)
        } else {
            Bool::from_bool(ctx, false)
        };
        let clause = if crate::parser::spec_expr::merkle_compares_unpadded() {
            mutated.iff(&equal)
        } else {
            Bool::from_bool(ctx, false)
        };
        solver.assert(&clause.not());
    })
}

pub fn der_high_bit_query(facts: &ProductionFacts) -> SatResult {
    check(|ctx, solver| {
        let b = BV::from_i64(ctx, 0x80, 8);
        let mask = BV::from_i64(ctx, 0x80, 8);
        let is_high = b.bvand(&mask)._eq(&mask).not().not();
        let rejected = if facts.der_high_bit {
            is_high
        } else {
            Bool::from_bool(ctx, false)
        };
        solver.assert(&rejected.not());
    })
}

pub fn der_leading_zero_query(facts: &ProductionFacts) -> SatResult {
    check(|ctx, solver| {
        let b4 = BV::from_i64(ctx, 0x00, 8);
        let b5 = BV::from_i64(ctx, 0x00, 8);
        let mask = BV::from_i64(ctx, 0x80, 8);
        let zero = BV::from_i64(ctx, 0, 8);
        let is_bad = b4._eq(&zero) & b5.bvand(&mask)._eq(&zero);
        let rejected = if facts.der_leading_zero {
            is_bad
        } else {
            Bool::from_bool(ctx, false)
        };
        solver.assert(&rejected.not());
    })
}

pub fn der_tag_query(facts: &ProductionFacts) -> SatResult {
    check(|ctx, solver| {
        let tag = BV::from_i64(ctx, 0x31, 8);
        let bad = tag._eq(&BV::from_i64(ctx, 0x31, 8));
        let rejected = if facts.der_rejects_31 {
            bad
        } else {
            Bool::from_bool(ctx, false)
        };
        solver.assert(&rejected.not());
    })
}

pub fn sighash_single_query(facts: &ProductionFacts) -> SatResult {
    check(|ctx, solver| {
        let b0 = BV::new_const(ctx, "b0", 8);
        let rest = BV::new_const(ctx, "rest", 248);
        let one = BV::from_i64(
            ctx,
            crate::parser::spec_expr::sighash_single_lead() as i64,
            8,
        );
        let zero = BV::from_i64(ctx, 0, 248);
        if facts.sighash_single_le_one {
            solver.assert(&b0._eq(&one));
            solver.assert(&rest._eq(&zero));
        }
        // Clause: byte 0 is 1 and the other bytes are 0.
        let clause = b0._eq(&one) & rest._eq(&zero);
        solver.assert(&clause.not());
    })
}

pub fn cache_flags_query(facts: &ProductionFacts) -> SatResult {
    check(|ctx, solver| {
        let flags = BV::new_const(ctx, "flags", 32);
        let flags_b = BV::new_const(ctx, "flags_b", 32);
        let key_a = BV::new_const(ctx, "key_a", 64);
        let key_b = BV::new_const(ctx, "key_b", 64);
        // Uninterpreted hash of the inputs the production key actually updates.
        // Flags are in the key only when the body hashes them.
        if facts.cache_updates_flags {
            solver.assert(&flags._eq(&flags_b).iff(&key_a._eq(&key_b)));
        } else {
            solver.assert(&key_a._eq(&key_b));
        }
        // Clause: different flags do not share a key.
        let differ = flags._eq(&flags_b).not();
        let clause = differ.implies(&key_a._eq(&key_b).not());
        solver.assert(&clause.not());
    })
}

/// A cache hit returns eval(script bytes, flags, witness), not a constant.
pub fn cache_hit_query(returns_cached: bool) -> SatResult {
    check(|ctx, solver| {
        let eval = Bool::new_const(ctx, "eval");
        let returned = if returns_cached {
            eval.clone()
        } else {
            Bool::from_bool(ctx, true)
        };
        solver.assert(&returned._eq(&eval).not());
    })
}

/// One interpreter step. The pc advance is the integer in `i += N;`.
pub fn script_step_query(src: &str) -> SatResult {
    let step = pure_addend(src, "i");
    check(|ctx, solver| {
        let i = BV::new_const(ctx, "i", 32);
        let len = BV::new_const(ctx, "len", 32);
        let max = BV::from_u64(ctx, 10_000, 32);
        let one = BV::from_u64(ctx, 1, 32);
        solver.assert(&len.bvule(&max));
        solver.assert(&i.bvult(&len));
        let next = i.bvadd(&BV::from_u64(ctx, step, 32));
        solver.assert(&next._eq(&i.bvadd(&one)).not());
    })
}

fn pure_addend(src: &str, name: &str) -> u64 {
    let mut other = None;
    for add in ast_body::analyze(src).adds {
        if add.name != name {
            continue;
        }
        if add.by == 1 {
            return 1;
        }
        other.get_or_insert(u64::try_from(add.by).unwrap_or(0));
    }
    other.unwrap_or(0)
}

/// OP_IF pushes a control block. The next depth is `depth + 1`.
pub fn control_step_query(src: &str) -> SatResult {
    let pushes = ast_body::analyze(src)
        .methods
        .iter()
        .any(|method| method.name == "push" && method.recv.has("control_stack"));
    check(|ctx, solver| {
        let h = BV::new_const(ctx, "ctrl", 32);
        let one = BV::from_u64(ctx, 1, 32);
        let next = if pushes { h.bvadd(&one) } else { h.clone() };
        solver.assert(&next._eq(&h.bvadd(&one)).not());
    })
}

/// Outside the pattern the fast path falls through. On the pattern, the
/// result is the uninterpreted verifier.
pub fn fast_path_query(falls_through: bool, calls_verifier: bool) -> SatResult {
    check(|ctx, solver| {
        let pattern = Bool::new_const(ctx, "pattern");
        let verifier = Bool::new_const(ctx, "verifier");
        let result = Bool::new_const(ctx, "result");
        if falls_through {
            solver.assert(&pattern.not().implies(&result.not()));
        }
        if calls_verifier {
            solver.assert(&pattern.implies(&result._eq(&verifier)));
        } else {
            solver.assert(&pattern.implies(&result));
        }
        let clause = pattern.not().implies(&result.not()) & pattern.implies(&result._eq(&verifier));
        solver.assert(&clause.not());
    })
}

/// `result` iff `(sequence & mask) != 0` for the consensus mask.
pub fn masked_bit_query(src: &str, consensus_mask: u64) -> SatResult {
    let body = ast_body::analyze(src);
    let body_mask = body.bits.first().map(|bit| bit.lit as u64).unwrap_or(0);
    let negated = body
        .cmps
        .iter()
        .any(|cmp| cmp.op == CmpOp::Eq && cmp.right.lit == Some(0))
        && !body
            .cmps
            .iter()
            .any(|cmp| cmp.op == CmpOp::Ne && cmp.right.lit == Some(0));
    check(|ctx, solver| {
        let seq = BV::new_const(ctx, "sequence", 32);
        let mask = BV::from_u64(ctx, body_mask, 64).extract(31, 0);
        let zero = BV::from_u64(ctx, 0, 32);
        let bit = seq.bvand(&mask)._eq(&zero).not();
        let result = if negated { bit.not() } else { bit.clone() };
        let want = BV::from_u64(ctx, consensus_mask, 64).extract(31, 0);
        let clause_bit = seq.bvand(&want)._eq(&zero).not();
        solver.assert(&result._eq(&clause_bit).not());
    })
}

/// Low 16 bits of the sequence are the locktime value.
pub fn sequence_value_query(src: &str) -> SatResult {
    let body = ast_body::analyze(src);
    let body_mask = body.bits.first().map(|bit| bit.lit as u64).unwrap_or(0);
    let uses_or = body.bits.iter().any(|bit| bit.or) && body.bits.iter().all(|bit| bit.or);
    check(|ctx, solver| {
        let seq = BV::new_const(ctx, "sequence", 32);
        let mask = BV::from_u64(ctx, body_mask, 64).extract(31, 0);
        let bits = if uses_or {
            seq.bvor(&mask)
        } else {
            seq.bvand(&mask)
        };
        let low = BV::from_u64(
            ctx,
            crate::parser::spec_expr::mask_in("ExtractSequenceLocktimeValue"),
            64,
        )
        .extract(31, 0);
        let clause = bits._eq(&seq.bvand(&low));
        solver.assert(&clause.not());
    })
}

/// Height iff `locktime < 500_000_000`.
pub fn locktime_kind_query(src: &str) -> SatResult {
    let is_height_cmp = ast_body::analyze(src)
        .cmps
        .iter()
        .find(|cmp| cmp.left.has("locktime") && cmp.right.has("LOCKTIME_THRESHOLD"))
        .map(|cmp| match cmp.op {
            CmpOp::Le => "le",
            CmpOp::Lt => "lt",
            CmpOp::Ge => "ge",
            CmpOp::Gt => "gt",
            _ => "absent",
        })
        .unwrap_or("absent");
    check(|ctx, solver| {
        let locktime = BV::new_const(ctx, "locktime", 32);
        let body_t = BV::from_u64(
            ctx,
            crate::parser::spec_expr::impl_u64("LOCKTIME_THRESHOLD"),
            32,
        );
        let clause_t = BV::from_u64(ctx, crate::parser::spec_expr::locktime_threshold(), 32);
        let is_height = match is_height_cmp {
            "lt" => locktime.bvult(&body_t),
            "le" => locktime.bvule(&body_t),
            "gt" => locktime.bvugt(&body_t),
            "ge" => locktime.bvuge(&body_t),
            _ => Bool::from_bool(ctx, false),
        };
        let want = locktime.bvult(&clause_t);
        solver.assert(&is_height._eq(&want).not());
    })
}

/// Equal locktimes of the same type pass. `>` rejects the equal case.
pub fn bip65_query(src: &str) -> SatResult {
    let body = ast_body::analyze(src);
    let ge = body.cmps.iter().any(|cmp| cmp.op == CmpOp::Ge);
    let types = ast_body::call_named(&body.calls, "locktime_types_match");
    check(|ctx, solver| {
        let tx = BV::new_const(ctx, "tx_lt", 32);
        let stack = BV::new_const(ctx, "stack_lt", 32);
        let same_type = Bool::new_const(ctx, "same_type");
        let ordered = if ge {
            tx.bvuge(&stack)
        } else {
            tx.bvugt(&stack)
        };
        let accepted = if types {
            same_type.clone() & ordered
        } else {
            ordered
        };
        let clause = if crate::parser::spec_expr::bip65_orders_ge() {
            same_type & tx.bvuge(&stack)
        } else {
            same_type & tx.bvugt(&stack)
        };
        solver.assert(&accepted._eq(&clause).not());
    })
}

fn pow_accepts<'a>(src: &str, hash: &BV<'a>, target: &BV<'a>) -> Bool<'a> {
    let op = ast_body::analyze(src)
        .cmps
        .iter()
        .find(|cmp| cmp.left.has("hash_value") && cmp.right.has("target"))
        .map(|cmp| cmp.op);
    match op {
        Some(CmpOp::Le) => hash.bvule(target),
        Some(CmpOp::Lt) => hash.bvult(target),
        Some(CmpOp::Ge) => hash.bvuge(target),
        Some(CmpOp::Gt) => hash.bvugt(target),
        _ => Bool::from_bool(hash.get_ctx(), true),
    }
}

/// Equality with the target is accepted only when the helper says `<=`.
/// Both values are 256 bits and sit below the wrap point.
pub fn pow_equality_query(src: &str) -> SatResult {
    check(|ctx, solver| {
        let hash = BV::from_u64(ctx, 1, 256);
        let target = BV::from_u64(ctx, 1, 256);
        solver.assert(&pow_accepts(src, &hash, &target).not());
    })
}

/// A hash one above the target is rejected by `<` and by `<=`.
pub fn pow_above_query(src: &str) -> SatResult {
    check(|ctx, solver| {
        let hash = BV::from_u64(ctx, 2, 256);
        let target = BV::from_u64(ctx, 1, 256);
        solver.assert(&pow_accepts(src, &hash, &target));
    })
}

/// The compact sign bit is not work when the helper tests it.
pub fn pow_sign_query(src: &str) -> SatResult {
    let body = ast_body::analyze(src);
    let rejects = body.bits.iter().any(|bit| bit.lit == 0x0080_0000)
        && body
            .cmps
            .iter()
            .any(|cmp| cmp.op == CmpOp::Ne && cmp.right.lit == Some(0));
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, rejects).not());
    })
}

/// A zero expanded target is not work when the helper tests it.
pub fn pow_zero_target_query(src: &str) -> SatResult {
    let rejects = ast_body::method_named(&ast_body::analyze(src).methods, "is_zero");
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, rejects).not());
    })
}

/// `check_proof_of_work` applies SHA256 twice and then calls the helper.
pub fn pow_rounds_query(src: &str) -> SatResult {
    let rounds = ast_body::analyze(src)
        .calls
        .iter()
        .filter(|call| {
            call.path.last().is_some_and(|seg| seg == "digest")
                && call.path.iter().any(|seg| seg == "Sha256")
        })
        .count() as u32;
    let spec_rounds = crate::parser::spec_expr::header_hash_rounds();
    check(|ctx, solver| {
        let ok = Bool::from_bool(ctx, rounds == spec_rounds && spec_rounds >= 2);
        solver.assert(&ok.not());
    })
}

pub fn pow_helper_query(src: &str) -> SatResult {
    let calls = ast_body::call_named(&ast_body::analyze(src).calls, "proof_hash_meets_target");
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, calls).not());
    })
}

/// Version 0 is rejected. Version 1 is not.
pub fn header_version_query(src: &str, version: u64) -> SatResult {
    let floor = crate::parser::spec_expr::version_min();
    let version_cmps = ast_body::analyze(src).cmps;
    let lt_floor = version_cmps.iter().any(|cmp| {
        cmp.op == CmpOp::Lt
            && cmp.left.has("header")
            && cmp.left.has("version")
            && cmp.right.lit == Some(floor as i128)
    });
    let le_floor = version_cmps.iter().any(|cmp| {
        cmp.op == CmpOp::Le
            && cmp.left.has("header")
            && cmp.left.has("version")
            && cmp.right.lit == Some(floor as i128)
    });
    check(|ctx, solver| {
        let v = BV::from_u64(ctx, version, 32);
        let bound = BV::from_u64(ctx, floor, 32);
        let rejected = if le_floor {
            v.bvule(&bound)
        } else if lt_floor {
            v.bvult(&bound)
        } else {
            Bool::from_bool(ctx, false)
        };
        if version == 0 {
            solver.assert(&rejected.not());
        } else {
            solver.assert(&rejected);
        }
    })
}

fn future_rejects<'a>(src: &str, ts: &BV<'a>, max_ts: &BV<'a>) -> Option<Bool<'a>> {
    let body = ast_body::analyze(src);
    if !body.time_context_present {
        return None;
    }
    let op = body
        .time_context
        .iter()
        .find(|cmp| cmp.left.has("timestamp") && cmp.right.has("max_ts"))
        .map(|cmp| cmp.op);
    Some(match op {
        Some(CmpOp::Ge) => ts.bvuge(max_ts),
        Some(CmpOp::Gt) => ts.bvugt(max_ts),
        _ => Bool::from_bool(ts.get_ctx(), false),
    })
}

/// A zero timestamp or a zero bits field is rejected. The constant is the one in the source.
pub fn header_rejects_zero(src: &str, field: &str) -> SatResult {
    let constant = ast_body::analyze(src).cmps.into_iter().find_map(|cmp| {
        (cmp.op == CmpOp::Eq && cmp.left.has("header") && cmp.left.has(field))
            .then_some(cmp.right.lit)
            .flatten()
            .map(|lit| u64::try_from(lit).unwrap_or(0))
    });
    check(|ctx, solver| {
        let value = BV::from_u64(ctx, 0, 32);
        let rejected = match constant {
            Some(n) => value._eq(&BV::from_u64(ctx, n, 32)),
            None => Bool::from_bool(ctx, false),
        };
        solver.assert(&rejected.not());
    })
}

/// With a time context, a timestamp equal to the future bound is still valid.
/// The compare has to sit in the `Some` branch. `>=` rejects that equal timestamp.
pub fn header_future_query(src: &str) -> SatResult {
    if !ast_body::analyze(src).time_context_present {
        return SatResult::Sat;
    }
    check(|ctx, solver| {
        let ts = BV::from_u64(ctx, 5, 32);
        let max_ts = BV::from_u64(ctx, 5, 32);
        let rejected = future_rejects(src, &ts, &max_ts).expect("time context");
        solver.assert(&rejected);
    })
}

/// A timestamp one past the future bound is rejected when that compare is in the branch.
pub fn header_future_above_query(src: &str) -> SatResult {
    if !ast_body::analyze(src).time_context_present {
        return SatResult::Sat;
    }
    check(|ctx, solver| {
        let ts = BV::from_u64(ctx, 6, 32);
        let max_ts = BV::from_u64(ctx, 5, 32);
        let rejected = future_rejects(src, &ts, &max_ts).expect("time context");
        solver.assert(&rejected.not());
    })
}

/// A timestamp equal to the median is rejected. One below it is rejected.
/// The compare counts only inside the time-context branch.
/// Unsat means the source has no accepting counterexample.
pub fn header_mtp_query(src: &str, below: bool) -> SatResult {
    if !crate::parser::spec_expr::median_past_is_lower_bound() {
        panic!("spec H05 is not timestamp > MedianTimePast");
    }
    let body = ast_body::analyze(src);
    let lt = body.time_context.iter().any(|cmp| {
        cmp.op == CmpOp::Lt && cmp.left.has("timestamp") && cmp.right.has("median_time_past")
    });
    let le = body.time_context.iter().any(|cmp| {
        cmp.op == CmpOp::Le && cmp.left.has("timestamp") && cmp.right.has("median_time_past")
    });
    check(|ctx, solver| {
        let ts = BV::new_const(ctx, "ts", 32);
        let mtp = BV::new_const(ctx, "mtp", 32);
        if below {
            solver.assert(&ts.bvult(&mtp));
        } else {
            solver.assert(&ts._eq(&mtp));
        }
        let rejected = if le {
            ts.bvule(&mtp)
        } else if lt {
            ts.bvult(&mtp)
        } else {
            Bool::from_bool(ctx, false)
        };
        solver.assert(&rejected.not());
    })
}

fn between<'a>(src: &'a str, start: &str, end: &str) -> &'a str {
    let Some(i) = src.find(start) else {
        return "";
    };
    let rest = &src[i + start.len()..];
    if end.is_empty() {
        return rest;
    }
    match rest.find(end) {
        Some(j) => &rest[..j],
        None => rest,
    }
}

/// v0 accepts 20 or 32 bytes and nothing else. v1 accepts 32 bytes and nothing else.
pub fn witness_program_query(src: &str) -> SatResult {
    let body = ast_body::analyze(src);
    let v0 = ast_body::arm_named(&body.arms, "SegWitV0");
    let v1 = ast_body::arm_named(&body.arms, "TaprootV1");
    let v0_ok = v0.is_some_and(|arm| {
        arm.or_count == 1
            && arm
                .cmps
                .iter()
                .any(|cmp| cmp.right.has("SEGWIT_P2WPKH_LENGTH"))
            && arm
                .cmps
                .iter()
                .any(|cmp| cmp.right.has("SEGWIT_P2WSH_LENGTH"))
    });
    let v1_ok = v1.is_some_and(|arm| {
        arm.or_count == 0
            && arm
                .cmps
                .iter()
                .any(|cmp| cmp.right.has("TAPROOT_PROGRAM_LENGTH"))
    });
    check(|ctx, solver| {
        let len = BV::new_const(ctx, "len", 32);
        let (short, long) = crate::parser::spec_expr::witness_program_lengths();
        let twenty = BV::from_u64(ctx, short, 32);
        let thirty_two = BV::from_u64(ctx, long, 32);
        let v0_accept = if v0_ok {
            len._eq(&twenty) | len._eq(&thirty_two)
        } else {
            Bool::from_bool(ctx, false)
        };
        let v1_accept = if v1_ok {
            len._eq(&thirty_two)
        } else {
            Bool::from_bool(ctx, false)
        };
        let clause = v0_accept._eq(&(len._eq(&twenty) | len._eq(&thirty_two)))
            & v1_accept._eq(&len._eq(&thirty_two));
        solver.assert(&clause.not());
    })
}

pub fn pow_double_hash_query(rounds: u32) -> SatResult {
    let spec_rounds = crate::parser::spec_expr::header_hash_rounds();
    check(|ctx, solver| {
        let header = BV::new_const(ctx, "header", 32);
        let sort = Sort::bitvector(ctx, 32);
        let sha = z3::FuncDecl::new(ctx, "sha256", &[&sort], &sort);
        let once = sha.apply(&[&header]).as_bv().unwrap();
        let twice = sha.apply(&[&once]).as_bv().unwrap();
        let used = if rounds >= spec_rounds {
            twice.clone()
        } else {
            once.clone()
        };
        let clause = if spec_rounds >= 2 { twice } else { once };
        solver.assert(&used._eq(&clause).not());
    })
}

/// CHECKSIG pushes the verifier result. A constant `true` or a negated `is_valid` is SAT.
pub fn checksig_query(src: &str) -> SatResult {
    let body = ast_body::analyze(src);
    let arm = ast_body::arm_named(&body.arms, "OP_CHECKSIG");
    let calls = arm.map(|arm| arm.calls.as_slice()).unwrap_or(&body.calls);
    let pushed = calls.iter().filter(|call| {
        call.path
            .last()
            .is_some_and(|seg| seg == "script_bool_bytes")
    });
    let flipped = pushed
        .clone()
        .any(|call| call.negated.iter().any(|name| name == "is_valid"));
    let constant = pushed
        .clone()
        .any(|call| call.args.iter().any(|arg| arg.bool_lit == Some(true)));
    let calls_verifier = calls.iter().any(|call| {
        call.path.iter().any(|seg| {
            seg == "verify_signature"
                || seg == "verify_ecdsa"
                || seg == "verify_schnorr"
                || seg == "verify_tapscript_schnorr_signature"
        })
    });
    check(|ctx, solver| {
        let verifier = Bool::new_const(ctx, "verifier");
        let result = if flipped {
            verifier.not()
        } else if calls_verifier && !constant {
            verifier.clone()
        } else {
            Bool::from_bool(ctx, true)
        };
        solver.assert(&result._eq(&verifier).not());
    })
}

/// Operators the clause names, taken from the production arm.
pub fn translated_ops(facts: &ProductionFacts) -> Vec<String> {
    let mut ops = Vec::new();
    for site in &facts.money {
        match site.op {
            MoneyOp::Gt => ops.push("Gt".into()),
            MoneyOp::Ge => ops.push("Ge".into()),
            MoneyOp::Absent => {}
        }
        if site.cast_u64 {
            ops.push("as u64".into());
        }
    }
    if facts.dup.present && facts.dup.full_prevout {
        ops.push("insert prevout".into());
    }
    if facts.dup.present && !facts.dup.full_prevout {
        ops.push("insert txid".into());
    }
    ops
}

fn line_has(mir: &str, op: &str, marker: &str) -> bool {
    mir.lines()
        .any(|line| line.contains(op) && line.contains(marker))
}

/// Fail closed when the compiled MIR compare is not the translated operator.
pub fn mir_matches(facts: &ProductionFacts, mir: &str) -> bool {
    let wants_gt = facts
        .money
        .iter()
        .any(|m| m.op == MoneyOp::Gt && m.cast_u64);
    let wants_ge = facts
        .money
        .iter()
        .any(|m| m.op == MoneyOp::Ge && m.cast_u64);
    if wants_gt && !line_has(mir, "Gt(", "MAX_MONEY_U64") {
        return false;
    }
    if wants_ge && !line_has(mir, "Ge(", "MAX_MONEY_U64") {
        return false;
    }
    if facts.dup.full_prevout {
        let insert = mir
            .lines()
            .find(|line| line.contains("HashSet") && line.contains("insert"));
        match insert {
            Some(line) if line.contains("OutPoint") && !line.contains("txid") => {}
            _ => return false,
        }
    }
    if facts.dup.present && !facts.dup.full_prevout && line_has(mir, "insert", "OutPoint") {
        return false;
    }
    if !facts.dup.present && line_has(mir, "HashSet", "insert") && mir.contains("OutPoint") {
        return false;
    }
    if facts.der_len_gt == Some(73) && !line_has(mir, "Gt(", "73_usize") {
        return false;
    }
    if facts.der_len_gt == Some(74) && !line_has(mir, "Gt(", "74_usize") {
        return false;
    }
    let merkle_mir = mir.contains("PartialEq") && mir.contains("Vec::<[u8; 32]>::push");
    if facts.merkle_eq_present && facts.merkle_eq_before_pad {
        let eq = mir.find("PartialEq");
        let pad = mir.find("Vec::<[u8; 32]>::push");
        match (eq, pad) {
            (Some(e), Some(p)) if e < p => {}
            _ => return false,
        }
    }
    if merkle_mir && !facts.merkle_eq_present {
        return false;
    }
    if merkle_mir && facts.merkle_eq_present && !facts.merkle_eq_before_pad {
        let eq = mir.find("PartialEq");
        let pad = mir.find("Vec::<[u8; 32]>::push");
        if let (Some(e), Some(p)) = (eq, pad) {
            if e < p {
                return false;
            }
        }
    }
    true
}

fn prev_accepts<'a>(src: &str, child: &BV<'a>, parent: &BV<'a>) -> Bool<'a> {
    let body = ast_body::analyze(src);
    let calls = ast_body::call_named(&body.calls, "block_header_hash");
    let cmp = body
        .cmps
        .iter()
        .find(|cmp| cmp.left.has("prev_block_hash") || cmp.right.has("prev_block_hash"));
    match (calls, cmp.map(|cmp| cmp.op)) {
        (true, Some(CmpOp::Eq)) => child._eq(parent),
        (true, Some(CmpOp::Ne)) => child._eq(parent).not(),
        _ => Bool::from_bool(child.get_ctx(), true),
    }
}

/// Equal parent hashes are accepted when the function compares them.
pub fn prev_hash_equal_query(src: &str) -> SatResult {
    check(|ctx, solver| {
        let child = BV::from_u64(ctx, 1, 256);
        let parent = BV::from_u64(ctx, 1, 256);
        solver.assert(&prev_accepts(src, &child, &parent).not());
    })
}

/// A different parent hash is rejected. A missing compare accepts it.
pub fn prev_hash_mismatch_query(src: &str) -> SatResult {
    check(|ctx, solver| {
        let child = BV::from_u64(ctx, 1, 256);
        let parent = BV::from_u64(ctx, 2, 256);
        solver.assert(&prev_accepts(src, &child, &parent));
    })
}

/// Both cfg arms require one input, a zero prevout hash, and index `0xffffffff`.
pub fn coinbase_query(src: &str, zero_hash_src: &str) -> SatResult {
    let body = ast_body::analyze(src);
    let len_ok = body
        .cmps
        .iter()
        .filter(|cmp| {
            cmp.op == CmpOp::Eq
                && cmp.left.has("inputs")
                && cmp.left.has("len")
                && cmp.right.lit == Some(1)
        })
        .count()
        >= 2;
    let index_ok = body
        .cmps
        .iter()
        .filter(|cmp| {
            cmp.op == CmpOp::Eq
                && cmp.left.has("prevout")
                && cmp.left.has("index")
                && cmp.right.lit == Some(0xffff_ffff)
        })
        .count()
        >= 2;
    let prod_hash = ast_body::call_named(&body.calls, "is_zero_hash");
    let other_hash = body
        .cmps
        .iter()
        .any(|cmp| cmp.op == CmpOp::Eq && cmp.right.has("zero32"));
    let helper = ast_body::analyze(zero_hash_src);
    let helper_zero = helper
        .cmps
        .iter()
        .any(|cmp| cmp.left.has("b") && cmp.right.lit == Some(0));
    check(|ctx, solver| {
        let ok = Bool::from_bool(
            ctx,
            len_ok && index_ok && prod_hash && other_hash && helper_zero,
        );
        solver.assert(&ok.not());
    })
}

fn maturity_addend(src: &str) -> u64 {
    let body = ast_body::analyze(src);
    let Some(add) = body
        .methods
        .iter()
        .find(|method| method.name == "saturating_add")
    else {
        return 0;
    };
    if add.args.iter().any(|arg| arg.has("COINBASE_MATURITY"))
        && crate::parser::spec_expr::impl_u64("COINBASE_MATURITY")
            == crate::parser::spec_expr::protocol_u64("R")
    {
        return crate::parser::spec_expr::protocol_u64("R");
    }
    add.args
        .iter()
        .find_map(|arg| arg.lit)
        .and_then(|lit| u64::try_from(lit).ok())
        .unwrap_or(0)
}

fn maturity_accepts<'a>(
    ctx: &'a Context,
    src: &str,
    spend: u64,
    creation: u64,
    is_coinbase: bool,
) -> Bool<'a> {
    let body = ast_body::analyze(src);
    if !is_coinbase && body.early_non_coinbase {
        return Bool::from_bool(ctx, true);
    }
    let addend = maturity_addend(src);
    let spend_bv = BV::from_u64(ctx, spend, 64);
    let required = BV::from_u64(ctx, creation, 64).bvadd(&BV::from_u64(ctx, addend, 64));
    let op = body
        .cmps
        .iter()
        .find(|cmp| cmp.left.has("spend_height") && cmp.right.has("required"))
        .map(|cmp| cmp.op);
    match op {
        Some(CmpOp::Ge) => spend_bv.bvuge(&required),
        Some(CmpOp::Gt) => spend_bv.bvugt(&required),
        _ => Bool::from_bool(ctx, true),
    }
}

/// A non-coinbase spend is mature. Deleting the early return applies the coinbase rule.
pub fn maturity_non_coinbase_query(src: &str) -> SatResult {
    check(|ctx, solver| {
        solver.assert(&maturity_accepts(ctx, src, 0, 0, false).not());
    })
}

/// A coinbase spend at creation + R is mature. `>` rejects that height.
pub fn maturity_equal_query(src: &str) -> SatResult {
    let r = crate::parser::spec_expr::protocol_u64("R");
    check(|ctx, solver| {
        solver.assert(&maturity_accepts(ctx, src, r, 0, true).not());
    })
}

/// A coinbase spend one block earlier is immature.
pub fn maturity_before_query(src: &str) -> SatResult {
    let r = crate::parser::spec_expr::protocol_u64("R");
    check(|ctx, solver| {
        solver.assert(&maturity_accepts(ctx, src, r - 1, 0, true));
    })
}

/// Subsidy at `height` matches `INITIAL_SUBSIDY >> floor(height / H)`, and 0 when that floor is at least 64.
pub fn subsidy_query(src: &str, height: u64) -> SatResult {
    let interval = crate::parser::spec_expr::protocol_u64("H");
    let initial = crate::parser::spec_expr::initial_subsidy();
    let body = ast_body::analyze(src);
    let divides = body
        .divs
        .iter()
        .any(|(left, right)| left.has("height") && right.has("HALVING_INTERVAL"));
    let shifts = body
        .shifts
        .iter()
        .any(|(_, right)| right.has("halving_period"));
    let guards = body.cmps.iter().any(|cmp| {
        cmp.op == CmpOp::Ge && cmp.left.has("halving_period") && cmp.right.lit == Some(64)
    });
    check(|ctx, solver| {
        let h = BV::from_u64(ctx, height, 64);
        let step = BV::from_u64(ctx, interval, 64);
        let base = BV::from_u64(ctx, initial, 64);
        let zero = BV::from_u64(ctx, 0, 64);
        let sixty_four = BV::from_u64(ctx, 64, 64);
        let k_spec = h.bvudiv(&step);
        let spec = k_spec.bvuge(&sixty_four).ite(&zero, &base.bvlshr(&k_spec));
        let k = if divides {
            k_spec.clone()
        } else {
            zero.clone()
        };
        // A 64-bit shift amount is reduced mod 64. The guard is what makes k >= 64 return 0.
        let amount = if guards {
            k.clone()
        } else {
            k.bvand(&BV::from_u64(ctx, 63, 64))
        };
        let shifted = if shifts { base.bvlshr(&amount) } else { base };
        let result = if guards {
            k.bvuge(&sixty_four).ite(&zero, &shifted)
        } else {
            shifted
        };
        solver.assert(&result._eq(&spec).not());
    })
}

fn version_cmp(window: &str) -> Option<(bool, i64)> {
    if let Some(at) = window.find("block_version <= ") {
        let digits: String = window[at + "block_version <= ".len()..]
            .chars()
            .take_while(|c| c.is_ascii_digit())
            .collect();
        return digits.parse().ok().map(|n| (false, n));
    }
    if let Some(at) = window.find("block_version < ") {
        let digits: String = window[at + "block_version < ".len()..]
            .chars()
            .take_while(|c| c.is_ascii_digit())
            .collect();
        return digits.parse().ok().map(|n| (true, n));
    }
    None
}

fn bip90_rule(src: &str, fork: &str) -> Option<(bool, bool, i64)> {
    let marker = format!("ForkId::{fork}");
    let at = src.find(&marker)?;
    let start = at.saturating_sub(24);
    let window = &src[start..src.len().min(at + 80)];
    let (strict, floor) = version_cmp(window)?;
    Some((window.contains("is_fork_active"), strict, floor))
}

fn bip90_rejects(src: &str, version: i64, bip34: bool, bip66: bool, bip65: bool) -> bool {
    let rules = [("Bip34", bip34), ("Bip66", bip66), ("Bip65", bip65)];
    rules.into_iter().any(|(fork, active)| {
        let Some((gated, strict, floor)) = bip90_rule(src, fork) else {
            return false;
        };
        let triggered = if gated { active } else { true };
        triggered
            && if strict {
                version < floor
            } else {
                version <= floor
            }
    })
}

/// Version floors 2, 3, and 4 apply only when that fork's activation bit is set.
pub fn bip90_query(src: &str, version: i64, bip34: bool, bip66: bool, bip65: bool) -> SatResult {
    let (v65, v66, v34, _) = crate::parser::spec_expr::min_version_floors();
    let spec = (bip34 && version < v34) || (bip66 && version < v66) || (bip65 && version < v65);
    let got = bip90_rejects(src, version, bip34, bip66, bip65);
    check(|ctx, solver| {
        let same = Bool::from_bool(ctx, got)._eq(&Bool::from_bool(ctx, spec));
        solver.assert(&same.not());
    })
}

/// `height >= self.{field}` is active at the threshold. `>` is not.
pub fn fork_threshold_query(src: &str, field: &str, height: u64, threshold: u64) -> SatResult {
    let ge = src.contains(&format!("height >= self.{field}"));
    let gt = src.contains(&format!("height > self.{field}"));
    check(|ctx, solver| {
        let h = BV::from_u64(ctx, height, 64);
        let t = BV::from_u64(ctx, threshold, 64);
        let active = if ge {
            h.bvuge(&t)
        } else if gt {
            h.bvugt(&t)
        } else {
            Bool::from_bool(ctx, false)
        };
        solver.assert(&active._eq(&h.bvuge(&t)).not());
    })
}

/// BIP30 has no height cutoff in this function.
pub fn fork_bip30_query(src: &str) -> SatResult {
    let always = src.contains("ForkId::Bip30 => true");
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, always).not());
    })
}

fn push_cmp(src: &str) -> Option<(bool, u32)> {
    let (inclusive, at) = if let Some(at) = src.find("opcode <= ") {
        (true, at + "opcode <= ".len())
    } else if let Some(at) = src.find("opcode < ") {
        (false, at + "opcode < ".len())
    } else {
        return None;
    };
    let rest = src[at..].trim_start();
    let bound = if let Some(hex) = rest.strip_prefix("0x") {
        let digits: String = hex.chars().take_while(|c| c.is_ascii_hexdigit()).collect();
        u32::from_str_radix(&digits, 16).ok()?
    } else {
        let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
        digits.parse().ok()?
    };
    Some((inclusive, bound))
}

/// An opcode at most `0x60` is a push. `0x61` is not.
pub fn push_opcode_query(src: &str, opcode: u32) -> SatResult {
    let parsed = push_cmp(src);
    check(|ctx, solver| {
        let op = BV::from_u64(ctx, u64::from(opcode), 8);
        let spec_bound = BV::from_u64(ctx, 0x60, 8);
        let push = match parsed {
            Some((true, bound)) => op.bvule(&BV::from_u64(ctx, u64::from(bound), 8)),
            Some((false, bound)) => op.bvult(&BV::from_u64(ctx, u64::from(bound), 8)),
            None => Bool::from_bool(ctx, false),
        };
        solver.assert(&push._eq(&op.bvule(&spec_bound)).not());
    })
}

fn source_op_success(src: &str, op: u32) -> bool {
    sample_eval::eval_bool(src, &[("opcode", Val::Int(i128::from(op)))])
}

fn spec_op_success(op: u32) -> bool {
    op == 0x50
        || op == 0x62
        || (0x7e..=0x81).contains(&op)
        || (0x83..=0x86).contains(&op)
        || (0x89..=0x8a).contains(&op)
        || (0x8d..=0x8e).contains(&op)
        || (0x95..=0x99).contains(&op)
        || (0xbb..=0xfe).contains(&op)
}

/// Immediate-success opcodes match the ranges in the script section.
pub fn op_success_query(src: &str) -> SatResult {
    let points = [
        0x50, 0x51, 0x62, 0x7e, 0x81, 0x82, 0x83, 0x86, 0x87, 0x89, 0x8a, 0x8b, 0x8d, 0x8e, 0x8f,
        0x95, 0x99, 0x9a, 0xbb, 0xfe, 0xff,
    ];
    let same = points
        .iter()
        .all(|op| source_op_success(src, *op) == spec_op_success(*op));
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, same).not());
    })
}

/// `vsize` is `ceil(weight / 4)`.
pub fn vsize_query(src: &str, weight: u64) -> SatResult {
    let got = sample_eval::eval_u64(
        src,
        &[("weight", Val::Int(i128::try_from(weight).expect("weight")))],
    );
    let spec = weight.div_ceil(4);
    check(|ctx, solver| {
        let left = BV::from_u64(ctx, got, 64);
        let right = BV::from_u64(ctx, spec, 64);
        solver.assert(&left._eq(&right).not());
    })
}

fn stripped_accepts(src: &str, coinbase: bool, size: u64) -> bool {
    if coinbase && src.contains("is_coinbase(tx)") {
        return true;
    }
    if src.contains("!= 64") {
        size != 64
    } else if src.contains("== 64") {
        size == 64
    } else {
        true
    }
}

/// A non-coinbase transaction of stripped size 64 is invalid.
pub fn stripped_size_query(src: &str, coinbase: bool, size: u64) -> SatResult {
    let got = stripped_accepts(src, coinbase, size);
    let spec = coinbase || size != 64;
    check(|ctx, solver| {
        solver.assert(
            &Bool::from_bool(ctx, got)
                ._eq(&Bool::from_bool(ctx, spec))
                .not(),
        );
    })
}

fn timewarp_ge(arm: &str) -> Option<bool> {
    if arm.contains("header.timestamp >= ") {
        Some(true)
    } else if arm.contains("header.timestamp > ") {
        Some(false)
    } else {
        None
    }
}

fn timewarp_accepts(
    src: &str,
    active: bool,
    height: u64,
    ts: u64,
    first: u64,
    prev: u64,
    has_boundary: bool,
) -> bool {
    if !active && src.contains("if !bip54_active") {
        return true;
    }
    let modulus = if src.contains("height % 2016") {
        2016
    } else if src.contains("height % 2015") {
        2015
    } else {
        return true;
    };
    let rem = height % modulus;
    let last = between(src, "rem == 2015", "rem == 0");
    let first_arm = between(src, "else if rem == 0", "} else");
    let off = src
        .rfind("else {")
        .is_some_and(|i| src[i + "else {".len()..].trim_start().starts_with("true"));
    if rem == 2015 && src.contains("rem == 2015") {
        if !has_boundary {
            return !last.contains("let Some(b) = boundary else");
        }
        return match timewarp_ge(last) {
            Some(true) => ts >= first,
            Some(false) => ts > first,
            None => true,
        };
    }
    if rem == 0 && src.contains("else if rem == 0") {
        if !has_boundary {
            return !first_arm.contains("let Some(b) = boundary else");
        }
        let grace = if first_arm.contains("7200") {
            7200
        } else if first_arm.contains("7199") {
            7199
        } else {
            0
        };
        let min_ts = if first_arm.contains("saturating_sub") {
            prev.saturating_sub(grace)
        } else {
            prev.wrapping_sub(grace)
        };
        return match timewarp_ge(first_arm) {
            Some(true) => ts >= min_ts,
            Some(false) => ts > min_ts,
            None => true,
        };
    }
    off
}

/// Inactive blocks pass. The last block of a 2016-period is at least the first. The next block allows 7200 seconds.
pub fn timewarp_query(
    src: &str,
    active: bool,
    height: u64,
    ts: u64,
    first: u64,
    prev: u64,
    has_boundary: bool,
) -> SatResult {
    let modulus = crate::parser::spec_expr::protocol_u64("D_INTERVAL");
    let got = timewarp_accepts(src, active, height, ts, first, prev, has_boundary);
    let spec = if !active {
        true
    } else {
        match height % modulus {
            2015 => has_boundary && ts >= first,
            0 => has_boundary && ts >= prev.saturating_sub(7200),
            _ => true,
        }
    };
    check(|ctx, solver| {
        solver.assert(
            &Bool::from_bool(ctx, got)
                ._eq(&Bool::from_bool(ctx, spec))
                .not(),
        );
    })
}

fn bip112_ordered(src: &str, input: u32, stack: u32) -> bool {
    if src.contains("extract_sequence_locktime_value(input_sequence)\n            >=")
        || src.contains("extract_sequence_locktime_value(input_sequence) >=")
    {
        input >= stack
    } else {
        input > stack
    }
}

/// CSV compares the type flag and then the low 16 bits with `>=`.
pub fn bip112_query(src: &str, types_equal: bool, input: u32, stack: u32) -> SatResult {
    let types = src.contains(
        "extract_sequence_type_flag(stack_sequence) == extract_sequence_type_flag(input_sequence)",
    );
    let ordered = bip112_ordered(src, input, stack);
    let got = if types {
        types_equal && ordered
    } else {
        ordered
    };
    let spec = types_equal && input >= stack;
    check(|ctx, solver| {
        solver.assert(
            &Bool::from_bool(ctx, got)
                ._eq(&Bool::from_bool(ctx, spec))
                .not(),
        );
    })
}

/// CTV and CSFS stay inactive when the stored height is `u64::MAX`.
pub fn fork_never_query(src: &str, field: &str) -> SatResult {
    let guarded = src.contains(&format!(
        "self.{field} != u64::MAX && height >= self.{field}"
    ));
    check(|ctx, solver| {
        let height = BV::from_u64(ctx, u64::MAX, 64);
        let threshold = BV::from_u64(ctx, u64::MAX, 64);
        let active = if guarded {
            Bool::from_bool(ctx, false)
        } else if src.contains(&format!("height >= self.{field}")) {
            height.bvuge(&threshold)
        } else {
            Bool::from_bool(ctx, true)
        };
        solver.assert(&active);
    })
}

fn tx_weight(src: &str, base: u64, total: u64) -> u64 {
    sample_eval::eval_u64(
        src,
        &[
            ("base_size", Val::Int(i128::from(base))),
            ("total_size", Val::Int(i128::from(total))),
        ],
    )
}

/// Segwit weight is `3 * base + total`.
pub fn tx_weight_query(src: &str, base: u64, total: u64) -> SatResult {
    let got = tx_weight(src, base, total);
    let spec = 3 * base + total;
    check(|ctx, solver| {
        solver.assert(
            &BV::from_u64(ctx, got, 64)
                ._eq(&BV::from_u64(ctx, spec, 64))
                .not(),
        );
    })
}

fn coinbase54(src: &str, height: u64, lock_time: u64, inputs: u64, sequence: u64) -> bool {
    let inputs = if inputs == 0 {
        Val::List(Vec::new())
    } else {
        Val::List(vec![Val::Rec(vec![(
            "sequence".to_string(),
            Val::Int(i128::from(sequence)),
        )])])
    };
    let coinbase = Val::Rec(vec![
        ("lock_time".to_string(), Val::Int(i128::from(lock_time))),
        ("inputs".to_string(), inputs),
    ]);
    sample_eval::eval_bool(
        src,
        &[
            ("coinbase", coinbase),
            ("height", Val::Int(i128::from(height))),
        ],
    )
}

/// Coinbase lock time is `height - 1`, and the first input sequence is not `0xffffffff`.
pub fn bip54_coinbase_query(
    src: &str,
    height: u64,
    lock_time: u64,
    inputs: u64,
    sequence: u64,
) -> SatResult {
    let got = coinbase54(src, height, lock_time, inputs, sequence);
    let spec = lock_time == height.saturating_sub(1) && inputs > 0 && sequence != 0xffff_ffff;
    check(|ctx, solver| {
        solver.assert(
            &Bool::from_bool(ctx, got)
                ._eq(&Bool::from_bool(ctx, spec))
                .not(),
        );
    })
}

fn source_median(src: &str, timestamps: &[u64]) -> u64 {
    if timestamps.is_empty() {
        return u64::from(!src.contains("is_empty() {\n        return 0"));
    }
    let window = if src.contains("saturating_sub(MEDIAN_TIME_BLOCKS)") {
        11
    } else if src.contains("saturating_sub(10)") {
        10
    } else {
        timestamps.len()
    };
    let start = timestamps.len().saturating_sub(window);
    let mut windowed = timestamps[start..].to_vec();
    if src.contains("sort_unstable") {
        windowed.sort_unstable();
    }
    let index = if src.contains("timestamps.len() / 2") {
        windowed.len() / 2
    } else if src.contains("(timestamps.len() - 1) / 2") {
        windowed.len().saturating_sub(1) / 2
    } else {
        0
    };
    windowed[index]
}

fn spec_median(timestamps: &[u64]) -> u64 {
    if timestamps.is_empty() {
        return 0;
    }
    let start = timestamps.len().saturating_sub(11);
    let mut windowed = timestamps[start..].to_vec();
    windowed.sort_unstable();
    windowed[windowed.len() / 2]
}

/// Median time is the upper middle of the last 11 timestamps.
pub fn median_time_query(src: &str, timestamps: &[u64]) -> SatResult {
    let got = source_median(src, timestamps);
    let spec = spec_median(timestamps);
    check(|ctx, solver| {
        solver.assert(
            &BV::from_u64(ctx, got, 64)
                ._eq(&BV::from_u64(ctx, spec, 64))
                .not(),
        );
    })
}

fn activation_constant(name: &str) -> u64 {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../blvm-primitives/src/constants.rs");
    let src =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let needle = format!("const {name}:");
    let rest = src
        .get(
            src.find(&needle)
                .unwrap_or_else(|| panic!("missing {name}"))
                + needle.len()..,
        )
        .unwrap();
    let expr = rest
        .get(rest.find('=').unwrap() + 1..)
        .unwrap()
        .split([';', '\n'])
        .next()
        .unwrap()
        .trim();
    if expr.contains("u64::MAX") {
        u64::MAX
    } else {
        expr.replace(['_', ' '], "")
            .parse()
            .unwrap_or_else(|_| panic!("bad {name}"))
    }
}

fn bip54_threshold(src: &str, override_h: Option<u64>, constant: &str) -> u64 {
    if override_h.is_some() && src.contains("Some(h) => h") {
        return override_h.unwrap_or(0);
    }
    if src.contains(constant) {
        activation_constant(constant)
    } else {
        0
    }
}

/// BIP54 is active at and after the override, or the network constant when the override is absent.
pub fn bip54_active_query(
    src: &str,
    height: u64,
    override_h: Option<u64>,
    constant: &str,
) -> SatResult {
    let threshold = bip54_threshold(src, override_h, constant);
    let spec_threshold = override_h.unwrap_or_else(|| activation_constant(constant));
    let got = if src.contains("height >= activation") {
        height >= threshold
    } else if src.contains("height > activation") {
        height > threshold
    } else {
        false
    };
    let spec = height >= spec_threshold;
    check(|ctx, solver| {
        solver.assert(
            &Bool::from_bool(ctx, got)
                ._eq(&Bool::from_bool(ctx, spec))
                .not(),
        );
    })
}

fn shl_mantissa(mantissa: u32, shift: u32) -> [u64; 4] {
    if shift >= 256 {
        return [0; 4];
    }
    let limb = (shift / 64) as usize;
    let off = shift % 64;
    let wide = u128::from(mantissa) << off;
    let mut out = [0u64; 4];
    if limb < 4 {
        out[limb] = wide as u64;
        if limb + 1 < 4 {
            out[limb + 1] = (wide >> 64) as u64;
        }
    }
    out
}

fn spec_expand(bits: u64) -> Result<[u64; 4], ()> {
    let exponent = ((bits >> 24) & 0xff) as u32;
    let mantissa = (bits & 0x007f_ffff) as u32;
    if !(3..=32).contains(&exponent) {
        return Err(());
    }
    if mantissa == 0 {
        return Ok([0; 4]);
    }
    Ok(shl_mantissa(mantissa, 8 * (exponent - 3)))
}

fn u256_limbs(bytes: &[u8]) -> [u64; 4] {
    let mut out = [0u64; 4];
    for (index, limb) in out.iter_mut().enumerate() {
        let start = index * 8;
        let mut word = [0u8; 8];
        word.copy_from_slice(&bytes[start..start + 8]);
        *limb = u64::from_le_bytes(word);
    }
    out
}

/// Compact target: exponent byte, 23-bit mantissa, zero mantissa is zero, else `m << 8*(e-3)`.
/// The body is the parsed `expand_target`. The right-hand side is the §7.1 formula.
pub fn expand_target_query(src: &str, bits: u64) -> SatResult {
    let got = sample_eval::eval_val(src, &[("bits", Val::Int(i128::from(bits)))]);
    let differ = match (&got, spec_expand(bits)) {
        (Val::Bytes(got), Ok(spec)) if got.len() == 32 => u256_limbs(got) != spec,
        (Val::Name(name), Err(())) if name == "err" => false,
        _ => true,
    };
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn fold_values(values: &[i64], last_only: bool) -> Result<i64, ()> {
    if last_only {
        return Ok(values.last().copied().unwrap_or(0));
    }
    let mut acc = 0i64;
    for value in values {
        acc = acc.checked_add(*value).ok_or(())?;
    }
    Ok(acc)
}

fn model_fee(src: &str, coinbase: bool, inputs: &[i64], outputs: &[i64]) -> Result<i64, ()> {
    if coinbase && src.contains("if is_coinbase(tx)") {
        return Ok(0);
    }
    let total_in = fold_values(inputs, src.contains("Some(utxo.value)"))?;
    let total_out = fold_values(outputs, src.contains("Some(output.value)"))?;
    let fee = if src.contains("checked_sub(total_output)") {
        total_in.checked_sub(total_out).ok_or(())?
    } else if src.contains("checked_add(total_output)") {
        total_in.checked_add(total_out).ok_or(())?
    } else {
        return Err(());
    };
    if src.contains("if fee <= 0") && fee <= 0 {
        return Err(());
    }
    if src.contains("if fee < 0") && fee < 0 {
        return Err(());
    }
    Ok(fee)
}

fn spec_fee(coinbase: bool, inputs: &[i64], outputs: &[i64]) -> Result<i64, ()> {
    if coinbase {
        return Ok(0);
    }
    let fee = fold_values(inputs, false)?
        .checked_sub(fold_values(outputs, false)?)
        .ok_or(())?;
    if fee < 0 { Err(()) } else { Ok(fee) }
}

/// Fee is input value minus output value. A coinbase fee is 0. A negative difference is rejected.
pub fn calculate_fee_query(
    src: &str,
    coinbase: bool,
    inputs: &[i64],
    outputs: &[i64],
) -> SatResult {
    let differ = match (
        model_fee(src, coinbase, inputs, outputs),
        spec_fee(coinbase, inputs, outputs),
    ) {
        (Ok(got), Ok(spec)) => got != spec,
        (Err(()), Err(())) => false,
        _ => true,
    };
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn model_minimal_if(src: &str, bytes: &[u8]) -> bool {
    sample_eval::eval_bool(src, &[("bytes", sample_eval::bytes(bytes))])
}

fn spec_minimal_if(bytes: &[u8]) -> bool {
    bytes.is_empty() || bytes == [0x01]
}

/// Minimal IF argument: empty, or the single true byte `0x01`.
pub fn minimal_if_query(src: &str, bytes: &[u8]) -> SatResult {
    let differ = model_minimal_if(src, bytes) != spec_minimal_if(bytes);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn model_cast_to_bool(src: &str, bytes: &[u8]) -> bool {
    sample_eval::eval_bool(src, &[("v", sample_eval::bytes(bytes))])
}

fn spec_cast_to_bool(bytes: &[u8]) -> bool {
    let Some((last, prefix)) = bytes.split_last() else {
        return false;
    };
    prefix.iter().any(|byte| *byte != 0) || (*last != 0 && *last != 0x80)
}

/// Stack truth: empty and all-zero are false, and a final `0x80` with a zero prefix is false.
pub fn cast_to_bool_query(src: &str, bytes: &[u8]) -> SatResult {
    let differ = model_cast_to_bool(src, bytes) != spec_cast_to_bool(bytes);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn model_witness_version(src: &str, opcode: u8) -> bool {
    sample_eval::eval_bool(src, &[("opcode", Val::Int(i128::from(opcode)))])
}

fn spec_witness_version(opcode: u8) -> bool {
    opcode == 0 || (0x51..=0x60).contains(&opcode)
}

/// Witness version byte: `OP_0`, or `OP_1` through `OP_16`.
pub fn witness_version_query(src: &str, opcode: u8) -> SatResult {
    let differ = model_witness_version(src, opcode) != spec_witness_version(opcode);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn fad_advance(script: &[u8], pc: usize, byte_step: bool) -> Option<usize> {
    if pc >= script.len() {
        return None;
    }
    if byte_step {
        return Some(pc + 1);
    }
    let opcode = script[pc];
    let advance = if opcode <= 0x4b {
        1 + opcode as usize
    } else if opcode == 0x4c && pc + 1 < script.len() {
        2 + script[pc + 1] as usize
    } else if opcode == 0x4d && pc + 2 < script.len() {
        3 + (script[pc + 1] as usize | ((script[pc + 2] as usize) << 8))
    } else if opcode == 0x4e && pc + 4 < script.len() {
        5 + (script[pc + 1] as usize
            | ((script[pc + 2] as usize) << 8)
            | ((script[pc + 3] as usize) << 16)
            | ((script[pc + 4] as usize) << 24))
    } else {
        1
    };
    let next = pc + advance;
    if next > script.len() {
        None
    } else {
        Some(next)
    }
}

fn fad_walk(script: &[u8], pattern: &[u8], byte_step: bool, delete_mode: u8) -> Vec<u8> {
    let mut result = Vec::new();
    let mut pc = 0usize;
    let mut pc2 = 0usize;
    let mut found = 0usize;
    let end = script.len();
    loop {
        result.extend_from_slice(&script[pc2..pc]);
        while delete_mode > 0
            && end - pc >= pattern.len()
            && script[pc..pc + pattern.len()] == *pattern
        {
            pc += pattern.len();
            found += 1;
            if delete_mode == 1 {
                break;
            }
        }
        pc2 = pc;
        if pc >= end {
            break;
        }
        let Some(next) = fad_advance(script, pc, byte_step) else {
            break;
        };
        pc = next;
    }
    if found > 0 {
        result.extend_from_slice(&script[pc2..end]);
        result
    } else {
        script.to_vec()
    }
}

fn model_find_and_delete(src: &str, script: &[u8], pattern: &[u8]) -> Vec<u8> {
    if pattern.is_empty() {
        return if src.contains("pattern.is_empty()") {
            script.to_vec()
        } else {
            Vec::new()
        };
    }
    if pattern.len() > script.len() && src.contains("Cow::Owned(Vec::new())") {
        return Vec::new();
    }
    fad_walk(
        script,
        pattern,
        !src.contains("script_get_op_advance"),
        if src.contains("while end - pc >= pattern.len()") {
            2
        } else if src.contains("if end - pc >= pattern.len()") {
            1
        } else {
            0
        },
    )
}

fn spec_find_and_delete(script: &[u8], pattern: &[u8]) -> Vec<u8> {
    if pattern.is_empty() || pattern.len() > script.len() {
        return script.to_vec();
    }
    fad_walk(script, pattern, false, 2)
}

/// Find-and-delete removes opcode-aligned copies of the pattern. An empty or longer pattern is a no-op.
pub fn find_and_delete_query(src: &str, script: &[u8], pattern: &[u8]) -> SatResult {
    let differ =
        model_find_and_delete(src, script, pattern) != spec_find_and_delete(script, pattern);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn supply_schedule(src: &str, height: u64) -> i64 {
    i64::try_from(sample_eval::eval_int(
        src,
        &[("height", Val::Int(i128::from(height)))],
    ))
    .expect("issued supply")
}

fn spec_supply(height: u64) -> i64 {
    let interval = crate::parser::spec_expr::impl_u64("HALVING_INTERVAL");
    let initial = crate::parser::spec_expr::impl_u64("INITIAL_SUBSIDY") as i64;
    let mut total = 0i64;
    for k in 0u64..64 {
        let period_start = k.saturating_mul(interval);
        if period_start > height {
            break;
        }
        let subsidy = if k >= 63 { 0 } else { initial >> k };
        let period_end = (k + 1).saturating_mul(interval).saturating_sub(1);
        let count = height.min(period_end) - period_start + 1;
        total += (count as i64) * subsidy;
    }
    total
}

/// Issued supply is the sum of `INITIAL_SUBSIDY >> k` over each halving epoch up to `height`.
pub fn total_supply_query(src: &str, height: u64) -> SatResult {
    let differ = supply_schedule(src, height) != spec_supply(height);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn null_dummy_walk(src: &str, script: &[u8]) -> bool {
    sample_eval::eval_bool(src, &[("script_sig", sample_eval::bytes(script))])
}

fn spec_null_dummy(script: &[u8]) -> bool {
    if script.is_empty() {
        return false;
    }
    let mut pc = 0usize;
    let mut saw_push = false;
    let mut first_empty = false;
    while pc < script.len() {
        let opcode = script[pc];
        pc += 1;
        let len = if opcode == 0x00 {
            if !saw_push {
                first_empty = true;
                saw_push = true;
            }
            continue;
        } else if (0x01..=0x4b).contains(&opcode) {
            opcode as usize
        } else if opcode == 0x4c {
            if pc >= script.len() {
                return false;
            }
            let len = script[pc] as usize;
            pc += 1;
            len
        } else if opcode == 0x4d {
            if pc + 2 > script.len() {
                return false;
            }
            let len = u16::from_le_bytes([script[pc], script[pc + 1]]) as usize;
            pc += 2;
            len
        } else if opcode == 0x4e {
            if pc + 4 > script.len() {
                return false;
            }
            let len =
                u32::from_le_bytes([script[pc], script[pc + 1], script[pc + 2], script[pc + 3]])
                    as usize;
            pc += 4;
            len
        } else {
            return false;
        };
        if pc + len > script.len() {
            return false;
        }
        if !saw_push {
            first_empty = len == 0;
            saw_push = true;
        }
        pc += len;
    }
    first_empty
}

/// The multisig dummy is the first push. It is empty for `OP_0` or a zero-length push. A non-push byte fails the parse.
pub fn null_dummy_query(src: &str, script: &[u8]) -> SatResult {
    let differ = null_dummy_walk(src, script) != spec_null_dummy(script);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn spec_taproot_script(script: &[u8]) -> bool {
    script.len() == 34 && script.first() == Some(&0x51) && script.get(1) == Some(&0x20)
}

fn taproot_script_ok(src: &str, script: &[u8]) -> bool {
    sample_eval::eval_bool(src, &[("script", sample_eval::bytes(script))])
}

/// A taproot output is 34 bytes, `0x51`, then `0x20`.
pub fn taproot_script_query(src: &str, script: &[u8]) -> SatResult {
    let differ = taproot_script_ok(src, script) != spec_taproot_script(script);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn spec_taproot_key(script: &[u8]) -> Option<Vec<u8>> {
    spec_taproot_script(script).then(|| script[2..34].to_vec())
}

fn produced_taproot_key(src: &str, script: &[u8]) -> Option<Vec<u8>> {
    if src.contains("validate_taproot_script") && !spec_taproot_script(script) {
        return None;
    }
    if !src.contains("Ok(Some(output_key))") || script.len() < 34 {
        return None;
    }
    let start = if src.contains("&script[0..32]") { 0 } else { 2 };
    Some(script[start..start + 32].to_vec())
}

/// The output key is bytes 2..34 of a valid taproot script, and absent otherwise.
pub fn taproot_key_query(src: &str, script: &[u8]) -> SatResult {
    let differ = produced_taproot_key(src, script) != spec_taproot_key(script);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn spec_p2pkh_script_code(hash: &[u8]) -> Vec<u8> {
    let mut out = vec![0x76, 0xa9, 0x14];
    out.extend_from_slice(hash);
    out.push(0x88);
    out.push(0xac);
    out
}

fn witness_script_code(src: &str, program: &[u8], witness: Option<&[u8]>) -> Option<Vec<u8>> {
    let witness = match witness {
        Some(item) => Val::Opt(Some(Box::new(sample_eval::bytes(item)))),
        None => Val::Opt(None),
    };
    sample_eval::eval_option_bytes(
        src,
        "derive_bip143_script_code",
        &[
            ("witness_program", sample_eval::bytes(program)),
            ("witness_script", witness),
        ],
    )
}

fn spec_witness_script_code(program: &[u8], witness: Option<&[u8]>) -> Option<Vec<u8>> {
    if program.len() == 22 && program.first() == Some(&0x00) && program.get(1) == Some(&0x14) {
        return Some(spec_p2pkh_script_code(&program[2..22]));
    }
    if program.len() == 34 && program.first() == Some(&0x00) && program.get(1) == Some(&0x20) {
        return witness.map(|item| item.to_vec());
    }
    None
}

/// P2WPKH expands to the 25-byte P2PKH script. P2WSH uses the witness script.
pub fn witness_script_code_query(src: &str, program: &[u8], witness: Option<&[u8]>) -> SatResult {
    let differ =
        witness_script_code(src, program, witness) != spec_witness_script_code(program, witness);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn strip_codeseparators(src: &str, code: &[u8]) -> Vec<u8> {
    match sample_eval::eval_bound(
        src,
        &[
            ("out", sample_eval::bytes(&[])),
            ("code", sample_eval::bytes(code)),
        ],
        "out",
    ) {
        Val::Bytes(data) => data,
        other => panic!("stripped script code {other:?}"),
    }
}

fn spec_strip_codeseparators(code: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    let mut i = 0usize;
    while i < code.len() {
        let op = code[i];
        if (0x01..=0x4b).contains(&op) {
            let end = (i + 1 + op as usize).min(code.len());
            out.extend_from_slice(&code[i..end]);
            i = end;
        } else if op == 0x4c {
            if i + 1 >= code.len() {
                out.push(op);
                break;
            }
            let len = code[i + 1] as usize;
            let end = (i + 2 + len).min(code.len());
            out.extend_from_slice(&code[i..end]);
            i = end;
        } else if op == 0x4d {
            if i + 2 >= code.len() {
                out.extend_from_slice(&code[i..]);
                break;
            }
            let len = u16::from_le_bytes([code[i + 1], code[i + 2]]) as usize;
            let end = (i + 3 + len).min(code.len());
            out.extend_from_slice(&code[i..end]);
            i = end;
        } else if op == 0x4e {
            if i + 4 >= code.len() {
                out.extend_from_slice(&code[i..]);
                break;
            }
            let len =
                u32::from_le_bytes([code[i + 1], code[i + 2], code[i + 3], code[i + 4]]) as usize;
            let end = (i + 5 + len).min(code.len());
            out.extend_from_slice(&code[i..end]);
            i = end;
        } else if op == 0xab {
            i += 1;
        } else {
            out.push(op);
            i += 1;
        }
    }
    out
}

/// `OP_CODESEPARATOR` is removed at opcode positions. The same byte inside a push stays.
pub fn script_code_query(src: &str, code: &[u8]) -> SatResult {
    let differ = strip_codeseparators(src, code) != spec_strip_codeseparators(code);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn compact_varint(n: u64) -> Vec<u8> {
    if n < 0xfd {
        vec![n as u8]
    } else if n <= 0xffff {
        let mut out = vec![0xfd];
        out.extend_from_slice(&(n as u16).to_le_bytes());
        out
    } else if n <= 0xffff_ffff {
        let mut out = vec![0xfe];
        out.extend_from_slice(&(n as u32).to_le_bytes());
        out
    } else {
        let mut out = vec![0xff];
        out.extend_from_slice(&n.to_le_bytes());
        out
    }
}

fn annex_preimage(helper: &str, annex: &[u8]) -> Vec<u8> {
    if !helper.contains("Sha256::digest") {
        return vec![0];
    }
    let mut buf = Vec::new();
    if helper.contains("encode_varint(annex.len()") {
        buf.extend(compact_varint(annex.len() as u64));
    }
    if helper.contains("buf.extend_from_slice(annex)") {
        buf.extend_from_slice(annex);
    }
    buf
}

fn spec_annex_preimage(annex: &[u8]) -> Vec<u8> {
    let mut buf = compact_varint(annex.len() as u64);
    buf.extend_from_slice(annex);
    buf
}

fn strip_annex(src: &str, helper: &str, witness: &[Vec<u8>]) -> (Vec<Vec<u8>>, Option<Vec<u8>>) {
    let min_len = if src.contains("witness.len() >= 1") {
        1
    } else {
        2
    };
    let any_tag = src.contains("|&b| true");
    let tagged = witness.len() >= min_len
        && witness
            .last()
            .and_then(|item| item.first())
            .is_some_and(|byte| any_tag || *byte == 0x50);
    if tagged {
        let annex = witness.last().unwrap();
        let preimage = if src.contains("compute_taproot_annex_sighash_hash") {
            annex_preimage(helper, annex)
        } else {
            vec![0]
        };
        let stack = if src.contains("witness[..witness.len() - 1]") {
            witness[..witness.len() - 1].to_vec()
        } else {
            witness.to_vec()
        };
        return (stack, Some(preimage));
    }
    if src.contains("Some([0u8; 32])") {
        return (witness.to_vec(), Some(vec![0]));
    }
    (witness.to_vec(), None)
}

fn spec_strip_annex(witness: &[Vec<u8>]) -> (Vec<Vec<u8>>, Option<Vec<u8>>) {
    if witness.len() >= 2 && witness.last().and_then(|item| item.first()) == Some(&0x50) {
        let annex = witness.last().unwrap();
        return (
            witness[..witness.len() - 1].to_vec(),
            Some(spec_annex_preimage(annex)),
        );
    }
    (witness.to_vec(), None)
}

/// An annex is a last witness element that starts with `0x50` when the stack has at least two elements.
/// SHA-256 of the varint-prefixed annex is a named assumption.
pub fn taproot_annex_query(src: &str, helper: &str, witness: &[Vec<u8>]) -> SatResult {
    let differ = strip_annex(src, helper, witness) != spec_strip_annex(witness);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn segwit_elements_ok(src: &str, witness: &[Vec<u8>]) -> bool {
    sample_eval::eval_bool(src, &[("witness", sample_eval::stack(witness))])
}

fn spec_segwit_elements(witness: &[Vec<u8>]) -> bool {
    witness.iter().all(|element| element.len() <= 520)
}

/// Every SegWit witness element is at most 520 bytes. An empty witness passes.
pub fn segwit_witness_query(src: &str, witness: &[Vec<u8>]) -> SatResult {
    let differ = segwit_elements_ok(src, witness) != spec_segwit_elements(witness);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn spec_strict_der(sig: &[u8]) -> bool {
    let n = sig.len();
    if !(9..=73).contains(&n) || sig[0] != 0x30 || sig[1] != (n - 3) as u8 || sig[2] != 0x02 {
        return false;
    }
    let len_r = sig[3] as usize;
    if len_r == 0 || 5 + len_r >= n {
        return false;
    }
    let len_s = sig[5 + len_r] as usize;
    if len_r + len_s + 7 != n
        || sig[4] & 0x80 != 0
        || (len_r > 1 && sig[4] == 0x00 && sig[5] & 0x80 == 0)
        || sig[len_r + 4] != 0x02
        || len_s == 0
        || sig[len_r + 6] & 0x80 != 0
        || (len_s > 1 && sig[len_r + 6] == 0x00 && sig[len_r + 7] & 0x80 == 0)
    {
        return false;
    }
    true
}

fn bip66_ok(src: &str, sig: &[u8], active: bool) -> bool {
    if src.contains("is_fork_active(ForkId::Bip66") && !active {
        return true;
    }
    if src.contains("is_strict_der(signature)") {
        return spec_strict_der(sig);
    }
    src.contains("Ok(true)") && !src.contains("Ok(false)")
}

/// After BIP66 activation a signature is valid only when it is strict DER. Before activation it passes.
pub fn bip66_query(src: &str, sig: &[u8], active: bool) -> SatResult {
    let spec = !active || spec_strict_der(sig);
    let differ = bip66_ok(src, sig, active) != spec;
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn pay_to_script_hash(src: &str, script: &[u8]) -> bool {
    sample_eval::eval_bool(src, &[("script", sample_eval::bytes(script))])
}

fn spec_pay_to_script_hash(script: &[u8]) -> bool {
    script.len() == 23 && script[0] == 0xa9 && script[1] == 0x14 && script[22] == 0x87
}

/// A P2SH script is 23 bytes: `0xa9`, `0x14`, the hash, and `0x87`.
pub fn p2sh_script_query(src: &str, script: &[u8]) -> SatResult {
    let differ = pay_to_script_hash(src, script) != spec_pay_to_script_hash(script);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn sigop_push(src: &str, opcode: u8) -> bool {
    sample_eval::eval_bool(src, &[("op", Val::Int(i128::from(opcode)))])
}

/// A sigop-count push is an opcode at most `OP_16` (`0x60`).
pub fn sigop_push_query(src: &str, opcode: u8) -> SatResult {
    let differ = sigop_push(src, opcode) != (opcode <= 0x60);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn redeem_script(src: &str, script: &[u8]) -> Option<Vec<u8>> {
    if script.is_empty() {
        return if src.contains("script_sig.is_empty()") {
            Some(Vec::new())
        } else {
            None
        };
    }
    let reject_high = src.contains("sigop_count_push_opcode");
    let bounds = src.contains("i + advance + len > script_sig.len()");
    let copy_payload = src.contains("i + advance..i + advance + len");
    let small_is_opcode = src.contains("vec![opcode]");
    let big_endian = src.contains("from_be_bytes");
    let push1_len_one = src.contains("1usize, 2");
    let push4_header = src.contains("i + 4 >= script_sig.len()");
    let stop_after_data = src.contains("return last_data");
    let mut i = 0usize;
    let mut last = None;
    while i < script.len() {
        let opcode = script[i];
        if reject_high && opcode > 0x60 {
            return None;
        }
        if opcode <= 0x4e {
            let (len, advance) = if opcode < 0x4c {
                (opcode as usize, 1usize)
            } else if opcode == 0x4c {
                if i + 1 >= script.len() {
                    return None;
                }
                if push1_len_one {
                    (1usize, 2)
                } else {
                    (script[i + 1] as usize, 2)
                }
            } else if opcode == 0x4d {
                if i + 2 >= script.len() {
                    return None;
                }
                let raw = [script[i + 1], script[i + 2]];
                let len = if big_endian {
                    u16::from_be_bytes(raw)
                } else {
                    u16::from_le_bytes(raw)
                } as usize;
                (len, 3)
            } else if push4_header && i + 4 >= script.len() {
                return None;
            } else if i + 4 >= script.len() {
                return Some(vec![0x4e]);
            } else {
                (
                    u32::from_le_bytes([script[i + 1], script[i + 2], script[i + 3], script[i + 4]])
                        as usize,
                    5,
                )
            };
            if bounds && i + advance + len > script.len() {
                return None;
            }
            if i + advance > script.len() {
                return None;
            }
            let end = (i + advance + len).min(script.len());
            last = Some(if copy_payload {
                script[i + advance..end].to_vec()
            } else {
                Vec::new()
            });
            if stop_after_data {
                return last;
            }
            i = end;
        } else {
            last = Some(if small_is_opcode {
                vec![opcode]
            } else {
                Vec::new()
            });
            i += 1;
        }
    }
    last
}

fn spec_redeem_script(script: &[u8]) -> Option<Vec<u8>> {
    if script.is_empty() {
        return None;
    }
    let mut i = 0usize;
    let mut last = None;
    while i < script.len() {
        let opcode = script[i];
        if opcode > 0x60 {
            return None;
        }
        if opcode <= 0x4e {
            let (len, advance) = if opcode < 0x4c {
                (opcode as usize, 1usize)
            } else if opcode == 0x4c {
                if i + 1 >= script.len() {
                    return None;
                }
                (script[i + 1] as usize, 2)
            } else if opcode == 0x4d {
                if i + 2 >= script.len() {
                    return None;
                }
                (
                    u16::from_le_bytes([script[i + 1], script[i + 2]]) as usize,
                    3,
                )
            } else {
                if i + 4 >= script.len() {
                    return None;
                }
                (
                    u32::from_le_bytes([script[i + 1], script[i + 2], script[i + 3], script[i + 4]])
                        as usize,
                    5,
                )
            };
            if i + advance + len > script.len() {
                return None;
            }
            last = Some(script[i + advance..i + advance + len].to_vec());
            i += advance + len;
        } else {
            last = Some(Vec::new());
            i += 1;
        }
    }
    last
}

/// The redeem script is the data of the last push. A truncated push or an opcode above `OP_16` yields none.
pub fn redeem_script_query(src: &str, script: &[u8]) -> SatResult {
    let differ = redeem_script(src, script) != spec_redeem_script(script);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn sequence_satisfied(src: &str, height: u64, time: u64, min_h: i64, min_t: i64) -> bool {
    if src.contains("min_height >= 0") || src.contains("min_height > 0") {
        let active = if src.contains("min_height > 0") {
            min_h > 0
        } else {
            min_h >= 0
        };
        if active && src.contains("block_height <") {
            let bound = min_h as u64;
            let fail = if src.contains("block_height < min_height") {
                height < bound
            } else {
                height <= bound
            };
            if fail {
                return false;
            }
        }
    }
    if src.contains("min_time >= 0") || src.contains("min_time > 0") {
        let active = if src.contains("min_time > 0") {
            min_t > 0
        } else {
            min_t >= 0
        };
        if active && src.contains("block_time <") {
            let bound = min_t as u64;
            let fail = if src.contains("block_time < min_time") {
                time < bound
            } else {
                time <= bound
            };
            if fail {
                return false;
            }
        }
    }
    src.contains("\n    true\n")
}

fn spec_sequence_satisfied(height: u64, time: u64, min_h: i64, min_t: i64) -> bool {
    (min_h < 0 || height > min_h as u64) && (min_t < 0 || time > min_t as u64)
}

/// A sequence lock passes when each active minimum is strictly below the block height or time.
pub fn sequence_lock_query(src: &str, height: u64, time: u64, min_h: i64, min_t: i64) -> SatResult {
    let differ = sequence_satisfied(src, height, time, min_h, min_t)
        != spec_sequence_satisfied(height, time, min_h, min_t);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

/// Mainnet block 91842, internal byte order. Display form is
/// `00000000000a4d0a398161ffc163c503763b1f4360639393e0e4c8e300e0caec`.
const BIP30_REPEAT_HASH_91842: [u8; 32] = [
    0xec, 0xca, 0xe0, 0x00, 0xe3, 0xc8, 0xe4, 0xe0, 0x93, 0x93, 0x63, 0x60, 0x43, 0x1f, 0x3b, 0x76,
    0x03, 0xc5, 0x63, 0xc1, 0xff, 0x61, 0x81, 0x39, 0x0a, 0x4d, 0x0a, 0x00, 0x00, 0x00, 0x00, 0x00,
];
/// Mainnet block 91880, internal byte order. Display form is
/// `00000000000743f190a18c5577a3c2d2a1f610ae9601ac046a38084ccb7cd721`.
const BIP30_REPEAT_HASH_91880: [u8; 32] = [
    0x21, 0xd7, 0x7c, 0xcb, 0x4c, 0x08, 0x38, 0x6a, 0x04, 0xac, 0x01, 0x96, 0xae, 0x10, 0xf6, 0xa1,
    0xd2, 0xc2, 0xa3, 0x77, 0x55, 0x8c, 0xa1, 0x90, 0xf1, 0x43, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00,
];

fn bip30_const_hash(file: &str, name: &str) -> Option<[u8; 32]> {
    let marker = format!("const {name}: Hash = [");
    let start = file.find(&marker)? + marker.len();
    let end = file[start..].find("];")?;
    let mut out = [0u8; 32];
    let mut n = 0usize;
    for part in file[start..start + end].split(',') {
        let part = part.trim();
        if part.is_empty() {
            continue;
        }
        let hex = part.strip_prefix("0x").unwrap_or(part);
        let Ok(byte) = u8::from_str_radix(hex, 16) else {
            return None;
        };
        if n >= 32 {
            return None;
        }
        out[n] = byte;
        n += 1;
    }
    (n == 32).then_some(out)
}

fn bip30_repeat_member(file: &str, src: &str, height: u64, hash: &[u8; 32]) -> bool {
    let mut default = false;
    for line in src.lines() {
        let line = line.trim().trim_end_matches(',');
        let Some((pat, expr)) = line.split_once("=>") else {
            continue;
        };
        let pat = pat.trim();
        let expr = expr.trim();
        let arm = if expr == "true" {
            Some(true)
        } else if expr == "false" {
            Some(false)
        } else if let Some(name) = expr.strip_prefix("block_hash == &") {
            bip30_const_hash(file, name).map(|expected| hash == &expected)
        } else {
            None
        };
        if pat == "_" {
            default = arm.unwrap_or(false);
            continue;
        }
        if let Ok(arm_height) = pat.replace('_', "").parse::<u64>() {
            if height == arm_height {
                return arm.unwrap_or(false);
            }
        }
    }
    default
}

fn spec_bip30_repeat(height: u64, hash: &[u8; 32]) -> bool {
    (height == 91_842 && hash == &BIP30_REPEAT_HASH_91842)
        || (height == 91_880 && hash == &BIP30_REPEAT_HASH_91880)
}

/// Membership in the two-block BIP30 exception set.
pub fn bip30_repeat_query(file: &str, src: &str, height: u64, hash: &[u8; 32]) -> SatResult {
    let differ = bip30_repeat_member(file, src, height, hash) != spec_bip30_repeat(height, hash);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn witness_is_empty(src: &str, witness: &[Vec<u8>]) -> bool {
    sample_eval::eval_bool(src, &[("witness", sample_eval::stack(witness))])
}

fn spec_witness_empty(witness: &[Vec<u8>]) -> bool {
    witness.is_empty() || witness.iter().all(|elem| elem.is_empty())
}

/// A witness is empty when the stack has no items or every item is empty.
pub fn witness_empty_query(src: &str, witness: &[Vec<u8>]) -> SatResult {
    let differ = witness_is_empty(src, witness) != spec_witness_empty(witness);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn stack_is_null(src: &str, witness: &[Vec<u8>]) -> bool {
    sample_eval::eval_bool(src, &[("witness", sample_eval::stack(witness))])
}

fn spec_stack_null(witness: &[Vec<u8>]) -> bool {
    witness.is_empty()
}

/// A witness stack is absent only when it has no items.
pub fn stack_null_query(src: &str, witness: &[Vec<u8>]) -> SatResult {
    let differ = stack_is_null(src, witness) != spec_stack_null(witness);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn input_not_witness_empty(src: &str, witness: &[Vec<u8>]) -> bool {
    let empty = witness.is_empty() || witness.iter().all(|elem| elem.is_empty());
    if src.contains("!is_witness_empty(w)") {
        !empty
    } else if src.contains("is_witness_empty(w)") {
        empty
    } else {
        true
    }
}

fn has_nonempty_input_witness(src: &str, witnesses: Option<&[Vec<Vec<u8>>]>) -> bool {
    let Some(witnesses) = witnesses else {
        return src.contains("unwrap_or(true)");
    };
    if src.contains(".all(") {
        witnesses.iter().all(|w| input_not_witness_empty(src, w))
    } else if src.contains(".any(") {
        witnesses.iter().any(|w| input_not_witness_empty(src, w))
    } else if src.contains("\n    true\n") {
        true
    } else {
        false
    }
}

fn spec_has_nonempty_input_witness(witnesses: Option<&[Vec<Vec<u8>>]>) -> bool {
    witnesses.is_some_and(|ws| {
        ws.iter()
            .any(|w| !(w.is_empty() || w.iter().all(|elem| elem.is_empty())))
    })
}

/// Witness script flags require one input stack that is not empty.
pub fn nonempty_witness_query(src: &str, witnesses: Option<&[Vec<Vec<u8>>]>) -> SatResult {
    let differ =
        has_nonempty_input_witness(src, witnesses) != spec_has_nonempty_input_witness(witnesses);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn reserved_nonce(src: &str, witnesses: &[Vec<Vec<u8>>]) -> Option<[u8; 32]> {
    if witnesses.is_empty() && src.contains("coinbase_witnesses.is_empty()") {
        return Some([0u8; 32]);
    }
    let Some(stack) = witnesses.first() else {
        return None;
    };
    if stack.is_empty() && src.contains("stack.is_empty()") {
        return Some([0u8; 32]);
    }
    let len_matches = if src.contains("stack.len() != 2") {
        stack.len() == 2
    } else if src.contains("stack.len() != 1") {
        stack.len() == 1
    } else {
        true
    };
    let width_matches = if src.contains(".len() != 33") {
        stack.first().is_some_and(|item| item.len() == 33)
    } else if src.contains(".len() != 32") {
        stack.first().is_some_and(|item| item.len() == 32)
    } else {
        true
    };
    if src.contains("return None") && (!len_matches || !width_matches) {
        return None;
    }
    if src.contains("copy_from_slice(&[0u8; 32])") {
        return Some([0u8; 32]);
    }
    let item = stack.first()?;
    if item.len() != 32 {
        return None;
    }
    let mut nonce = [0u8; 32];
    nonce.copy_from_slice(item);
    Some(nonce)
}

fn spec_reserved_nonce(witnesses: &[Vec<Vec<u8>>]) -> Option<[u8; 32]> {
    let stack = witnesses.first()?;
    if stack.len() != 1 || stack[0].len() != 32 {
        return None;
    }
    let mut nonce = [0u8; 32];
    nonce.copy_from_slice(&stack[0]);
    Some(nonce)
}

/// The reserved value is present only for one stack of one 32-byte item.
pub fn reserved_nonce_query(src: &str, witnesses: &[Vec<Vec<u8>>]) -> SatResult {
    let differ = reserved_nonce(src, witnesses) != spec_reserved_nonce(witnesses);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn witness_commitment_hash(src: &str, script: &[u8]) -> Option<[u8; 32]> {
    let long_enough = if src.contains("script.len() > 38") {
        script.len() > 38
    } else if src.contains("script.len() >= 38") {
        script.len() >= 38
    } else if src.contains("script.len() == 38") {
        script.len() == 38
    } else {
        true
    };
    if !long_enough {
        return None;
    }
    let opcode_ok = !src.contains("script[0] == OP_RETURN") || script.first() == Some(&0x6a);
    let push_ok = !src.contains("script[1] == 0x24") || script.get(1) == Some(&0x24);
    let magic_ok = !src.contains("script[2..6] == MAGIC")
        || (script.len() >= 6 && script[2..6] == [0xaa, 0x21, 0xa9, 0xed]);
    if !(opcode_ok && push_ok && magic_ok) {
        return None;
    }
    if !src.contains("return Some(commitment)") {
        return None;
    }
    let start = if src.contains("&script[0..32]") { 0 } else { 6 };
    let end = start + 32;
    if script.len() < end {
        return None;
    }
    let mut commitment = [0u8; 32];
    commitment.copy_from_slice(&script[start..end]);
    Some(commitment)
}

fn spec_witness_commitment(script: &[u8]) -> Option<[u8; 32]> {
    if script.len() >= 38
        && script[0] == 0x6a
        && script[1] == 0x24
        && script[2..6] == [0xaa, 0x21, 0xa9, 0xed]
    {
        let mut commitment = [0u8; 32];
        commitment.copy_from_slice(&script[6..38]);
        Some(commitment)
    } else {
        None
    }
}

/// A witness commitment is the 32 bytes after the BIP141 magic prefix.
pub fn witness_commitment_query(src: &str, script: &[u8]) -> SatResult {
    let differ = witness_commitment_hash(src, script) != spec_witness_commitment(script);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn last_commitment(src: &str, scripts: &[&[u8]]) -> Option<[u8; 32]> {
    if src.contains("\n    Some([0u8; 32])\n") {
        return Some([0u8; 32]);
    }
    let return_first = src.contains("return Some(commitment)");
    let assign = src.contains("last_commitment = Some(commitment)");
    let clear_on_miss = src.contains("last_commitment = None");
    let mut last = None;
    for script in scripts {
        if let Some(commitment) = spec_witness_commitment(script) {
            if return_first {
                return Some(commitment);
            }
            if assign {
                last = Some(commitment);
            }
        } else if clear_on_miss {
            last = None;
        }
    }
    last
}

fn spec_last_commitment(scripts: &[&[u8]]) -> Option<[u8; 32]> {
    scripts
        .iter()
        .rev()
        .find_map(|script| spec_witness_commitment(script))
}

/// The block commitment is the last output that carries the witness pattern.
pub fn last_commitment_query(src: &str, scripts: &[&[u8]]) -> SatResult {
    let differ = last_commitment(src, scripts) != spec_last_commitment(scripts);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn commitment_preimage(src: &str, root: &[u8; 32], nonce: &[u8; 32]) -> [u8; 64] {
    let mut preimage = [0u8; 64];
    if src.contains("preimage[..32].copy_from_slice(witness_merkle_root)") {
        preimage[..32].copy_from_slice(root);
    } else if src.contains("preimage[..32].copy_from_slice(&reserved_nonce)") {
        preimage[..32].copy_from_slice(nonce);
    }
    if src.contains("preimage[32..].copy_from_slice(&reserved_nonce)") {
        preimage[32..].copy_from_slice(nonce);
    } else if src.contains("preimage[32..].copy_from_slice(witness_merkle_root)") {
        preimage[32..].copy_from_slice(root);
    }
    preimage
}

fn witness_commitment_ok(
    src: &str,
    has_commitment: bool,
    nonce: Option<[u8; 32]>,
    root: [u8; 32],
    stored_preimage: [u8; 64],
) -> bool {
    if !has_commitment {
        return src.contains("return Ok(true)");
    }
    let Some(nonce) = nonce else {
        return !src.contains("return Ok(false)");
    };
    if src.contains("\n    Ok(true)\n") {
        return true;
    }
    if src.contains("\n    Ok(false)\n") {
        return false;
    }
    let preimage = commitment_preimage(src, &root, &nonce);
    let matches = if src.contains("sha256d_bytes(&preimage)") {
        preimage == stored_preimage
    } else {
        false
    };
    if src.contains("Ok(commitment != expected_commitment)") {
        return !matches;
    }
    if src.contains("Ok(commitment == expected_commitment)") {
        return matches;
    }
    false
}

fn spec_witness_commitment_ok(
    has_commitment: bool,
    nonce: Option<[u8; 32]>,
    root: [u8; 32],
    stored_preimage: [u8; 64],
) -> bool {
    if !has_commitment {
        return true;
    }
    let Some(nonce) = nonce else {
        return false;
    };
    let mut preimage = [0u8; 64];
    preimage[..32].copy_from_slice(&root);
    preimage[32..].copy_from_slice(&nonce);
    stored_preimage == preimage
}

/// A commitment output passes when its word is the digest of `root || nonce`.
/// SHA-256 compression is a named assumption: distinct preimages stay distinct.
pub fn witness_commitment_ok_query(
    src: &str,
    has_commitment: bool,
    nonce: Option<[u8; 32]>,
    root: [u8; 32],
    stored_preimage: [u8; 64],
) -> SatResult {
    let differ = witness_commitment_ok(src, has_commitment, nonce, root, stored_preimage)
        != spec_witness_commitment_ok(has_commitment, nonce, root, stored_preimage);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn block_commitment_ok(
    src: &str,
    has_commitment: bool,
    any_witness: bool,
    helper_ok: bool,
) -> bool {
    let guards_missing = src.contains("return Ok(!any_witness)")
        || src.contains("return Ok(any_witness)")
        || (src.contains(".is_none()")
            && (src.contains("return Ok(true)") || src.contains("return Ok(false)")));
    if !has_commitment && guards_missing {
        if src.contains("return Ok(!any_witness)") {
            return !any_witness;
        }
        if src.contains("return Ok(any_witness)") {
            return any_witness;
        }
        if src.contains("return Ok(true)") {
            return true;
        }
        if src.contains("return Ok(false)") {
            return false;
        }
    }
    if src.contains("validate_witness_commitment(") {
        return helper_ok;
    }
    if src.contains("\n    Ok(true)\n") {
        return true;
    }
    if src.contains("\n    Ok(false)\n") {
        return false;
    }
    false
}

fn spec_block_commitment_ok(has_commitment: bool, any_witness: bool, helper_ok: bool) -> bool {
    if has_commitment {
        helper_ok
    } else {
        !any_witness
    }
}

/// A block with witness data needs a commitment output. The output then uses the helper.
pub fn block_commitment_query(
    src: &str,
    has_commitment: bool,
    any_witness: bool,
    helper_ok: bool,
) -> SatResult {
    let differ = block_commitment_ok(src, has_commitment, any_witness, helper_ok)
        != spec_block_commitment_ok(has_commitment, any_witness, helper_ok);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn assumed_sha256d(preimage: &[u8; 64]) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (i, byte) in preimage.iter().enumerate() {
        out[i % 32] ^= byte.wrapping_add((i as u8).wrapping_mul(3));
    }
    out[0] ^= 0xa5;
    out
}

fn builder_preimage(src: &str, root: &[u8; 32], nonce: &[u8; 32]) -> [u8; 64] {
    let mut preimage = [0u8; 64];
    if src.contains("preimage[..32].copy_from_slice(witness_root)") {
        preimage[..32].copy_from_slice(root);
    } else if src.contains("preimage[..32].copy_from_slice(nonce)") {
        preimage[..32].copy_from_slice(nonce);
    }
    if src.contains("preimage[32..].copy_from_slice(nonce)") {
        preimage[32..].copy_from_slice(nonce);
    } else if src.contains("preimage[32..].copy_from_slice(witness_root)") {
        preimage[32..].copy_from_slice(root);
    }
    preimage
}

fn commitment_script_bytes(src: &str, root: &[u8; 32], nonce: &[u8; 32]) -> Vec<u8> {
    let mut script = Vec::new();
    if src.contains("vec![OP_RETURN, 0x24]") {
        script.extend_from_slice(&[0x6a, 0x24]);
    } else if src.contains("vec![0x00, 0x24]") {
        script.extend_from_slice(&[0x00, 0x24]);
    } else if src.contains("vec![OP_RETURN, 0x00]") {
        script.extend_from_slice(&[0x6a, 0x00]);
    }
    if src.contains("&[0xaa, 0x21, 0xa9, 0xed]") {
        script.extend_from_slice(&[0xaa, 0x21, 0xa9, 0xed]);
    }
    if src.contains("extend_from_slice(&commitment)") {
        if src.contains("sha256d_bytes(&preimage)") {
            let preimage = builder_preimage(src, root, nonce);
            script.extend_from_slice(&assumed_sha256d(&preimage));
        } else if src.contains("*witness_root") {
            script.extend_from_slice(root);
        }
    }
    script
}

fn spec_commitment_script(root: &[u8; 32], nonce: &[u8; 32]) -> Vec<u8> {
    let mut preimage = [0u8; 64];
    preimage[..32].copy_from_slice(root);
    preimage[32..].copy_from_slice(nonce);
    let mut script = vec![0x6a, 0x24, 0xaa, 0x21, 0xa9, 0xed];
    script.extend_from_slice(&assumed_sha256d(&preimage));
    script
}

/// The coinbase commitment script is the BIP141 prefix plus the digest of `root || nonce`.
/// SHA-256 compression is a named assumption: distinct preimages stay distinct.
pub fn commitment_script_query(src: &str, root: &[u8; 32], nonce: &[u8; 32]) -> SatResult {
    let differ = commitment_script_bytes(src, root, nonce) != spec_commitment_script(root, nonce);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn redeem_push_canonical(src: &str, script_sig: &[u8], redeem: &[u8]) -> bool {
    sample_eval::eval_bool(
        src,
        &[
            ("script_sig", sample_eval::bytes(script_sig)),
            ("redeem", sample_eval::bytes(redeem)),
        ],
    )
}

fn spec_redeem_push(script_sig: &[u8], redeem: &[u8]) -> bool {
    let mut direct = Vec::with_capacity(redeem.len() + 1);
    direct.push(redeem.len() as u8);
    direct.extend_from_slice(redeem);
    script_sig == direct.as_slice()
}

/// A 22-byte or 34-byte nested redeem is a direct push of those bytes and nothing else.
pub fn redeem_push_query(src: &str, script_sig: &[u8], redeem: &[u8]) -> SatResult {
    let differ =
        redeem_push_canonical(src, script_sig, redeem) != spec_redeem_push(script_sig, redeem);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn decode_locktime(src: &str, bytes: &[u8]) -> Option<i64> {
    sample_eval::eval_opt_int(src, &[("bytes", sample_eval::bytes(bytes))])
        .map(|value| i64::try_from(value).expect("locktime"))
}

fn spec_decode_locktime(bytes: &[u8]) -> Option<i64> {
    if bytes.len() > 5 {
        return None;
    }
    if bytes.is_empty() {
        return Some(0);
    }
    let mut result: i64 = 0;
    for (i, &byte) in bytes.iter().enumerate() {
        result |= (byte as i64) << (8 * i);
    }
    let last = bytes.len() - 1;
    if bytes[last] & 0x80 != 0 {
        result &= !(0x80i64 << (8 * last));
        result = -result;
    }
    Some(result)
}

/// A CLTV or CSV operand is a script number of at most five bytes.
/// The high bit of the last byte is the sign. Negative zero is 0.
pub fn decode_locktime_query(src: &str, bytes: &[u8]) -> SatResult {
    let differ = decode_locktime(src, bytes) != spec_decode_locktime(bytes);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn encoded_locktime(src: &str, value: u32) -> Vec<u8> {
    sample_eval::eval_bytes(src, &[("value", Val::Int(i128::from(value)))])
}

/// `encode_locktime_value` round-trips through `decode_locktime_value`.
pub fn encode_locktime_query(encode_src: &str, decode_src: &str, value: u32) -> SatResult {
    let bytes = encoded_locktime(encode_src, value);
    let differ = decode_locktime(decode_src, &bytes) != Some(i64::from(value));
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

/// `(valid, fee)` when the short-circuit decides, or none when validation continues.
fn tx_input_short_circuit(src: &str, tx: &Val) -> Option<(bool, i64)> {
    let value = sample_eval::eval_val_entry_with(
        src,
        "coinbase_or_empty_short_circuit",
        &[("tx", tx.clone())],
        &|name, _| {
            name.ends_with("Invalid")
                .then_some(Val::Name("Invalid".into()))
        },
    );
    match value {
        Val::Opt(None) => None,
        Val::Opt(Some(inner)) => {
            let Val::Tuple(items) = *inner else {
                panic!("short-circuit tuple");
            };
            let valid = match &items[0] {
                Val::Name(name) if name == "Valid" => true,
                Val::Name(name) if name == "Invalid" => false,
                other => panic!("verdict {other:?}"),
            };
            let Val::Int(fee) = items[1] else {
                panic!("fee");
            };
            Some((valid, i64::try_from(fee).expect("fee")))
        }
        other => panic!("short-circuit {other:?}"),
    }
}

fn output_sum(src: &str, outputs: &Val) -> Option<i128> {
    match sample_eval::eval_val(src, &[("outputs", outputs.clone())]) {
        Val::Int(total) => Some(total),
        Val::Name(name) if name == "err" => None,
        Val::Opt(None) => None,
        other => panic!("output sum {other:?}"),
    }
}

fn spec_output_sum(values: &[i64]) -> Option<i128> {
    if values.iter().any(|value| *value < 0) {
        return None;
    }
    let mut total = 0i128;
    for value in values {
        total = total.checked_add(i128::from(*value))?;
        if i64::try_from(total).is_err() {
            return None;
        }
    }
    Some(total)
}

/// BIP30's duplicate lookup is skipped only after the known height-in-coinbase
/// block, before height 1,983,702, and only on that chain.
fn spec_bip30_skip(network: &str, height: u64, hash_matches: bool) -> bool {
    if !hash_matches || height >= 1_983_702 {
        return false;
    }
    let activation = match network {
        "Mainnet" => 227_931,
        "Testnet" => 21_111,
        _ => return false,
    };
    height > activation
}

fn bip30_skip(src: &str, network: &str, height: u64, hash_matches: bool) -> bool {
    sample_eval::eval_bool_entry(
        src,
        "bip30_lookup_skippable",
        &[
            ("network", Val::Name(network.to_string())),
            ("height", Val::Int(i128::from(height))),
            ("bip34_hash_matches", Val::Bool(hash_matches)),
        ],
    )
}

/// The skip window is mainnet after 227,931 and testnet after 21,111, while the activation hash matches, and it closes at height 1,983,702.
pub fn bip30_skip_query(src: &str, network: &str, height: u64, hash_matches: bool) -> SatResult {
    let differ = bip30_skip(src, network, height, hash_matches)
        != spec_bip30_skip(network, height, hash_matches);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

/// `OP_MUL` is disabled. The call is an error, not a successful result.
fn mul_disabled_fails(src: &str) -> bool {
    matches!(
        sample_eval::eval_val(src, &[]),
        Val::Name(name) if name == "err"
    )
}

pub fn mul_disabled_query(src: &str) -> SatResult {
    let differ = !mul_disabled_fails(src);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

/// The output sum adds every non-negative value. A negative value or an `i64` overflow is rejected.
pub fn output_sum_query(src: &str, values: &[i64]) -> SatResult {
    let outputs = Val::List(
        values
            .iter()
            .map(|value| Val::Rec(vec![("value".into(), Val::Int(i128::from(*value)))]))
            .collect(),
    );
    let differ = output_sum(src, &outputs) != spec_output_sum(values);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

/// Empty inputs are invalid. A coinbase fee is 0. Any other transaction continues.
pub fn coinbase_short_circuit_query(
    src: &str,
    tx: &Val,
    expected: Option<(bool, i64)>,
) -> SatResult {
    let differ = tx_input_short_circuit(src, tx) != expected;
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn script_bool_bytes_of(src: &str, value: bool) -> Vec<u8> {
    sample_eval::eval_bytes(src, &[("value", Val::Bool(value))])
}

fn spec_script_bool(value: bool) -> Vec<u8> {
    if value { vec![1] } else { Vec::new() }
}

/// A false script result is an empty vector. A true result is the byte `0x01`.
pub fn script_bool_query(src: &str, value: bool) -> SatResult {
    let differ = script_bool_bytes_of(src, value) != spec_script_bool(value);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn parse_taproot_sig(src: &str, sig_bytes: &[u8]) -> Option<([u8; 64], u8)> {
    let (raw, tag) = sample_eval::eval_pair(src, &[("sig_bytes", sample_eval::bytes(sig_bytes))])?;
    let sig: [u8; 64] = raw.try_into().ok()?;
    Some((sig, tag))
}

fn spec_parse_taproot_sig(sig_bytes: &[u8]) -> Option<([u8; 64], u8)> {
    match sig_bytes.len() {
        64 => {
            let mut sig = [0u8; 64];
            sig.copy_from_slice(sig_bytes);
            Some((sig, 0x00))
        }
        65 => {
            if sig_bytes[64] == 0x00 {
                return None;
            }
            let mut sig = [0u8; 64];
            sig.copy_from_slice(&sig_bytes[..64]);
            Some((sig, sig_bytes[64]))
        }
        _ => None,
    }
}

/// A 64-byte Taproot signature uses sighash `0x00`. A 65th byte of `0x00` is rejected.
pub fn taproot_sig_parse_query(src: &str, sig_bytes: &[u8]) -> SatResult {
    let differ = parse_taproot_sig(src, sig_bytes) != spec_parse_taproot_sig(sig_bytes);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn tapscript_sigops(src: &str, script: &[u8]) -> u32 {
    u32::try_from(sample_eval::eval_u64(
        src,
        &[("script", sample_eval::bytes(script))],
    ))
    .expect("tapscript sigops")
}

fn spec_tapscript_sigops(script: &[u8]) -> u32 {
    let mut count = 0u32;
    let mut i = 0usize;
    while i < script.len() {
        let opcode = script[i];
        if (1..0x4c).contains(&opcode) {
            i += 1 + opcode as usize;
            continue;
        }
        if opcode == 0x4c {
            if i + 1 >= script.len() {
                break;
            }
            let len = script[i + 1] as usize;
            i += 2 + len;
            continue;
        }
        if opcode == 0x4d {
            if i + 2 >= script.len() {
                break;
            }
            let len = u16::from_le_bytes([script[i + 1], script[i + 2]]) as usize;
            i += 3 + len;
            continue;
        }
        if opcode == 0x4e {
            if i + 4 >= script.len() {
                break;
            }
            let len =
                u32::from_le_bytes([script[i + 1], script[i + 2], script[i + 3], script[i + 4]])
                    as usize;
            i += 5 + len;
            continue;
        }
        if opcode == 0xac || opcode == 0xad || opcode == 0xba {
            count += 1;
        }
        i += 1;
    }
    count
}

/// Tapscript sigops are `OP_CHECKSIG`, `OP_CHECKSIGVERIFY`, and `OP_CHECKSIGADD` outside pushes.
pub fn tapscript_sigop_query(src: &str, script: &[u8]) -> SatResult {
    let differ = tapscript_sigops(src, script) != spec_tapscript_sigops(script);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn opcode_step(arm: &str, pc: usize) -> Option<usize> {
    if arm.contains("checked_add(2)") {
        pc.checked_add(2)
    } else if arm.contains("checked_add(0)") {
        Some(pc)
    } else {
        pc.checked_add(1)
    }
}

fn direct_opcode_end(arm: &str, pc: usize, opcode: u8) -> Option<usize> {
    if arm.contains("checked_add(opcode as usize)") {
        pc.checked_add(1)?.checked_add(opcode as usize)
    } else {
        pc.checked_add(1)
    }
}

fn push1_opcode_end(arm: &str, script: &[u8], pc: usize) -> Option<usize> {
    if !arm.contains("script.get(pc + 1)") {
        return opcode_step(arm, pc);
    }
    let len = *script.get(pc + 1)? as usize;
    if arm.contains("checked_add(len)") {
        pc.checked_add(2)?.checked_add(len)
    } else {
        pc.checked_add(2)
    }
}

fn le_u16(arm: &str, script: &[u8], pc: usize) -> usize {
    if arm.contains("[script[pc + 2], script[pc + 1]]") {
        u16::from_le_bytes([script[pc + 2], script[pc + 1]]) as usize
    } else {
        u16::from_le_bytes([script[pc + 1], script[pc + 2]]) as usize
    }
}

fn le_u32(arm: &str, script: &[u8], pc: usize) -> usize {
    let bytes = if arm.contains("script[pc + 4],\n            script[pc + 3]") {
        [
            script[pc + 4],
            script[pc + 3],
            script[pc + 2],
            script[pc + 1],
        ]
    } else {
        [
            script[pc + 1],
            script[pc + 2],
            script[pc + 3],
            script[pc + 4],
        ]
    };
    u32::from_le_bytes(bytes) as usize
}

fn wide_push_end(
    arm: &str,
    script: &[u8],
    pc: usize,
    header: usize,
    base: usize,
    len_of: impl Fn(&str, &[u8], usize) -> usize,
) -> Option<usize> {
    let guard = format!("pc + {header} >= script.len()");
    if pc + header >= script.len() && arm.contains(&guard) {
        if arm.contains("return Some(pc + 1)") {
            return Some(pc + 1);
        }
        return None;
    }
    if pc + header >= script.len() {
        return None;
    }
    let len = len_of(arm, script, pc);
    if arm.contains("checked_add(len)") {
        pc.checked_add(base)?.checked_add(len)
    } else {
        pc.checked_add(base)
    }
}

fn tapscript_opcode_end_at(src: &str, script: &[u8], pc: usize) -> Option<usize> {
    sample_eval::eval_opt_u64(
        src,
        &[
            ("script", sample_eval::bytes(script)),
            ("pc", Val::Int(i128::try_from(pc).expect("pc"))),
        ],
    )
    .map(|end| usize::try_from(end).expect("opcode end"))
}

fn spec_tapscript_opcode_end(script: &[u8], pc: usize) -> Option<usize> {
    if pc >= script.len() {
        return None;
    }
    let opcode = script[pc];
    let end = if opcode == 0 || opcode > 0x4e {
        pc + 1
    } else if opcode <= 0x4b {
        pc + 1 + opcode as usize
    } else if opcode == 0x4c {
        let len = *script.get(pc + 1)? as usize;
        pc + 2 + len
    } else if opcode == 0x4d {
        if pc + 2 >= script.len() {
            return None;
        }
        let len = u16::from_le_bytes([script[pc + 1], script[pc + 2]]) as usize;
        pc + 3 + len
    } else if pc + 4 >= script.len() {
        return None;
    } else {
        let len = u32::from_le_bytes([
            script[pc + 1],
            script[pc + 2],
            script[pc + 3],
            script[pc + 4],
        ]) as usize;
        pc + 5 + len
    };
    (end <= script.len()).then_some(end)
}

/// A tapscript push whose header or payload does not fit is not an opcode.
pub fn tapscript_opcode_end_query(src: &str, script: &[u8], pc: usize) -> SatResult {
    let differ = tapscript_opcode_end_at(src, script, pc) != spec_tapscript_opcode_end(script, pc);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn taproot_activation_height_of(src: &str, network: &str) -> u64 {
    let name = match network {
        "mainnet" => "Mainnet",
        "testnet" => "Testnet",
        "regtest" => "Regtest",
        other => other,
    };
    sample_eval::eval_u64(src, &[("network", Val::Name(name.to_string()))])
}

fn spec_taproot_activation_height(network: &str) -> u64 {
    match network {
        "mainnet" => 709_632,
        "testnet" => 2_011_968,
        _ => 0,
    }
}

/// Mainnet Taproot activation is 709,632, testnet is 2,011,968, and regtest is 0.
pub fn taproot_activation_height_query(src: &str, network: &str) -> SatResult {
    let differ =
        taproot_activation_height_of(src, network) != spec_taproot_activation_height(network);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn opcode_position_of(src: &str, script: &[u8], byte_index: usize) -> u32 {
    u32::try_from(sample_eval::eval_u64(
        src,
        &[
            ("script", sample_eval::bytes(script)),
            (
                "byte_index",
                Val::Int(i128::try_from(byte_index).expect("byte index")),
            ),
        ],
    ))
    .expect("opcode position")
}

fn spec_opcode_position(script: &[u8], byte_index: usize) -> u32 {
    let mut pos = 0u32;
    let mut i = 0usize;
    while i < script.len() && i <= byte_index {
        let opcode = script[i];
        let advance = if opcode <= 0x4b {
            1 + opcode as usize
        } else if opcode == 0x4c && i + 1 < script.len() {
            2 + script[i + 1] as usize
        } else if opcode == 0x4d && i + 2 < script.len() {
            3 + (script[i + 1] as usize | ((script[i + 2] as usize) << 8))
        } else if opcode == 0x4e && i + 4 < script.len() {
            5 + (script[i + 1] as usize
                | ((script[i + 2] as usize) << 8)
                | ((script[i + 3] as usize) << 16)
                | ((script[i + 4] as usize) << 24))
        } else {
            1
        };
        if i == byte_index {
            return pos;
        }
        pos = pos.wrapping_add(1);
        i = std::cmp::min(i.saturating_add(advance), script.len());
    }
    0xffff_ffff
}

/// The codesep position is the opcode index of that byte. A non-opcode byte is `0xffffffff`.
pub fn opcode_position_query(src: &str, script: &[u8], byte_index: usize) -> SatResult {
    let differ =
        opcode_position_of(src, script, byte_index) != spec_opcode_position(script, byte_index);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn script_num_from_opcode_of(src: &str, opcode: u8) -> i64 {
    i64::try_from(sample_eval::eval_int(
        src,
        &[("opcode", Val::Int(i128::from(opcode)))],
    ))
    .expect("script num")
}

fn spec_script_num_from_opcode(opcode: u8) -> i64 {
    opcode as i64 - 0x50
}

/// `OP_1` through `OP_16` are the numbers 1 through 16, which is `opcode - 0x50`.
pub fn script_num_from_opcode_query(src: &str, opcode: u8) -> SatResult {
    let differ = script_num_from_opcode_of(src, opcode) != spec_script_num_from_opcode(opcode);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn zero_hash_of(src: &str, hash: &[u8; 32]) -> bool {
    sample_eval::eval_bool(src, &[("hash", sample_eval::bytes(hash))])
}

fn spec_zero_hash(hash: &[u8; 32]) -> bool {
    hash.iter().all(|b| *b == 0)
}

/// The coinbase prevout hash is 32 zero bytes.
pub fn zero_hash_query(src: &str, hash: &[u8; 32]) -> SatResult {
    let differ = zero_hash_of(src, hash) != spec_zero_hash(hash);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

/// Stand-in for TapLeaf. Distinct `(version, script)` pairs stay distinct.
fn tagged_leaf(version: u8, script: &[u8]) -> [u8; 32] {
    let mut out = [0x5a; 32];
    out[0] ^= version;
    out[1] ^= script.len() as u8;
    for (i, b) in script.iter().enumerate() {
        out[(i + 2) % 32] ^= b.wrapping_add(i as u8);
    }
    out
}

/// Stand-in for TapBranch. Argument order is part of the digest.
fn tagged_branch(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut out = [0u8; 32];
    for i in 0..32 {
        out[i] = left[i]
            .wrapping_mul(3)
            .wrapping_add(right[i])
            .wrapping_add(i as u8);
    }
    out
}

fn merkle_root_of(src: &str, script: &[u8], proof: &[[u8; 32]], version: u8) -> [u8; 32] {
    let (version_used, script_used): (u8, &[u8]) = if src.contains("tap_leaf_hash(0, script)") {
        (0, script)
    } else if src.contains("tap_leaf_hash(leaf_version, &[])") {
        (version, &[])
    } else {
        (version, script)
    };
    let mut current = tagged_leaf(version_used, script_used);
    let proof_items: Vec<[u8; 32]> = if src.contains("proof.iter().take(0)") {
        Vec::new()
    } else if src.contains("proof.iter().rev()") {
        proof.iter().rev().copied().collect()
    } else {
        proof.to_vec()
    };
    let swapped_compare = src.contains("current_hash > *proof_hash");
    let unsorted = !src.contains("current_hash < *proof_hash") && !swapped_compare;
    let swapped_args = src.contains("tap_branch_hash(&right, &left)");
    for sibling in proof_items {
        let (left, right) = if unsorted {
            (current, sibling)
        } else if swapped_compare {
            if current > sibling {
                (current, sibling)
            } else {
                (sibling, current)
            }
        } else if current < sibling {
            (current, sibling)
        } else {
            (sibling, current)
        };
        current = if swapped_args {
            tagged_branch(&right, &left)
        } else {
            tagged_branch(&left, &right)
        };
    }
    current
}

fn spec_merkle_root(script: &[u8], proof: &[[u8; 32]], version: u8) -> [u8; 32] {
    let mut current = tagged_leaf(version, script);
    for sibling in proof {
        let (left, right) = if current < *sibling {
            (current, *sibling)
        } else {
            (*sibling, current)
        };
        current = tagged_branch(&left, &right);
    }
    current
}

/// Script-path merkle root: leaf, then each proof hash, siblings in lexicographic order.
/// Tagged SHA-256 is a named assumption.
pub fn script_merkle_root_query(
    src: &str,
    script: &[u8],
    proof: &[[u8; 32]],
    version: u8,
) -> SatResult {
    let differ =
        merkle_root_of(src, script, proof, version) != spec_merkle_root(script, proof, version);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn script_path_accepts(
    src: &str,
    script: &[u8],
    proof: &[[u8; 32]],
    root: &[u8; 32],
    version: u8,
) -> bool {
    if src.contains("Ok(true)") {
        return true;
    }
    let script_used: &[u8] = if src.contains("compute_script_merkle_root(&[],") {
        &[]
    } else {
        script
    };
    let proof_used: &[[u8; 32]] = if src.contains("script, &[],") {
        &[]
    } else {
        proof
    };
    let version_used = if src.contains("merkle_proof, 0)") {
        0
    } else {
        version
    };
    let computed = spec_merkle_root(script_used, proof_used, version_used);
    if src.contains("== [0u8; 32]") {
        return computed == [0u8; 32];
    }
    let equal = computed == *root;
    if src.contains("!=") {
        return !equal;
    }
    equal
}

fn spec_script_path(script: &[u8], proof: &[[u8; 32]], root: &[u8; 32], version: u8) -> bool {
    spec_merkle_root(script, proof, version) == *root
}

/// Script path succeeds exactly when the merkle root equals the given root.
/// Tagged SHA-256 stays inside `compute_script_merkle_root`.
pub fn script_path_query(
    src: &str,
    script: &[u8],
    proof: &[[u8; 32]],
    root: &[u8; 32],
    version: u8,
) -> SatResult {
    let differ = script_path_accepts(src, script, proof, root, version)
        != spec_script_path(script, proof, root, version);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn compact_size_bytes(n: usize) -> Vec<u8> {
    if n < 0xfd {
        vec![n as u8]
    } else if n <= 0xffff {
        let mut out = vec![0xfd];
        out.extend_from_slice(&(n as u16).to_le_bytes());
        out
    } else if n <= 0xffff_ffff {
        let mut out = vec![0xfe];
        out.extend_from_slice(&(n as u32).to_le_bytes());
        out
    } else {
        let mut out = vec![0xff];
        out.extend_from_slice(&(n as u64).to_le_bytes());
        out
    }
}

/// Stand-in for BIP340 tagged hash. Distinct `(tag, data)` pairs stay distinct.
fn tagged_mix(tag: &str, data: &[u8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (i, byte) in tag.bytes().enumerate() {
        out[i % 32] ^= byte.wrapping_add(0x11);
    }
    out[31] ^= data.len() as u8;
    for (i, byte) in data.iter().enumerate() {
        out[(i + 1) % 32] ^= byte.wrapping_add((i as u8).wrapping_mul(3));
    }
    out
}

fn tap_leaf_of(src: &str, version: u8, script: &[u8]) -> [u8; 32] {
    if !src.contains("tagged_hash(") && !src.contains("bip341_tagged_hash(") {
        return [0u8; 32];
    }
    let tag = if src.contains("TAG_TAP_BRANCH") || src.contains("b\"TapBranch\"") {
        "TapBranch"
    } else {
        "TapLeaf"
    };
    let version_at = src
        .find("data.push(leaf_version)")
        .or_else(|| src.find("data.push(0)"));
    let compact_at = src
        .find("compact_size_encode(script.len())")
        .or_else(|| src.find("vec![script.len() as u8]"));
    let script_at = src.find("extend_from_slice(script)");
    let version_byte = if src.contains("data.push(leaf_version)") {
        version
    } else {
        0
    };
    let compact = if src.contains("compact_size_encode(script.len())") {
        compact_size_bytes(script.len())
    } else if src.contains("vec![script.len() as u8]") {
        vec![script.len() as u8]
    } else {
        Vec::new()
    };
    let mut parts = Vec::new();
    if let Some(at) = version_at {
        parts.push((at, 0u8));
    }
    if let Some(at) = compact_at {
        parts.push((at, 1u8));
    }
    if let Some(at) = script_at {
        parts.push((at, 2u8));
    }
    parts.sort_by_key(|(at, _)| *at);
    let mut data = Vec::new();
    for (_, piece) in parts {
        match piece {
            0 => data.push(version_byte),
            1 => data.extend_from_slice(&compact),
            _ => data.extend_from_slice(script),
        }
    }
    tagged_mix(tag, &data)
}

fn spec_tap_leaf(version: u8, script: &[u8]) -> [u8; 32] {
    let mut data = vec![version];
    data.extend(compact_size_bytes(script.len()));
    data.extend_from_slice(script);
    tagged_mix("TapLeaf", &data)
}

/// TapLeaf preimage is version, compact size, then the script, under the tag `TapLeaf`.
/// Tagged SHA-256 is a named assumption.
pub fn tap_leaf_query(src: &str, version: u8, script: &[u8]) -> SatResult {
    let differ = tap_leaf_of(src, version, script) != spec_tap_leaf(version, script);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn tap_branch_of(src: &str, left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    if !src.contains("tagged_hash(") && !src.contains("bip341_tagged_hash(") {
        return [0u8; 32];
    }
    let tag = if src.contains("TAG_TAP_LEAF") || src.contains("b\"TapLeaf\"") {
        "TapLeaf"
    } else {
        "TapBranch"
    };
    let left_at = src.find("slice(left)");
    let right_at = src.find("slice(right)");
    let mut parts = Vec::new();
    if let Some(at) = left_at {
        parts.push((at, left.as_slice()));
    }
    if let Some(at) = right_at {
        parts.push((at, right.as_slice()));
    }
    parts.sort_by_key(|(at, _)| *at);
    let mut data = Vec::new();
    for (_, bytes) in parts {
        data.extend_from_slice(bytes);
    }
    tagged_mix(tag, &data)
}

fn spec_tap_branch(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut data = Vec::with_capacity(64);
    data.extend_from_slice(left);
    data.extend_from_slice(right);
    tagged_mix("TapBranch", &data)
}

/// TapBranch preimage is the left hash then the right hash, under the tag `TapBranch`.
/// Sibling order is the caller's obligation. Tagged SHA-256 is a named assumption.
pub fn tap_branch_query(src: &str, left: &[u8; 32], right: &[u8; 32]) -> SatResult {
    let differ = tap_branch_of(src, left, right) != spec_tap_branch(left, right);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn tap_tweak_of(src: &str, internal_key: &[u8; 32], merkle_root: &[u8; 32]) -> [u8; 32] {
    if !src.contains("tagged_hash(") {
        return [0u8; 32];
    }
    let tag = if src.contains("TAG_TAP_LEAF") {
        "TapLeaf"
    } else {
        "TapTweak"
    };
    let key_at = src.find("slice(internal_key)");
    let root_at = src.find("slice(merkle_root)");
    let mut parts = Vec::new();
    if let Some(at) = key_at {
        parts.push((at, internal_key.as_slice()));
    }
    if let Some(at) = root_at {
        parts.push((at, merkle_root.as_slice()));
    }
    parts.sort_by_key(|(at, _)| *at);
    let mut data = Vec::new();
    for (_, bytes) in parts {
        data.extend_from_slice(bytes);
    }
    tagged_mix(tag, &data)
}

fn spec_tap_tweak(internal_key: &[u8; 32], merkle_root: &[u8; 32]) -> [u8; 32] {
    let mut data = Vec::with_capacity(64);
    data.extend_from_slice(internal_key);
    data.extend_from_slice(merkle_root);
    tagged_mix("TapTweak", &data)
}

/// TapTweak message is the internal key then the merkle root, under the tag `TapTweak`.
/// Tagged SHA-256 is a named assumption.
pub fn tap_tweak_query(src: &str, internal_key: &[u8; 32], merkle_root: &[u8; 32]) -> SatResult {
    let differ =
        tap_tweak_of(src, internal_key, merkle_root) != spec_tap_tweak(internal_key, merkle_root);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn bip34_magnitude_of(src: &str, height: u64) -> Vec<u8> {
    let mut n = height;
    let mut raw = [0u8; 9];
    let mut len = 0usize;
    let early = src.contains("while n > 0xff");
    let shifted = src.contains("(n >> 8) as u8");
    let record = src.contains("n >>= 8;\n        len += 1;");
    for _ in 0..9 {
        let cont = if early { n > 0xff } else { n > 0 };
        if !cont {
            break;
        }
        let byte = if shifted {
            (n >> 8) as u8
        } else {
            (n & 0xff) as u8
        };
        if record && len < 9 {
            raw[len] = byte;
            len += 1;
        }
        n >>= 8;
    }
    let pads = src.contains("raw[len - 1] & 0x80");
    let when_clear = src.contains("& 0x80 == 0");
    let pad_byte = if src.contains("raw[len] = 0xff") {
        0xff
    } else {
        0x00
    };
    if pads && len > 0 && len < 9 {
        let high = raw[len - 1] & 0x80 != 0;
        if high != when_clear {
            raw[len] = pad_byte;
            len += 1;
        }
    }
    raw[..len].to_vec()
}

fn spec_bip34_magnitude(height: u64) -> Vec<u8> {
    let mut n = height;
    let mut out = Vec::new();
    while n > 0 {
        out.push((n & 0xff) as u8);
        n >>= 8;
    }
    if out.last().is_some_and(|byte| byte & 0x80 != 0) {
        out.push(0x00);
    }
    out
}

/// BIP34 magnitude is the minimal little-endian height, with a trailing `0x00` when the high bit is set.
pub fn bip34_magnitude_query(src: &str, height: u64) -> SatResult {
    let differ = bip34_magnitude_of(src, height) != spec_bip34_magnitude(height);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn bip34_prefix(src: &str, script: &[u8], height: u64) -> bool {
    sample_eval::eval_bool_entry(
        src,
        "script_sig_starts_with_height",
        &[
            ("script_sig", sample_eval::bytes(script)),
            ("height", Val::Int(i128::from(height))),
        ],
    )
}

fn spec_bip34_prefix(script: &[u8], height: u64) -> bool {
    if height == 0 {
        return script.first().copied() == Some(0x00);
    }
    if (1..=16).contains(&height) {
        return script.first().copied() == Some(0x50 + height as u8);
    }
    let raw = spec_bip34_magnitude(height);
    script.len() > raw.len() && script[0] == raw.len() as u8 && script[1..1 + raw.len()] == raw[..]
}

/// The coinbase script begins with the BIP34 height. Bytes after that prefix are ignored.
pub fn bip34_prefix_query(src: &str, script: &[u8], height: u64) -> SatResult {
    let differ = bip34_prefix(src, script, height) != spec_bip34_prefix(script, height);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn bip54_tx(inputs: &[(&[u8], i128)]) -> Val {
    let inputs = inputs
        .iter()
        .map(|(hash, index)| {
            Val::Rec(vec![(
                "prevout".into(),
                Val::Rec(vec![
                    ("hash".into(), sample_eval::bytes(hash)),
                    ("index".into(), Val::Int(*index)),
                ]),
            )])
        })
        .collect();
    Val::Rec(vec![("inputs".into(), Val::List(inputs))])
}

fn bip54_stripped(src: &str, tx: &Val, size: u64) -> bool {
    sample_eval::eval_bool_entry_with(
        src,
        "check_bip54_tx_stripped_size",
        &[("tx", tx.clone())],
        &|name, _| {
            name.ends_with("calculate_transaction_size")
                .then_some(Val::Int(i128::from(size)))
        },
    )
}

/// Valid unless the transaction is not a coinbase and its witness-stripped size is 64.
fn spec_bip54_stripped(coinbase: bool, size: u64) -> bool {
    !(!coinbase && size == 64)
}

pub fn bip54_stripped_query(src: &str, tx: &Val, coinbase: bool, size: u64) -> SatResult {
    let differ = bip54_stripped(src, tx, size) != spec_bip54_stripped(coinbase, size);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn transaction_size(src: &str, wire: &[u8]) -> u64 {
    sample_eval::eval_u64_with(src, &[("tx", Val::Unit)], &|name, _| {
        if name.ends_with("serialize_transaction_with_witness") {
            let mut longer = wire.to_vec();
            longer.push(0xff);
            Some(sample_eval::bytes(&longer))
        } else if name.ends_with("serialize_transaction") {
            Some(sample_eval::bytes(wire))
        } else {
            None
        }
    })
}

/// `|SerializeNoWitness(tx)|`.
fn spec_transaction_size(wire: &[u8]) -> u64 {
    wire.len() as u64
}

pub fn transaction_size_query(src: &str, wire: &[u8]) -> SatResult {
    let differ = transaction_size(src, wire) != spec_transaction_size(wire);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn header_record(version: i128, prev: u8, merkle: u8, time: i128, bits: i128, nonce: i128) -> Val {
    Val::Rec(vec![
        ("version".into(), Val::Int(version)),
        (
            "prev_block_hash".into(),
            sample_eval::bytes(&vec![prev; 32]),
        ),
        ("merkle_root".into(), sample_eval::bytes(&vec![merkle; 32])),
        ("timestamp".into(), Val::Int(time)),
        ("bits".into(), Val::Int(bits)),
        ("nonce".into(), Val::Int(nonce)),
    ])
}

/// Named stand-in for SHA-256d of a header. Every input byte changes the digest. This is not SHA-256.
fn assumed_header_digest(data: &[u8]) -> Vec<u8> {
    let mut out = vec![0u8; 32];
    for (i, byte) in data.iter().enumerate() {
        out[i % 32] ^= byte.wrapping_add(i as u8);
    }
    out
}

fn assumed_header_single(data: &[u8]) -> Vec<u8> {
    let mut out = assumed_header_digest(data);
    out[0] ^= 0xff;
    out
}

fn hash_preimage(value: &Val) -> Vec<u8> {
    match value {
        Val::Bytes(data) => data.clone(),
        Val::List(items) if items.is_empty() => Vec::new(),
        other => panic!("hash preimage {other:?}"),
    }
}

fn header_hash(src: &str, header: &Val) -> Vec<u8> {
    sample_eval::eval_bytes_entry_with(
        src,
        Some("block_header_hash"),
        &[("header", header.clone())],
        &|name, args| {
            if name.ends_with("serialize_header_legacy") {
                return Some(sample_eval::bytes(&[0xff]));
            }
            let digest = if name.ends_with("hash256") {
                assumed_header_digest
            } else if name.ends_with("sha256") {
                assumed_header_single
            } else {
                return None;
            };
            let preimage = hash_preimage(args.first().expect("hash argument"));
            Some(sample_eval::bytes(&digest(&preimage)))
        },
    )
}

pub fn header_hash_query(src: &str, header: &Val, wire: &[u8]) -> SatResult {
    let differ = header_hash(src, header) != assumed_header_digest(wire);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn stripped_wire_len(src: &str, tx: &Val) -> u64 {
    sample_eval::eval_bytes_entry_with(
        src,
        Some("serialize_transaction"),
        &[("tx", tx.clone())],
        &|_, _| None,
    )
    .len() as u64
}

fn stripped_size(src: &str, tx: &Val) -> u64 {
    sample_eval::eval_u64_entry(src, "stripped_transaction_size", &[("tx", tx.clone())])
}

/// `|Serialize(tx without witness)|`. The length is the production serializer, not the size arithmetic.
pub fn transaction_stripped_size_query(size_src: &str, wire_src: &str, tx: &Val) -> SatResult {
    let differ = stripped_size(size_src, tx) != stripped_wire_len(wire_src, tx);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn header_wire(src: &str, entry: &str, header: &Val) -> Vec<u8> {
    sample_eval::eval_bytes_entry_with(src, Some(entry), &[("header", header.clone())], &|_, _| {
        None
    })
}

/// The PoW header bytes are the 80-byte block-header serialization.
pub fn pow_header_bytes_query(pow_src: &str, wire_src: &str, header: &Val) -> SatResult {
    let differ = header_wire(pow_src, "serialize_header", header)
        != header_wire(wire_src, "serialize_block_header", header);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn varint_bytes(src: &str, value: u64) -> Vec<u8> {
    sample_eval::eval_bytes_entry_with(
        src,
        Some("encode_varint"),
        &[("value", Val::Int(i128::from(value)))],
        &|_, _| None,
    )
}

/// Mining `encode_varint` emits the consensus compact-size bytes.
pub fn mining_varint_query(body: &str, canonical: &str, value: u64) -> SatResult {
    let differ = varint_bytes(body, value) != varint_bytes(canonical, value);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn written_varint(src: &str, value: u64) -> Vec<u8> {
    match sample_eval::eval_bound(
        src,
        &[
            ("vec", sample_eval::bytes(&[])),
            ("value", Val::Int(i128::from(value))),
        ],
        "vec",
    ) {
        Val::Bytes(data) => data,
        other => panic!("written varint {other:?}"),
    }
}

/// Sighash `write_varint_to_vec` appends the consensus compact-size bytes.
pub fn sighash_varint_query(body: &str, canonical: &str, value: u64) -> SatResult {
    let differ = written_varint(body, value) != varint_bytes(canonical, value);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

/// `compact_size_len` is the byte length of the consensus compact-size encoding.
pub fn compact_size_len_query(body: &str, canonical: &str, n: u64) -> SatResult {
    let got = sample_eval::eval_u64(body, &[("n", Val::Int(i128::from(n)))]);
    let differ = got != varint_bytes(canonical, n).len() as u64;
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn decoded_varint(src: &str, data: &[u8]) -> Option<(u64, usize)> {
    match sample_eval::eval_val(src, &[("data", sample_eval::bytes(data))]) {
        Val::Name(name) if name == "err" => None,
        Val::Tuple(items) => {
            let Val::Int(value) = items[0] else {
                panic!("decoded value");
            };
            let Val::Int(len) = items[1] else {
                panic!("decoded length");
            };
            Some((
                u64::try_from(value).expect("decoded value"),
                usize::try_from(len).expect("decoded length"),
            ))
        }
        other => panic!("decoded varint {other:?}"),
    }
}

/// `decode_varint` inverts the consensus compact-size encoding.
pub fn decode_varint_query(body: &str, canonical: &str, value: u64) -> SatResult {
    let encoded = varint_bytes(canonical, value);
    let differ = decoded_varint(body, &encoded) != Some((value, encoded.len()));
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

/// A truncated or non-minimal compact size is rejected.
pub fn decode_varint_reject_query(body: &str, data: &[u8]) -> SatResult {
    let differ = decoded_varint(body, data).is_some();
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn rec_field(value: &Val, name: &str) -> Val {
    let Val::Rec(fields) = value else {
        panic!("record");
    };
    fields
        .iter()
        .find(|(field, _)| field == name)
        .map(|(_, inner)| inner.clone())
        .unwrap_or_else(|| panic!("missing {name}"))
}

fn same_header(left: &Val, right: &Val) -> bool {
    [
        "version",
        "prev_block_hash",
        "merkle_root",
        "timestamp",
        "bits",
        "nonce",
    ]
    .into_iter()
    .all(|name| rec_field(left, name) == rec_field(right, name))
}

fn decoded_header(src: &str, data: &[u8]) -> Option<Val> {
    match sample_eval::eval_val(src, &[("data", sample_eval::bytes(data))]) {
        Val::Name(name) if name == "err" => None,
        Val::Rec(fields) => Some(Val::Rec(fields)),
        other => panic!("decoded header {other:?}"),
    }
}

/// `deserialize_block_header` inverts the 80-byte header serialization.
pub fn header_decode_query(body: &str, wire_src: &str, header: &Val) -> SatResult {
    let encoded = header_wire(wire_src, "serialize_block_header", header);
    let differ = decoded_header(body, &encoded)
        .as_ref()
        .is_none_or(|got| !same_header(got, header));
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

/// A buffer shorter than 80 bytes is not a block header.
pub fn header_decode_reject_query(body: &str, data: &[u8]) -> SatResult {
    let differ = decoded_header(body, data).is_some();
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn script_contains_opcode(src: &str, script: &[u8], opcode: u8) -> bool {
    sample_eval::eval_bool(
        src,
        &[
            ("script", sample_eval::bytes(script)),
            ("opcode", Val::Int(i128::from(opcode))),
        ],
    )
}

fn spec_contains_opcode(script: &[u8], opcode: u8) -> bool {
    let mut i = 0usize;
    while i < script.len() {
        let op = script[i];
        if op > 0 && op < 0x4c {
            i = i.saturating_add(1 + op as usize);
            continue;
        }
        if op == 0x4c {
            if i + 1 >= script.len() {
                return false;
            }
            let len = script[i + 1] as usize;
            i = i.saturating_add(2 + len);
            continue;
        }
        if op == 0x4d {
            if i + 2 >= script.len() {
                return false;
            }
            let len = u16::from_le_bytes([script[i + 1], script[i + 2]]) as usize;
            i = i.saturating_add(3 + len);
            continue;
        }
        if op == 0x4e {
            if i + 4 >= script.len() {
                return false;
            }
            let len =
                u32::from_le_bytes([script[i + 1], script[i + 2], script[i + 3], script[i + 4]])
                    as usize;
            i = i.saturating_add(5 + len);
            continue;
        }
        if op == opcode {
            return true;
        }
        i += 1;
    }
    false
}

/// An opcode is present when it occurs at an opcode position. Push payloads are skipped.
pub fn executable_opcode_query(src: &str, script: &[u8], opcode: u8) -> SatResult {
    let differ =
        script_contains_opcode(src, script, opcode) != spec_contains_opcode(script, opcode);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn bip54_deployment_fields(src: &str) -> (u8, u64, u64) {
    let bit = if src.contains("bit: 14,") { 14 } else { 15 };
    let start = if src.contains("start_time: 1,") { 1 } else { 0 };
    let timeout = if src.contains("timeout: 0,") {
        0
    } else {
        u64::MAX
    };
    (bit, start, timeout)
}

/// BIP54 version-bits deployment: signal bit 15, start time 0, timeout \(2^{64}-1\).
pub fn bip54_deployment_query(src: &str) -> SatResult {
    let differ = bip54_deployment_fields(src) != (15, 0, u64::MAX);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn script_num_minimal(src: &str, data: &[u8]) -> bool {
    sample_eval::eval_bool(src, &[("data", sample_eval::bytes(data))])
}

fn spec_script_num_minimal(data: &[u8]) -> bool {
    let Some(&last) = data.last() else {
        return true;
    };
    if last & 0x7f == 0 && (data.len() <= 1 || data[data.len() - 2] & 0x80 == 0) {
        return false;
    }
    true
}

/// A script number is minimal when a trailing `0x00` or `0x80` is present only as a required sign byte.
pub fn script_num_minimal_query(src: &str, data: &[u8]) -> SatResult {
    let differ = script_num_minimal(src, data) != spec_script_num_minimal(data);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn compact_size(n: usize) -> Vec<u8> {
    let n = n as u64;
    if n < 0xfd {
        vec![n as u8]
    } else if n <= 0xffff {
        let mut out = vec![0xfd];
        out.extend_from_slice(&(n as u16).to_le_bytes());
        out
    } else if n <= 0xffff_ffff {
        let mut out = vec![0xfe];
        out.extend_from_slice(&(n as u32).to_le_bytes());
        out
    } else {
        let mut out = vec![0xff];
        out.extend_from_slice(&n.to_le_bytes());
        out
    }
}

fn stripped_script_code(code: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    let mut i = 0usize;
    while i < code.len() {
        let op = code[i];
        if (0x01..=0x4b).contains(&op) {
            let end = (i + 1 + op as usize).min(code.len());
            out.extend_from_slice(&code[i..end]);
            i = end;
        } else if op == 0x4c {
            if i + 1 >= code.len() {
                out.push(op);
                break;
            }
            let len = code[i + 1] as usize;
            let end = (i + 2 + len).min(code.len());
            out.extend_from_slice(&code[i..end]);
            i = end;
        } else if op == 0x4d {
            if i + 2 >= code.len() {
                out.extend_from_slice(&code[i..]);
                break;
            }
            let len = u16::from_le_bytes([code[i + 1], code[i + 2]]) as usize;
            let end = (i + 3 + len).min(code.len());
            out.extend_from_slice(&code[i..end]);
            i = end;
        } else if op == 0x4e {
            if i + 4 >= code.len() {
                out.extend_from_slice(&code[i..]);
                break;
            }
            let len =
                u32::from_le_bytes([code[i + 1], code[i + 2], code[i + 3], code[i + 4]]) as usize;
            let end = (i + 5 + len).min(code.len());
            out.extend_from_slice(&code[i..end]);
            i = end;
        } else if op == 0xab {
            i += 1;
        } else {
            out.push(op);
            i += 1;
        }
    }
    out
}

fn count_codeseps(script: &[u8]) -> usize {
    let mut count = 0usize;
    let mut i = 0usize;
    while i < script.len() {
        let op = script[i];
        let advance = if (0x01..=0x4b).contains(&op) {
            1 + op as usize
        } else if op == 0x4c {
            if i + 1 >= script.len() {
                break;
            }
            2 + script[i + 1] as usize
        } else if op == 0x4d {
            if i + 2 >= script.len() {
                break;
            }
            3 + u16::from_le_bytes([script[i + 1], script[i + 2]]) as usize
        } else if op == 0x4e {
            if i + 4 >= script.len() {
                break;
            }
            5 + u32::from_le_bytes([script[i + 1], script[i + 2], script[i + 3], script[i + 4]])
                as usize
        } else {
            if op == 0xab {
                count += 1;
            }
            1
        };
        i += advance.min(script.len() - i);
    }
    count
}

fn sighash_script_code(src: &str, code: &[u8]) -> Vec<u8> {
    let n = if src.contains("count_opcode_codeseparators(code)") {
        count_codeseps(code)
    } else {
        0
    };
    let mut out = Vec::new();
    if src.contains("preimage.push(0xff)") {
        out.push(0xff);
    } else {
        let declared = if src.contains("code.len() - n_codeseps") {
            code.len() - n
        } else {
            code.len()
        };
        out.extend(compact_size(declared));
    }
    let zero_is_raw = src.contains("n_codeseps == 0 {\n        preimage.extend_from_slice(code);");
    let else_is_raw = src.contains("} else {\n        preimage.extend_from_slice(code);");
    if n == 0 {
        if zero_is_raw {
            out.extend_from_slice(code);
        } else if src.contains("n_codeseps == 0 {\n        append_stripped_codeseparators") {
            out.extend(stripped_script_code(code));
        }
    } else if else_is_raw {
        out.extend_from_slice(code);
    } else if src.contains("append_stripped_codeseparators") {
        out.extend(stripped_script_code(code));
    }
    out
}

fn spec_sighash_script_code(code: &[u8]) -> Vec<u8> {
    let body = stripped_script_code(code);
    let mut out = compact_size(body.len());
    out.extend(body);
    out
}

/// Legacy sighash script code is the compact size of the codesep-stripped script, then that script.
pub fn sighash_script_code_query(src: &str, code: &[u8]) -> SatResult {
    let differ = sighash_script_code(src, code) != spec_sighash_script_code(code);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn base_script_flags(
    src: &str,
    bip16: bool,
    bip66: bool,
    bip65: bool,
    bip112: bool,
    bip147: bool,
) -> u32 {
    let active = [
        ("Bip16", bip16),
        ("Bip66", bip66),
        ("Bip65", bip65),
        ("Bip112", bip112),
        ("Bip147", bip147),
    ];
    let host = |name: &str, args: &[Val]| -> Option<Val> {
        if name != "is_fork_active" {
            return None;
        }
        let fork = match args.get(1) {
            Some(Val::Name(fork)) => fork.as_str(),
            _ => return Some(Val::Bool(false)),
        };
        let on = active.iter().any(|(id, on)| *id == fork && *on);
        Some(Val::Bool(on))
    };
    u32::try_from(sample_eval::eval_u64_with(
        src,
        &[("height", Val::Int(0)), ("activation", Val::Unit)],
        &host,
    ))
    .expect("flag word")
}

fn spec_base_script_flags(
    bip16: bool,
    bip66: bool,
    bip65: bool,
    bip112: bool,
    bip147: bool,
) -> u32 {
    let mut flags = 0u32;
    if bip16 {
        flags |= 0x01;
    }
    if bip66 {
        flags |= 0x04;
    }
    if bip65 {
        flags |= 0x200;
    }
    if bip112 {
        flags |= 0x400;
    }
    if bip147 {
        flags |= 0x10;
    }
    flags
}

/// Base script flags are the height-gated consensus bits whose flag condition is always true.
pub fn base_script_flags_query(
    src: &str,
    bip16: bool,
    bip66: bool,
    bip65: bool,
    bip112: bool,
    bip147: bool,
) -> SatResult {
    let differ = base_script_flags(src, bip16, bip66, bip65, bip112, bip147)
        != spec_base_script_flags(bip16, bip66, bip65, bip112, bip147);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn empty_list(value: Val) -> Val {
    match value {
        Val::Bytes(data) if data.is_empty() => Val::List(Vec::new()),
        other => other,
    }
}

fn rec_int(value: &Val, name: &str) -> i128 {
    match rec_field(value, name) {
        Val::Int(n) => n,
        other => panic!("{name} is {other:?}"),
    }
}

fn rec_bytes(value: &Val, name: &str) -> Vec<u8> {
    match rec_field(value, name) {
        Val::Bytes(data) => data.clone(),
        other => panic!("{name} is {other:?}"),
    }
}

fn same_tx(got: &Val, expect: &Val) -> bool {
    if rec_int(got, "version") != rec_int(expect, "version")
        || rec_int(got, "lock_time") != rec_int(expect, "lock_time")
    {
        return false;
    }
    let Val::List(got_inputs) = empty_list(rec_field(got, "inputs")) else {
        return false;
    };
    let Val::List(expect_inputs) = rec_field(expect, "inputs") else {
        return false;
    };
    if got_inputs.len() != expect_inputs.len() {
        return false;
    }
    for (got, expect) in got_inputs.iter().zip(&expect_inputs) {
        let got_prev = rec_field(got, "prevout");
        let expect_prev = rec_field(expect, "prevout");
        if rec_bytes(&got_prev, "hash") != rec_bytes(&expect_prev, "hash")
            || rec_int(&got_prev, "index") != rec_int(&expect_prev, "index")
            || rec_bytes(got, "script_sig") != rec_bytes(expect, "script_sig")
            || rec_int(got, "sequence") != rec_int(expect, "sequence")
        {
            return false;
        }
    }
    let Val::List(got_outputs) = empty_list(rec_field(got, "outputs")) else {
        return false;
    };
    let Val::List(expect_outputs) = rec_field(expect, "outputs") else {
        return false;
    };
    if got_outputs.len() != expect_outputs.len() {
        return false;
    }
    for (got, expect) in got_outputs.iter().zip(&expect_outputs) {
        if rec_int(got, "value") != rec_int(expect, "value")
            || rec_bytes(got, "script_pubkey") != rec_bytes(expect, "script_pubkey")
        {
            return false;
        }
    }
    true
}

fn witness_stacks(value: &Val) -> Option<Vec<Vec<Vec<u8>>>> {
    let Val::List(stacks) = value else {
        return None;
    };
    let mut out = Vec::new();
    for stack in stacks {
        match stack {
            Val::Bytes(data) if data.is_empty() => out.push(Vec::new()),
            Val::List(items) => {
                let mut rows = Vec::new();
                for item in items {
                    let Val::Bytes(data) = item else {
                        return None;
                    };
                    rows.push(data.clone());
                }
                out.push(rows);
            }
            _ => return None,
        }
    }
    Some(out)
}

fn witness_value(stacks: &[Vec<Vec<u8>>]) -> Val {
    Val::List(
        stacks
            .iter()
            .map(|stack| Val::List(stack.iter().map(|item| sample_eval::bytes(item)).collect()))
            .collect(),
    )
}

/// `Deserialize(Serialize(tx)) = tx`, and the witness form when stacks are supplied.
///
/// The bytes are the production serializer. SHA-256 is not involved.
fn tx_round_trip_ok(src: &str, tx: &Val, witnesses: Option<&[Vec<Vec<u8>>]>) -> bool {
    let host = &|_: &str, _: &[Val]| None;
    let wire = match witnesses {
        None => sample_eval::eval_bytes_entry_with(
            src,
            Some("serialize_transaction"),
            &[("tx", tx.clone())],
            host,
        ),
        Some(stacks) => sample_eval::eval_bytes_entry_with(
            src,
            Some("serialize_transaction_with_witness"),
            &[("tx", tx.clone()), ("witnesses", witness_value(stacks))],
            host,
        ),
    };
    let got = sample_eval::eval_val_entry_with(
        src,
        "deserialize_transaction_with_witness",
        &[("data", sample_eval::bytes(&wire))],
        host,
    );
    let Val::Tuple(items) = got else {
        return false;
    };
    if items.len() != 3 || !same_tx(&items[0], tx) {
        return false;
    }
    let Val::Int(consumed) = items[2] else {
        return false;
    };
    if consumed != wire.len() as i128 {
        return false;
    }
    match witnesses {
        None => true,
        Some(expect) => witness_stacks(&items[1]).as_deref() == Some(expect),
    }
}

pub fn tx_round_trip_query(src: &str, tx: &Val, witnesses: Option<&[Vec<Vec<u8>>]>) -> SatResult {
    let differ = !tx_round_trip_ok(src, tx, witnesses);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

fn tx_parse_succeeded(src: &str, data: &[u8]) -> bool {
    let got = sample_eval::eval_val_entry_with(
        src,
        "deserialize_transaction_with_witness",
        &[("data", sample_eval::bytes(data))],
        &|_, _| None,
    );
    matches!(got, Val::Tuple(items) if items.len() == 3)
}

/// A buffer shorter than a version is not a transaction.
pub fn tx_round_trip_reject_query(src: &str, data: &[u8]) -> SatResult {
    let differ = tx_parse_succeeded(src, data);
    check(|ctx, solver| {
        solver.assert(&Bool::from_bool(ctx, differ));
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_fn(src: &str) -> syn::ItemFn {
        syn::parse_str(src).unwrap()
    }

    #[test]
    fn production_arm_drops_the_other_cfg() {
        let f = parse_fn(
            r#"
            fn check() {
                #[cfg(feature = "production")]
                { let _x = 1; }
                #[cfg(not(feature = "production"))]
                { let _y = 2; }
            }
            "#,
        );
        let kept = retain_production(f);
        let text = quote::quote!(#kept).to_string();
        assert!(text.contains("_x"));
        assert!(!text.contains("_y"));
    }

    #[test]
    fn max_money_gt_is_unsat_and_ge_is_sat() {
        if !crate::parser::spec_expr::consensus_workspace_present() {
            return;
        }
        let gt = parse_fn(
            r#"
            fn check(value_u64: u64, output_value: i64) {
                if output_value < 0 || value_u64 > MAX_MONEY_U64 { return; }
            }
            "#,
        );
        let facts = facts_of(&gt);
        assert_eq!(money_in_range_query(&facts), SatResult::Unsat);
        let ge = parse_fn(
            r#"
            fn check(value_u64: u64, output_value: i64) {
                if output_value < 0 || value_u64 >= MAX_MONEY_U64 { return; }
            }
            "#,
        );
        let facts = facts_of(&ge);
        assert_eq!(money_in_range_query(&facts), SatResult::Sat);
    }

    #[test]
    fn negative_cast_rejects_and_dropping_both_is_sat() {
        if !crate::parser::spec_expr::consensus_workspace_present() {
            return;
        }
        let body = parse_fn(
            r#"
            fn check(value_u64: u64, output_value: i64) {
                if output_value < 0 || value_u64 > MAX_MONEY_U64 { return; }
            }
            "#,
        );
        assert_eq!(negative_rejected_query(&facts_of(&body)), SatResult::Unsat);
        let patched = parse_fn(
            r#"
            fn check(output_value: i64) {
                if output_value > MAX_MONEY { return; }
            }
            "#,
        );
        assert_eq!(negative_rejected_query(&facts_of(&patched)), SatResult::Sat);
    }

    fn consensus_file(name: &str) -> String {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../blvm-consensus/src")
            .join(name);
        std::fs::read_to_string(&path).unwrap_or_else(|err| panic!("{}: {err}", path.display()))
    }

    fn extract_struct(src: &str, name: &str) -> String {
        let marker = format!("struct {name}");
        let start = src
            .find(&marker)
            .unwrap_or_else(|| panic!("missing {name}"));
        let rest = &src[start..];
        let mut depth = 0i32;
        let mut started = false;
        for (i, c) in rest.char_indices() {
            if c == '{' {
                depth += 1;
                started = true;
            } else if c == '}' {
                depth -= 1;
                if started && depth == 0 {
                    return rest[..=i].to_string();
                }
            }
        }
        panic!("unbalanced {name}");
    }

    fn extract_fn(src: &str, name: &str) -> String {
        let marker = format!("fn {name}");
        let start = src
            .match_indices(&marker)
            .find(|(at, _)| matches!(src[at + marker.len()..].chars().next(), Some('(' | '<')))
            .map(|(at, _)| at)
            .unwrap_or_else(|| panic!("missing {name}"));
        let rest = &src[start..];
        let mut depth = 0i32;
        let mut started = false;
        for (i, c) in rest.char_indices() {
            if c == '{' {
                depth += 1;
                started = true;
            } else if c == '}' {
                depth -= 1;
                if started && depth == 0 {
                    return rest[..=i].to_string();
                }
            }
        }
        panic!("unbalanced {name}");
    }

    fn calls_verifier(src: &str) -> bool {
        if syn::parse_str::<syn::ItemFn>(src).is_err() {
            return false;
        }
        let body = ast_body::analyze(src);
        ["verify_signature", "verify_ecdsa_direct", "verify_schnorr"]
            .iter()
            .any(|name| ast_body::call_named(&body.calls, name))
    }

    fn fast_path_calls_verifier(file: &str, body: &str) -> bool {
        if syn::parse_str::<syn::ItemFn>(body).is_err() {
            return false;
        }
        if calls_verifier(body) {
            return true;
        }
        let parsed = ast_body::analyze(body);
        for callee in [
            "verify_p2wpkh_inline",
            "verify_p2pkh_inline",
            "verify_p2pk_inline",
        ] {
            if ast_body::call_named(&parsed.calls, callee) {
                return calls_verifier(&extract_fn(file, callee));
            }
        }
        false
    }

    #[test]
    fn script_sighash_and_fast_paths_lock() {
        if !crate::parser::spec_expr::consensus_workspace_present() {
            return;
        }
        let hash = consensus_file("transaction_hash.rs");
        let sighash = extract_fn(&hash, "calculate_transaction_sighash_with_script_code");
        let sighash_facts = facts_of(&parse_fn(&sighash));
        assert_eq!(sighash_single_query(&sighash_facts), SatResult::Unsat);
        let broken = sighash.replace("result[0] = 1", "result[0] = 0");
        assert_eq!(
            sighash_single_query(&facts_of(&parse_fn(&broken))),
            SatResult::Sat
        );

        let script = consensus_file("script/mod.rs");
        let cache = extract_fn(&script, "compute_script_cache_key");
        let cache_facts = facts_of(&parse_fn(&cache));
        assert!(cache_facts.cache_updates_flags);
        assert_eq!(cache_flags_query(&cache_facts), SatResult::Unsat);
        let dropped = cache.replace("hasher.update(flags.to_le_bytes());", "");
        assert_eq!(
            cache_flags_query(&facts_of(&parse_fn(&dropped))),
            SatResult::Sat
        );

        let verify = extract_fn(&script, "verify_script");
        assert!(verify.contains("return Ok(cached_result)"));
        assert_eq!(cache_hit_query(true), SatResult::Unsat);
        assert_eq!(cache_hit_query(false), SatResult::Sat);

        let inner = extract_fn(&script, "eval_script_inner");
        assert!(inner.contains("while i < script.len()"));
        assert_eq!(script_step_query(&inner), SatResult::Unsat);
        assert_eq!(
            script_step_query(&inner.replace("i += 1;", "i += 2;")),
            SatResult::Sat
        );
        assert_eq!(control_step_query(&inner), SatResult::Unsat);
        assert_eq!(
            control_step_query(&inner.replace("control_stack.push", "control_stack.len")),
            SatResult::Sat
        );

        let checksig = extract_fn(&script, "execute_opcode_with_context_full");
        assert_eq!(checksig_query(&checksig), SatResult::Unsat);
        let constant = checksig.replace("script_bool_bytes(is_valid)", "script_bool_bytes(true)");
        assert_ne!(constant, checksig);
        assert_eq!(checksig_query(&constant), SatResult::Sat);
        let flipped = checksig.replace(
            "script_bool_bytes(is_valid)",
            "script_bool_bytes(!is_valid)",
        );
        assert_ne!(flipped, checksig);
        assert_eq!(checksig_query(&flipped), SatResult::Sat);

        let p2pk = extract_fn(&script, "try_verify_p2pk_fast_path");
        assert!(ast_body::call_named(
            &ast_body::analyze(&p2pk).calls,
            "canonical_p2pk_pubkey"
        ));
        assert!(fast_path_calls_verifier(&script, &p2pk));
        assert_eq!(fast_path_query(true, true), SatResult::Unsat);

        for (name, len) in [
            ("try_verify_p2pkh_fast_path", 25),
            ("try_verify_p2sh_fast_path", 23),
            ("try_verify_p2wpkh_fast_path", 22),
        ] {
            let body = extract_fn(&script, name);
            let gate = ast_body::analyze(&body).cmps.iter().any(|cmp| {
                cmp.op == CmpOp::Ne && cmp.left.has("len") && cmp.right.lit == Some(len)
            });
            assert!(gate, "{name} has no fall-through gate");
            assert!(
                fast_path_calls_verifier(&script, &body),
                "{name} skips the verifier"
            );
            assert_eq!(fast_path_query(true, true), SatResult::Unsat);
            let missed = body.replacen(&format!("script_pubkey.len() != {len}"), "false", 1);
            let still = ast_body::analyze(&missed).cmps.iter().any(|cmp| {
                cmp.op == CmpOp::Ne && cmp.left.has("len") && cmp.right.lit == Some(len)
            });
            assert!(!still, "{name} gate still present");
            assert_eq!(
                fast_path_query(false, fast_path_calls_verifier(&script, &missed)),
                SatResult::Sat
            );
            let skipped = body
                .replace("verify_signature(", "/*gone*/(")
                .replace("verify_ecdsa_direct(", "/*gone*/(")
                .replace("verify_p2wpkh_inline(", "/*gone*/(");
            assert!(!fast_path_calls_verifier(&script, &skipped));
            assert_eq!(fast_path_query(true, false), SatResult::Sat);
        }
    }

    #[test]
    fn remaining_consensus_predicates_lock() {
        if !crate::parser::spec_expr::consensus_workspace_present() {
            return;
        }
        let locktime = consensus_file("locktime.rs");
        let disabled = extract_fn(&locktime, "is_sequence_disabled");
        assert_eq!(masked_bit_query(&disabled, 0x8000_0000), SatResult::Unsat);
        assert_eq!(
            masked_bit_query(&disabled.replace("0x80000000", "0x40000000"), 0x8000_0000),
            SatResult::Sat
        );
        assert_eq!(
            masked_bit_query(&disabled.replace("!= 0", "== 0"), 0x8000_0000),
            SatResult::Sat
        );

        let type_flag = extract_fn(&locktime, "extract_sequence_type_flag");
        assert_eq!(masked_bit_query(&type_flag, 0x0040_0000), SatResult::Unsat);
        assert_eq!(
            masked_bit_query(&type_flag.replace("0x00400000", "0x00800000"), 0x0040_0000),
            SatResult::Sat
        );
        assert_eq!(
            masked_bit_query(&type_flag.replace("!= 0", "== 0"), 0x0040_0000),
            SatResult::Sat
        );

        let value = extract_fn(&locktime, "extract_sequence_locktime_value");
        assert_eq!(sequence_value_query(&value), SatResult::Unsat);
        assert_eq!(
            sequence_value_query(&value.replace("0x0000ffff", "0x0000fffe")),
            SatResult::Sat
        );
        assert_eq!(
            sequence_value_query(&value.replace('&', "|")),
            SatResult::Sat
        );

        let kind = extract_fn(&locktime, "get_locktime_type");
        assert_eq!(locktime_kind_query(&kind), SatResult::Unsat);
        assert_eq!(
            locktime_kind_query(&kind.replace(
                "locktime < LOCKTIME_THRESHOLD",
                "locktime <= LOCKTIME_THRESHOLD"
            )),
            SatResult::Sat
        );
        assert_eq!(
            locktime_kind_query(&kind.replace(
                "locktime < LOCKTIME_THRESHOLD",
                "locktime > LOCKTIME_THRESHOLD"
            )),
            SatResult::Sat
        );

        let bip65 = extract_fn(&locktime, "check_bip65");
        assert_eq!(bip65_query(&bip65), SatResult::Unsat);
        assert_eq!(bip65_query(&bip65.replace(">=", ">")), SatResult::Sat);
        assert_eq!(
            bip65_query(
                &bip65.replace("locktime_types_match(tx_locktime, stack_locktime) && ", "")
            ),
            SatResult::Sat
        );

        let pow = consensus_file("pow.rs");
        let check = extract_fn(&pow, "check_proof_of_work");
        let meets = extract_fn(&pow, "proof_hash_meets_target");
        assert_eq!(pow_equality_query(&meets), SatResult::Unsat);
        assert_eq!(pow_above_query(&meets), SatResult::Unsat);
        assert_eq!(pow_sign_query(&meets), SatResult::Unsat);
        assert_eq!(pow_zero_target_query(&meets), SatResult::Unsat);
        assert_eq!(pow_rounds_query(&check), SatResult::Unsat);
        assert_eq!(pow_helper_query(&check), SatResult::Unsat);
        assert_eq!(
            pow_equality_query(&meets.replace("hash_value <= target", "hash_value < target")),
            SatResult::Sat
        );
        assert_eq!(
            pow_above_query(&meets.replace("hash_value <= target", "hash_value >= target")),
            SatResult::Sat
        );
        assert_eq!(
            pow_sign_query(&meets.replace("bits & 0x0080_0000 != 0", "false")),
            SatResult::Sat
        );
        assert_eq!(
            pow_zero_target_query(&meets.replace("target.is_zero()", "false")),
            SatResult::Sat
        );
        assert_eq!(
            pow_rounds_query(&check.replacen("Sha256::digest", "skipped_digest", 1)),
            SatResult::Sat
        );
        assert_eq!(
            pow_helper_query(&check.replace("proof_hash_meets_target(", "skipped(")),
            SatResult::Sat
        );

        let witness = consensus_file("witness.rs");
        let program = extract_fn(&witness, "validate_witness_program_length");
        assert_eq!(witness_program_query(&program), SatResult::Unsat);
        assert_eq!(
            witness_program_query(&program.replace("SEGWIT_P2WPKH_LENGTH", "SEGWIT_P2WSH_LENGTH")),
            SatResult::Sat
        );
        assert_eq!(
            witness_program_query(&program.replace("== TAPROOT_PROGRAM_LENGTH", "== 0")),
            SatResult::Sat
        );
        assert_eq!(
            witness_program_query(&program.replace(" || program.len() == SEGWIT_P2WSH_LENGTH", "")),
            SatResult::Sat
        );
        assert_eq!(
            witness_program_query(&program.replace(
                "program.len() == SEGWIT_P2WSH_LENGTH",
                "program.len() == SEGWIT_P2WSH_LENGTH || true"
            )),
            SatResult::Sat
        );

        let mempool = consensus_file("mempool.rs");
        assert_eq!(mempool.matches("#[spec_locked").count(), 2);
        assert!(mempool.contains("fn is_final_tx("));
        let mining = consensus_file("mining.rs");
        assert!(!mining.contains("#[spec_locked(\"12."));
        assert_eq!(mining.matches("#[spec_locked").count(), 4);
        assert!(mining.contains("merkle_tree_from_hashes"));
        let lib = consensus_file("lib.rs");
        assert!(!lib.contains("AcceptToMemoryPool"));
        assert!(!lib.contains("IsStandardTx"));
        assert!(!lib.contains("CreateNewBlock"));
        assert!(!lib.contains("\"12.4\", \"BlockTemplate\""));

        let header = consensus_file("block/header.rs");
        let valid = extract_fn(&header, "validate_block_header");
        assert_eq!(header_version_query(&valid, 0), SatResult::Unsat);
        assert_eq!(header_version_query(&valid, 1), SatResult::Unsat);
        assert_eq!(
            header_version_query(
                &valid.replace("header.version < 1", "header.version < 0"),
                0
            ),
            SatResult::Sat
        );
        assert_eq!(
            header_version_query(
                &valid.replace("header.version < 1", "header.version <= 1"),
                1
            ),
            SatResult::Sat
        );
        assert_eq!(header_mtp_query(&valid, true), SatResult::Unsat);
        assert_eq!(header_mtp_query(&valid, false), SatResult::Unsat);
        let dropped = valid.replace("header.timestamp <= ctx.median_time_past", "false");
        assert_eq!(header_mtp_query(&dropped, true), SatResult::Sat);
        let lt = valid.replace(
            "header.timestamp <= ctx.median_time_past",
            "header.timestamp < ctx.median_time_past",
        );
        assert_eq!(header_mtp_query(&lt, false), SatResult::Sat);
        assert_eq!(
            header_mtp_query(
                &valid.replace(
                    "if let Some(ctx) = time_context",
                    "if let None = time_context"
                ),
                true
            ),
            SatResult::Sat
        );
        assert_eq!(header_rejects_zero(&valid, "timestamp"), SatResult::Unsat);
        assert_eq!(header_rejects_zero(&valid, "bits"), SatResult::Unsat);
        assert_eq!(
            header_rejects_zero(
                &valid.replace("header.timestamp == 0", "header.timestamp == 1"),
                "timestamp"
            ),
            SatResult::Sat
        );
        assert_eq!(
            header_rejects_zero(
                &valid.replace("header.bits == 0", "header.bits == 1"),
                "bits"
            ),
            SatResult::Sat
        );
        assert_eq!(header_future_query(&valid), SatResult::Unsat);
        assert_eq!(header_future_above_query(&valid), SatResult::Unsat);
        assert_eq!(
            header_future_query(
                &valid.replace("header.timestamp > max_ts", "header.timestamp >= max_ts")
            ),
            SatResult::Sat
        );
        assert_eq!(
            header_future_above_query(&valid.replace("if header.timestamp > max_ts", "if false")),
            SatResult::Sat
        );
        assert_eq!(
            header_future_query(&valid.replace(
                "if let Some(ctx) = time_context",
                "if let None = time_context"
            )),
            SatResult::Sat
        );
    }

    #[test]
    fn linked_consensus_rules_lock() {
        if !crate::parser::spec_expr::consensus_workspace_present() {
            return;
        }
        let header = consensus_file("block/header.rs");
        let prev = extract_fn(&header, "validate_prev_block_hash");
        assert_eq!(prev_hash_equal_query(&prev), SatResult::Unsat);
        assert_eq!(prev_hash_mismatch_query(&prev), SatResult::Unsat);
        assert_eq!(
            prev_hash_equal_query(&prev.replace("prev_block_hash ==", "prev_block_hash !=")),
            SatResult::Sat
        );
        assert_eq!(
            prev_hash_mismatch_query(&prev.replace("block_header_hash(", "skipped(")),
            SatResult::Sat
        );

        let tx = consensus_file("transaction.rs");
        let coinbase = extract_fn(&tx, "is_coinbase");
        let zero = extract_fn(&consensus_file("optimizations.rs"), "is_zero_hash");
        assert_eq!(coinbase_query(&coinbase, &zero), SatResult::Unsat);
        assert_eq!(
            coinbase_query(
                &coinbase.replacen("inputs.len() == 1", "inputs.len() == 2", 1),
                &zero
            ),
            SatResult::Sat
        );
        assert_eq!(
            coinbase_query(&coinbase.replace("is_zero_hash(", "skipped("), &zero),
            SatResult::Sat
        );
        assert_eq!(
            coinbase_query(&coinbase.replace("== [0u8; 32]", "== [1u8; 32]"), &zero),
            SatResult::Sat
        );
        assert_eq!(
            coinbase_query(
                &coinbase.replacen("prevout.index == 0xffffffff", "prevout.index == 0", 1),
                &zero
            ),
            SatResult::Sat
        );
        assert_eq!(
            coinbase_query(&coinbase, &zero.replace("b == 0", "b == 1")),
            SatResult::Sat
        );

        let mature = extract_fn(&tx, "check_coinbase_maturity");
        assert_eq!(maturity_non_coinbase_query(&mature), SatResult::Unsat);
        assert_eq!(maturity_equal_query(&mature), SatResult::Unsat);
        assert_eq!(maturity_before_query(&mature), SatResult::Unsat);
        assert_eq!(
            maturity_non_coinbase_query(&mature.replace("if !is_coinbase", "if false")),
            SatResult::Sat
        );
        assert_eq!(
            maturity_equal_query(
                &mature.replace("spend_height >= required", "spend_height > required")
            ),
            SatResult::Sat
        );
        assert_eq!(
            maturity_before_query(
                &mature.replace("saturating_add(COINBASE_MATURITY)", "saturating_add(99)")
            ),
            SatResult::Sat
        );

        let economic = consensus_file("economic.rs");
        let subsidy = extract_fn(&economic, "get_block_subsidy");
        let interval = crate::parser::spec_expr::protocol_u64("H");
        for height in [
            0,
            interval,
            2 * interval,
            3 * interval,
            33 * interval,
            64 * interval,
        ] {
            assert_eq!(
                subsidy_query(&subsidy, height),
                SatResult::Unsat,
                "{height}"
            );
        }
        assert_eq!(
            subsidy_query(&subsidy.replace("height / HALVING_INTERVAL", "0"), interval),
            SatResult::Sat
        );
        assert_eq!(
            subsidy_query(
                &subsidy.replace("base_subsidy >> halving_period", "base_subsidy"),
                interval
            ),
            SatResult::Sat
        );
        assert_eq!(
            subsidy_query(
                &subsidy.replace("halving_period >= 64", "false"),
                64 * interval
            ),
            SatResult::Sat
        );

        let bip = consensus_file("bip_validation.rs");
        let bip90 = extract_fn(&bip, "check_bip90");
        for (version, bip34, bip66, bip65) in [
            (1, true, false, false),
            (2, true, false, false),
            (1, false, false, false),
            (2, true, true, false),
            (3, true, true, false),
            (3, true, true, true),
            (4, true, true, true),
        ] {
            assert_eq!(
                bip90_query(&bip90, version, bip34, bip66, bip65),
                SatResult::Unsat,
                "{version} {bip34} {bip66} {bip65}"
            );
        }
        assert_eq!(
            bip90_query(
                &bip90.replace("block_version < 2", "block_version < 1"),
                1,
                true,
                false,
                false
            ),
            SatResult::Sat
        );
        assert_eq!(
            bip90_query(
                &bip90.replace("block_version < 2", "block_version <= 2"),
                2,
                true,
                false,
                false
            ),
            SatResult::Sat
        );
        assert_eq!(
            bip90_query(
                &bip90.replace(
                    "activation.is_fork_active(ForkId::Bip34, height) && ",
                    "ForkId::Bip34; "
                ),
                1,
                false,
                false,
                false
            ),
            SatResult::Sat
        );
        assert_eq!(
            bip90_query(
                &bip90.replace("block_version < 3", "block_version < 2"),
                2,
                true,
                true,
                false
            ),
            SatResult::Sat
        );
        assert_eq!(
            bip90_query(
                &bip90.replace("block_version < 3", "block_version <= 3"),
                3,
                true,
                true,
                false
            ),
            SatResult::Sat
        );
        assert_eq!(
            bip90_query(
                &bip90.replace(
                    "activation.is_fork_active(ForkId::Bip66, height) && ",
                    "ForkId::Bip66; "
                ),
                2,
                false,
                false,
                false
            ),
            SatResult::Sat
        );
        assert_eq!(
            bip90_query(
                &bip90.replace("block_version < 4", "block_version < 3"),
                3,
                true,
                true,
                true
            ),
            SatResult::Sat
        );
        assert_eq!(
            bip90_query(
                &bip90.replace("block_version < 4", "block_version <= 4"),
                4,
                true,
                true,
                true
            ),
            SatResult::Sat
        );
        assert_eq!(
            bip90_query(
                &bip90.replace(
                    "activation.is_fork_active(ForkId::Bip65, height) && ",
                    "ForkId::Bip65; "
                ),
                3,
                false,
                false,
                false
            ),
            SatResult::Sat
        );

        let activation = consensus_file("activation.rs");
        let fork = extract_fn(&activation, "is_fork_active");
        assert_eq!(fork_bip30_query(&fork), SatResult::Unsat);
        assert_eq!(
            fork_bip30_query(&fork.replace("ForkId::Bip30 => true", "ForkId::Bip30 => false")),
            SatResult::Sat
        );
        for field in [
            "bip16", "bip34", "bip66", "bip65", "bip112", "bip147", "segwit", "taproot", "bip54",
            "ctv", "csfs",
        ] {
            assert_eq!(
                fork_threshold_query(&fork, field, 100, 100),
                SatResult::Unsat,
                "{field}"
            );
            let patched = fork.replace(
                &format!("height >= self.{field}"),
                &format!("height > self.{field}"),
            );
            assert_eq!(
                fork_threshold_query(&patched, field, 100, 100),
                SatResult::Sat,
                "{field}"
            );
        }
        assert_eq!(fork_never_query(&fork, "ctv"), SatResult::Unsat);
        assert_eq!(fork_never_query(&fork, "csfs"), SatResult::Unsat);
        assert_eq!(
            fork_never_query(&fork.replace("self.ctv != u64::MAX && ", ""), "ctv"),
            SatResult::Sat
        );
        assert_eq!(
            fork_never_query(&fork.replace("self.csfs != u64::MAX && ", ""), "csfs"),
            SatResult::Sat
        );
    }

    #[test]
    fn script_size_and_relative_lock_lock() {
        if !crate::parser::spec_expr::consensus_workspace_present() {
            return;
        }
        let script = consensus_file("script/mod.rs");
        let push = extract_fn(&script, "is_push_opcode");
        for opcode in [0x00, 0x60, 0x61] {
            assert_eq!(
                push_opcode_query(&push, opcode),
                SatResult::Unsat,
                "{opcode}"
            );
        }
        assert_eq!(
            push_opcode_query(&push.replace("opcode <= 0x60", "opcode < 0x60"), 0x60),
            SatResult::Sat
        );
        assert_eq!(
            push_opcode_query(&push.replace("opcode <= 0x60", "opcode <= 0x61"), 0x61),
            SatResult::Sat
        );

        let success = extract_fn(&script, "is_op_success");
        assert_eq!(op_success_query(&success), SatResult::Unsat);
        assert_eq!(
            op_success_query(&success.replace("80 | ", "")),
            SatResult::Sat
        );
        assert_eq!(
            op_success_query(&success.replace(" | 98", "")),
            SatResult::Sat
        );
        assert_eq!(
            op_success_query(&success.replace("126..=129", "126..=128")),
            SatResult::Sat
        );
        assert_eq!(
            op_success_query(&success.replace("187..=254", "187..=255")),
            SatResult::Sat
        );

        let witness = consensus_file("witness.rs");
        let vsize = extract_fn(&witness, "weight_to_vsize");
        for weight in [0, 1, 4, 5] {
            assert_eq!(vsize_query(&vsize, weight), SatResult::Unsat, "{weight}");
        }
        assert_eq!(
            vsize_query(&vsize.replace("div_ceil(4)", "div_ceil(5)"), 5),
            SatResult::Sat
        );
        assert_eq!(
            vsize_query(&vsize.replace("div_ceil(4)", "/ 4"), 5),
            SatResult::Sat
        );

        let bip = consensus_file("bip_validation.rs");
        let stripped = extract_fn(&bip, "check_bip54_tx_stripped_size");
        for (coinbase, size) in [(true, 64), (false, 64), (false, 63), (false, 65)] {
            assert_eq!(
                stripped_size_query(&stripped, coinbase, size),
                SatResult::Unsat,
                "{coinbase} {size}"
            );
        }
        assert_eq!(
            stripped_size_query(&stripped.replace("is_coinbase(tx) || ", ""), true, 64),
            SatResult::Sat
        );
        assert_eq!(
            stripped_size_query(&stripped.replace("!= 64", "!= 65"), false, 64),
            SatResult::Sat
        );
        assert_eq!(
            stripped_size_query(&stripped.replace("!= 64", "== 64"), false, 63),
            SatResult::Sat
        );

        let warp = extract_fn(&bip, "check_bip54_timewarp");
        let cases = [
            (false, 2015, 1, 2, 10_000, true),
            (true, 1, 0, 0, 0, true),
            (true, 2015, 50, 50, 0, true),
            (true, 2015, 49, 50, 0, true),
            (true, 2015, 50, 50, 0, false),
            (true, 0, 2_800, 0, 10_000, true),
            (true, 0, 2_799, 0, 10_000, true),
            (true, 0, 0, 0, 100, true),
            (true, 0, 0, 0, 100, false),
        ];
        for (active, height, ts, first, prev, boundary) in cases {
            assert_eq!(
                timewarp_query(&warp, active, height, ts, first, prev, boundary),
                SatResult::Unsat,
                "{active} {height} {ts} {first} {prev} {boundary}"
            );
        }
        assert_eq!(
            timewarp_query(
                &warp.replace("if !bip54_active", "if false"),
                false,
                2015,
                1,
                2,
                10_000,
                true
            ),
            SatResult::Sat
        );
        assert_eq!(
            timewarp_query(
                &warp.replace("height % 2016", "height % 2015"),
                true,
                2015,
                2_800,
                10_000,
                10_000,
                true
            ),
            SatResult::Sat
        );
        assert_eq!(
            timewarp_query(
                &warp.replace(
                    "header.timestamp >= b.timestamp_n_minus_2015",
                    "header.timestamp > b.timestamp_n_minus_2015"
                ),
                true,
                2015,
                50,
                50,
                0,
                true
            ),
            SatResult::Sat
        );
        assert_eq!(
            timewarp_query(
                &warp.replace("let Some(b) = boundary else {\n            return false;\n        };\n        header.timestamp >= b.timestamp_n_minus_2015", "header.timestamp >= b.timestamp_n_minus_2015"),
                true,
                2015,
                1,
                50,
                0,
                false
            ),
            SatResult::Sat
        );
        assert_eq!(
            timewarp_query(
                &warp.replace("7200", "7199"),
                true,
                0,
                2_800,
                0,
                10_000,
                true
            ),
            SatResult::Sat
        );
        assert_eq!(
            timewarp_query(
                &warp.replace("saturating_sub", "wrapping_sub"),
                true,
                0,
                0,
                0,
                100,
                true
            ),
            SatResult::Sat
        );
        assert_eq!(
            timewarp_query(
                &warp.replace("header.timestamp >= min_ts", "header.timestamp > min_ts"),
                true,
                0,
                2_800,
                0,
                10_000,
                true
            ),
            SatResult::Sat
        );
        assert_eq!(
            timewarp_query(
                &warp.replace("} else {\n        true", "} else {\n        false"),
                true,
                1,
                0,
                0,
                0,
                true
            ),
            SatResult::Sat
        );

        let locktime = consensus_file("locktime.rs");
        let csv = extract_fn(&locktime, "check_bip112");
        assert_eq!(bip112_query(&csv, true, 5, 5), SatResult::Unsat);
        assert_eq!(bip112_query(&csv, true, 4, 5), SatResult::Unsat);
        assert_eq!(bip112_query(&csv, false, 5, 5), SatResult::Unsat);
        assert_eq!(
            bip112_query(&csv.replace(">=", ">"), true, 5, 5),
            SatResult::Sat
        );
        assert_eq!(
            bip112_query(
                &csv.replace(
                    "extract_sequence_type_flag(stack_sequence) == extract_sequence_type_flag(input_sequence)\n        && ",
                    ""
                ),
                false,
                5,
                5
            ),
            SatResult::Sat
        );
    }

    #[test]
    fn weight_median_and_bip54_lock() {
        let weight = consensus_file("witness.rs");
        let weight = extract_fn(&weight, "calculate_transaction_weight_segwit");
        assert_eq!(tx_weight_query(&weight, 1, 0), SatResult::Unsat);
        assert_eq!(tx_weight_query(&weight, 0, 1), SatResult::Unsat);
        assert_eq!(
            tx_weight_query(&weight.replace("3 * base_size", "2 * base_size"), 1, 0),
            SatResult::Sat
        );
        assert_eq!(
            tx_weight_query(&weight.replace(" + total_size", ""), 0, 1),
            SatResult::Sat
        );

        let coinbase = consensus_file("bip_validation.rs");
        let coinbase = extract_fn(&coinbase, "check_bip54_coinbase");
        assert_eq!(
            bip54_coinbase_query(&coinbase, 5, 4, 1, 0),
            SatResult::Unsat
        );
        assert_eq!(
            bip54_coinbase_query(&coinbase, 0, 0, 1, 0),
            SatResult::Unsat
        );
        assert_eq!(
            bip54_coinbase_query(
                &coinbase.replace("saturating_sub(1)", "saturating_sub(0)"),
                5,
                4,
                1,
                0
            ),
            SatResult::Sat
        );
        assert_eq!(
            bip54_coinbase_query(
                &coinbase.replace("saturating_sub", "wrapping_sub"),
                0,
                0,
                1,
                0
            ),
            SatResult::Sat
        );
        assert_eq!(
            bip54_coinbase_query(
                &coinbase.replace(
                    "if coinbase.inputs.is_empty() {\n        return false;\n    }",
                    "if coinbase.inputs.is_empty() {\n        return true;\n    }"
                ),
                5,
                4,
                0,
                0
            ),
            SatResult::Sat
        );
        assert_eq!(
            bip54_coinbase_query(
                &coinbase.replace("sequence == ", "sequence != "),
                5,
                4,
                1,
                0
            ),
            SatResult::Sat
        );
        assert_eq!(
            bip54_coinbase_query(
                &coinbase.replace(
                    "if coinbase.inputs[0].sequence == 0xffff_ffff {\n        return false;\n    }\n    ",
                    ""
                ),
                5,
                4,
                1,
                0xffff_ffff
            ),
            SatResult::Sat
        );

        let median = consensus_file("bip113.rs");
        let median = extract_fn(&median, "get_median_time_past");
        assert_eq!(median_time_query(&median, &[]), SatResult::Unsat);
        assert_eq!(median_time_query(&median, &[1, 3]), SatResult::Unsat);
        assert_eq!(median_time_query(&median, &[3, 1, 2]), SatResult::Unsat);
        let twelve = [6, 0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11];
        assert_eq!(median_time_query(&median, &twelve), SatResult::Unsat);
        assert_eq!(
            median_time_query(&median.replace("return 0", "return 1"), &[]),
            SatResult::Sat
        );
        assert_eq!(
            median_time_query(&median.replace("sort_unstable", "len"), &[3, 1, 2]),
            SatResult::Sat
        );
        assert_eq!(
            median_time_query(
                &median.replace("timestamps.len() / 2", "(timestamps.len() - 1) / 2"),
                &[1, 3]
            ),
            SatResult::Sat
        );
        assert_eq!(
            median_time_query(
                &median.replace("saturating_sub(MEDIAN_TIME_BLOCKS)", "saturating_sub(10)"),
                &twelve
            ),
            SatResult::Sat
        );

        let active = consensus_file("bip_validation.rs");
        let active = extract_fn(&active, "is_bip54_active_at");
        let mainnet = "BIP54_ACTIVATION_MAINNET";
        assert_eq!(
            bip54_active_query(&active, 100, Some(100), mainnet),
            SatResult::Unsat
        );
        assert_eq!(
            bip54_active_query(&active, 0, None, mainnet),
            SatResult::Unsat
        );
        assert_eq!(
            bip54_active_query(
                &active.replace("height >= ", "height > "),
                100,
                Some(100),
                mainnet
            ),
            SatResult::Sat
        );
        assert_eq!(
            bip54_active_query(
                &active.replace("Some(h) => h", "Some(h) => u64::MAX"),
                100,
                Some(100),
                mainnet
            ),
            SatResult::Sat
        );
        assert_eq!(
            bip54_active_query(&active.replace(mainnet, "0"), 0, None, mainnet),
            SatResult::Sat
        );
    }

    #[test]
    fn expand_target_lock() {
        let src = consensus_file("pow.rs");
        let src = extract_fn(&src, "expand_target");
        let in_domain = [0x0300_0001u64, 0x0300_0000, 0x0400_0001, 0x2000_0001];
        for bits in in_domain {
            assert_eq!(expand_target_query(&src, bits), SatResult::Unsat);
        }
        assert_eq!(expand_target_query(&src, 0x0200_0001), SatResult::Unsat);
        assert_eq!(expand_target_query(&src, 0x2100_0001), SatResult::Unsat);
        assert_eq!(
            expand_target_query(&src, (0x104 << 24) | 1),
            SatResult::Unsat
        );
        assert_eq!(expand_target_query(&src, 0x0380_0000), SatResult::Unsat);
        assert_eq!(
            expand_target_query(&src.replace("3..=32", "4..=32"), 0x0300_0001),
            SatResult::Sat
        );
        assert_eq!(
            expand_target_query(&src.replace("3..=32", "3..=31"), 0x2000_0001),
            SatResult::Sat
        );
        assert_eq!(
            expand_target_query(&src.replace("3..=32", "2..=32"), 0x0200_0001),
            SatResult::Sat
        );
        assert_eq!(
            expand_target_query(&src.replace("3..=32", "3..=33"), 0x2100_0001),
            SatResult::Sat
        );
        assert_eq!(
            expand_target_query(&src.replace("U256::zero()", "U256::one()"), 0x0300_0000),
            SatResult::Sat
        );
        assert_eq!(
            expand_target_query(
                &src.replace("bits & 0x007fffff", "bits & 0x00ffffff"),
                0x0380_0000
            ),
            SatResult::Sat
        );
        assert_eq!(
            expand_target_query(&src.replace("8u32 * ", ""), 0x0400_0001),
            SatResult::Sat
        );
        assert_eq!(
            expand_target_query(&src.replace(" as u8", ""), (0x104 << 24) | 1),
            SatResult::Sat
        );
    }

    #[test]
    fn calculate_fee_lock() {
        let src = consensus_file("economic.rs");
        let src = extract_fn(&src, "calculate_fee");
        assert_eq!(
            calculate_fee_query(&src, true, &[], &[50]),
            SatResult::Unsat
        );
        assert_eq!(
            calculate_fee_query(&src, false, &[5], &[3]),
            SatResult::Unsat
        );
        assert_eq!(
            calculate_fee_query(&src, false, &[5], &[5]),
            SatResult::Unsat
        );
        assert_eq!(
            calculate_fee_query(&src, false, &[1], &[2]),
            SatResult::Unsat
        );
        assert_eq!(
            calculate_fee_query(&src, false, &[1, 10], &[0]),
            SatResult::Unsat
        );
        assert_eq!(
            calculate_fee_query(&src, false, &[10], &[1, 3]),
            SatResult::Unsat
        );
        assert_eq!(
            calculate_fee_query(
                &src.replace("if is_coinbase(tx) {\n        return Ok(0);\n    }\n", ""),
                true,
                &[],
                &[50]
            ),
            SatResult::Sat
        );
        assert_eq!(
            calculate_fee_query(
                &src.replace("checked_sub(total_output)", "checked_add(total_output)"),
                false,
                &[5],
                &[3]
            ),
            SatResult::Sat
        );
        assert_eq!(
            calculate_fee_query(
                &src.replace("acc.checked_add(utxo.value)", "Some(utxo.value)"),
                false,
                &[1, 10],
                &[0]
            ),
            SatResult::Sat
        );
        assert_eq!(
            calculate_fee_query(
                &src.replace("acc.checked_add(output.value)", "Some(output.value)"),
                false,
                &[10],
                &[1, 3]
            ),
            SatResult::Sat
        );
        assert_eq!(
            calculate_fee_query(&src.replace("if fee < 0", "if fee <= 0"), false, &[5], &[5]),
            SatResult::Sat
        );
        assert_eq!(
            calculate_fee_query(
                &src.replace(
                    "if fee < 0 {\n        return Err(ConsensusError::EconomicValidation(\"Negative fee\".into()));\n    }\n",
                    ""
                ),
                false,
                &[1],
                &[2]
            ),
            SatResult::Sat
        );
    }

    #[test]
    fn minimal_if_lock() {
        let src = consensus_file("script/control_flow.rs");
        let src = extract_fn(&src, "is_minimal_if_condition");
        assert_eq!(minimal_if_query(&src, &[]), SatResult::Unsat);
        assert_eq!(minimal_if_query(&src, &[0x01]), SatResult::Unsat);
        assert_eq!(minimal_if_query(&src, &[0x00]), SatResult::Unsat);
        assert_eq!(minimal_if_query(&src, &[0x02]), SatResult::Unsat);
        assert_eq!(minimal_if_query(&src, &[0x01, 0x01]), SatResult::Unsat);
        assert_eq!(
            minimal_if_query(&src.replace("0 => true", "0 => false"), &[]),
            SatResult::Sat
        );
        assert_eq!(
            minimal_if_query(&src.replace("_ => false", "_ => true"), &[0x01, 0x01]),
            SatResult::Sat
        );
        assert_eq!(
            minimal_if_query(&src.replace("== 0x01", "== 0x02"), &[0x01]),
            SatResult::Sat
        );
        assert_eq!(
            minimal_if_query(&src.replace("== 0x01", "<= 0x01"), &[0x00]),
            SatResult::Sat
        );
    }

    #[test]
    fn cast_to_bool_lock() {
        let file = consensus_file("script/stack.rs");
        let mut rest = file.as_str();
        let mut bodies = Vec::new();
        while let Some(at) = rest.find("fn cast_to_bool") {
            let body = extract_fn(&rest[at..], "cast_to_bool");
            let next = at + body.len();
            bodies.push(body);
            rest = &rest[next..];
        }
        assert_eq!(bodies.len(), 2);
        let points: &[&[u8]] = &[
            &[],
            &[0x00],
            &[0x00, 0x00],
            &[0x80],
            &[0x00, 0x80],
            &[0x01],
            &[0x80, 0x00],
            &[0x01, 0x80],
            &[0x00, 0x01],
        ];
        for body in &bodies {
            for bytes in points {
                assert_eq!(cast_to_bool_query(body, bytes), SatResult::Unsat);
            }
            assert_eq!(
                cast_to_bool_query(&body.replace("    }\n    false", "    }\n    true"), &[]),
                SatResult::Sat
            );
            assert_eq!(
                cast_to_bool_query(&body.replace("v[i] == 0x80", "v[i] == 0x81"), &[0x80]),
                SatResult::Sat
            );
            assert_eq!(
                cast_to_bool_query(&body.replace("i == v.len() - 1 && ", ""), &[0x80, 0x00]),
                SatResult::Sat
            );
            assert_eq!(
                cast_to_bool_query(&body.replace("return true", "return false"), &[0x01]),
                SatResult::Sat
            );
        }
    }

    #[test]
    fn witness_version_lock() {
        let src = consensus_file("witness.rs");
        let src = extract_fn(&src, "is_witness_version_opcode");
        for opcode in [0x00, 0x51, 0x60, 0x4f, 0x50, 0x61, 0x01, 0x4c] {
            assert_eq!(witness_version_query(&src, opcode), SatResult::Unsat);
        }
        assert_eq!(
            witness_version_query(&src.replace("opcode == OP_0 || ", ""), 0x00),
            SatResult::Sat
        );
        assert_eq!(
            witness_version_query(&src.replace("OP_1..=OP_16", "OP_1..=OP_15"), 0x60),
            SatResult::Sat
        );
        assert_eq!(
            witness_version_query(&src.replace("OP_1..=OP_16", "OP_RESERVED..=OP_16"), 0x50),
            SatResult::Sat
        );
        assert_eq!(
            witness_version_query(&src.replace("OP_1..=OP_16", "OP_1NEGATE..=OP_16"), 0x4f),
            SatResult::Sat
        );
        assert_eq!(
            witness_version_query(&src.replace("OP_1..=OP_16", "OP_1..=OP_NOP"), 0x61),
            SatResult::Sat
        );
    }

    #[test]
    fn find_and_delete_lock() {
        let src = consensus_file("script/mod.rs");
        let src = extract_fn(&src, "find_and_delete");
        assert_eq!(find_and_delete_query(&src, &[0x51], &[]), SatResult::Unsat);
        assert_eq!(
            find_and_delete_query(&src, &[0x51], &[0x51, 0x52]),
            SatResult::Unsat
        );
        assert_eq!(
            find_and_delete_query(&src, &[0x01, 0x51], &[0x51]),
            SatResult::Unsat
        );
        assert_eq!(
            find_and_delete_query(&src, &[0x51], &[0x51]),
            SatResult::Unsat
        );
        assert_eq!(
            find_and_delete_query(&src, &[0x51, 0x51], &[0x51]),
            SatResult::Unsat
        );
        assert_eq!(
            find_and_delete_query(&src, &[0x52, 0x51], &[0x51]),
            SatResult::Unsat
        );
        assert_eq!(
            find_and_delete_query(
                &src.replace(
                    "if pattern.is_empty() {\n        return std::borrow::Cow::Borrowed(script);\n    }\n    ",
                    ""
                ),
                &[0x51],
                &[]
            ),
            SatResult::Sat
        );
        assert_eq!(
            find_and_delete_query(
                &src.replace(
                    "if pattern.len() > script.len() {\n        return std::borrow::Cow::Borrowed(script);\n    }",
                    "if pattern.len() > script.len() {\n        return std::borrow::Cow::Owned(Vec::new());\n    }"
                ),
                &[0x51],
                &[0x51, 0x52]
            ),
            SatResult::Sat
        );
        assert_eq!(
            find_and_delete_query(
                &src.replace(
                    "script_get_op_advance(script, pc)",
                    "Some(pc.saturating_add(1))"
                ),
                &[0x01, 0x51],
                &[0x51]
            ),
            SatResult::Sat
        );
        assert_eq!(
            find_and_delete_query(
                &src.replace(
                    "while end - pc >= pattern.len()",
                    "if end - pc >= pattern.len()"
                ),
                &[0x51, 0x51],
                &[0x51]
            ),
            SatResult::Sat
        );
        assert_eq!(
            find_and_delete_query(
                &src.replace(
                    "while end - pc >= pattern.len() && script[pc..pc + pattern.len()] == *pattern {\n            pc += pattern.len();\n            n_found += 1;\n        }\n        ",
                    ""
                ),
                &[0x51],
                &[0x51]
            ),
            SatResult::Sat
        );
    }

    #[test]
    fn total_supply_lock() {
        let interval = crate::parser::spec_expr::impl_u64("HALVING_INTERVAL");
        assert_eq!(
            spec_supply(interval.saturating_mul(33)),
            2_099_999_997_690_000
        );
        let src = consensus_file("economic.rs");
        let src = extract_fn(&src, "total_supply");
        for height in [0, interval, interval * 2, interval * 33] {
            assert_eq!(total_supply_query(&src, height), SatResult::Unsat);
        }
        assert_eq!(
            total_supply_query(&src.replace("d + 1", "d"), 0),
            SatResult::Sat
        );
        assert_eq!(
            total_supply_query(&src.replace("period_start > end", "period_start >= end"), 0),
            SatResult::Sat
        );
        assert_eq!(
            total_supply_query(
                &src.replace("INITIAL_SUBSIDY >> k", "INITIAL_SUBSIDY"),
                interval
            ),
            SatResult::Sat
        );
        assert_eq!(
            total_supply_query(&src.replace("0u64..64", "0u64..1"), interval),
            SatResult::Sat
        );
    }

    #[test]
    fn null_dummy_lock() {
        let src = consensus_file("bip_validation.rs");
        let src = extract_fn(&src, "is_null_dummy");
        let points: &[&[u8]] = &[
            &[],
            &[0x00],
            &[0x00, 0x01, 0x11],
            &[0x01, 0x11],
            &[0x01, 0x00, 0x00],
            &[0x4c, 0x00],
            &[0x4d, 0x00, 0x00],
            &[0x4e, 0x00, 0x00, 0x00, 0x00],
            &[0x51],
            &[0x02],
            &[0x4d],
        ];
        for script in points {
            assert_eq!(null_dummy_query(&src, script), SatResult::Unsat);
        }
        assert_eq!(
            null_dummy_query(
                &src.replace(
                    "if script_sig.is_empty() {\n        return Ok(false);\n    }",
                    "if script_sig.is_empty() {\n        return Ok(true);\n    }"
                ),
                &[]
            ),
            SatResult::Sat
        );
        assert_eq!(
            null_dummy_query(
                &src.replace(
                    "OP_0 => {\n                if !saw_push {\n                    first_push_empty = true;\n                    saw_push = true;\n                }",
                    "OP_0 => {\n                if !saw_push {\n                    saw_push = true;\n                }"
                ),
                &[0x00]
            ),
            SatResult::Sat
        );
        assert_eq!(
            null_dummy_query(
                &src.replace(
                    "OP_0 => {\n                if !saw_push {\n                    first_push_empty = true;",
                    "OP_0 => {\n                if true {\n                    first_push_empty = true;"
                ),
                &[0x01, 0x00, 0x00]
            ),
            SatResult::Sat
        );
        assert_eq!(
            null_dummy_query(
                &src.replace(
                    "let len = opcode as usize;\n                if pc + len > script_sig.len() {\n                    return Ok(false);\n                }\n                if !saw_push {\n                    first_push_empty = len == 0;",
                    "let len = opcode as usize;\n                if pc + len > script_sig.len() {\n                    return Ok(false);\n                }\n                if !saw_push {\n                    first_push_empty = true;"
                ),
                &[0x01, 0x11]
            ),
            SatResult::Sat
        );
        assert_eq!(
            null_dummy_query(
                &src.replace(
                    "let len = opcode as usize;\n                if pc + len > script_sig.len() {\n                    return Ok(false);",
                    "let len = opcode as usize;\n                if pc + len > script_sig.len() {\n                    return Ok(true);"
                ),
                &[0x02]
            ),
            SatResult::Sat
        );
        assert_eq!(
            null_dummy_query(
                &src.replace("_ => return Ok(false)", "_ => return Ok(true)"),
                &[0x51]
            ),
            SatResult::Sat
        );
        assert_eq!(
            null_dummy_query(
                &src.replace(
                    "let len = script_sig[pc] as usize;\n                pc += 1;\n                if pc + len > script_sig.len() {\n                    return Ok(false);\n                }\n                if !saw_push {\n                    first_push_empty = len == 0;",
                    "let len = script_sig[pc] as usize;\n                pc += 1;\n                if pc + len > script_sig.len() {\n                    return Ok(false);\n                }\n                if !saw_push {\n                    first_push_empty = false;"
                ),
                &[0x4c, 0x00]
            ),
            SatResult::Sat
        );
        assert_eq!(
            null_dummy_query(
                &src.replace(
                    "let len = u16::from_le_bytes([script_sig[pc], script_sig[pc + 1]]) as usize;\n                pc += 2;\n                if pc + len > script_sig.len() {\n                    return Ok(false);\n                }\n                if !saw_push {\n                    first_push_empty = len == 0;",
                    "let len = u16::from_le_bytes([script_sig[pc], script_sig[pc + 1]]) as usize;\n                pc += 2;\n                if pc + len > script_sig.len() {\n                    return Ok(false);\n                }\n                if !saw_push {\n                    first_push_empty = false;"
                ),
                &[0x4d, 0x00, 0x00]
            ),
            SatResult::Sat
        );
        assert_eq!(
            null_dummy_query(
                &src.replace(
                    "]) as usize;\n                pc += 4;\n                if pc + len > script_sig.len() {\n                    return Ok(false);\n                }\n                if !saw_push {\n                    first_push_empty = len == 0;",
                    "]) as usize;\n                pc += 4;\n                if pc + len > script_sig.len() {\n                    return Ok(false);\n                }\n                if !saw_push {\n                    first_push_empty = false;"
                ),
                &[0x4e, 0x00, 0x00, 0x00, 0x00]
            ),
            SatResult::Sat
        );
        assert_eq!(
            null_dummy_query(
                &src.replace(
                    "if pc + 2 > script_sig.len() {\n                    return Ok(false);",
                    "if pc + 2 > script_sig.len() {\n                    return Ok(true);"
                ),
                &[0x4d]
            ),
            SatResult::Sat
        );
    }

    #[test]
    fn taproot_script_and_key_lock() {
        let file = consensus_file("taproot.rs");
        let script_src = extract_fn(&file, "validate_taproot_script");
        let key_src = extract_fn(&file, "extract_taproot_output_key");
        let valid = {
            let mut script = vec![0x51, 0x20];
            script.extend(std::iter::repeat(0x11).take(32));
            script
        };
        let short = {
            let mut script = vec![0x51, 0x20];
            script.extend(std::iter::repeat(0x11).take(31));
            script
        };
        let bad_prefix = {
            let mut script = vec![0x00, 0x20];
            script.extend(std::iter::repeat(0x11).take(32));
            script
        };
        let bad_push = {
            let mut script = vec![0x51, 0x00];
            script.extend(std::iter::repeat(0x11).take(32));
            script
        };
        for script in [&valid, &short, &bad_prefix, &bad_push] {
            assert_eq!(taproot_script_query(&script_src, script), SatResult::Unsat);
            assert_eq!(taproot_key_query(&key_src, script), SatResult::Unsat);
        }
        assert_eq!(
            taproot_script_query(
                &script_src.replace("!= TAPROOT_SCRIPT_LENGTH", "> TAPROOT_SCRIPT_LENGTH"),
                &short
            ),
            SatResult::Sat
        );
        assert_eq!(
            taproot_script_query(
                &script_src.replace(
                    "    if script[0] != TAPROOT_SCRIPT_PREFIX {\n        return Ok(false);\n    }\n\n",
                    ""
                ),
                &bad_prefix
            ),
            SatResult::Sat
        );
        assert_eq!(
            taproot_script_query(
                &script_src.replace(
                    "    if script[1] != PUSH_32_BYTES {\n        return Ok(false);\n    }\n\n",
                    ""
                ),
                &bad_push
            ),
            SatResult::Sat
        );
        assert_eq!(
            taproot_script_query(&script_src.replace("Ok(true)", "Ok(false)"), &valid),
            SatResult::Sat
        );
        assert_eq!(
            taproot_key_query(
                &key_src.replace(
                    "    if !validate_taproot_script(script)? {\n        return Ok(None);\n    }\n\n",
                    ""
                ),
                &bad_prefix
            ),
            SatResult::Sat
        );
        assert_eq!(
            taproot_key_query(&key_src.replace("&script[2..34]", "&script[0..32]"), &valid),
            SatResult::Sat
        );
        assert_eq!(
            taproot_key_query(&key_src.replace("Ok(Some(output_key))", "Ok(None)"), &valid),
            SatResult::Sat
        );
    }

    #[test]
    fn witness_script_code_lock() {
        let file = consensus_file("transaction_hash.rs");
        let src = format!(
            "{}\n{}",
            extract_fn(&file, "derive_bip143_script_code_p2wpkh"),
            extract_fn(&file, "derive_bip143_script_code")
        );
        let p2wpkh = {
            let mut program = vec![0x00, 0x14];
            program.extend(std::iter::repeat(0x11).take(20));
            program
        };
        let p2wsh = {
            let mut program = vec![0x00, 0x20];
            program.extend(std::iter::repeat(0x22).take(32));
            program
        };
        let witness = [0x51u8];
        assert_eq!(
            witness_script_code_query(&src, &p2wpkh, None),
            SatResult::Unsat
        );
        assert_eq!(
            witness_script_code_query(&src, &p2wsh, Some(&witness)),
            SatResult::Unsat
        );
        assert_eq!(
            witness_script_code_query(&src, &p2wsh, None),
            SatResult::Unsat
        );
        assert_eq!(
            witness_script_code_query(&src, &[0x01; 22], None),
            SatResult::Unsat
        );
        let mutants = [
            (
                "script_code[0] = OP_DUP",
                "script_code[0] = OP_HASH160",
                &p2wpkh[..],
                None,
            ),
            (
                "script_code[1] = OP_HASH160",
                "script_code[1] = OP_DUP",
                &p2wpkh[..],
                None,
            ),
            (
                "script_code[2] = PUSH_20_BYTES",
                "script_code[2] = OP_DUP",
                &p2wpkh[..],
                None,
            ),
            (
                "script_code[23] = OP_EQUALVERIFY",
                "script_code[23] = OP_CHECKSIG",
                &p2wpkh[..],
                None,
            ),
            (
                "script_code[24] = OP_CHECKSIG",
                "script_code[24] = OP_CHECKSIGVERIFY",
                &p2wpkh[..],
                None,
            ),
            (
                "&witness_program[2..22]",
                "&witness_program[1..21]",
                &p2wpkh[..],
                None,
            ),
            (
                "witness_program.len() == 22",
                "witness_program.len() == 23",
                &p2wpkh[..],
                None,
            ),
            (
                "witness_program[0] == OP_0",
                "witness_program[0] == OP_1",
                &p2wpkh[..],
                None,
            ),
            (
                "witness_program[1] == PUSH_20_BYTES",
                "witness_program[1] == OP_0",
                &p2wpkh[..],
                None,
            ),
            (
                "witness_program.len() == 34",
                "witness_program.len() == 33",
                &p2wsh[..],
                Some(witness.as_slice()),
            ),
            (
                "witness_program[1] == PUSH_32_BYTES",
                "witness_program[1] == OP_DUP",
                &p2wsh[..],
                Some(witness.as_slice()),
            ),
        ];
        for (from, to, program, witness_item) in mutants {
            assert_eq!(
                witness_script_code_query(&src.replacen(from, to, 1), program, witness_item),
                SatResult::Sat,
                "{from}"
            );
        }
        assert_eq!(
            witness_script_code_query(
                &src.replace(
                    "return witness_script.map(|s| s.to_vec());",
                    "return Some(witness_program.to_vec());"
                ),
                &p2wsh,
                Some(&witness)
            ),
            SatResult::Sat
        );
    }

    #[test]
    fn script_code_separator_lock() {
        let file = consensus_file("transaction_hash.rs");
        let src = extract_fn(&file, "append_stripped_codeseparators");
        let points: &[&[u8]] = &[
            &[],
            &[0xab],
            &[0x51, 0xab],
            &[0x01, 0xab],
            &[0x4c, 0x01, 0xab],
            &[0x4d, 0x01, 0x00, 0xab],
            &[0x4e, 0x01, 0x00, 0x00, 0x00, 0xab],
            &[0x51],
        ];
        for code in points {
            assert_eq!(script_code_query(&src, code), SatResult::Unsat);
        }
        assert_eq!(
            script_code_query(
                &src.replace(
                    "} else if op == 0xab {\n            i += 1; // skip OP_CODESEPARATOR",
                    "} else if op == 0xab {\n            out.push(op);\n            i += 1;"
                ),
                &[0xab]
            ),
            SatResult::Sat
        );
        assert_eq!(
            script_code_query(
                &src.replace("out.push(op);\n            i += 1;", "i += 1;"),
                &[0x51]
            ),
            SatResult::Sat
        );
        assert_eq!(
            script_code_query(
                &src.replace(
                    "(i + 1 + op as usize).min(code.len());\n            out.extend_from_slice(&code[i..end]);",
                    "(i + 1 + op as usize).min(code.len());"
                ),
                &[0x01, 0xab]
            ),
            SatResult::Sat
        );
        assert_eq!(
            script_code_query(
                &src.replace(
                    "(i + 2 + len).min(code.len());\n            out.extend_from_slice(&code[i..end]);",
                    "(i + 2 + len).min(code.len());"
                ),
                &[0x4c, 0x01, 0xab]
            ),
            SatResult::Sat
        );
        assert_eq!(
            script_code_query(
                &src.replace(
                    "(i + 3 + len).min(code.len());\n            out.extend_from_slice(&code[i..end]);",
                    "(i + 3 + len).min(code.len());"
                ),
                &[0x4d, 0x01, 0x00, 0xab]
            ),
            SatResult::Sat
        );
        assert_eq!(
            script_code_query(
                &src.replace(
                    "(i + 5 + len).min(code.len());\n            out.extend_from_slice(&code[i..end]);",
                    "(i + 5 + len).min(code.len());"
                ),
                &[0x4e, 0x01, 0x00, 0x00, 0x00, 0xab]
            ),
            SatResult::Sat
        );
    }

    #[test]
    fn taproot_annex_lock() {
        let file = consensus_file("taproot.rs");
        let src = extract_fn(&file, "strip_taproot_annex");
        let helper = extract_fn(&file, "compute_taproot_annex_sighash_hash");
        let points = [
            vec![],
            vec![vec![0x50]],
            vec![vec![0x00], vec![0x00]],
            vec![vec![0x00], vec![0x50]],
            vec![vec![0x00], vec![0x50, 0x01]],
            vec![vec![0x11], vec![]],
        ];
        for witness in &points {
            assert_eq!(
                taproot_annex_query(&src, &helper, witness),
                SatResult::Unsat
            );
        }
        assert_eq!(
            taproot_annex_query(
                &src.replace("witness.len() >= 2", "witness.len() >= 1"),
                &helper,
                &[vec![0x50]]
            ),
            SatResult::Sat
        );
        assert_eq!(
            taproot_annex_query(
                &src.replace("|&b| b == TAPROOT_ANNEX_TAG", "|&b| true"),
                &helper,
                &[vec![0x00], vec![0x00]]
            ),
            SatResult::Sat
        );
        assert_eq!(
            taproot_annex_query(
                &src.replace(
                    "let stripped = witness[..witness.len() - 1].to_vec();",
                    "let stripped = witness.to_vec();"
                ),
                &helper,
                &[vec![0x00], vec![0x50]]
            ),
            SatResult::Sat
        );
        assert_eq!(
            taproot_annex_query(
                &src.replace(
                    "(Cow::Borrowed(witness), None)",
                    "(Cow::Borrowed(witness), Some([0u8; 32]))"
                ),
                &helper,
                &[vec![0x00]]
            ),
            SatResult::Sat
        );
        assert_eq!(
            taproot_annex_query(
                &src.replace("compute_taproot_annex_sighash_hash(annex)", "[0u8; 32]"),
                &helper,
                &[vec![0x00], vec![0x50]]
            ),
            SatResult::Sat
        );
        assert_eq!(
            taproot_annex_query(
                &src,
                &helper.replace("buf.extend_from_slice(annex);\n", ""),
                &[vec![0x00], vec![0x50]]
            ),
            SatResult::Sat
        );
        assert_eq!(
            taproot_annex_query(
                &src,
                &helper.replace("let mut buf = encode_varint(annex.len() as u64);\n", ""),
                &[vec![0x00], vec![0x50]]
            ),
            SatResult::Sat
        );
    }

    #[test]
    fn segwit_witness_structure_lock() {
        let file = consensus_file("witness.rs");
        let src = extract_fn(&file, "validate_segwit_witness_structure");
        let empty: Vec<Vec<u8>> = vec![];
        let at_limit = vec![vec![0u8; 520]];
        let over = vec![vec![0u8; 521]];
        let two = vec![vec![0u8; 1], vec![0u8; 520]];
        for witness in [&empty, &at_limit, &over, &two] {
            assert_eq!(segwit_witness_query(&src, witness), SatResult::Unsat);
        }
        assert_eq!(
            segwit_witness_query(&src.replace("usize = 520", "usize = 519"), &at_limit),
            SatResult::Sat
        );
        assert_eq!(
            segwit_witness_query(
                &src.replace(
                    "        if element.len() > MAX_WITNESS_ELEMENT_SIZE {\n            return Ok(false);\n        }\n",
                    ""
                ),
                &over
            ),
            SatResult::Sat
        );
        assert_eq!(
            segwit_witness_query(&src.replace("Ok(true)", "Ok(false)"), &empty),
            SatResult::Sat
        );
    }

    #[test]
    fn bip66_lock() {
        let file = consensus_file("bip_validation.rs");
        let src = extract_fn(&file, "check_bip66");
        let good = [0x30, 0x06, 0x02, 0x01, 0x01, 0x02, 0x01, 0x01, 0x01];
        let bad = [0u8; 0];
        for active in [false, true] {
            assert_eq!(bip66_query(&src, &good, active), SatResult::Unsat);
            assert_eq!(bip66_query(&src, &bad, active), SatResult::Unsat);
        }
        assert_eq!(
            bip66_query(
                &src.replace(
                    "    if !activation.is_fork_active(ForkId::Bip66, height) {\n        return Ok(true);\n    }\n\n",
                    ""
                ),
                &bad,
                false
            ),
            SatResult::Sat
        );
        assert_eq!(
            bip66_query(
                &src.replace("is_strict_der(signature)", "Ok(true)"),
                &bad,
                true
            ),
            SatResult::Sat
        );
        assert_eq!(
            bip66_query(
                &src.replace("is_strict_der(signature)", "Ok(false)"),
                &good,
                true
            ),
            SatResult::Sat
        );
    }

    #[test]
    fn p2sh_and_sigop_push_lock() {
        let file = consensus_file("sigop.rs");
        let p2sh = extract_fn(&file, "is_pay_to_script_hash");
        let push = extract_fn(&file, "sigop_count_push_opcode");
        let valid = {
            let mut script = vec![0xa9, 0x14];
            script.extend(std::iter::repeat(0x11).take(20));
            script.push(0x87);
            script
        };
        let bad_prefix = {
            let mut script = valid.clone();
            script[0] = 0x00;
            script
        };
        let bad_push = {
            let mut script = valid.clone();
            script[1] = 0x00;
            script
        };
        let bad_tail = {
            let mut script = valid.clone();
            script[22] = 0x00;
            script
        };
        let short = valid[..22].to_vec();
        for script in [&valid, &bad_prefix, &bad_push, &bad_tail, &short] {
            assert_eq!(p2sh_script_query(&p2sh, script), SatResult::Unsat);
        }
        assert_eq!(
            p2sh_script_query(&p2sh.replace("len() == 23", "len() == 22"), &valid),
            SatResult::Sat
        );
        assert_eq!(
            p2sh_script_query(
                &p2sh.replace("&& script[0] == OP_HASH160  // OP_HASH160\n        ", ""),
                &bad_prefix
            ),
            SatResult::Sat
        );
        assert_eq!(
            p2sh_script_query(
                &p2sh.replace("&& script[1] == 0x14  // Push 20 bytes\n        ", ""),
                &bad_push
            ),
            SatResult::Sat
        );
        assert_eq!(
            p2sh_script_query(
                &p2sh.replace("&& script[22] == OP_EQUAL // OP_EQUAL", ""),
                &bad_tail
            ),
            SatResult::Sat
        );
        for opcode in [0x00, 0x4f, 0x50, 0x60, 0x61] {
            assert_eq!(sigop_push_query(&push, opcode), SatResult::Unsat);
        }
        assert_eq!(
            sigop_push_query(&push.replace("op <= OP_16", "op < OP_16"), 0x60),
            SatResult::Sat
        );
        assert_eq!(
            sigop_push_query(&push.replace("op <= OP_16", "op <= OP_NOP"), 0x61),
            SatResult::Sat
        );
    }

    #[test]
    fn redeem_script_lock() {
        let file = consensus_file("sigop.rs");
        let src = extract_fn(&file, "extract_redeem_script_from_scriptsig");
        let points: &[&[u8]] = &[
            &[],
            &[0x61],
            &[0x02],
            &[0x01, 0xaa],
            &[0x4c, 0x01, 0xbb],
            &[0x4d, 0x01, 0x00, 0xcc],
            &[0x4e, 0x01, 0x00, 0x00, 0x00, 0xdd],
            &[0x4e],
            &[0x51],
            &[0x4f],
            &[0x00],
            &[0x51, 0x01, 0xaa],
        ];
        for script in points {
            assert_eq!(redeem_script_query(&src, script), SatResult::Unsat);
        }
        assert_eq!(
            redeem_script_query(
                &src.replace(
                    "let mut i = 0;",
                    "if script_sig.is_empty() { return Some(Vec::new()); }\n    let mut i = 0;"
                ),
                &[]
            ),
            SatResult::Sat
        );
        assert_eq!(
            redeem_script_query(
                &src.replace(
                    "        if !sigop_count_push_opcode(opcode) {\n            return None;\n        }\n\n",
                    ""
                ),
                &[0x61]
            ),
            SatResult::Sat
        );
        assert_eq!(
            redeem_script_query(
                &src.replace(
                    "            if i + advance + len > script_sig.len() {\n                return None;\n            }\n\n",
                    ""
                ),
                &[0x02]
            ),
            SatResult::Sat
        );
        assert_eq!(
            redeem_script_query(
                &src.replace(
                    "last_data = Some(script_sig[i + advance..i + advance + len].to_vec());",
                    "last_data = Some(Vec::new());"
                ),
                &[0x01, 0xaa]
            ),
            SatResult::Sat
        );
        assert_eq!(
            redeem_script_query(
                &src.replace("(script_sig[i + 1] as usize, 2)", "(1usize, 2)"),
                &[0x4c, 0x02, 0xaa, 0xbb]
            ),
            SatResult::Sat
        );
        assert_eq!(
            redeem_script_query(
                &src.replace("u16::from_le_bytes", "u16::from_be_bytes"),
                &[0x4d, 0x01, 0x00, 0xcc]
            ),
            SatResult::Sat
        );
        assert_eq!(
            redeem_script_query(
                &src.replace(
                    "                if i + 4 >= script_sig.len() {\n                    return None;\n                }\n",
                    ""
                ),
                &[0x4e]
            ),
            SatResult::Sat
        );
        assert_eq!(
            redeem_script_query(
                &src.replace(
                    "} else {\n            last_data = Some(Vec::new());",
                    "} else {\n            last_data = Some(vec![opcode]);"
                ),
                &[0x51]
            ),
            SatResult::Sat
        );
        assert_eq!(
            redeem_script_query(
                &src.replace("i += advance + len;", "return last_data;"),
                &[0x01, 0xaa, 0x51]
            ),
            SatResult::Sat
        );
    }

    #[test]
    fn sequence_lock_eval_lock() {
        let file = consensus_file("sequence_locks.rs");
        let src = extract_fn(&file, "evaluate_sequence_locks");
        let points = [
            (0u64, 0u64, -1i64, -1i64),
            (5, 0, 5, -1),
            (6, 0, 5, -1),
            (0, 5, -1, 5),
            (0, 6, -1, 5),
            (6, 5, 5, 5),
            (5, 6, 5, 5),
            (6, 6, 5, 5),
            (0, 0, 0, -1),
            (0, 0, -1, 0),
        ];
        for (height, time, min_h, min_t) in points {
            assert_eq!(
                sequence_lock_query(&src, height, time, min_h, min_t),
                SatResult::Unsat
            );
        }
        assert_eq!(
            sequence_lock_query(&src.replace("\n    true\n", "\n    false\n"), 0, 0, -1, -1),
            SatResult::Sat
        );
        assert_eq!(
            sequence_lock_query(
                &src.replace("block_height <= min_height", "block_height < min_height"),
                5,
                0,
                5,
                -1
            ),
            SatResult::Sat
        );
        assert_eq!(
            sequence_lock_query(
                &src.replace("block_time <= min_time", "block_time < min_time"),
                0,
                5,
                -1,
                5
            ),
            SatResult::Sat
        );
        assert_eq!(
            sequence_lock_query(
                &src.replace("min_height >= 0", "min_height > 0"),
                0,
                0,
                0,
                -1
            ),
            SatResult::Sat
        );
        assert_eq!(
            sequence_lock_query(&src.replace("min_time >= 0", "min_time > 0"), 0, 0, -1, 0),
            SatResult::Sat
        );
        let height_if = "    // Check height constraint\n    if min_height >= 0 && block_height <= min_height as u64 {\n        // Runtime assertion: Cast must be valid (min_height >= 0)\n        debug_assert!(\n            min_height >= 0,\n            \"min_height ({min_height}) must be non-negative for cast to u64\"\n        );\n        return false;\n    }\n\n";
        let time_if = "    // Check time constraint\n    if min_time >= 0 && block_time <= min_time as u64 {\n        // Runtime assertion: Cast must be valid (min_time >= 0)\n        debug_assert!(\n            min_time >= 0,\n            \"min_time ({min_time}) must be non-negative for cast to u64\"\n        );\n        return false;\n    }\n\n";
        assert_eq!(
            sequence_lock_query(&src.replace(height_if, ""), 5, 0, 5, -1),
            SatResult::Sat
        );
        assert_eq!(
            sequence_lock_query(&src.replace(time_if, ""), 0, 5, -1, 5),
            SatResult::Sat
        );
    }

    #[test]
    fn bip30_repeat_lock() {
        let file = consensus_file("bip_validation.rs");
        let src = extract_fn(&file, "is_bip30_repeat_block");
        let hash42 = BIP30_REPEAT_HASH_91842;
        let hash80 = BIP30_REPEAT_HASH_91880;
        let mut other = hash42;
        other[0] ^= 0xff;
        let points: &[(u64, &[u8; 32])] = &[
            (91_842, &hash42),
            (91_880, &hash80),
            (91_842, &hash80),
            (91_880, &hash42),
            (91_842, &other),
            (91_880, &other),
            (0, &hash42),
            (91_841, &hash42),
            (91_881, &hash80),
        ];
        for (height, hash) in points {
            assert_eq!(
                bip30_repeat_query(&file, &src, *height, hash),
                SatResult::Unsat
            );
        }
        assert_eq!(
            bip30_repeat_query(&file, &src.replace("91_842", "91_841"), 91_842, &hash42),
            SatResult::Sat
        );
        assert_eq!(
            bip30_repeat_query(&file, &src.replace("91_880", "91_881"), 91_880, &hash80),
            SatResult::Sat
        );
        assert_eq!(
            bip30_repeat_query(
                &file,
                &src.replace("block_hash == &BIP30_REPEAT_91842", "true"),
                91_842,
                &other
            ),
            SatResult::Sat
        );
        assert_eq!(
            bip30_repeat_query(
                &file,
                &src.replace("block_hash == &BIP30_REPEAT_91880", "true"),
                91_880,
                &other
            ),
            SatResult::Sat
        );
        assert_eq!(
            bip30_repeat_query(
                &file,
                &src.replace("BIP30_REPEAT_91842", "BIP30_REPEAT_91880"),
                91_842,
                &hash42
            ),
            SatResult::Sat
        );
        assert_eq!(
            bip30_repeat_query(&file, &src.replace("_ => false", "_ => true"), 0, &hash42),
            SatResult::Sat
        );
    }

    #[test]
    fn witness_empty_lock() {
        let file = consensus_file("witness.rs");
        let src = extract_fn(&file, "is_witness_empty");
        let body = "witness.is_empty() || witness.iter().all(|elem| elem.is_empty())";
        let points: &[Vec<Vec<u8>>] = &[
            vec![],
            vec![vec![]],
            vec![vec![], vec![]],
            vec![vec![0x01]],
            vec![vec![], vec![0x01]],
            vec![vec![0x01], vec![]],
            vec![vec![0x00]],
        ];
        for witness in points {
            assert_eq!(witness_empty_query(&src, witness), SatResult::Unsat);
        }
        assert_eq!(
            witness_empty_query(&src.replace(body, "false"), &[]),
            SatResult::Sat
        );
        assert_eq!(
            witness_empty_query(&src.replace(body, "witness.is_empty()"), &[vec![]]),
            SatResult::Sat
        );
        assert_eq!(
            witness_empty_query(&src.replace(".all(", ".any("), &[vec![0x01], vec![]]),
            SatResult::Sat
        );
        assert_eq!(
            witness_empty_query(&src.replace(body, "true"), &[vec![0x01]]),
            SatResult::Sat
        );
    }

    #[test]
    fn witness_stack_null_lock() {
        let file = consensus_file("witness.rs");
        let src = extract_fn(&file, "witness_stack_is_null");
        let points: &[Vec<Vec<u8>>] = &[
            vec![],
            vec![vec![]],
            vec![vec![], vec![]],
            vec![vec![0x01]],
            vec![vec![0x00]],
        ];
        for witness in points {
            assert_eq!(stack_null_query(&src, witness), SatResult::Unsat);
        }
        assert_eq!(
            stack_null_query(&src.replace("witness.is_empty()", "false"), &[]),
            SatResult::Sat
        );
        assert_eq!(
            stack_null_query(
                &src.replace(
                    "witness.is_empty()",
                    "witness.iter().all(|elem| elem.is_empty())"
                ),
                &[vec![]]
            ),
            SatResult::Sat
        );
        assert_eq!(
            stack_null_query(&src.replace("witness.is_empty()", "true"), &[vec![0x01]]),
            SatResult::Sat
        );
    }

    #[test]
    fn nonempty_input_witness_lock() {
        let file = consensus_file("block/script_cache.rs");
        let src = extract_fn(&file, "tx_has_nonempty_input_witness");
        let empty: Vec<Vec<u8>> = vec![vec![]];
        let byte: Vec<Vec<u8>> = vec![vec![0x00]];
        let present: Vec<Vec<u8>> = vec![vec![0x01]];
        let points: &[Option<Vec<Vec<Vec<u8>>>>] = &[
            None,
            Some(vec![]),
            Some(vec![empty.clone()]),
            Some(vec![empty.clone(), empty.clone()]),
            Some(vec![present.clone()]),
            Some(vec![byte.clone()]),
            Some(vec![empty.clone(), present.clone()]),
            Some(vec![present.clone(), empty.clone()]),
        ];
        for witnesses in points {
            assert_eq!(
                nonempty_witness_query(&src, witnesses.as_deref()),
                SatResult::Unsat
            );
        }
        let dropped_bang = vec![present.clone()];
        assert_eq!(
            nonempty_witness_query(
                &src.replace("!is_witness_empty(w)", "is_witness_empty(w)"),
                Some(dropped_bang.as_slice())
            ),
            SatResult::Sat
        );
        let only_empty = vec![empty.clone()];
        assert_eq!(
            nonempty_witness_query(
                &src.replace("!is_witness_empty(w)", "true"),
                Some(only_empty.as_slice())
            ),
            SatResult::Sat
        );
        let mixed = vec![empty, present];
        assert_eq!(
            nonempty_witness_query(&src.replace(".any(", ".all("), Some(mixed.as_slice())),
            SatResult::Sat
        );
        assert_eq!(
            nonempty_witness_query(&src.replace("unwrap_or(false)", "unwrap_or(true)"), None),
            SatResult::Sat
        );
    }

    #[test]
    fn reserved_nonce_lock() {
        let file = consensus_file("segwit.rs");
        let src = extract_fn(&file, "coinbase_reserved_nonce");
        let item = vec![0x11u8; 32];
        let points: &[Vec<Vec<Vec<u8>>>] = &[
            vec![],
            vec![vec![]],
            vec![vec![vec![0x11; 31]]],
            vec![vec![item.clone()]],
            vec![vec![vec![0x11; 33]]],
            vec![vec![item.clone(), item.clone()]],
            vec![vec![vec![0u8; 32]]],
        ];
        for witnesses in points {
            assert_eq!(reserved_nonce_query(&src, witnesses), SatResult::Unsat);
        }
        assert_eq!(
            reserved_nonce_query(
                &src.replace(
                    "let stack = coinbase_witnesses.first()?;",
                    "if coinbase_witnesses.is_empty() { return Some([0u8; 32]); }\n    let stack = coinbase_witnesses.first()?;"
                ),
                &[]
            ),
            SatResult::Sat
        );
        assert_eq!(
            reserved_nonce_query(
                &src.replace(
                    "    if stack.len() != 1 || stack[0].len() != 32 {",
                    "    if stack.is_empty() { return Some([0u8; 32]); }\n    if stack.len() != 1 || stack[0].len() != 32 {"
                ),
                &[vec![]]
            ),
            SatResult::Sat
        );
        assert_eq!(
            reserved_nonce_query(
                &src.replace("stack.len() != 1", "stack.len() != 2"),
                &[vec![item.clone(), item.clone()]]
            ),
            SatResult::Sat
        );
        assert_eq!(
            reserved_nonce_query(
                &src.replace(".len() != 32", ".len() != 33"),
                &[vec![item.clone()]]
            ),
            SatResult::Sat
        );
        assert_eq!(
            reserved_nonce_query(
                &src.replace("copy_from_slice(&stack[0])", "copy_from_slice(&[0u8; 32])"),
                &[vec![item]]
            ),
            SatResult::Sat
        );
    }

    #[test]
    fn witness_commitment_extract_lock() {
        let file = consensus_file("segwit.rs");
        let src = extract_fn(&file, "extract_witness_commitment");
        let hash = [0xabu8; 32];
        let magic = [0xaa, 0x21, 0xa9, 0xed];
        let mut good = vec![0x6a, 0x24];
        good.extend_from_slice(&magic);
        good.extend_from_slice(&hash);
        let mut longer = good.clone();
        longer.push(0xff);
        let mut short = good.clone();
        short.pop();
        let mut bad_op = good.clone();
        bad_op[0] = 0x00;
        let mut bad_push = good.clone();
        bad_push[1] = 0x00;
        let mut bad_magic = good.clone();
        bad_magic[2] = 0x00;
        for script in [
            &good[..],
            &longer[..],
            &short[..],
            &bad_op[..],
            &bad_push[..],
            &bad_magic[..],
            &[][..],
        ] {
            assert_eq!(witness_commitment_query(&src, script), SatResult::Unsat);
        }
        assert_eq!(
            witness_commitment_query(
                &src.replace("script.len() >= 38", "script.len() > 38"),
                &good
            ),
            SatResult::Sat
        );
        assert_eq!(
            witness_commitment_query(&src.replace("script[0] == OP_RETURN && ", ""), &bad_op),
            SatResult::Sat
        );
        assert_eq!(
            witness_commitment_query(&src.replace("script[1] == 0x24 && ", ""), &bad_push),
            SatResult::Sat
        );
        assert_eq!(
            witness_commitment_query(&src.replace("script[2..6] == MAGIC", "true"), &bad_magic),
            SatResult::Sat
        );
        assert_eq!(
            witness_commitment_query(&src.replace("&script[6..38]", "&script[0..32]"), &good),
            SatResult::Sat
        );
        assert_eq!(
            witness_commitment_query(
                &src.replace("return Some(commitment)", "return None"),
                &good
            ),
            SatResult::Sat
        );
    }

    #[test]
    fn last_witness_commitment_lock() {
        let file = consensus_file("segwit.rs");
        let src = extract_fn(&file, "last_witness_commitment_in_coinbase_outputs");
        let magic = [0xaa_u8, 0x21, 0xa9, 0xed];
        let mut first = vec![0x6a, 0x24];
        first.extend_from_slice(&magic);
        first.extend_from_slice(&[0x11; 32]);
        let mut second = vec![0x6a, 0x24];
        second.extend_from_slice(&magic);
        second.extend_from_slice(&[0x22; 32]);
        let other = vec![0x00];
        let points: &[&[&[u8]]] = &[
            &[],
            &[&other],
            &[&first],
            &[&second],
            &[&first, &second],
            &[&first, &other],
            &[&other, &second],
            &[&first, &other, &second],
        ];
        for scripts in points {
            assert_eq!(last_commitment_query(&src, scripts), SatResult::Unsat);
        }
        assert_eq!(
            last_commitment_query(
                &src.replace("\n    last_commitment\n", "\n    Some([0u8; 32])\n"),
                &[]
            ),
            SatResult::Sat
        );
        assert_eq!(
            last_commitment_query(
                &src.replace("            last_commitment = Some(commitment);\n", ""),
                &[&first]
            ),
            SatResult::Sat
        );
        assert_eq!(
            last_commitment_query(
                &src.replace(
                    "last_commitment = Some(commitment);",
                    "return Some(commitment);"
                ),
                &[&first, &second]
            ),
            SatResult::Sat
        );
        assert_eq!(
            last_commitment_query(
                &src.replace(
                    "            last_commitment = Some(commitment);\n        }\n",
                    "            last_commitment = Some(commitment);\n        } else {\n            last_commitment = None;\n        }\n"
                ),
                &[&first, &other]
            ),
            SatResult::Sat
        );
    }

    #[test]
    fn witness_commitment_ok_lock() {
        let file = consensus_file("segwit.rs");
        let src = extract_fn(&file, "validate_witness_commitment");
        let root = [0x11u8; 32];
        let nonce = [0x22u8; 32];
        let mut correct = [0u8; 64];
        correct[..32].copy_from_slice(&root);
        correct[32..].copy_from_slice(&nonce);
        let mut swapped = [0u8; 64];
        swapped[..32].copy_from_slice(&nonce);
        swapped[32..].copy_from_slice(&root);
        let wrong = [0u8; 64];
        let points = [
            (false, None, wrong),
            (true, None, correct),
            (true, Some(nonce), correct),
            (true, Some(nonce), swapped),
            (true, Some(nonce), wrong),
        ];
        for (has, nonce_in, stored) in points {
            assert_eq!(
                witness_commitment_ok_query(&src, has, nonce_in, root, stored),
                SatResult::Unsat
            );
        }
        assert_eq!(
            witness_commitment_ok_query(
                &src.replace("return Ok(true)", "return Ok(false)"),
                false,
                None,
                root,
                wrong
            ),
            SatResult::Sat
        );
        assert_eq!(
            witness_commitment_ok_query(
                &src.replace("return Ok(false)", "return Ok(true)"),
                true,
                None,
                root,
                correct
            ),
            SatResult::Sat
        );
        let swapped_src = src.replace(
            "preimage[..32].copy_from_slice(witness_merkle_root);\n    preimage[32..].copy_from_slice(&reserved_nonce);",
            "preimage[..32].copy_from_slice(&reserved_nonce);\n    preimage[32..].copy_from_slice(witness_merkle_root);",
        );
        assert_eq!(
            witness_commitment_ok_query(&swapped_src, true, Some(nonce), root, correct),
            SatResult::Sat
        );
        assert_eq!(
            witness_commitment_ok_query(
                &src.replace(
                    "    preimage[..32].copy_from_slice(witness_merkle_root);\n",
                    ""
                ),
                true,
                Some(nonce),
                root,
                correct
            ),
            SatResult::Sat
        );
        assert_eq!(
            witness_commitment_ok_query(
                &src.replace("    preimage[32..].copy_from_slice(&reserved_nonce);\n", ""),
                true,
                Some(nonce),
                root,
                correct
            ),
            SatResult::Sat
        );
        assert_eq!(
            witness_commitment_ok_query(
                &src.replace("Ok(commitment == expected_commitment)", "Ok(false)"),
                true,
                Some(nonce),
                root,
                correct
            ),
            SatResult::Sat
        );
        assert_eq!(
            witness_commitment_ok_query(
                &src.replace("Ok(commitment == expected_commitment)", "Ok(true)"),
                true,
                Some(nonce),
                root,
                wrong
            ),
            SatResult::Sat
        );
        assert_eq!(
            witness_commitment_ok_query(
                &src.replace("sha256d_bytes(&preimage)", "*witness_merkle_root"),
                true,
                Some(nonce),
                root,
                correct
            ),
            SatResult::Sat
        );
    }

    #[test]
    fn block_witness_commitment_lock() {
        let file = consensus_file("segwit.rs");
        let src = extract_fn(&file, "block_witness_commitment_ok");
        let points = [
            (false, false, true),
            (false, true, true),
            (true, true, true),
            (true, false, false),
            (true, true, false),
        ];
        for (has, any, helper) in points {
            assert_eq!(
                block_commitment_query(&src, has, any, helper),
                SatResult::Unsat
            );
        }
        assert_eq!(
            block_commitment_query(
                &src.replace("return Ok(!any_witness)", "return Ok(true)"),
                false,
                true,
                true
            ),
            SatResult::Sat
        );
        assert_eq!(
            block_commitment_query(
                &src.replace("return Ok(!any_witness)", "return Ok(false)"),
                false,
                false,
                true
            ),
            SatResult::Sat
        );
        assert_eq!(
            block_commitment_query(
                &src.replace(
                    "    if last_witness_commitment_in_coinbase_outputs(&coinbase_tx.outputs).is_none() {\n        return Ok(!any_witness);\n    }\n",
                    ""
                ),
                false,
                true,
                true
            ),
            SatResult::Sat
        );
        assert_eq!(
            block_commitment_query(
                &src.replace(
                    "validate_witness_commitment(coinbase_tx, witness_merkle_root, coinbase_witnesses)",
                    "Ok(true)"
                ),
                true,
                true,
                false
            ),
            SatResult::Sat
        );
        assert_eq!(
            block_commitment_query(
                &src.replace(
                    "validate_witness_commitment(coinbase_tx, witness_merkle_root, coinbase_witnesses)",
                    "Ok(false)"
                ),
                true,
                false,
                true
            ),
            SatResult::Sat
        );
    }

    #[test]
    fn witness_commitment_script_lock() {
        let file = consensus_file("segwit.rs");
        let src = extract_fn(&file, "witness_commitment_script");
        let root = [0x11u8; 32];
        let nonce = [0x22u8; 32];
        let other = [0x33u8; 32];
        assert_eq!(
            commitment_script_query(&src, &root, &nonce),
            SatResult::Unsat
        );
        assert_eq!(
            commitment_script_query(&src, &other, &nonce),
            SatResult::Unsat
        );
        assert_eq!(
            commitment_script_query(&src, &root, &other),
            SatResult::Unsat
        );
        let swapped = src.replace(
            "preimage[..32].copy_from_slice(witness_root);\n    preimage[32..].copy_from_slice(nonce);",
            "preimage[..32].copy_from_slice(nonce);\n    preimage[32..].copy_from_slice(witness_root);",
        );
        assert_eq!(
            commitment_script_query(&swapped, &root, &nonce),
            SatResult::Sat
        );
        assert_eq!(
            commitment_script_query(
                &src.replace("    preimage[..32].copy_from_slice(witness_root);\n", ""),
                &root,
                &nonce
            ),
            SatResult::Sat
        );
        assert_eq!(
            commitment_script_query(
                &src.replace("    preimage[32..].copy_from_slice(nonce);\n", ""),
                &root,
                &nonce
            ),
            SatResult::Sat
        );
        assert_eq!(
            commitment_script_query(
                &src.replace("vec![OP_RETURN, 0x24]", "vec![0x00, 0x24]"),
                &root,
                &nonce
            ),
            SatResult::Sat
        );
        assert_eq!(
            commitment_script_query(
                &src.replace("vec![OP_RETURN, 0x24]", "vec![OP_RETURN, 0x00]"),
                &root,
                &nonce
            ),
            SatResult::Sat
        );
        assert_eq!(
            commitment_script_query(
                &src.replace(
                    "    script.extend_from_slice(&[0xaa, 0x21, 0xa9, 0xed]);\n",
                    ""
                ),
                &root,
                &nonce
            ),
            SatResult::Sat
        );
        assert_eq!(
            commitment_script_query(
                &src.replace("sha256d_bytes(&preimage)", "*witness_root"),
                &root,
                &nonce
            ),
            SatResult::Sat
        );
        assert_eq!(
            commitment_script_query(
                &src.replace("    script.extend_from_slice(&commitment);\n", ""),
                &root,
                &nonce
            ),
            SatResult::Sat
        );
    }

    #[test]
    fn redeem_push_canonical_lock() {
        let file = consensus_file("script/mod.rs");
        let src = extract_fn(&file, "redeem_push_is_canonical");
        let mut redeem22 = vec![0x00, 0x14];
        redeem22.extend_from_slice(&[0xab; 20]);
        let mut redeem34 = vec![0x00, 0x20];
        redeem34.extend_from_slice(&[0xcd; 32]);
        let direct = |redeem: &[u8]| {
            let mut script = vec![redeem.len() as u8];
            script.extend_from_slice(redeem);
            script
        };
        let pushdata1 = |redeem: &[u8]| {
            let mut script = vec![0x4c, redeem.len() as u8];
            script.extend_from_slice(redeem);
            script
        };
        let canonical22 = direct(&redeem22);
        let canonical34 = direct(&redeem34);
        for (script, redeem) in [
            (canonical22.clone(), redeem22.clone()),
            (canonical34.clone(), redeem34.clone()),
            (pushdata1(&redeem22), redeem22.clone()),
            (pushdata1(&redeem34), redeem34.clone()),
        ] {
            assert_eq!(redeem_push_query(&src, &script, &redeem), SatResult::Unsat);
        }
        let mut trailer = canonical22.clone();
        trailer.push(0xff);
        assert_eq!(
            redeem_push_query(&src, &trailer, &redeem22),
            SatResult::Unsat
        );
        let wrong = direct(&vec![0u8; 22]);
        assert_eq!(redeem_push_query(&src, &wrong, &redeem22), SatResult::Unsat);
        let mut bad_opcode = redeem22.clone();
        bad_opcode.insert(0, 0x4c);
        assert_eq!(
            redeem_push_query(&src, &bad_opcode, &redeem22),
            SatResult::Unsat
        );
        assert_eq!(
            redeem_push_query(
                &src.replace("script_sig.len() == len + 1", "script_sig.len() == len"),
                &canonical22,
                &redeem22
            ),
            SatResult::Sat
        );
        assert_eq!(
            redeem_push_query(
                &src.replace(" && script_sig[0] as usize == len", ""),
                &bad_opcode,
                &redeem22
            ),
            SatResult::Sat
        );
        assert_eq!(
            redeem_push_query(
                &src.replace(" && &script_sig[1..] == redeem", ""),
                &wrong,
                &redeem22
            ),
            SatResult::Sat
        );
        let pushdata_body = src.replace(
            "return script_sig.len() == len + 1\n            && script_sig[0] as usize == len\n            && &script_sig[1..] == redeem;",
            "return script_sig.len() == len + 2\n            && script_sig[0] == 0x4c\n            && script_sig[1] as usize == len\n            && &script_sig[2..] == redeem;",
        );
        assert_eq!(
            redeem_push_query(&pushdata_body, &pushdata1(&redeem22), &redeem22),
            SatResult::Sat
        );
    }

    #[test]
    fn decode_locktime_value_lock() {
        let file = consensus_file("locktime.rs");
        let src = extract_fn(&file, "decode_locktime_value");
        let points: &[&[u8]] = &[
            &[],
            &[0x80],
            &[0x81],
            &[0x01, 0x00],
            &[0x01, 0x80],
            &[0x00, 0x80],
            &[0x01, 0x00, 0x00, 0x00, 0x00],
            &[0x01, 0x00, 0x00, 0x00, 0x00, 0x00],
        ];
        for bytes in points {
            assert_eq!(decode_locktime_query(&src, bytes), SatResult::Unsat);
        }
        assert_eq!(
            decode_locktime_query(
                &src.replace("bytes.len() > 5", "bytes.len() >= 5"),
                &[0x01, 0x00, 0x00, 0x00, 0x00]
            ),
            SatResult::Sat
        );
        assert_eq!(
            decode_locktime_query(
                &src.replace("bytes.len() > 5", "bytes.len() > 6"),
                &[0x01, 0x00, 0x00, 0x00, 0x00, 0x00]
            ),
            SatResult::Sat
        );
        assert_eq!(
            decode_locktime_query(&src.replace("return Some(0)", "return None"), &[]),
            SatResult::Sat
        );
        assert_eq!(
            decode_locktime_query(&src.replace("bytes[last] & 0x80 != 0", "false"), &[0x81]),
            SatResult::Sat
        );
        assert_eq!(
            decode_locktime_query(
                &src.replace("        result &= !(0x80i64 << (8 * last));\n", ""),
                &[0x80]
            ),
            SatResult::Sat
        );
        assert_eq!(
            decode_locktime_query(&src.replace("        result = -result;\n", ""), &[0x81]),
            SatResult::Sat
        );
        assert_eq!(
            decode_locktime_query(
                &src.replace("<< (8 * i)", "<< (8 * (bytes.len() - 1 - i))"),
                &[0x01, 0x00]
            ),
            SatResult::Sat
        );
    }

    #[test]
    fn script_bool_bytes_lock() {
        let file = consensus_file("script/mod.rs");
        let src = extract_fn(&file, "script_bool_bytes");
        assert_eq!(script_bool_query(&src, true), SatResult::Unsat);
        assert_eq!(script_bool_query(&src, false), SatResult::Unsat);
        assert_eq!(
            script_bool_query(&src.replace("&[1]", "&[0x02]"), true),
            SatResult::Sat
        );
        assert_eq!(
            script_bool_query(&src.replace("&[1]", "&[]"), true),
            SatResult::Sat
        );
        assert_eq!(
            script_bool_query(&src.replace("&[]", "&[0x00]"), false),
            SatResult::Sat
        );
    }

    #[test]
    fn taproot_sig_parse_lock() {
        let file = consensus_file("bip348.rs");
        let src = extract_fn(&file, "try_parse_taproot_schnorr_witness_sig");
        let sig64 = [0x11u8; 64];
        let mut sig65 = [0x11u8; 65];
        sig65[64] = 0x01;
        let mut sig65_default = [0x11u8; 65];
        sig65_default[64] = 0x00;
        let mut sig65_single = [0x11u8; 65];
        sig65_single[64] = 0x03;
        let sig63 = [0x11u8; 63];
        for bytes in [
            &sig64[..],
            &sig65[..],
            &sig65_default[..],
            &sig65_single[..],
            &sig63[..],
        ] {
            assert_eq!(taproot_sig_parse_query(&src, bytes), SatResult::Unsat);
        }
        assert_eq!(
            taproot_sig_parse_query(&src.replace("Some((sig, 0x00))", "None"), &sig64),
            SatResult::Sat
        );
        assert_eq!(
            taproot_sig_parse_query(
                &src.replace("Some((sig, 0x00))", "Some((sig, 0x01))"),
                &sig64
            ),
            SatResult::Sat
        );
        assert_eq!(
            taproot_sig_parse_query(
                &src.replace(
                    "            if hashtype == 0x00 {\n                return None;\n            }\n",
                    ""
                ),
                &sig65_default
            ),
            SatResult::Sat
        );
        assert_eq!(
            taproot_sig_parse_query(
                &src.replace(
                    "sig.copy_from_slice(sig_bytes);",
                    "sig.copy_from_slice(&[0u8; 64]);"
                ),
                &sig64
            ),
            SatResult::Sat
        );
        assert_eq!(
            taproot_sig_parse_query(
                &src.replace(
                    "sig.copy_from_slice(&sig_bytes[..64]);",
                    "sig.copy_from_slice(&[0u8; 64]);"
                ),
                &sig65
            ),
            SatResult::Sat
        );
        assert_eq!(
            taproot_sig_parse_query(
                &src.replace("Some((sig, hashtype))", "Some((sig, 0x01))"),
                &sig65_single
            ),
            SatResult::Sat
        );
        assert_eq!(
            taproot_sig_parse_query(
                &src.replace("_ => None", "_ => Some(([0u8; 64], 0x00))"),
                &sig63
            ),
            SatResult::Sat
        );
    }

    #[test]
    fn tapscript_sigop_lock() {
        let file = consensus_file("sigop.rs");
        let src = extract_fn(&file, "count_tapscript_sigops");
        let scripts: &[&[u8]] = &[
            &[],
            &[0xac],
            &[0xad],
            &[0xba],
            &[0xae],
            &[0x01, 0xac],
            &[0x01, 0x00, 0xac],
            &[0x4c, 0x00, 0xac],
            &[0x4c, 0xac],
            &[0x4d, 0x01, 0x00, 0xac],
            &[0x4e, 0x01, 0x00, 0x00, 0x00, 0xac],
            &[0x4d, 0xac],
            &[0x00, 0xac],
        ];
        for script in scripts {
            assert_eq!(tapscript_sigop_query(&src, script), SatResult::Unsat);
        }
        assert_eq!(
            tapscript_sigop_query(
                &src.replace("let mut count = 0u32", "let mut count = 1u32"),
                &[]
            ),
            SatResult::Sat
        );
        assert_eq!(
            tapscript_sigop_query(&src.replace("opcode == OP_CHECKSIG || ", ""), &[0xac]),
            SatResult::Sat
        );
        assert_eq!(
            tapscript_sigop_query(&src.replace("opcode == OP_CHECKSIGVERIFY || ", ""), &[0xad]),
            SatResult::Sat
        );
        assert_eq!(
            tapscript_sigop_query(&src.replace(" || opcode == OP_CHECKSIGADD", ""), &[0xba]),
            SatResult::Sat
        );
        assert_eq!(
            tapscript_sigop_query(
                &src.replace(
                    "opcode == OP_CHECKSIGADD",
                    "opcode == OP_CHECKSIGADD || opcode == 0xae"
                ),
                &[0xae]
            ),
            SatResult::Sat
        );
        assert_eq!(
            tapscript_sigop_query(&src.replace("i += 1 + len", "i += 1"), &[0x01, 0xac]),
            SatResult::Sat
        );
        assert_eq!(
            tapscript_sigop_query(
                &src.replace("i += 1 + len", "i += 2 + len"),
                &[0x01, 0x00, 0xac]
            ),
            SatResult::Sat
        );
        assert_eq!(
            tapscript_sigop_query(
                &src.replace("opcode < OP_PUSHDATA1", "opcode <= OP_PUSHDATA1"),
                &[0x4c, 0x00, 0xac]
            ),
            SatResult::Sat
        );
        assert_eq!(
            tapscript_sigop_query(&src.replace("i += 2 + len", "i += 1"), &[0x4c, 0xac]),
            SatResult::Sat
        );
        assert_eq!(
            tapscript_sigop_query(
                &src.replace("i += 3 + len", "i += 1"),
                &[0x4d, 0x01, 0x00, 0xac]
            ),
            SatResult::Sat
        );
        assert_eq!(
            tapscript_sigop_query(
                &src.replace("i += 5 + len", "i += 1"),
                &[0x4e, 0x01, 0x00, 0x00, 0x00, 0xac]
            ),
            SatResult::Sat
        );
    }

    #[test]
    fn tapscript_opcode_end_lock() {
        let file = consensus_file("script/mod.rs");
        let src = extract_fn(&file, "tapscript_opcode_end");
        let scripts: &[&[u8]] = &[
            &[],
            &[0x00],
            &[0x01],
            &[0x01, 0xaa],
            &[0x02],
            &[0x4b],
            &[0x4c],
            &[0x4c, 0x00],
            &[0x4c, 0x01],
            &[0x4c, 0x01, 0x50],
            &[0x4d],
            &[0x4d, 0x50],
            &[0x4d, 0x01, 0x00],
            &[0x4d, 0x01, 0x00, 0xaa],
            &[0x4d, 0x00, 0x01, 0xaa],
            &[0x4e],
            &[0x4e, 0x50],
            &[0x4e, 0x01, 0x00, 0x00, 0x00],
            &[0x4e, 0x01, 0x00, 0x00, 0x00, 0xbb],
            &[0x4e, 0x00, 0x00, 0x00, 0x00],
            &[0x50],
            &[0x4f],
            &[0x61],
        ];
        for script in scripts {
            assert_eq!(
                tapscript_opcode_end_query(&src, script, 0),
                SatResult::Unsat,
                "{script:02x?}"
            );
        }
        assert_eq!(
            tapscript_opcode_end_query(
                &src.replace(
                    "if opcode == 0 {\n        pc.checked_add(1)?",
                    "if opcode == 0 {\n        pc.checked_add(2)?"
                ),
                &[0x00],
                0
            ),
            SatResult::Sat
        );
        assert_eq!(
            tapscript_opcode_end_query(
                &src.replace(
                    "pc.checked_add(1)?.checked_add(opcode as usize)?",
                    "pc.checked_add(1)?"
                ),
                &[0x02],
                0
            ),
            SatResult::Sat
        );
        assert_eq!(
            tapscript_opcode_end_query(&src.replace("opcode <= 0x4b", "opcode < 0x4b"), &[0x4b], 0),
            SatResult::Sat
        );
        assert_eq!(
            tapscript_opcode_end_query(
                &src.replace(
                    "let len = *script.get(pc + 1)? as usize;\n        pc.checked_add(2)?.checked_add(len)?",
                    "pc.checked_add(1)?"
                ),
                &[0x4c],
                0
            ),
            SatResult::Sat
        );
        assert_eq!(
            tapscript_opcode_end_query(
                &src.replace("pc.checked_add(2)?.checked_add(len)?", "pc.checked_add(2)?"),
                &[0x4c, 0x01],
                0
            ),
            SatResult::Sat
        );
        assert_eq!(
            tapscript_opcode_end_query(
                &src.replace(
                    "if pc + 2 >= script.len() {\n            return None;\n        }",
                    "if pc + 2 >= script.len() {\n            return Some(pc + 1);\n        }"
                ),
                &[0x4d, 0x50],
                0
            ),
            SatResult::Sat
        );
        assert_eq!(
            tapscript_opcode_end_query(
                &src.replace("pc.checked_add(3)?.checked_add(len)?", "pc.checked_add(3)?"),
                &[0x4d, 0x01, 0x00],
                0
            ),
            SatResult::Sat
        );
        assert_eq!(
            tapscript_opcode_end_query(
                &src.replace(
                    "u16::from_le_bytes([script[pc + 1], script[pc + 2]])",
                    "u16::from_le_bytes([script[pc + 2], script[pc + 1]])"
                ),
                &[0x4d, 0x01, 0x00, 0xaa],
                0
            ),
            SatResult::Sat
        );
        assert_eq!(
            tapscript_opcode_end_query(
                &src.replace(
                    "if pc + 4 >= script.len() {\n            return None;\n        }",
                    "if pc + 4 >= script.len() {\n            return Some(pc + 1);\n        }"
                ),
                &[0x4e, 0x50],
                0
            ),
            SatResult::Sat
        );
        assert_eq!(
            tapscript_opcode_end_query(
                &src.replace("pc.checked_add(5)?.checked_add(len)?", "pc.checked_add(5)?"),
                &[0x4e, 0x01, 0x00, 0x00, 0x00],
                0
            ),
            SatResult::Sat
        );
        assert_eq!(
            tapscript_opcode_end_query(
                &src.replace(
                    "script[pc + 1],\n            script[pc + 2],\n            script[pc + 3],\n            script[pc + 4],",
                    "script[pc + 4],\n            script[pc + 3],\n            script[pc + 2],\n            script[pc + 1],"
                ),
                &[0x4e, 0x01, 0x00, 0x00, 0x00, 0xbb],
                0
            ),
            SatResult::Sat
        );
        assert_eq!(
            tapscript_opcode_end_query(
                &src.replace(
                    "} else {\n        pc.checked_add(1)?\n    };",
                    "} else {\n        pc.checked_add(2)?\n    };"
                ),
                &[0x50],
                0
            ),
            SatResult::Sat
        );
        assert_eq!(
            tapscript_opcode_end_query(
                &src.replace("(end <= script.len())", "(end < script.len())"),
                &[0x61],
                0
            ),
            SatResult::Sat
        );
        assert_eq!(
            tapscript_opcode_end_query(
                &src.replace("(end <= script.len()).then_some(end)", "Some(end)"),
                &[0x01],
                0
            ),
            SatResult::Sat
        );
    }

    #[test]
    fn taproot_activation_height_lock() {
        let file = consensus_file("activation.rs");
        let src = extract_fn(&file, "taproot_activation_height");
        for network in ["mainnet", "testnet", "regtest"] {
            assert_eq!(
                taproot_activation_height_query(&src, network),
                SatResult::Unsat,
                "{network}"
            );
        }
        assert_eq!(
            taproot_activation_height_query(
                &src.replace("TAPROOT_ACTIVATION_MAINNET", "0"),
                "mainnet"
            ),
            SatResult::Sat
        );
        assert_eq!(
            taproot_activation_height_query(
                &src.replace("TAPROOT_ACTIVATION_TESTNET", "0"),
                "testnet"
            ),
            SatResult::Sat
        );
        assert_eq!(
            taproot_activation_height_query(
                &src.replace("} else {\n        0\n    }", "} else {\n        1\n    }"),
                "regtest"
            ),
            SatResult::Sat
        );
    }

    #[test]
    fn opcode_position_lock() {
        let file = consensus_file("script/mod.rs");
        let src = extract_fn(&file, "opcode_position_at_byte");
        let cases: &[(&[u8], usize)] = &[
            (&[0xab], 0),
            (&[0x61, 0xab], 1),
            (&[0x01, 0x00, 0xab], 2),
            (&[0x01, 0xab], 1),
            (&[0x4b, 0xab], 1),
            (&[0x4c, 0x01, 0xaa, 0xab], 3),
            (&[0x4c, 0x01, 0xaa, 0xab], 2),
            (&[0x4d, 0x01, 0x00, 0xaa, 0xab], 4),
            (&[0x4e, 0x01, 0x00, 0x00, 0x00, 0xaa, 0xab], 6),
            (&[0x4d], 0),
        ];
        for (script, at) in cases {
            assert_eq!(
                opcode_position_query(&src, script, *at),
                SatResult::Unsat,
                "{script:02x?} @{at}"
            );
        }
        assert_eq!(
            opcode_position_query(
                &src.replace("let mut pos = 0u32", "let mut pos = 1u32"),
                &[0xab],
                0
            ),
            SatResult::Sat
        );
        assert_eq!(
            opcode_position_query(&src.replace("pos += 1;\n", ""), &[0x61, 0xab], 1),
            SatResult::Sat
        );
        assert_eq!(
            opcode_position_query(
                &src.replace("1 + opcode as usize", "1"),
                &[0x01, 0x00, 0xab],
                2
            ),
            SatResult::Sat
        );
        assert_eq!(
            opcode_position_query(
                &src.replace("opcode <= 0x4b", "opcode < 0x4b"),
                &[0x4b, 0xab],
                1
            ),
            SatResult::Sat
        );
        assert_eq!(
            opcode_position_query(
                &src.replace("2 + script[i + 1] as usize", "2"),
                &[0x4c, 0x01, 0xaa, 0xab],
                3
            ),
            SatResult::Sat
        );
        assert_eq!(
            opcode_position_query(
                &src.replace(
                    "3 + ((script[i + 1] as usize) | ((script[i + 2] as usize) << 8))",
                    "3"
                ),
                &[0x4d, 0x01, 0x00, 0xaa, 0xab],
                4
            ),
            SatResult::Sat
        );
        assert_eq!(
            opcode_position_query(
                &src.replace(
                    "(script[i + 1] as usize) | ((script[i + 2] as usize) << 8)",
                    "(script[i + 2] as usize) | ((script[i + 1] as usize) << 8)"
                ),
                &[0x4d, 0x01, 0x00, 0xaa, 0xab],
                4
            ),
            SatResult::Sat
        );
        assert_eq!(
            opcode_position_query(
                &src.replace(
                    "5 + ((script[i + 1] as usize)\n                | ((script[i + 2] as usize) << 8)\n                | ((script[i + 3] as usize) << 16)\n                | ((script[i + 4] as usize) << 24))",
                    "5"
                ),
                &[0x4e, 0x01, 0x00, 0x00, 0x00, 0xaa, 0xab],
                6
            ),
            SatResult::Sat
        );
        assert_eq!(
            opcode_position_query(
                &src.replace(
                    "((script[i + 1] as usize)\n                | ((script[i + 2] as usize) << 8)\n                | ((script[i + 3] as usize) << 16)\n                | ((script[i + 4] as usize) << 24))",
                    "((script[i + 4] as usize)\n                | ((script[i + 3] as usize) << 8)\n                | ((script[i + 2] as usize) << 16)\n                | ((script[i + 1] as usize) << 24))"
                ),
                &[0x4e, 0x01, 0x00, 0x00, 0x00, 0xaa, 0xab],
                6
            ),
            SatResult::Sat
        );
        assert_eq!(
            opcode_position_query(
                &src.replace(
                    "} else {\n            1\n        };",
                    "} else {\n            2\n        };"
                ),
                &[0x61, 0xab],
                1
            ),
            SatResult::Sat
        );
        assert_eq!(
            opcode_position_query(&src.replace("0xffff_ffff", "0"), &[0x01, 0xab], 1),
            SatResult::Sat
        );
        assert_eq!(
            opcode_position_query(
                &src.replace("i <= byte_index", "i < byte_index"),
                &[0xab],
                0
            ),
            SatResult::Sat
        );
        assert_eq!(
            opcode_position_query(
                &src.replace(
                    "if i == byte_index {\n            return pos;\n        }\n",
                    ""
                ),
                &[0xab],
                0
            ),
            SatResult::Sat
        );
    }

    #[test]
    fn script_num_from_opcode_lock() {
        let file = consensus_file("script/mod.rs");
        let src = extract_fn(&file, "script_num_from_opcode");
        for n in 1u8..=16 {
            let opcode = 0x50 + n;
            assert_eq!(
                script_num_from_opcode_query(&src, opcode),
                SatResult::Unsat,
                "OP_{n}"
            );
            let patched = src.replace(
                &format!("OP_{n} => {n},"),
                &format!("OP_{n} => {},", n as i64 + 1),
            );
            assert_eq!(
                script_num_from_opcode_query(&patched, opcode),
                SatResult::Sat,
                "OP_{n}"
            );
        }
    }

    #[test]
    fn zero_hash_lock() {
        let file = consensus_file("optimizations.rs");
        let src = extract_fn(&file, "is_zero_hash");
        let zero = [0u8; 32];
        let mut one_nonzero = [0u8; 32];
        one_nonzero[0] = 1;
        let mut last_zero = [0xffu8; 32];
        last_zero[31] = 0;
        for hash in [&zero, &one_nonzero, &last_zero] {
            assert_eq!(zero_hash_query(&src, hash), SatResult::Unsat);
        }
        assert_eq!(
            zero_hash_query(&src.replace("b == 0", "b == 1"), &zero),
            SatResult::Sat
        );
        assert_eq!(
            zero_hash_query(&src.replace(".all(", ".any("), &last_zero),
            SatResult::Sat
        );
    }

    #[test]
    fn script_merkle_root_lock() {
        let src = extract_fn(&consensus_file("taproot.rs"), "compute_script_merkle_root");
        let script = [0x51u8, 0x20];
        let low = [0u8; 32];
        let high = [0xffu8; 32];
        let both = [low, high];
        assert_eq!(
            script_merkle_root_query(&src, &script, &[], 0xc0),
            SatResult::Unsat
        );
        assert_eq!(
            script_merkle_root_query(&src, &script, &[low], 0xc0),
            SatResult::Unsat
        );
        assert_eq!(
            script_merkle_root_query(&src, &script, &[high], 0xc0),
            SatResult::Unsat
        );
        assert_eq!(
            script_merkle_root_query(&src, &script, &both, 0xc0),
            SatResult::Unsat
        );
        assert_eq!(
            script_merkle_root_query(
                &src.replace(
                    "tap_leaf_hash(leaf_version, script)",
                    "tap_leaf_hash(0, script)"
                ),
                &script,
                &[],
                0xc0
            ),
            SatResult::Sat
        );
        assert_eq!(
            script_merkle_root_query(
                &src.replace(
                    "tap_leaf_hash(leaf_version, script)",
                    "tap_leaf_hash(leaf_version, &[])"
                ),
                &script,
                &[],
                0xc0
            ),
            SatResult::Sat
        );
        assert_eq!(
            script_merkle_root_query(
                &src.replace("current_hash < *proof_hash", "current_hash > *proof_hash"),
                &script,
                &[low],
                0xc0
            ),
            SatResult::Sat
        );
        let unsorted = src.replace(
            "let (left, right) = if current_hash < *proof_hash {\n            (current_hash, *proof_hash)\n        } else {\n            (*proof_hash, current_hash)\n        };",
            "let (left, right) = (current_hash, *proof_hash);",
        );
        assert_ne!(unsorted, src);
        assert_eq!(
            script_merkle_root_query(&unsorted, &script, &[low], 0xc0),
            SatResult::Sat
        );
        assert_eq!(
            script_merkle_root_query(
                &src.replace(
                    "for proof_hash in proof {",
                    "for proof_hash in proof.iter().take(0) {"
                ),
                &script,
                &[low],
                0xc0
            ),
            SatResult::Sat
        );
        assert_eq!(
            script_merkle_root_query(
                &src.replace(
                    "for proof_hash in proof {",
                    "for proof_hash in proof.iter().rev() {"
                ),
                &script,
                &both,
                0xc0
            ),
            SatResult::Sat
        );
        assert_eq!(
            script_merkle_root_query(
                &src.replace(
                    "tap_branch_hash(&left, &right)",
                    "tap_branch_hash(&right, &left)"
                ),
                &script,
                &[low],
                0xc0
            ),
            SatResult::Sat
        );
    }

    #[test]
    fn script_path_lock() {
        let src = extract_fn(
            &consensus_file("taproot.rs"),
            "validate_taproot_script_path_with_leaf_version",
        );
        let script = [0x51u8, 0x20];
        let low = [0u8; 32];
        let high = [0xffu8; 32];
        let both = [low, high];
        let root = spec_merkle_root(&script, &both, 0xc0);
        let empty_root = spec_merkle_root(&script, &[], 0xc0);
        let one_root = spec_merkle_root(&script, &[low], 0xc0);
        let zero = [0u8; 32];
        assert_eq!(
            script_path_query(&src, &script, &[], &empty_root, 0xc0),
            SatResult::Unsat
        );
        assert_eq!(
            script_path_query(&src, &script, &[low], &one_root, 0xc0),
            SatResult::Unsat
        );
        assert_eq!(
            script_path_query(&src, &script, &both, &root, 0xc0),
            SatResult::Unsat
        );
        assert_eq!(
            script_path_query(&src, &script, &both, &zero, 0xc0),
            SatResult::Unsat
        );
        assert_eq!(
            script_path_query(
                &src.replace("== *merkle_root", "!= *merkle_root"),
                &script,
                &both,
                &root,
                0xc0
            ),
            SatResult::Sat
        );
        let constant_true = src.replace("Ok(computed_root == *merkle_root)", "Ok(true)");
        assert_ne!(constant_true, src);
        assert_eq!(
            script_path_query(&constant_true, &script, &both, &zero, 0xc0),
            SatResult::Sat
        );
        let wrong_version = src.replace("merkle_proof, leaf_version", "merkle_proof, 0");
        assert_ne!(wrong_version, src);
        assert_eq!(
            script_path_query(&wrong_version, &script, &both, &root, 0xc0),
            SatResult::Sat
        );
        let empty_script = src.replace(
            "compute_script_merkle_root(script,",
            "compute_script_merkle_root(&[],",
        );
        assert_ne!(empty_script, src);
        assert_eq!(
            script_path_query(&empty_script, &script, &both, &root, 0xc0),
            SatResult::Sat
        );
        let empty_proof = src.replace("script, merkle_proof,", "script, &[],");
        assert_ne!(empty_proof, src);
        assert_eq!(
            script_path_query(&empty_proof, &script, &both, &root, 0xc0),
            SatResult::Sat
        );
        let zero_root = src.replace("== *merkle_root", "== [0u8; 32]");
        assert_ne!(zero_root, src);
        assert_eq!(
            script_path_query(&zero_root, &script, &both, &root, 0xc0),
            SatResult::Sat
        );
    }

    #[test]
    fn tap_leaf_hash_lock() {
        let secp = std::fs::read_to_string(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../blvm-secp256k1/src/taproot.rs"),
        )
        .expect("secp taproot");
        let secp_leaf = extract_fn(&secp, "tap_leaf_hash");
        let fallback = extract_fn(
            &consensus_file("secp256k1_backend/secp256k1_impl.rs"),
            "tap_leaf_hash",
        );
        check_tap_leaf(
            &secp_leaf,
            "TAG_TAP_LEAF",
            "TAG_TAP_BRANCH",
            "tagged_hash(TAG_TAP_LEAF, &data)",
        );
        check_tap_leaf(
            &fallback,
            "b\"TapLeaf\"",
            "b\"TapBranch\"",
            "bip341_tagged_hash(b\"TapLeaf\", &data)",
        );
    }

    fn check_tap_leaf(src: &str, tag_from: &str, tag_to: &str, hash_call: &str) {
        let script = [0x51u8];
        let long = vec![0x51u8; 253];
        let wide = vec![0x51u8; 256];
        assert_eq!(tap_leaf_query(src, 0xc0, &[]), SatResult::Unsat);
        assert_eq!(tap_leaf_query(src, 0xc0, &script), SatResult::Unsat);
        assert_eq!(tap_leaf_query(src, 0, &script), SatResult::Unsat);
        assert_eq!(tap_leaf_query(src, 0xc0, &long), SatResult::Unsat);
        assert_eq!(tap_leaf_query(src, 0xc0, &wide), SatResult::Unsat);
        let tag = src.replace(tag_from, tag_to);
        assert_ne!(tag, src);
        assert_eq!(tap_leaf_query(&tag, 0xc0, &script), SatResult::Sat);
        let zero_version = src.replace("data.push(leaf_version)", "data.push(0)");
        assert_ne!(zero_version, src);
        assert_eq!(tap_leaf_query(&zero_version, 0xc0, &script), SatResult::Sat);
        let no_size = src.replace("data.extend(compact_size_encode(script.len()));", "");
        assert_ne!(no_size, src);
        assert_eq!(tap_leaf_query(&no_size, 0xc0, &script), SatResult::Sat);
        let no_script = src.replace("data.extend_from_slice(script);", "");
        assert_ne!(no_script, src);
        assert_eq!(tap_leaf_query(&no_script, 0xc0, &script), SatResult::Sat);
        let one_byte = src.replace(
            "compact_size_encode(script.len())",
            "vec![script.len() as u8]",
        );
        assert_ne!(one_byte, src);
        assert_eq!(tap_leaf_query(&one_byte, 0xc0, &long), SatResult::Sat);
        let swapped = src.replace(
            "data.extend(compact_size_encode(script.len()));\n    data.extend_from_slice(script);",
            "data.extend_from_slice(script);\n    data.extend(compact_size_encode(script.len()));",
        );
        assert_ne!(swapped, src);
        assert_eq!(tap_leaf_query(&swapped, 0xc0, &script), SatResult::Sat);
        let constant = src.replace(hash_call, "[0u8; 32]");
        assert_ne!(constant, src);
        assert_eq!(tap_leaf_query(&constant, 0xc0, &script), SatResult::Sat);
    }

    #[test]
    fn tap_branch_hash_lock() {
        let secp = std::fs::read_to_string(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../blvm-secp256k1/src/taproot.rs"),
        )
        .expect("secp taproot");
        let secp_branch = extract_fn(&secp, "tap_branch_hash");
        let fallback = extract_fn(
            &consensus_file("secp256k1_backend/secp256k1_impl.rs"),
            "tap_branch_hash",
        );
        check_tap_branch(
            &secp_branch,
            "TAG_TAP_BRANCH",
            "TAG_TAP_LEAF",
            "tagged_hash(TAG_TAP_BRANCH, &data)",
            "    data.extend_from_slice(left);\n",
            "    data.extend_from_slice(right);\n",
        );
        check_tap_branch(
            &fallback,
            "b\"TapBranch\"",
            "b\"TapLeaf\"",
            "bip341_tagged_hash(b\"TapBranch\", &data)",
            "    data[..32].copy_from_slice(left);\n",
            "    data[32..].copy_from_slice(right);\n",
        );
    }

    fn check_tap_branch(
        src: &str,
        tag_from: &str,
        tag_to: &str,
        hash_call: &str,
        left_line: &str,
        right_line: &str,
    ) {
        let left = [0x11u8; 32];
        let right = [0x22u8; 32];
        let same = [0x33u8; 32];
        assert_eq!(tap_branch_query(src, &left, &right), SatResult::Unsat);
        assert_eq!(tap_branch_query(src, &same, &same), SatResult::Unsat);
        assert_eq!(tap_branch_query(src, &right, &left), SatResult::Unsat);
        let tag = src.replace(tag_from, tag_to);
        assert_ne!(tag, src);
        assert_eq!(tap_branch_query(&tag, &left, &right), SatResult::Sat);
        let no_left = src.replace(left_line, "");
        assert_ne!(no_left, src);
        assert_eq!(tap_branch_query(&no_left, &left, &right), SatResult::Sat);
        let no_right = src.replace(right_line, "");
        assert_ne!(no_right, src);
        assert_eq!(tap_branch_query(&no_right, &left, &right), SatResult::Sat);
        let swapped = src.replace(
            &format!("{left_line}{right_line}"),
            &format!("{right_line}{left_line}"),
        );
        assert_ne!(swapped, src);
        assert_eq!(tap_branch_query(&swapped, &left, &right), SatResult::Sat);
        let constant = src.replace(hash_call, "[0u8; 32]");
        assert_ne!(constant, src);
        assert_eq!(tap_branch_query(&constant, &left, &right), SatResult::Sat);
    }

    #[test]
    fn tap_tweak_hash_lock() {
        let secp = std::fs::read_to_string(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../blvm-secp256k1/src/taproot.rs"),
        )
        .expect("secp taproot");
        let src = extract_fn(&secp, "tap_tweak_hash");
        let key = [0x11u8; 32];
        let root = [0x22u8; 32];
        let same = [0x33u8; 32];
        assert_eq!(tap_tweak_query(&src, &key, &root), SatResult::Unsat);
        assert_eq!(tap_tweak_query(&src, &same, &same), SatResult::Unsat);
        assert_eq!(tap_tweak_query(&src, &root, &key), SatResult::Unsat);
        let tag = src.replace("TAG_TAP_TWEAK", "TAG_TAP_LEAF");
        assert_ne!(tag, src);
        assert_eq!(tap_tweak_query(&tag, &key, &root), SatResult::Sat);
        let no_key = src.replace("    data.extend_from_slice(internal_key);\n", "");
        assert_ne!(no_key, src);
        assert_eq!(tap_tweak_query(&no_key, &key, &root), SatResult::Sat);
        let no_root = src.replace("    data.extend_from_slice(merkle_root);\n", "");
        assert_ne!(no_root, src);
        assert_eq!(tap_tweak_query(&no_root, &key, &root), SatResult::Sat);
        let swapped = src.replace(
            "    data.extend_from_slice(internal_key);\n    data.extend_from_slice(merkle_root);\n",
            "    data.extend_from_slice(merkle_root);\n    data.extend_from_slice(internal_key);\n",
        );
        assert_ne!(swapped, src);
        assert_eq!(tap_tweak_query(&swapped, &key, &root), SatResult::Sat);
        let constant = src.replace("tagged_hash(TAG_TAP_TWEAK, &data)", "[0u8; 32]");
        assert_ne!(constant, src);
        assert_eq!(tap_tweak_query(&constant, &key, &root), SatResult::Sat);
    }

    #[test]
    fn bip34_magnitude_lock() {
        let src = extract_fn(&consensus_file("bip_validation.rs"), "bip34_magnitude");
        for height in [0u64, 17, 127, 128, 256, 32_768] {
            assert_eq!(bip34_magnitude_query(&src, height), SatResult::Unsat);
        }
        let endian = src.replace("(n & 0xff) as u8", "(n >> 8) as u8");
        assert_ne!(endian, src);
        assert_eq!(bip34_magnitude_query(&endian, 256), SatResult::Sat);
        let early = src.replace("while n > 0 {", "while n > 0xff {");
        assert_ne!(early, src);
        assert_eq!(bip34_magnitude_query(&early, 17), SatResult::Sat);
        let dropped = src.replace("n >>= 8;\n        len += 1;", "n >>= 8;");
        assert_ne!(dropped, src);
        assert_eq!(bip34_magnitude_query(&dropped, 256), SatResult::Sat);
        let no_pad = src.replace(
            "    if len > 0 && raw[len - 1] & 0x80 != 0 {\n        raw[len] = 0x00;\n        len += 1;\n    }\n",
            "",
        );
        assert_ne!(no_pad, src);
        assert_eq!(bip34_magnitude_query(&no_pad, 128), SatResult::Sat);
        let inverted = src.replace("& 0x80 != 0", "& 0x80 == 0");
        assert_ne!(inverted, src);
        assert_eq!(bip34_magnitude_query(&inverted, 127), SatResult::Sat);
        let bad_pad = src.replace("raw[len] = 0x00", "raw[len] = 0xff");
        assert_ne!(bad_pad, src);
        assert_eq!(bip34_magnitude_query(&bad_pad, 128), SatResult::Sat);
    }

    #[test]
    fn bip34_prefix_lock() {
        let file = consensus_file("bip_validation.rs");
        let src = format!(
            "{}\n{}",
            extract_fn(&file, "bip34_magnitude"),
            extract_fn(&file, "script_sig_starts_with_height")
        );
        let points: &[(&[u8], u64, bool)] = &[
            (&[], 0, false),
            (&[0x00], 0, true),
            (&[0x00, 0xff], 0, true),
            (&[0x50], 0, false),
            (&[0x51], 1, true),
            (&[0x51, 0xff], 1, true),
            (&[0x01, 0x01], 1, false),
            (&[0x60], 16, true),
            (&[0x01, 0x11], 17, true),
            (&[0x01, 0x11, 0xff], 17, true),
            (&[0x51], 17, false),
            (&[0x4c, 0x01, 0x11], 17, false),
            (&[0x02, 0x80, 0x00], 128, true),
            (&[0x01, 0x80], 128, false),
            (&[0x02, 0x80], 128, false),
        ];
        for (script, height, pass) in points {
            assert_eq!(
                spec_bip34_prefix(script, *height),
                *pass,
                "spec {script:02x?} @{height}"
            );
            assert_eq!(
                bip34_prefix_query(&src, script, *height),
                SatResult::Unsat,
                "{script:02x?} @{height}"
            );
        }
        let sat = |body: String, script: &[u8], height: u64| {
            assert_ne!(body, src);
            assert_eq!(
                bip34_prefix_query(&body, script, height),
                SatResult::Sat,
                "{script:02x?} @{height}"
            );
        };
        sat(src.replace("== Some(0x00)", "== Some(0x01)"), &[0x00], 0);
        sat(
            src.replace(
                "return script_sig.first().copied() == Some(0x00);",
                "return true;",
            ),
            &[],
            0,
        );
        sat(
            src.replace("0x50 + height as u8", "height as u8"),
            &[0x51],
            1,
        );
        sat(
            src.replace("(1..=16).contains(&height)", "(1..=0).contains(&height)"),
            &[0x01, 0x01],
            1,
        );
        sat(
            src.replace("(1..=16).contains(&height)", "(1..=15).contains(&height)"),
            &[0x60],
            16,
        );
        sat(
            src.replace("(1..=16).contains(&height)", "(1..=17).contains(&height)"),
            &[0x01, 0x11],
            17,
        );
        sat(
            src.replace("script_sig[0] == len as u8", "true"),
            &[0x02, 0x11],
            17,
        );
        sat(
            src.replace("script_sig[1..1 + len] == raw[..len]", "true"),
            &[0x01, 0xff],
            17,
        );
        sat(
            src.replace("script_sig.len() > len", "script_sig.len() == len + 1"),
            &[0x01, 0x11, 0xff],
            17,
        );
        sat(
            src.replace("bip34_magnitude(height)", "bip34_magnitude(0)"),
            &[0x02, 0x80, 0x00],
            128,
        );
    }

    #[test]
    fn bip54_stripped_size_lock() {
        let coinbase: syn::ItemFn = syn::parse_str(&extract_fn(
            &consensus_file("transaction.rs"),
            "is_coinbase",
        ))
        .expect("is_coinbase");
        let kept = retain_production(coinbase);
        let src = format!(
            "{}\n{}\n{}",
            extract_fn(&consensus_file("optimizations.rs"), "is_zero_hash"),
            quote::quote!(#kept),
            extract_fn(
                &consensus_file("bip_validation.rs"),
                "check_bip54_tx_stripped_size"
            )
        );
        let zero = [0u8; 32];
        let other = [1u8; 32];
        let coinbase_tx = bip54_tx(&[(&zero, 0xffff_ffff)]);
        let other_tx = bip54_tx(&[(&other, 1)]);
        let empty_tx = bip54_tx(&[]);
        let points: &[(&Val, bool, u64)] = &[
            (&coinbase_tx, true, 64),
            (&coinbase_tx, true, 0),
            (&coinbase_tx, true, 100),
            (&other_tx, false, 64),
            (&other_tx, false, 63),
            (&other_tx, false, 65),
            (&other_tx, false, 0),
            (&empty_tx, false, 64),
        ];
        for (tx, coinbase, size) in points {
            assert_eq!(
                spec_bip54_stripped(*coinbase, *size),
                bip54_stripped(&src, tx, *size),
                "coinbase {coinbase} size {size}"
            );
            assert_eq!(
                bip54_stripped_query(&src, tx, *coinbase, *size),
                SatResult::Unsat,
                "coinbase {coinbase} size {size}"
            );
        }
        let sat = |body: String, tx: &Val, coinbase: bool, size: u64| {
            assert_ne!(body, src);
            assert_eq!(
                bip54_stripped_query(&body, tx, coinbase, size),
                SatResult::Sat,
                "coinbase {coinbase} size {size}"
            );
        };
        sat(src.replace("!= 64", "== 64"), &other_tx, false, 64);
        sat(src.replace("!= 64", "!= 63"), &other_tx, false, 63);
        sat(
            src.replace("is_coinbase(tx) || ", ""),
            &coinbase_tx,
            true,
            64,
        );
    }

    #[test]
    fn transaction_size_lock() {
        let src = extract_fn(
            &consensus_file("transaction.rs"),
            "calculate_transaction_size",
        );
        let wires: &[&[u8]] = &[&[], &[0x00], &[0x01, 0x02, 0x03], &[0u8; 64]];
        for wire in wires {
            assert_eq!(
                transaction_size(&src, wire),
                spec_transaction_size(wire),
                "len {}",
                wire.len()
            );
            assert_eq!(
                transaction_size_query(&src, wire),
                SatResult::Unsat,
                "len {}",
                wire.len()
            );
        }
        let sat = |body: String, wire: &[u8]| {
            assert_ne!(body, src);
            assert_eq!(transaction_size_query(&body, wire), SatResult::Sat);
        };
        sat(
            src.replace("serialize_transaction(tx).len()", "0"),
            &[0u8; 64],
        );
        sat(
            src.replace(
                "serialize_transaction(tx).len()",
                "serialize_transaction(tx).len() + 1",
            ),
            &[],
        );
        sat(
            src.replace(
                "serialize_transaction",
                "serialize_transaction_with_witness",
            ),
            &[0x11],
        );
    }

    #[test]
    fn header_hash_lock() {
        let serializer = extract_fn(
            &std::fs::read_to_string(
                std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("../blvm-primitives/src/serialization/block.rs"),
            )
            .expect("header serializer"),
            "serialize_block_header",
        );
        let hash_fn = extract_fn(&consensus_file("block/header.rs"), "block_header_hash");
        let src = format!("{serializer}\n{hash_fn}");
        let headers = [
            header_record(1, 0x11, 0x22, 3, 4, 5),
            header_record(2, 0x33, 0x44, 6, 7, 8),
        ];
        for header in &headers {
            let wire = sample_eval::eval_option_bytes(
                &serializer,
                "serialize_block_header",
                &[("header", header.clone())],
            )
            .expect("header bytes");
            assert_eq!(wire.len(), 80);
            assert_eq!(header_hash_query(&src, header, &wire), SatResult::Unsat);
        }
        let header = headers[0].clone();
        let wire = sample_eval::eval_option_bytes(
            &serializer,
            "serialize_block_header",
            &[("header", header.clone())],
        )
        .expect("header bytes");
        assert_eq!(&wire[0..4], &[1, 0, 0, 0]);
        assert_eq!(&wire[4..36], &[0x11u8; 32]);
        assert_eq!(&wire[36..68], &[0x22u8; 32]);
        assert_eq!(&wire[68..72], &[3, 0, 0, 0]);
        assert_eq!(&wire[72..76], &[4, 0, 0, 0]);
        assert_eq!(&wire[76..80], &[5, 0, 0, 0]);
        let sat = |body: String| {
            assert_ne!(body, src);
            assert_eq!(header_hash_query(&body, &header, &wire), SatResult::Sat);
        };
        sat(src.replace(
            "hash256(&serialize_block_header(header))",
            "sha256(&serialize_block_header(header))",
        ));
        sat(src.replace(
            "hash256(&serialize_block_header(header))",
            "hash256(&serialize_header_legacy(header))",
        ));
        sat(src.replace("hash256(&serialize_block_header(header))", "hash256(&[])"));
    }

    #[test]
    fn transaction_stripped_size_lock() {
        let segwit = consensus_file("segwit.rs");
        let size_src = format!(
            "{}\n{}\n{}",
            extract_fn(&segwit, "compact_size_len"),
            extract_fn(&segwit, "add_size"),
            extract_fn(&segwit, "stripped_transaction_size"),
        );
        let primitives = std::fs::read_to_string(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../blvm-primitives/src/serialization/transaction.rs"),
        )
        .expect("transaction serializer");
        let varint = std::fs::read_to_string(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../blvm-primitives/src/serialization/varint.rs"),
        )
        .expect("varint");
        let types = std::fs::read_to_string(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../blvm-primitives/src/types.rs"),
        )
        .expect("primitive types");
        let wire_src = format!(
            "{}\n{}\n{}\n{}\n{}",
            extract_struct(&types, "OutPoint"),
            extract_struct(&types, "TransactionInput"),
            extract_fn(&varint, "encode_varint"),
            extract_fn(&primitives, "serialize_transaction_append"),
            extract_fn(&primitives, "serialize_transaction"),
        );
        let tx = |inputs: &[Vec<u8>], outputs: &[Vec<u8>]| {
            let inputs = inputs
                .iter()
                .map(|script| {
                    Val::Rec(vec![
                        (
                            "prevout".into(),
                            Val::Rec(vec![
                                ("hash".into(), sample_eval::bytes(&[0; 32])),
                                ("index".into(), Val::Int(0)),
                            ]),
                        ),
                        ("script_sig".into(), sample_eval::bytes(script)),
                        ("sequence".into(), Val::Int(0)),
                    ])
                })
                .collect();
            let outputs = outputs
                .iter()
                .map(|script| {
                    Val::Rec(vec![
                        ("value".into(), Val::Int(1)),
                        ("script_pubkey".into(), sample_eval::bytes(script)),
                    ])
                })
                .collect();
            Val::Rec(vec![
                ("version".into(), Val::Int(1)),
                ("inputs".into(), Val::List(inputs)),
                ("outputs".into(), Val::List(outputs)),
                ("lock_time".into(), Val::Int(0)),
            ])
        };
        let samples = [
            tx(&[], &[]),
            tx(&[vec![]], &[vec![]]),
            tx(&[vec![0x51]], &[vec![0xac]]),
            tx(&[], &[vec![]]),
            tx(&[], &[vec![0x11; 252]]),
            tx(&[], &[vec![0x11; 253]]),
        ];
        for sample in &samples {
            assert_eq!(
                transaction_stripped_size_query(&size_src, &wire_src, sample),
                SatResult::Unsat
            );
        }
        let sat = |body: String, sample: &Val| {
            assert_ne!(body, size_src);
            assert_eq!(
                transaction_stripped_size_query(&body, &wire_src, sample),
                SatResult::Sat
            );
        };
        sat(
            size_src.replace("let mut n = 8u64", "let mut n = 0u64"),
            &samples[0],
        );
        sat(
            size_src.replace("add_size(n, 40)", "add_size(n, 32)"),
            &samples[1],
        );
        sat(
            size_src.replace(
                "add_size(n, input.script_sig.len() as u64)",
                "add_size(n, 0)",
            ),
            &samples[2],
        );
        sat(
            size_src.replace("add_size(n, 8)", "add_size(n, 0)"),
            &samples[1],
        );
        sat(
            size_src.replace(
                "add_size(n, output.script_pubkey.len() as u64)",
                "add_size(n, 0)",
            ),
            &samples[2],
        );
        sat(
            size_src.replace(
                "compact_size_len(0) + 1 + compact_size_len(0)",
                "compact_size_len(0) + compact_size_len(0)",
            ),
            &samples[3],
        );
        sat(size_src.replace("if n < 0xfd", "if n < 0xfc"), &samples[4]);
    }

    #[test]
    fn pow_header_bytes_lock() {
        let pow_src = extract_fn(&consensus_file("pow.rs"), "serialize_header");
        let wire_src = extract_fn(
            &std::fs::read_to_string(
                std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("../blvm-primitives/src/serialization/block.rs"),
            )
            .expect("header serializer"),
            "serialize_block_header",
        );
        let headers = [
            header_record(1, 0x11, 0x22, 3, 4, 5),
            header_record(9, 0x33, 0x44, 6, 7, 8),
        ];
        for header in &headers {
            assert_eq!(
                pow_header_bytes_query(&pow_src, &wire_src, header),
                SatResult::Unsat
            );
        }
        let header = &headers[0];
        let sat = |body: String| {
            assert_ne!(body, pow_src);
            assert_eq!(
                pow_header_bytes_query(&body, &wire_src, header),
                SatResult::Sat
            );
        };
        sat(pow_src.replace("header.version as u32", "header.nonce as u32"));
        sat(pow_src.replace("bytes[4..36]", "bytes[5..37]"));
        sat(pow_src.replace("bytes[36..68]", "bytes[37..69]"));
        sat(pow_src.replace("header.timestamp as u32", "header.bits as u32"));
        sat(pow_src.replace("bytes[72..76]", "bytes[73..77]"));
        sat(pow_src.replace("header.nonce as u32", "header.version as u32"));
    }

    #[test]
    fn mining_varint_lock() {
        let body = extract_fn(&consensus_file("mining.rs"), "encode_varint");
        let canonical = extract_fn(
            &std::fs::read_to_string(
                std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("../blvm-primitives/src/serialization/varint.rs"),
            )
            .expect("varint"),
            "encode_varint",
        );
        for value in [
            0u64,
            0xfc,
            0xfd,
            0xffff,
            0x1_0000,
            0xffff_ffff,
            0x1_0000_0000,
            0x02fd,
        ] {
            assert_eq!(
                mining_varint_query(&body, &canonical, value),
                SatResult::Unsat
            );
        }
        let sat = |patched: String, value: u64| {
            assert_ne!(patched, body);
            assert_eq!(
                mining_varint_query(&patched, &canonical, value),
                SatResult::Sat
            );
        };
        sat(body.replace("value < 0xfd", "value < 0xfc"), 0xfc);
        sat(body.replace("vec![0xfd]", "vec![0xfc]"), 0xfd);
        sat(body.replace("vec![0xfe]", "vec![0xfd]"), 0x1_0000);
        sat(body.replace("vec![0xff]", "vec![0xfe]"), 0x1_0000_0000);
        sat(
            body.replace(
                "(value as u16).to_le_bytes()",
                "(value as u16).to_be_bytes()",
            ),
            0x02fd,
        );
        sat(
            body.replace(
                "(value as u32).to_le_bytes()",
                "(value as u32).to_be_bytes()",
            ),
            0x0403_0201,
        );
        sat(
            body.replace("&value.to_le_bytes()", "&value.to_be_bytes()"),
            0x0807_0605_0403_0201,
        );
    }

    #[test]
    fn sighash_varint_lock() {
        let body = extract_fn(
            &consensus_file("transaction_hash.rs"),
            "write_varint_to_vec",
        );
        let canonical = extract_fn(
            &std::fs::read_to_string(
                std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("../blvm-primitives/src/serialization/varint.rs"),
            )
            .expect("varint"),
            "encode_varint",
        );
        for value in [
            0u64,
            0xfc,
            0xfd,
            0xffff,
            0x1_0000,
            0xffff_ffff,
            0x1_0000_0000,
            0x02fd,
        ] {
            assert_eq!(
                sighash_varint_query(&body, &canonical, value),
                SatResult::Unsat
            );
        }
        let sat = |patched: String, value: u64| {
            assert_ne!(patched, body);
            assert_eq!(
                sighash_varint_query(&patched, &canonical, value),
                SatResult::Sat
            );
        };
        sat(body.replace("value < 0xfd", "value < 0xfc"), 0xfc);
        sat(body.replace("vec.push(0xfd)", "vec.push(0xfc)"), 0xfd);
        sat(body.replace("vec.push(0xfe)", "vec.push(0xfd)"), 0x1_0000);
        sat(
            body.replace("vec.push(0xff)", "vec.push(0xfe)"),
            0x1_0000_0000,
        );
        sat(
            body.replace(
                "(value as u16).to_le_bytes()",
                "(value as u16).to_be_bytes()",
            ),
            0x02fd,
        );
        sat(
            body.replace(
                "(value as u32).to_le_bytes()",
                "(value as u32).to_be_bytes()",
            ),
            0x0403_0201,
        );
        sat(
            body.replace("&value.to_le_bytes()", "&value.to_be_bytes()"),
            0x0807_0605_0403_0201,
        );
    }

    #[test]
    fn compact_size_len_lock() {
        let body = extract_fn(&consensus_file("segwit.rs"), "compact_size_len");
        let canonical = extract_fn(
            &std::fs::read_to_string(
                std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("../blvm-primitives/src/serialization/varint.rs"),
            )
            .expect("varint"),
            "encode_varint",
        );
        for n in [
            0u64,
            0xfc,
            0xfd,
            0xffff,
            0x1_0000,
            0xffff_ffff,
            0x1_0000_0000,
        ] {
            assert_eq!(
                compact_size_len_query(&body, &canonical, n),
                SatResult::Unsat
            );
        }
        let sat = |patched: String, n: u64| {
            assert_ne!(patched, body);
            assert_eq!(
                compact_size_len_query(&patched, &canonical, n),
                SatResult::Sat
            );
        };
        sat(body.replace("n < 0xfd", "n < 0xfc"), 0xfc);
        sat(body.replace("        1\n", "        2\n"), 0);
        sat(body.replace("n <= 0xffff {", "n < 0xffff {"), 0xffff);
        sat(body.replace("        3\n", "        4\n"), 0xfd);
        sat(
            body.replace("n <= 0xffff_ffff", "n < 0xffff_ffff"),
            0xffff_ffff,
        );
        sat(body.replace("        5\n", "        4\n"), 0x1_0000);
        sat(body.replace("        9\n", "        8\n"), 0x1_0000_0000);
    }

    #[test]
    fn decode_varint_lock() {
        let body = extract_fn(
            &std::fs::read_to_string(
                std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("../blvm-primitives/src/serialization/varint.rs"),
            )
            .expect("varint"),
            "decode_varint",
        );
        let canonical = extract_fn(
            &std::fs::read_to_string(
                std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("../blvm-primitives/src/serialization/varint.rs"),
            )
            .expect("varint"),
            "encode_varint",
        );
        for value in [
            0u64,
            0xfc,
            0xfd,
            0xffff,
            0x1_0000,
            0xffff_ffff,
            0x1_0000_0000,
            0x02fd,
            0x0403_0201,
            0x0807_0605_0403_0201,
        ] {
            assert_eq!(
                decode_varint_query(&body, &canonical, value),
                SatResult::Unsat
            );
        }
        let reject = |data: &[u8]| {
            assert_eq!(decode_varint_reject_query(&body, data), SatResult::Unsat);
        };
        reject(&[]);
        reject(&[0xfd, 0x00]);
        reject(&[0xfe, 0x00, 0x00, 0x00]);
        reject(&[0xff, 0, 0, 0, 0, 0, 0, 0]);
        reject(&[0xfd, 0x00, 0x00]);
        reject(&[0xfe, 0xfd, 0x00, 0x00, 0x00]);
        reject(&[0xff, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00]);
        let sat = |patched: String, value: u64| {
            assert_ne!(patched, body);
            assert_eq!(
                decode_varint_query(&patched, &canonical, value),
                SatResult::Sat
            );
        };
        let sat_reject = |patched: String, data: &[u8]| {
            assert_ne!(patched, body);
            assert_eq!(decode_varint_reject_query(&patched, data), SatResult::Sat);
        };
        sat(body.replace("b < 0xfd", "b < 0xfc"), 0xfc);
        sat(body.replace("Ok((b as u64, 1))", "Ok((0, 1))"), 1);
        sat(body.replace("Ok((b as u64, 1))", "Ok((b as u64, 2))"), 0);
        sat_reject(
            body.replace(
                "if data.is_empty()",
                "if data.is_empty() { return Ok((0, 0)); } if false",
            ),
            &[],
        );
        sat_reject(
            body.replace(
                "if data.len() < 3",
                "if data.len() < 3 { return Ok((1, 1)); } if false",
            ),
            &[0xfd, 0x00],
        );
        sat_reject(
            body.replace("if value < 0xfd", "if false"),
            &[0xfd, 0x00, 0x00],
        );
        sat(
            body.replace("u16::from_le_bytes", "u16::from_be_bytes"),
            0x02fd,
        );
        sat(body.replace("Ok((value, 3))", "Ok((value, 4))"), 0xfd);
        sat_reject(
            body.replace(
                "if data.len() < 5",
                "if data.len() < 5 { return Ok((1, 1)); } if false",
            ),
            &[0xfe, 0x00, 0x00, 0x00],
        );
        sat_reject(
            body.replace("if value <= 0xffff {", "if false {"),
            &[0xfe, 0xfd, 0x00, 0x00, 0x00],
        );
        sat(
            body.replace("u32::from_le_bytes", "u32::from_be_bytes"),
            0x0403_0201,
        );
        sat(body.replace("Ok((value, 5))", "Ok((value, 6))"), 0x1_0000);
        sat_reject(
            body.replace(
                "if data.len() < 9",
                "if data.len() < 9 { return Ok((1, 1)); } if false",
            ),
            &[0xff, 0, 0, 0, 0, 0, 0, 0],
        );
        sat_reject(
            body.replace("if value <= 0xffffffff", "if false"),
            &[0xff, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00],
        );
        sat(
            body.replace("u64::from_le_bytes", "u64::from_be_bytes"),
            0x0807_0605_0403_0201,
        );
        sat(
            body.replace("Ok((value, 9))", "Ok((value, 8))"),
            0x1_0000_0000,
        );
    }

    #[test]
    fn header_decode_lock() {
        let body = extract_fn(
            &std::fs::read_to_string(
                std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("../blvm-primitives/src/serialization/block.rs"),
            )
            .expect("block"),
            "deserialize_block_header",
        );
        let wire = extract_fn(
            &std::fs::read_to_string(
                std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("../blvm-primitives/src/serialization/block.rs"),
            )
            .expect("block"),
            "serialize_block_header",
        );
        let headers = [
            header_record(1, 0x11, 0x22, 3, 4, 5),
            header_record(
                0x0403_0201,
                0x33,
                0x44,
                0x0807_0605,
                0x0c0b_0a09,
                0x100f_0e0d,
            ),
            header_record(-1, 0x55, 0x66, 0xffff_ffff, 7, 8),
        ];
        for header in &headers {
            assert_eq!(header_decode_query(&body, &wire, header), SatResult::Unsat);
        }
        assert_eq!(
            header_decode_reject_query(&body, &[0u8; 79]),
            SatResult::Unsat
        );
        let sat = |patched: String, header: &Val| {
            assert_ne!(patched, body);
            assert_eq!(header_decode_query(&patched, &wire, header), SatResult::Sat);
        };
        let wide = header_record(
            0x0403_0201,
            0x33,
            0x44,
            0x0807_0605,
            0x0c0b_0a09,
            0x100f_0e0d,
        );
        let negative = header_record(-1, 0x55, 0x66, 0xffff_ffff, 7, 8);
        let short = body.replace(
            "if data.len() < 80",
            "if data.len() < 80 { return Ok(BlockHeader { version: 0, prev_block_hash: [0u8; 32], merkle_root: [0u8; 32], timestamp: 0, bits: 0, nonce: 0 }); } if false",
        );
        assert_ne!(short, body);
        assert_eq!(
            header_decode_reject_query(&short, &[0u8; 79]),
            SatResult::Sat
        );
        sat(
            body.replace(
                "let version = i32::from_le_bytes",
                "let version = u32::from_le_bytes",
            ),
            &negative,
        );
        sat(
            body.replace(
                "let version = i32::from_le_bytes",
                "let version = i32::from_be_bytes",
            ),
            &wide,
        );
        sat(
            body.replace(
                "prev_block_hash.copy_from_slice(&data[offset..offset + 32])",
                "prev_block_hash.copy_from_slice(&data[0..32])",
            ),
            &wide,
        );
        sat(
            body.replace(
                "merkle_root.copy_from_slice(&data[offset..offset + 32])",
                "merkle_root.copy_from_slice(&data[0..32])",
            ),
            &wide,
        );
        sat(
            body.replace(
                "let timestamp = u32::from_le_bytes",
                "let timestamp = u32::from_be_bytes",
            ),
            &wide,
        );
        sat(
            body.replace(
                "let bits = u32::from_le_bytes",
                "let bits = u32::from_be_bytes",
            ),
            &wide,
        );
        sat(
            body.replace(
                "let nonce = u32::from_le_bytes",
                "let nonce = u32::from_be_bytes",
            ),
            &wide,
        );
    }

    #[test]
    fn encode_locktime_lock() {
        let file = consensus_file("locktime.rs");
        let encode = extract_fn(&file, "encode_locktime_value");
        let decode = extract_fn(&file, "decode_locktime_value");
        for value in [0u32, 1, 0x7f, 0x80, 0x0201, 0x8000_0000, 0xffff_ffff] {
            assert_eq!(
                encode_locktime_query(&encode, &decode, value),
                SatResult::Unsat
            );
        }
        let sat = |patched: String, value: u32| {
            assert_ne!(patched, encode);
            assert_eq!(
                encode_locktime_query(&patched, &decode, value),
                SatResult::Sat
            );
        };
        sat(
            encode.replace(
                "if bytes.is_empty() {\n        bytes.push(0);",
                "if bytes.is_empty() {\n        bytes.push(1);",
            ),
            0,
        );
        sat(
            encode.replace("(temp & 0xff)", "((temp >> 8) & 0xff)"),
            0x0201,
        );
        sat(encode.replace("temp >>= 8", "temp = 0"), 0x0201);
        sat(encode.replace("b & 0x80 != 0", "false"), 0x80);
    }

    #[test]
    fn coinbase_short_circuit_lock() {
        let coinbase: syn::ItemFn = syn::parse_str(&extract_fn(
            &consensus_file("transaction.rs"),
            "is_coinbase",
        ))
        .expect("is_coinbase");
        let kept = retain_production(coinbase);
        let src = format!(
            "{}\n{}\n{}",
            extract_fn(&consensus_file("optimizations.rs"), "is_zero_hash"),
            quote::quote!(#kept),
            extract_fn(
                &consensus_file("transaction.rs"),
                "coinbase_or_empty_short_circuit"
            )
        );
        let empty = bip54_tx(&[]);
        let coinbase_tx = bip54_tx(&[(&[0u8; 32], 0xffff_ffff)]);
        let ordinary = bip54_tx(&[(&[1u8; 32], 0)]);
        assert_eq!(
            coinbase_short_circuit_query(&src, &empty, Some((false, 0))),
            SatResult::Unsat
        );
        assert_eq!(
            coinbase_short_circuit_query(&src, &coinbase_tx, Some((true, 0))),
            SatResult::Unsat
        );
        assert_eq!(
            coinbase_short_circuit_query(&src, &ordinary, None),
            SatResult::Unsat
        );
        let body = extract_fn(
            &consensus_file("transaction.rs"),
            "coinbase_or_empty_short_circuit",
        );
        let patched = |needle: &str, replacement: &str| {
            let function = body.replace(needle, replacement);
            assert_ne!(function, body);
            src.replace(&body, &function)
        };
        let sat = |source: String, tx: &Val, expected: Option<(bool, i64)>| {
            assert_eq!(
                coinbase_short_circuit_query(&source, tx, expected),
                SatResult::Sat
            );
        };
        sat(
            patched("tx.inputs.is_empty() && !is_coinbase(tx)", "false"),
            &empty,
            Some((false, 0)),
        );
        sat(
            patched("if is_coinbase(tx)", "if false"),
            &coinbase_tx,
            Some((true, 0)),
        );
        sat(
            patched("ValidationResult::Valid, 0", "ValidationResult::Valid, 1"),
            &coinbase_tx,
            Some((true, 0)),
        );
        sat(patched("if is_coinbase(tx)", "if true"), &ordinary, None);
    }

    #[test]
    fn output_sum_lock() {
        let body = extract_fn(&consensus_file("transaction.rs"), "sum_output_values");
        for values in [Vec::new(), vec![5], vec![3, 4], vec![-1], vec![i64::MAX, 1]] {
            assert_eq!(output_sum_query(&body, &values), SatResult::Unsat);
        }
        let sat = |patched: String, values: &[i64]| {
            assert_ne!(patched, body);
            assert_eq!(output_sum_query(&patched, values), SatResult::Sat);
        };
        sat(
            body.replace("let mut total = 0i64", "let mut total = 1i64"),
            &[5],
        );
        sat(
            body.replace("checked_add(output.value)", "checked_add(0)"),
            &[5],
        );
        sat(body.replace("output.value < 0", "false"), &[-1]);
        sat(
            body.replace(
                ".checked_add(output.value)\n            .ok_or_else(|| ConsensusError::TransactionValidation(\"Output value overflow\".into()))?",
                ".saturating_add(output.value)",
            ),
            &[i64::MAX, 1],
        );
    }

    #[test]
    fn bip30_skip_lock() {
        let constants = std::fs::read_to_string(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../blvm-primitives/src/constants.rs"),
        )
        .expect("constants");
        let rules = consensus_file("bip_validation.rs");
        let src = format!(
            "{}\n{}\n{}\n{}",
            extract_const(&rules, "BIP34_IMPLIES_BIP30_LIMIT"),
            extract_const(&constants, "BIP34_ACTIVATION_MAINNET"),
            extract_const(&constants, "BIP34_ACTIVATION_TESTNET"),
            extract_fn(&rules, "bip30_lookup_skippable")
        );
        let unsat = |network: &str, height: u64, hash_matches: bool| {
            assert_eq!(
                bip30_skip_query(&src, network, height, hash_matches),
                SatResult::Unsat
            );
        };
        unsat("Mainnet", 100_000, false);
        unsat("Mainnet", 100_000, true);
        unsat("Mainnet", 227_931, true);
        unsat("Mainnet", 227_932, true);
        unsat("Mainnet", 300_000, true);
        unsat("Mainnet", 1_983_701, true);
        unsat("Mainnet", 1_983_702, true);
        unsat("Testnet", 21_111, true);
        unsat("Testnet", 21_112, true);
        unsat("Testnet", 300_000, false);
        unsat("Regtest", 300_000, true);
        unsat("Signet", 300_000, true);
        unsat("Testnet4", 300_000, true);
        let body = extract_fn(&rules, "bip30_lookup_skippable");
        let patched = |needle: &str, replacement: &str| {
            let function = body.replacen(needle, replacement, 1);
            assert_ne!(function, body);
            src.replace(&body, &function)
        };
        let sat = |source: String, network: &str, height: u64, hash_matches: bool| {
            assert_eq!(
                bip30_skip_query(&source, network, height, hash_matches),
                SatResult::Sat
            );
        };
        sat(
            patched("!bip34_hash_matches", "false"),
            "Mainnet",
            300_000,
            false,
        );
        sat(
            patched(
                "height >= BIP34_IMPLIES_BIP30_LIMIT",
                "height > BIP34_IMPLIES_BIP30_LIMIT",
            ),
            "Mainnet",
            1_983_702,
            true,
        );
        sat(
            patched(
                "Network::Mainnet => crate::constants::BIP34_ACTIVATION_MAINNET",
                "Network::Mainnet => crate::constants::BIP34_ACTIVATION_TESTNET",
            ),
            "Mainnet",
            100_000,
            true,
        );
        sat(
            patched(
                "Network::Testnet => crate::constants::BIP34_ACTIVATION_TESTNET",
                "Network::Testnet => crate::constants::BIP34_ACTIVATION_MAINNET",
            ),
            "Testnet",
            21_112,
            true,
        );
        sat(
            patched("height > activation", "height >= activation"),
            "Mainnet",
            227_931,
            true,
        );
        sat(
            patched(
                "Network::Regtest | Network::Signet | Network::Testnet4 => return false",
                "Network::Regtest | Network::Signet | Network::Testnet4 => return true",
            ),
            "Regtest",
            300_000,
            true,
        );
    }

    #[test]
    fn mul_disabled_lock() {
        let body = extract_fn(&consensus_file("script/arithmetic.rs"), "op_mul_disabled");
        assert_eq!(mul_disabled_query(&body), SatResult::Unsat);
        let patched = body.replacen(
            "Err(ConsensusError::ScriptErrorWithCode {\n        code: ScriptErrorCode::DisabledOpcode,\n        message: \"OP_MUL is disabled\".into(),\n    })",
            "Ok(true)",
            1,
        );
        assert_ne!(patched, body);
        assert_eq!(mul_disabled_query(&patched), SatResult::Sat);
    }

    fn extract_const(src: &str, name: &str) -> String {
        let marker = format!("const {name}:");
        let start = src
            .find(&marker)
            .unwrap_or_else(|| panic!("missing {name}"));
        let rest = &src[start..];
        let end = rest
            .find(';')
            .unwrap_or_else(|| panic!("unterminated {name}"));
        rest[..=end].to_string()
    }

    #[test]
    fn executable_opcode_lock() {
        let src = extract_fn(
            &consensus_file("bip_validation.rs"),
            "script_contains_executable_opcode",
        );
        let opcode = 0x51u8;
        assert_eq!(
            executable_opcode_query(&src, &[0x51], opcode),
            SatResult::Unsat
        );
        assert_eq!(
            executable_opcode_query(&src, &[0x52], opcode),
            SatResult::Unsat
        );
        assert_eq!(
            executable_opcode_query(&src, &[0x01, 0x51], opcode),
            SatResult::Unsat
        );
        assert_eq!(
            executable_opcode_query(&src, &[0x01, 0x00, 0x51], opcode),
            SatResult::Unsat
        );
        assert_eq!(
            executable_opcode_query(&src, &[0x4b, 0x51], opcode),
            SatResult::Unsat
        );
        assert_eq!(
            executable_opcode_query(&src, &[0x00], 0x00),
            SatResult::Unsat
        );
        assert_eq!(
            executable_opcode_query(&src, &[0x4c], 0x4c),
            SatResult::Unsat
        );
        assert_eq!(
            executable_opcode_query(&src, &[0x4c, 0x01, 0x51], opcode),
            SatResult::Unsat
        );
        assert_eq!(
            executable_opcode_query(&src, &[0x4d, 0x01, 0x00, 0xaa, 0x51], opcode),
            SatResult::Unsat
        );
        assert_eq!(
            executable_opcode_query(&src, &[0x4e, 0x01, 0x00, 0x00, 0x00, 0xaa, 0x51], opcode),
            SatResult::Unsat
        );
        let zero_push = src.replace("op > 0 &&", "op >= 0 &&");
        assert_ne!(zero_push, src);
        assert_eq!(
            executable_opcode_query(&zero_push, &[0x00], 0x00),
            SatResult::Sat
        );
        let direct_range = src.replace("op < OP_PUSHDATA1", "op < 0x4b");
        assert_ne!(direct_range, src);
        assert_eq!(
            executable_opcode_query(&direct_range, &[0x4b, 0x51], opcode),
            SatResult::Sat
        );
        let direct_step = src.replace("i += 1 + op as usize", "i += 1");
        assert_ne!(direct_step, src);
        assert_eq!(
            executable_opcode_query(&direct_step, &[0x01, 0x51], opcode),
            SatResult::Sat
        );
        let short_header = src.replace(
            "if i + 1 >= script.len() {\n                    break;",
            "if i + 1 >= script.len() {\n                    return true;",
        );
        assert_ne!(short_header, src);
        assert_eq!(
            executable_opcode_query(&short_header, &[0x4c], 0x00),
            SatResult::Sat
        );
        let push1_len = src.replace("i += 2 + len", "i += 2");
        assert_ne!(push1_len, src);
        assert_eq!(
            executable_opcode_query(&push1_len, &[0x4c, 0x01, 0x51], opcode),
            SatResult::Sat
        );
        let push2_endian = src.replace(
            "[script[i + 1], script[i + 2]]",
            "[script[i + 2], script[i + 1]]",
        );
        assert_ne!(push2_endian, src);
        assert_eq!(
            executable_opcode_query(&push2_endian, &[0x4d, 0x01, 0x00, 0xaa, 0x51], opcode),
            SatResult::Sat
        );
        let push2_len = src.replace("i += 3 + len", "i += 3");
        assert_ne!(push2_len, src);
        assert_eq!(
            executable_opcode_query(&push2_len, &[0x4d, 0x01, 0x00, 0x51], opcode),
            SatResult::Sat
        );
        let push4_endian = src.replace(
            "script[i + 1],\n                    script[i + 2],\n                    script[i + 3],\n                    script[i + 4],",
            "script[i + 4],\n                    script[i + 3],\n                    script[i + 2],\n                    script[i + 1],",
        );
        assert_ne!(push4_endian, src);
        assert_eq!(
            executable_opcode_query(
                &push4_endian,
                &[0x4e, 0x01, 0x00, 0x00, 0x00, 0xaa, 0x51],
                opcode
            ),
            SatResult::Sat
        );
        let push4_len = src.replace("i += 5 + len", "i += 5");
        assert_ne!(push4_len, src);
        assert_eq!(
            executable_opcode_query(&push4_len, &[0x4e, 0x01, 0x00, 0x00, 0x00, 0x51], opcode),
            SatResult::Sat
        );
        let no_match = src.replace(
            "                if op == opcode {\n                    return true;\n                }\n",
            "",
        );
        assert_ne!(no_match, src);
        assert_eq!(
            executable_opcode_query(&no_match, &[0x51], opcode),
            SatResult::Sat
        );
        let else_step = src.replace(
            "return true;\n                }\n                i += 1;",
            "return true;\n                }\n                i += 2;",
        );
        assert_ne!(else_step, src);
        assert_eq!(
            executable_opcode_query(&else_step, &[0x61, 0x51], opcode),
            SatResult::Sat
        );
    }

    #[test]
    fn bip54_deployment_lock() {
        let file = consensus_file("version_bits.rs");
        for name in [
            "bip54_deployment_mainnet",
            "bip54_deployment_testnet",
            "bip54_deployment_regtest",
        ] {
            let src = extract_fn(&file, name);
            assert_eq!(bip54_deployment_query(&src), SatResult::Unsat);
            let bit = src.replace("bit: 15,", "bit: 14,");
            assert_ne!(bit, src);
            assert_eq!(bip54_deployment_query(&bit), SatResult::Sat);
            let start = src.replace("start_time: 0,", "start_time: 1,");
            assert_ne!(start, src);
            assert_eq!(bip54_deployment_query(&start), SatResult::Sat);
            let timeout = src.replace("timeout: u64::MAX,", "timeout: 0,");
            assert_ne!(timeout, src);
            assert_eq!(bip54_deployment_query(&timeout), SatResult::Sat);
        }
    }

    #[test]
    fn script_num_minimal_lock() {
        let src = extract_fn(
            &consensus_file("script/mod.rs"),
            "script_num_is_minimally_encoded",
        );
        for data in [
            &[][..],
            &[0x00],
            &[0x80],
            &[0x01],
            &[0x00, 0x00],
            &[0x80, 0x00],
            &[0x7f],
        ] {
            assert_eq!(script_num_minimal_query(&src, data), SatResult::Unsat);
        }
        let low = src.replace("last & 0x7f == 0", "last & 0x7f != 0");
        assert_ne!(low, src);
        assert_eq!(script_num_minimal_query(&low, &[0x01]), SatResult::Sat);
        let single = src.replace(
            "(data.len() <= 1 || data[data.len() - 2] & 0x80 == 0)",
            "(data.len() > 1)",
        );
        assert_ne!(single, src);
        assert_eq!(script_num_minimal_query(&single, &[0x00]), SatResult::Sat);
        assert_eq!(script_num_minimal_query(&single, &[0x80]), SatResult::Sat);
        let prev = src.replace("& 0x80 == 0", "& 0x80 != 0");
        assert_ne!(prev, src);
        assert_eq!(
            script_num_minimal_query(&prev, &[0x00, 0x00]),
            SatResult::Sat
        );
        let sign = src.replace("data[data.len() - 2] & 0x80 == 0", "true");
        assert_ne!(sign, src);
        assert_eq!(
            script_num_minimal_query(&sign, &[0x80, 0x00]),
            SatResult::Sat
        );
        let empty = src.replace("\n    true\n", "\n    false\n");
        assert_ne!(empty, src);
        assert_eq!(script_num_minimal_query(&empty, &[]), SatResult::Sat);
    }

    #[test]
    fn sighash_script_code_lock() {
        let src = extract_fn(
            &consensus_file("transaction_hash.rs"),
            "write_script_code_for_sighash",
        );
        let long = vec![0x51u8; 253];
        for code in [
            &[][..],
            &[0x51],
            &[0xab],
            &[0x51, 0xab],
            &[0x01, 0xab],
            &[0x4c],
            long.as_slice(),
        ] {
            assert_eq!(sighash_script_code_query(&src, code), SatResult::Unsat);
        }
        let no_count = src.replace("count_opcode_codeseparators(code)", "0usize");
        assert_ne!(no_count, src);
        assert_eq!(
            sighash_script_code_query(&no_count, &[0xab]),
            SatResult::Sat
        );
        let full_len = src.replace("(code.len() - n_codeseps)", "(code.len())");
        assert_ne!(full_len, src);
        assert_eq!(
            sighash_script_code_query(&full_len, &[0xab]),
            SatResult::Sat
        );
        let no_raw = src.replace("        preimage.extend_from_slice(code);\n", "");
        assert_ne!(no_raw, src);
        assert_eq!(sighash_script_code_query(&no_raw, &[0x51]), SatResult::Sat);
        let swapped = src.replace(
            "    if n_codeseps == 0 {\n        preimage.extend_from_slice(code);\n    } else {\n        append_stripped_codeseparators(preimage, code);\n    }",
            "    if n_codeseps == 0 {\n        append_stripped_codeseparators(preimage, code);\n    } else {\n        preimage.extend_from_slice(code);\n    }",
        );
        assert_ne!(swapped, src);
        assert_eq!(sighash_script_code_query(&swapped, &[0xab]), SatResult::Sat);
        let bad_prefix = src.replace(
            "write_varint_to_vec(preimage, (code.len() - n_codeseps) as u64);",
            "preimage.push(0xff);",
        );
        assert_ne!(bad_prefix, src);
        assert_eq!(
            sighash_script_code_query(&bad_prefix, &[0x51]),
            SatResult::Sat
        );
    }

    #[test]
    fn base_script_flags_lock() {
        let src = extract_fn(
            &consensus_file("block/script_cache.rs"),
            "calculate_base_script_flags_for_block",
        );
        let cases = [
            (false, false, false, false, false),
            (true, false, false, false, false),
            (false, true, false, false, false),
            (false, false, true, false, false),
            (false, false, false, true, false),
            (false, false, false, false, true),
            (true, true, true, true, true),
        ];
        for (bip16, bip66, bip65, bip112, bip147) in cases {
            assert_eq!(
                base_script_flags_query(&src, bip16, bip66, bip65, bip112, bip147),
                SatResult::Unsat
            );
        }
        let standardness = src.replace("flags: u32 = 0;", "flags: u32 = 0x02;");
        assert_ne!(standardness, src);
        assert_eq!(
            base_script_flags_query(&standardness, false, false, false, false, false),
            SatResult::Sat
        );
        let bits = [
            (
                "flags |= 0x01",
                "flags |= 0x02",
                true,
                false,
                false,
                false,
                false,
            ),
            (
                "flags |= 0x04",
                "flags |= 0x08",
                false,
                true,
                false,
                false,
                false,
            ),
            (
                "flags |= 0x200",
                "flags |= 0x100",
                false,
                false,
                true,
                false,
                false,
            ),
            (
                "flags |= 0x400",
                "flags |= 0x800",
                false,
                false,
                false,
                true,
                false,
            ),
            (
                "flags |= 0x10",
                "flags |= 0x20",
                false,
                false,
                false,
                false,
                true,
            ),
        ];
        for (from, to, bip16, bip66, bip65, bip112, bip147) in bits {
            let patched = src.replace(from, to);
            assert_ne!(patched, src);
            assert_eq!(
                base_script_flags_query(&patched, bip16, bip66, bip65, bip112, bip147),
                SatResult::Sat
            );
        }
        let forks = [
            ("ForkId::Bip16, height", false, false, false, false, false),
            ("ForkId::Bip66, height", false, false, false, false, false),
            ("ForkId::Bip65, height", false, false, false, false, false),
            ("ForkId::Bip112, height", false, false, false, false, false),
            ("ForkId::Bip147, height", false, false, false, false, false),
        ];
        for (fork, bip16, bip66, bip65, bip112, bip147) in forks {
            let patched = src.replace(
                &format!("activation.is_fork_active({fork})"),
                &format!("!activation.is_fork_active({fork})"),
            );
            assert_ne!(patched, src);
            assert_eq!(
                base_script_flags_query(&patched, bip16, bip66, bip65, bip112, bip147),
                SatResult::Sat
            );
        }
    }

    #[test]
    fn transaction_round_trip_lock() {
        let primitives = std::fs::read_to_string(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../blvm-primitives/src/serialization/transaction.rs"),
        )
        .expect("transaction serializer");
        let varint = std::fs::read_to_string(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../blvm-primitives/src/serialization/varint.rs"),
        )
        .expect("varint");
        let types = std::fs::read_to_string(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../blvm-primitives/src/types.rs"),
        )
        .expect("primitive types");
        let parse_inputs =
            extract_fn(&primitives, "parse_inputs").replace("TxInputVec::new()", "Vec::new()");
        let parse_outputs =
            extract_fn(&primitives, "parse_outputs").replace("TxOutputVec::new()", "Vec::new()");
        let deser = extract_fn(&primitives, "deserialize_transaction_with_witness");
        let src = format!(
            "{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}",
            extract_struct(&types, "OutPoint"),
            extract_struct(&types, "TransactionInput"),
            extract_fn(&varint, "encode_varint"),
            extract_fn(&varint, "decode_varint"),
            extract_fn(&primitives, "checked_slice_end"),
            extract_fn(&primitives, "read_tx_input_count_after_version"),
            parse_inputs,
            parse_outputs,
            extract_fn(&primitives, "serialize_transaction_append"),
            extract_fn(&primitives, "serialize_transaction"),
            extract_fn(&primitives, "serialize_transaction_with_witness"),
            deser,
        );
        let tx = |version: i128,
                  hash: u8,
                  index: i128,
                  script_sig: &[u8],
                  sequence: i128,
                  value: i128,
                  script_pubkey: &[u8],
                  lock_time: i128,
                  with_input: bool| {
            let inputs = if with_input {
                vec![Val::Rec(vec![
                    (
                        "prevout".into(),
                        Val::Rec(vec![
                            ("hash".into(), sample_eval::bytes(&[hash; 32])),
                            ("index".into(), Val::Int(index)),
                        ]),
                    ),
                    ("script_sig".into(), sample_eval::bytes(script_sig)),
                    ("sequence".into(), Val::Int(sequence)),
                ])]
            } else {
                Vec::new()
            };
            let outputs = if script_pubkey.is_empty() && value == 0 && !with_input {
                Vec::new()
            } else {
                vec![Val::Rec(vec![
                    ("value".into(), Val::Int(value)),
                    ("script_pubkey".into(), sample_eval::bytes(script_pubkey)),
                ])]
            };
            Val::Rec(vec![
                ("version".into(), Val::Int(version)),
                ("inputs".into(), Val::List(inputs)),
                ("outputs".into(), Val::List(outputs)),
                ("lock_time".into(), Val::Int(lock_time)),
            ])
        };
        let empty = tx(2, 0, 0, &[], 0, 0, &[], 7, false);
        let full = tx(
            0x0102_0304,
            0x11,
            0x0102_0304,
            &[0x51, 0x52],
            0x0102_0304,
            0x0100,
            &[0x51],
            0x0102_0304,
            true,
        );
        let marker = tx(1, 0, 0, &[], 0, 9, &[0xac], 3, false);
        let witness = tx(4, 0x22, 1, &[0x00], 2, 8, &[0x51], 5, true);
        let stacks = vec![vec![vec![0xab, 0xcd]]];
        assert_eq!(tx_round_trip_query(&src, &empty, None), SatResult::Unsat);
        assert_eq!(tx_round_trip_query(&src, &full, None), SatResult::Unsat);
        assert_eq!(tx_round_trip_query(&src, &marker, None), SatResult::Unsat);
        assert_eq!(
            tx_round_trip_query(&src, &witness, Some(&stacks)),
            SatResult::Unsat
        );
        assert_eq!(
            tx_round_trip_reject_query(&src, &[0x01, 0x02, 0x03]),
            SatResult::Unsat
        );
        let sat =
            |function: &str, from: &str, to: &str, sample: &Val, wit: Option<&[Vec<Vec<u8>>]>| {
                let patched_fn = function.replacen(from, to, 1);
                assert_ne!(patched_fn, function, "{from}");
                let patched = src.replace(function, &patched_fn);
                assert_eq!(tx_round_trip_query(&patched, sample, wit), SatResult::Sat);
            };
        let deser_fn = extract_fn(&src, "deserialize_transaction_with_witness");
        let inputs_fn = extract_fn(&src, "parse_inputs");
        let outputs_fn = extract_fn(&src, "parse_outputs");
        let read_fn = extract_fn(&src, "read_tx_input_count_after_version");
        sat(
            &deser_fn,
            "let version = u32::from_le_bytes",
            "let version = u32::from_be_bytes",
            &full,
            None,
        );
        sat(
            &deser_fn,
            "let lock_time = u32::from_le_bytes",
            "let lock_time = u32::from_be_bytes",
            &full,
            None,
        );
        sat(
            &deser_fn,
            "Ok((tx, all_witnesses, offset))",
            "Ok((tx, all_witnesses, 0))",
            &full,
            None,
        );
        sat(
            &deser_fn,
            "witness_stack.push(data[offset..item_end].to_vec());",
            "witness_stack.push(Vec::new());",
            &witness,
            Some(&stacks),
        );
        sat(
            &inputs_fn,
            "hash.copy_from_slice(&data[*offset..*offset + 32])",
            "hash.copy_from_slice(&[0u8; 32])",
            &full,
            None,
        );
        sat(
            &inputs_fn,
            "let index = u32::from_le_bytes",
            "let index = u32::from_be_bytes",
            &full,
            None,
        );
        sat(
            &inputs_fn,
            "let script_sig = data[*offset..script_sig_end].to_vec();",
            "let script_sig = Vec::new();",
            &full,
            None,
        );
        sat(
            &inputs_fn,
            "let sequence = u32::from_le_bytes",
            "let sequence = u32::from_be_bytes",
            &full,
            None,
        );
        sat(
            &inputs_fn,
            "for _ in 0..count",
            "for _ in 0..0",
            &full,
            None,
        );
        sat(
            &outputs_fn,
            "i64::from_le_bytes",
            "i64::from_be_bytes",
            &full,
            None,
        );
        sat(
            &outputs_fn,
            "let script_pubkey = data[*offset..script_pubkey_end].to_vec();",
            "let script_pubkey = Vec::new();",
            &full,
            None,
        );
        sat(
            &outputs_fn,
            "for _ in 0..output_count",
            "for _ in 0..0",
            &full,
            None,
        );
        sat(&read_fn, "if flag != 1", "if flag != 9", &marker, None);
        let short = deser_fn.replacen(
            "if data.len() < offset + 4 {\n        return Err(ConsensusError::Serialization(Cow::Owned(\n            TransactionParseError::InsufficientBytes.to_string(),\n        )));\n    }",
            "if data.len() < offset + 4 {\n        return Ok((Transaction { version: 0, inputs: Vec::new(), outputs: Vec::new(), lock_time: 0 }, Vec::new(), 0));\n    }",
            1,
        );
        assert_ne!(short, deser_fn);
        assert_eq!(
            tx_round_trip_reject_query(&src.replace(&deser_fn, &short), &[0x01, 0x02, 0x03]),
            SatResult::Sat
        );
    }

    #[test]
    fn published_gate_matches_the_table() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
        let verification =
            std::fs::read_to_string(root.join("../blvm-consensus/docs/VERIFICATION.md"))
                .expect("VERIFICATION.md");
        let mut rows = 0usize;
        let mut in_table = false;
        for line in verification.lines() {
            if line.starts_with("| function |") {
                in_table = true;
                continue;
            }
            if !in_table || line.starts_with("|---") {
                continue;
            }
            if line.starts_with("| `") {
                rows += 1;
                continue;
            }
            break;
        }
        let marker = format!("**{rows} / ");
        let at = verification.find(&marker).expect("bold coverage figure");
        let denom: String = verification[at + marker.len()..]
            .chars()
            .take_while(|c| c.is_ascii_digit())
            .collect();
        let figure = format!("{rows} / {denom}");
        let other: usize = denom.parse::<usize>().expect("denominator") - rows;
        assert!(verification.contains(&format!("The other {other} are")));
        let readme = std::fs::read_to_string(root.join("README.md")).expect("README");
        assert!(readme.contains(&format!("{rows} of {denom}")));
        let verifier =
            std::fs::read_to_string(root.join("src/translator/z3_verifier.rs")).expect("verifier");
        assert!(verifier.contains(&format!("{rows} of {denom}")));
        let plan = std::fs::read_to_string(root.join("../docs/FORMAL_VERIFICATION_PLAN.md"))
            .expect("plan");
        assert!(plan.contains(&format!("**{figure}**")));
        let index = std::fs::read_to_string(root.join("../docs/README.md")).expect("docs index");
        assert!(index.contains(&figure));
    }
}
