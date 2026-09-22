//! Lock queries over the production `cfg` arm.
//!
//! The formula is built from that arm. Unpatched `body ∧ ¬clause` is UNSAT.
//! A source patch that breaks the clause makes the same query SAT.
//! The MIR text is checked afterwards: the compiled compare must be the
//! operator this translation used.

use syn::visit::Visit;
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
            let arg = quote::quote!(#node).to_string();
            self.facts.dup.present = true;
            let txid_only = arg.contains("txid");
            self.facts.dup.full_prevout = arg.contains("prevout") && !txid_only;
        }
        if name == "update" {
            let arg = quote::quote!(#node).to_string();
            if arg.contains("flags") {
                self.facts.cache_updates_flags = true;
            }
        }
        syn::visit::visit_expr_method_call(self, node);
    }

    fn visit_expr_binary(&mut self, node: &'ast syn::ExprBinary) {
        let text = quote::quote!(#node).to_string();
        if text.contains("MAX_MONEY") {
            let op = match node.op {
                syn::BinOp::Gt(_) => MoneyOp::Gt,
                syn::BinOp::Ge(_) => MoneyOp::Ge,
                _ => MoneyOp::Absent,
            };
            if op != MoneyOp::Absent {
                self.facts.money.push(MoneySite {
                    lt_zero: false,
                    cast_u64: text.contains("as u64")
                        || text.contains("value_u64")
                        || text.contains("total_u64"),
                    op,
                });
            }
        }
        if matches!(node.op, syn::BinOp::Lt(_))
            && text.contains("value")
            && text.contains('0')
            && !text.contains("MAX_MONEY")
        {
            self.facts.money.push(MoneySite {
                lt_zero: true,
                cast_u64: false,
                op: MoneyOp::Absent,
            });
        }
        if text.contains("signature") && text.contains("73") && matches!(node.op, syn::BinOp::Gt(_))
        {
            self.facts.der_len_gt = Some(73);
        }
        if text.contains("signature") && text.contains("74") && matches!(node.op, syn::BinOp::Gt(_))
        {
            self.facts.der_len_gt = Some(74);
        }
        syn::visit::visit_expr_binary(self, node);
    }
}

pub fn facts_of(func: &syn::ItemFn) -> ProductionFacts {
    let kept = retain_production(func.clone());
    let mut v = FactVisit::new();
    v.visit_block(&kept.block);
    let text = quote::quote!(#kept).to_string();
    v.facts.der_high_bit =
        text.contains("signature [4] & 0x80") || text.contains("signature[4] & 0x80");
    v.facts.der_leading_zero =
        text.contains("signature [4] == 0x00") || text.contains("signature[4] == 0x00");
    v.facts.der_tag_30 = text.contains("0x30");
    v.facts.der_rejects_31 = text.contains("!= 0x30") && !text.contains("0x31");
    v.facts.merkle_eq_present = text.contains("hashes [pos] ==") || text.contains("hashes[pos] ==");
    v.facts.merkle_eq_before_pad = v.facts.merkle_eq_present && eq_before_pad(&kept);
    v.facts.sighash_single_le_one =
        text.contains("result [0] = 1") || text.contains("result[0] = 1");
    v.facts
}

fn eq_before_pad(func: &syn::ItemFn) -> bool {
    let text = quote::quote!(#func).to_string();
    let eq = text
        .find("hashes [pos] ==")
        .or_else(|| text.find("hashes[pos] =="));
    let pad = text.find("len () & 1").or_else(|| text.find("len() & 1"));
    match (eq, pad) {
        (Some(e), Some(p)) => e < p,
        (Some(_), None) => true,
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
    let step = pure_addend(src, "i += ");
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

fn pure_addend(src: &str, prefix: &str) -> u64 {
    let mut other = None;
    for line in src.lines() {
        let t = line.trim();
        let Some(rest) = t.strip_prefix(prefix) else {
            continue;
        };
        let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
        if digits.is_empty() || !rest[digits.len()..].starts_with(';') {
            continue;
        }
        let n: u64 = digits.parse().unwrap_or(0);
        if n == 1 {
            return 1;
        }
        other.get_or_insert(n);
    }
    other.unwrap_or(0)
}

/// OP_IF pushes a control block. The next depth is `depth + 1`.
pub fn control_step_query(src: &str) -> SatResult {
    let pushes = src.contains("control_stack.push");
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
    let body_mask = hex_mask(src).unwrap_or(0);
    let negated = src.contains("== 0") && !src.contains("!= 0");
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
    let body_mask = hex_mask(src).unwrap_or(0);
    let uses_or = src.contains('|') && !src.contains('&');
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
    let is_height_cmp = if src.contains("locktime <= ") {
        "le"
    } else if src.contains("locktime < ") {
        "lt"
    } else if src.contains("locktime >= ") {
        "ge"
    } else if src.contains("locktime > ") {
        "gt"
    } else {
        "absent"
    };
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
    let ge = src.contains(">=");
    let types = src.contains("locktime_types_match");
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

/// Accept iff `hash < target`. The hash is sha256(sha256(header)).
pub fn pow_compare_query(strict_lt: bool) -> SatResult {
    let spec_strict = crate::parser::spec_expr::header_hash_strict();
    check(|ctx, solver| {
        let hash = BV::new_const(ctx, "hash", 32);
        let target = BV::new_const(ctx, "target", 32);
        let accepted = if strict_lt {
            hash.bvult(&target)
        } else {
            hash.bvule(&target)
        };
        solver.assert(&hash._eq(&target));
        if spec_strict {
            solver.assert(&accepted);
        } else {
            solver.assert(&accepted.not());
        }
    })
}

/// Version 0 is rejected. Version 1 is not.
pub fn header_version_query(src: &str, version: u64) -> SatResult {
    let floor = crate::parser::spec_expr::version_min();
    let lt_floor = src.contains(&format!("header.version < {floor}"));
    let le_floor = src.contains(&format!("header.version <= {floor}"));
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

/// A timestamp equal to the median is accepted. One below it is not.
pub fn header_mtp_query(src: &str, below: bool) -> SatResult {
    if !crate::parser::spec_expr::median_past_is_lower_bound() {
        panic!("spec H05 is not timestamp ≥ MedianTimePast");
    }
    let lt = src.contains("header.timestamp < ctx.median_time_past");
    let le = src.contains("header.timestamp <= ctx.median_time_past");
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
        if below {
            solver.assert(&rejected.not());
        } else {
            solver.assert(&rejected);
        }
    })
}

/// v0 is 20 or 32 bytes. v1 is 32 bytes.
pub fn witness_program_query(src: &str) -> SatResult {
    let v0_20 = src.contains("SEGWIT_P2WPKH_LENGTH");
    let v0_32 = src.contains("SEGWIT_P2WSH_LENGTH");
    let v1_32 = src.contains("TAPROOT_PROGRAM_LENGTH");
    check(|ctx, solver| {
        let len = BV::new_const(ctx, "len", 32);
        let (short, long) = crate::parser::spec_expr::witness_program_lengths();
        let twenty = BV::from_u64(ctx, short, 32);
        let thirty_two = BV::from_u64(ctx, long, 32);
        let mut v0 = Bool::from_bool(ctx, false);
        if v0_20 {
            v0 |= len._eq(&twenty);
        }
        if v0_32 {
            v0 |= len._eq(&thirty_two);
        }
        let v1 = if v1_32 {
            len._eq(&thirty_two)
        } else {
            Bool::from_bool(ctx, false)
        };
        let clause_v0 = len._eq(&twenty) | len._eq(&thirty_two);
        let clause_v1 = len._eq(&thirty_two);
        let clause = v0._eq(&clause_v0) & v1._eq(&clause_v1);
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

fn hex_mask(src: &str) -> Option<u64> {
    let rest = src.split("0x").nth(1)?;
    let digits: String = rest
        .chars()
        .take_while(|c| c.is_ascii_hexdigit() || *c == '_')
        .filter(|c| *c != '_')
        .collect();
    u64::from_str_radix(&digits, 16).ok()
}

/// CHECKSIG pushes 1 iff the uninterpreted verifier returned true.
/// `if true { 1 }` and a flipped `is_valid` bit are SAT.
pub fn checksig_query(src: &str) -> SatResult {
    let flipped = src.contains("if is_valid { 0 } else { 1 }");
    let constant = src.contains("if true { 1 }");
    let calls = src.contains("verify_signature(")
        || src.contains("verify_ecdsa")
        || src.contains("verify_schnorr")
        || src.contains("verify_tapscript_schnorr_signature(");
    check(|ctx, solver| {
        let verifier = Bool::new_const(ctx, "verifier");
        let result = if flipped {
            verifier.not()
        } else if calls && !constant {
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

    fn extract_fn(src: &str, name: &str) -> String {
        let marker = format!("fn {name}(");
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

    fn calls_verifier(src: &str) -> bool {
        src.contains("verify_signature(")
            || src.contains("verify_ecdsa_direct(")
            || src.contains("verify_schnorr")
    }

    fn fast_path_calls_verifier(file: &str, body: &str) -> bool {
        if calls_verifier(body) {
            return true;
        }
        for callee in [
            "verify_p2wpkh_inline",
            "verify_p2pkh_inline",
            "verify_p2pk_inline",
        ] {
            if body.contains(&format!("{callee}(")) {
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
        let arm = checksig
            .split("OP_CHECKSIG =>")
            .nth(1)
            .expect("OP_CHECKSIG arm");
        assert!(calls_verifier(arm));
        assert_eq!(checksig_query(arm), SatResult::Unsat);
        let constant = arm.replace("if is_valid { 1 } else { 0 }", "if true { 1 } else { 0 }");
        assert_eq!(checksig_query(&constant), SatResult::Sat);
        let flipped = arm.replace(
            "if is_valid { 1 } else { 0 }",
            "if is_valid { 0 } else { 1 }",
        );
        assert_eq!(checksig_query(&flipped), SatResult::Sat);

        for (name, gate) in [
            ("try_verify_p2pk_fast_path", "len != 35 && len != 67"),
            ("try_verify_p2pkh_fast_path", "script_pubkey.len() != 25"),
            ("try_verify_p2sh_fast_path", "script_pubkey.len() != 23"),
            ("try_verify_p2wpkh_fast_path", "script_pubkey.len() != 22"),
        ] {
            let body = extract_fn(&script, name);
            assert!(body.contains(gate), "{name} has no fall-through gate");
            assert!(
                fast_path_calls_verifier(&script, &body),
                "{name} skips the verifier"
            );
            assert_eq!(fast_path_query(true, true), SatResult::Unsat);
            let missed = body.replacen(gate, "false", 1);
            assert!(!missed.contains(gate), "{name} gate still present");
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
        assert!(check.contains("hash_value < target"));
        assert_eq!(check.matches("Sha256::digest").count(), 2);
        assert_eq!(pow_compare_query(true), SatResult::Unsat);
        assert_eq!(pow_compare_query(false), SatResult::Sat);
        assert_eq!(pow_double_hash_query(2), SatResult::Unsat);
        assert_eq!(pow_double_hash_query(1), SatResult::Sat);

        let witness = consensus_file("witness.rs");
        let program = extract_fn(&witness, "validate_witness_program_length");
        assert_eq!(witness_program_query(&program), SatResult::Unsat);
        assert_eq!(
            witness_program_query(&program.replace("SEGWIT_P2WPKH_LENGTH", "SEGWIT_P2WSH_LENGTH")),
            SatResult::Sat
        );
        assert_eq!(
            witness_program_query(&program.replace("TAPROOT_PROGRAM_LENGTH", "0")),
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
        let dropped = valid.replace("header.timestamp < ctx.median_time_past", "false");
        assert_eq!(header_mtp_query(&dropped, true), SatResult::Sat);
        let le = valid.replace(
            "header.timestamp < ctx.median_time_past",
            "header.timestamp <= ctx.median_time_past",
        );
        assert_eq!(header_mtp_query(&le, false), SatResult::Sat);
    }
}
