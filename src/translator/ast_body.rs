//! Facts taken from a parsed function body.
//!
//! A query asks this walk what the syntax tree does. It does not search the
//! source text for a line.

use syn::visit::Visit;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CmpOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

#[derive(Clone, Debug, Default)]
pub struct Key {
    pub idents: Vec<String>,
    pub lit: Option<i128>,
    pub bool_lit: Option<bool>,
    pub index: Option<i128>,
}

impl Key {
    pub fn has(&self, name: &str) -> bool {
        self.idents.iter().any(|ident| ident == name)
    }
}

#[derive(Clone, Debug)]
pub struct Cmp {
    pub left: Key,
    pub op: CmpOp,
    pub right: Key,
}

#[derive(Clone, Debug)]
pub struct Bit {
    pub or: bool,
    pub left: Key,
    pub lit: i128,
}

#[derive(Clone, Debug)]
pub struct Call {
    pub path: Vec<String>,
    pub args: Vec<Key>,
    pub negated: Vec<String>,
}

#[derive(Clone, Debug)]
pub struct Method {
    pub recv: Key,
    pub name: String,
    pub args: Vec<Key>,
}

#[derive(Clone, Debug)]
pub struct AddAssign {
    pub name: String,
    pub by: i128,
}

#[derive(Clone, Debug)]
pub struct IndexStore {
    pub base: String,
    pub index: i128,
    pub value: i128,
}

#[derive(Clone, Debug)]
pub struct Arm {
    pub pat: Vec<String>,
    pub cmps: Vec<Cmp>,
    pub calls: Vec<Call>,
    pub or_count: usize,
}

#[derive(Clone, Debug, Default)]
pub struct Analysis {
    pub cmps: Vec<Cmp>,
    pub bits: Vec<Bit>,
    pub calls: Vec<Call>,
    pub methods: Vec<Method>,
    pub adds: Vec<AddAssign>,
    pub stores: Vec<IndexStore>,
    pub arms: Vec<Arm>,
    /// Comparisons inside `if let Some(_) = time_context`.
    pub time_context: Vec<Cmp>,
    pub time_context_present: bool,
    /// Visit order of the merkle compare and the odd-length pad mask.
    pub marks: Vec<&'static str>,
    pub early_non_coinbase: bool,
    pub divs: Vec<(Key, Key)>,
    pub shifts: Vec<(Key, Key)>,
}

pub fn parse_fn(src: &str) -> syn::ItemFn {
    syn::parse_str(src).unwrap_or_else(|err| {
        let head: String = src.chars().take(180).collect();
        panic!("function parse: {err}\n{head}")
    })
}

pub fn analyze(src: &str) -> Analysis {
    let func = parse_fn(src);
    let mut out = Analysis::default();
    walk_block(&func.block, &mut out);
    out
}

pub fn key_of(expr: &syn::Expr) -> Key {
    match expr {
        syn::Expr::Path(path) => Key {
            idents: path_idents(&path.path),
            ..Key::default()
        },
        syn::Expr::Field(field) => {
            let mut key = key_of(&field.base);
            key.idents.push(field.member_name());
            key
        }
        syn::Expr::Lit(lit) => Key {
            lit: lit_int(&lit.lit),
            bool_lit: match &lit.lit {
                syn::Lit::Bool(value) => Some(value.value),
                _ => None,
            },
            ..Key::default()
        },
        syn::Expr::Paren(inner) => key_of(&inner.expr),
        syn::Expr::Group(inner) => key_of(&inner.expr),
        syn::Expr::Reference(inner) => key_of(&inner.expr),
        syn::Expr::Unary(op) => key_of(&op.expr),
        syn::Expr::Cast(cast) => key_of(&cast.expr),
        syn::Expr::Repeat(repeat) => {
            let elem = key_of(&repeat.expr).lit;
            let len = key_of(&repeat.len).lit;
            let mut key = Key::default();
            if elem == Some(0) && len == Some(32) {
                key.idents.push("zero32".into());
            }
            key
        }
        syn::Expr::MethodCall(call) => {
            let mut key = key_of(&call.receiver);
            key.idents.push(call.method.to_string());
            key
        }
        syn::Expr::Index(index) => {
            let mut key = key_of(&index.expr);
            key.index = key_of(&index.index).lit;
            key
        }
        syn::Expr::Binary(bin)
            if matches!(bin.op, syn::BinOp::BitAnd(_) | syn::BinOp::BitOr(_)) =>
        {
            key_of(&bin.left)
        }
        _ => Key::default(),
    }
}

fn path_idents(path: &syn::Path) -> Vec<String> {
    path.segments
        .iter()
        .map(|seg| seg.ident.to_string())
        .collect()
}

fn lit_int(lit: &syn::Lit) -> Option<i128> {
    match lit {
        syn::Lit::Int(value) => value.base10_parse().ok(),
        syn::Lit::Bool(_) => None,
        _ => None,
    }
}

fn cmp_op(op: &syn::BinOp) -> Option<CmpOp> {
    Some(match op {
        syn::BinOp::Eq(_) => CmpOp::Eq,
        syn::BinOp::Ne(_) => CmpOp::Ne,
        syn::BinOp::Lt(_) => CmpOp::Lt,
        syn::BinOp::Le(_) => CmpOp::Le,
        syn::BinOp::Gt(_) => CmpOp::Gt,
        syn::BinOp::Ge(_) => CmpOp::Ge,
        _ => return None,
    })
}

fn walk_block(block: &syn::Block, out: &mut Analysis) {
    for stmt in &block.stmts {
        walk_stmt(stmt, out);
    }
}

fn walk_stmt(stmt: &syn::Stmt, out: &mut Analysis) {
    match stmt {
        syn::Stmt::Local(local) => {
            if let Some(init) = &local.init {
                walk_expr(&init.expr, out);
            }
        }
        syn::Stmt::Expr(expr, _) => walk_expr(expr, out),
        syn::Stmt::Macro(_) | syn::Stmt::Item(_) => {}
    }
}

fn walk_expr(expr: &syn::Expr, out: &mut Analysis) {
    match expr {
        syn::Expr::Binary(bin) => {
            if let Some(op) = cmp_op(&bin.op) {
                let left = key_of(&bin.left);
                let right = key_of(&bin.right);
                if left.has("hashes") && op == CmpOp::Eq {
                    out.marks.push("merkle-eq");
                }
                out.cmps.push(Cmp { left, op, right });
            }
            if matches!(bin.op, syn::BinOp::BitAnd(_) | syn::BinOp::BitOr(_)) {
                if let Some(lit) = key_of(&bin.right).lit {
                    let left = key_of(&bin.left);
                    if left.has("len") && lit == 1 {
                        out.marks.push("len-and-1");
                    }
                    out.bits.push(Bit {
                        or: matches!(bin.op, syn::BinOp::BitOr(_)),
                        left,
                        lit,
                    });
                }
            }
            if matches!(bin.op, syn::BinOp::Div(_)) {
                out.divs.push((key_of(&bin.left), key_of(&bin.right)));
            }
            if matches!(bin.op, syn::BinOp::Shr(_)) {
                out.shifts.push((key_of(&bin.left), key_of(&bin.right)));
            }
            walk_expr(&bin.left, out);
            walk_expr(&bin.right, out);
        }
        syn::Expr::Assign(assign) => {
            if let syn::Expr::Index(index) = &*assign.left {
                if let (Some(base), Some(at), Some(value)) = (
                    key_of(&index.expr).idents.last().cloned(),
                    key_of(&index.index).lit,
                    key_of(&assign.right).lit,
                ) {
                    out.stores.push(IndexStore {
                        base,
                        index: at,
                        value,
                    });
                }
            }
            walk_expr(&assign.left, out);
            walk_expr(&assign.right, out);
        }
        syn::Expr::Call(call) => {
            if let syn::Expr::Path(path) = &*call.func {
                let mut negated = Vec::new();
                let args = call
                    .args
                    .iter()
                    .map(|arg| {
                        if let syn::Expr::Unary(op) = arg {
                            if matches!(op.op, syn::UnOp::Not(_)) {
                                negated.extend(key_of(&op.expr).idents);
                            }
                        }
                        key_of(arg)
                    })
                    .collect();
                out.calls.push(Call {
                    path: path_idents(&path.path),
                    args,
                    negated,
                });
            }
            walk_expr(&call.func, out);
            for arg in &call.args {
                walk_expr(arg, out);
            }
        }
        syn::Expr::MethodCall(call) => {
            out.methods.push(Method {
                recv: key_of(&call.receiver),
                name: call.method.to_string(),
                args: call.args.iter().map(key_of).collect(),
            });
            walk_expr(&call.receiver, out);
            for arg in &call.args {
                walk_expr(arg, out);
            }
        }
        syn::Expr::If(item) => {
            if not_ident(&item.cond, "is_coinbase") && returns_true(&item.then_branch) {
                out.early_non_coinbase = true;
            }
            let in_time = is_time_context(&item.cond);
            if in_time {
                out.time_context_present = true;
                let before = out.cmps.len();
                walk_block(&item.then_branch, out);
                out.time_context.extend(out.cmps[before..].iter().cloned());
            } else {
                walk_expr(&item.cond, out);
                walk_block(&item.then_branch, out);
            }
            if let Some((_, else_expr)) = &item.else_branch {
                walk_expr(else_expr, out);
            }
        }
        syn::Expr::Match(item) => {
            walk_expr(&item.expr, out);
            for arm in &item.arms {
                let start_cmps = out.cmps.len();
                let start_calls = out.calls.len();
                walk_expr(&arm.body, out);
                out.arms.push(Arm {
                    pat: pat_idents(&arm.pat),
                    cmps: out.cmps[start_cmps..].to_vec(),
                    calls: out.calls[start_calls..].to_vec(),
                    or_count: or_count(&arm.body),
                });
            }
        }
        syn::Expr::Block(block) => walk_block(&block.block, out),
        syn::Expr::Loop(item) => walk_block(&item.body, out),
        syn::Expr::While(item) => {
            walk_expr(&item.cond, out);
            walk_block(&item.body, out);
        }
        syn::Expr::ForLoop(item) => {
            walk_expr(&item.expr, out);
            walk_block(&item.body, out);
        }
        syn::Expr::Return(ret) => {
            if let Some(inner) = &ret.expr {
                walk_expr(inner, out);
            }
        }
        syn::Expr::Closure(closure) => walk_expr(&closure.body, out),
        syn::Expr::Array(array) => {
            for elem in &array.elems {
                walk_expr(elem, out);
            }
        }
        syn::Expr::Repeat(repeat) => {
            walk_expr(&repeat.expr, out);
            walk_expr(&repeat.len, out);
        }
        syn::Expr::Index(index) => {
            walk_expr(&index.expr, out);
            walk_expr(&index.index, out);
        }
        syn::Expr::Field(field) => walk_expr(&field.base, out),
        syn::Expr::Cast(cast) => walk_expr(&cast.expr, out),
        syn::Expr::Unary(op) => walk_expr(&op.expr, out),
        syn::Expr::Reference(inner) => walk_expr(&inner.expr, out),
        syn::Expr::Paren(inner) => walk_expr(&inner.expr, out),
        syn::Expr::Group(inner) => walk_expr(&inner.expr, out),
        syn::Expr::Try(item) => walk_expr(&item.expr, out),
        syn::Expr::Range(range) => {
            if let Some(start) = &range.start {
                walk_expr(start, out);
            }
            if let Some(end) = &range.end {
                walk_expr(end, out);
            }
        }
        syn::Expr::Let(binder) => {
            walk_expr(&binder.expr, out);
        }
        syn::Expr::Tuple(tuple) => {
            for elem in &tuple.elems {
                walk_expr(elem, out);
            }
        }
        _ => {}
    }
    if let syn::Expr::Binary(bin) = expr {
        if let syn::BinOp::AddAssign(_) = bin.op {
            if let (Some(name), Some(by)) = (
                key_of(&bin.left).idents.last().cloned(),
                key_of(&bin.right).lit,
            ) {
                out.adds.push(AddAssign { name, by });
            }
        }
    }
}

fn not_ident(expr: &syn::Expr, name: &str) -> bool {
    let syn::Expr::Unary(op) = expr else {
        return false;
    };
    matches!(op.op, syn::UnOp::Not(_)) && key_of(&op.expr).has(name)
}

fn returns_true(block: &syn::Block) -> bool {
    block.stmts.iter().any(|stmt| match stmt {
        syn::Stmt::Expr(syn::Expr::Return(ret), _) => ret
            .expr
            .as_ref()
            .is_some_and(|expr| key_of(expr).bool_lit == Some(true)),
        _ => false,
    })
}
fn is_time_context(cond: &syn::Expr) -> bool {
    let syn::Expr::Let(binder) = cond else {
        return false;
    };
    pat_idents(&binder.pat).iter().any(|name| name == "Some")
        && key_of(&binder.expr).has("time_context")
}

fn pat_idents(pat: &syn::Pat) -> Vec<String> {
    match pat {
        syn::Pat::Path(path) => path_idents(&path.path),
        syn::Pat::TupleStruct(tuple) => path_idents(&tuple.path),
        syn::Pat::Ident(ident) => vec![ident.ident.to_string()],
        syn::Pat::Wild(_) => vec!["_".into()],
        syn::Pat::Or(or) => or.cases.iter().flat_map(pat_idents).collect(),
        syn::Pat::Reference(refer) => pat_idents(&refer.pat),
        syn::Pat::Type(typed) => pat_idents(&typed.pat),
        _ => Vec::new(),
    }
}

fn or_count(expr: &syn::Expr) -> usize {
    let mut n = 0;
    or_count_into(expr, &mut n);
    n
}

fn or_count_into(expr: &syn::Expr, n: &mut usize) {
    match expr {
        syn::Expr::Binary(bin) => {
            if matches!(bin.op, syn::BinOp::Or(_)) {
                *n += 1;
            }
            or_count_into(&bin.left, n);
            or_count_into(&bin.right, n);
        }
        syn::Expr::Block(block) => {
            for stmt in &block.block.stmts {
                if let syn::Stmt::Expr(inner, _) = stmt {
                    or_count_into(inner, n);
                }
            }
        }
        syn::Expr::Paren(inner) => or_count_into(&inner.expr, n),
        syn::Expr::Group(inner) => or_count_into(&inner.expr, n),
        _ => {}
    }
}

pub fn idents_in(expr: &syn::Expr) -> Vec<String> {
    let mut names = Vec::new();
    struct Collect<'a>(&'a mut Vec<String>);
    impl syn::visit::Visit<'_> for Collect<'_> {
        fn visit_ident(&mut self, ident: &syn::Ident) {
            self.0.push(ident.to_string());
        }
    }
    Collect(&mut names).visit_expr(expr);
    names
}

trait FieldName {
    fn member_name(&self) -> String;
}

impl FieldName for syn::ExprField {
    fn member_name(&self) -> String {
        match &self.member {
            syn::Member::Named(ident) => ident.to_string(),
            syn::Member::Unnamed(index) => index.index.to_string(),
        }
    }
}

pub fn cmp_between<'a>(cmps: &'a [Cmp], left: &str, right: &str) -> Option<&'a Cmp> {
    cmps.iter()
        .find(|cmp| cmp.left.has(left) && cmp.right.has(right))
}

pub fn call_named(calls: &[Call], name: &str) -> bool {
    calls
        .iter()
        .any(|call| call.path.last().is_some_and(|seg| seg == name))
}

pub fn method_named(methods: &[Method], name: &str) -> bool {
    methods.iter().any(|method| method.name == name)
}

pub fn arm_named<'a>(arms: &'a [Arm], name: &str) -> Option<&'a Arm> {
    arms.iter()
        .find(|arm| arm.pat.iter().any(|seg| seg == name))
}
