//! Evaluate a patched consensus function on concrete arguments.
//!
//! The body is the `syn` tree of that function. An unknown construct fails
//! the query. A token search of the source is not this evaluator.

use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq)]
pub enum Val {
    Bool(bool),
    Int(i128),
    Bytes(Vec<u8>),
    List(Vec<Val>),
    Tuple(Vec<Val>),
    Rec(Vec<(String, Val)>),
    Iter(Vec<Val>),
    Opt(Option<Box<Val>>),
    Name(String),
    Unit,
}

pub fn bytes(data: &[u8]) -> Val {
    Val::Bytes(data.to_vec())
}

pub fn stack(items: &[Vec<u8>]) -> Val {
    Val::List(items.iter().cloned().map(Val::Bytes).collect())
}

pub fn eval_bool_entry(src: &str, entry: &str, args: &[(&str, Val)]) -> bool {
    eval_bool_entry_with(src, entry, args, &|_, _| None)
}

pub fn eval_bool_entry_with(
    src: &str,
    entry: &str,
    args: &[(&str, Val)],
    host: &dyn Fn(&str, &[Val]) -> Option<Val>,
) -> bool {
    match eval_named(src, Some(entry), args, host) {
        Val::Bool(value) => value,
        other => panic!("sample eval expected a bool, got {other:?}"),
    }
}

pub fn eval_bool(src: &str, args: &[(&str, Val)]) -> bool {
    eval_bool_with(src, args, &|_, _| None)
}

pub fn eval_bool_with(
    src: &str,
    args: &[(&str, Val)],
    host: &dyn Fn(&str, &[Val]) -> Option<Val>,
) -> bool {
    match eval(src, args, host) {
        Val::Bool(value) => value,
        other => panic!("sample eval expected a bool, got {other:?}"),
    }
}

pub fn eval_u64(src: &str, args: &[(&str, Val)]) -> u64 {
    eval_u64_with(src, args, &|_, _| None)
}

pub fn eval_opt_int(src: &str, args: &[(&str, Val)]) -> Option<i128> {
    match eval(src, args, &|_, _| None) {
        Val::Opt(None) => None,
        Val::Opt(Some(inner)) => Some(as_int(&inner)),
        Val::Int(value) => Some(value),
        other => panic!("sample eval expected an option, got {other:?}"),
    }
}

pub fn eval_bound(src: &str, args: &[(&str, Val)], name: &str) -> Val {
    let (_value, ctx) = run(src, None, args, &|_, _| None);
    ctx.get(name)
        .unwrap_or_else(|| panic!("sample eval missing binding {name}"))
}

pub fn eval_int(src: &str, args: &[(&str, Val)]) -> i128 {
    match eval(src, args, &|_, _| None) {
        Val::Int(value) => value,
        other => panic!("sample eval expected an int, got {other:?}"),
    }
}

pub fn eval_val(src: &str, args: &[(&str, Val)]) -> Val {
    eval(src, args, &|_, _| None)
}

pub fn eval_val_with(
    src: &str,
    args: &[(&str, Val)],
    host: &dyn Fn(&str, &[Val]) -> Option<Val>,
) -> Val {
    eval(src, args, host)
}

pub fn eval_val_entry_with(
    src: &str,
    entry: &str,
    args: &[(&str, Val)],
    host: &dyn Fn(&str, &[Val]) -> Option<Val>,
) -> Val {
    eval_named(src, Some(entry), args, host)
}

pub fn eval_opt_u64(src: &str, args: &[(&str, Val)]) -> Option<u64> {
    match eval(src, args, &|_, _| None) {
        Val::Opt(None) => None,
        Val::Opt(Some(inner)) => {
            Some(u64::try_from(as_int(&inner)).unwrap_or_else(|_| panic!("sample eval int")))
        }
        Val::Int(value) => {
            Some(u64::try_from(value).unwrap_or_else(|_| panic!("sample eval int {value}")))
        }
        other => panic!("sample eval expected an option, got {other:?}"),
    }
}

pub fn eval_pair(src: &str, args: &[(&str, Val)]) -> Option<(Vec<u8>, u8)> {
    let value = eval(src, args, &|_, _| None);
    let items = match value {
        Val::Opt(None) => return None,
        Val::Opt(Some(inner)) => match *inner {
            Val::Tuple(items) => items,
            other => panic!("sample eval expected a pair, got {other:?}"),
        },
        Val::Tuple(items) => items,
        other => panic!("sample eval expected a pair, got {other:?}"),
    };
    let raw = as_bytes(items.first().expect("pair bytes"));
    let tag = u8::try_from(as_int(items.get(1).expect("pair tag"))).expect("pair tag");
    Some((raw, tag))
}

pub fn eval_bytes(src: &str, args: &[(&str, Val)]) -> Vec<u8> {
    eval_bytes_entry_with(src, None, args, &|_, _| None)
}

pub fn eval_bytes_entry_with(
    src: &str,
    entry: Option<&str>,
    args: &[(&str, Val)],
    host: &dyn Fn(&str, &[Val]) -> Option<Val>,
) -> Vec<u8> {
    match eval_named(src, entry, args, host) {
        Val::Bytes(data) => data,
        Val::List(items) => items
            .iter()
            .map(|item| u8::try_from(as_int(item)).unwrap_or_else(|_| panic!("sample byte")))
            .collect(),
        other => panic!("sample eval expected bytes, got {other:?}"),
    }
}
pub fn eval_u64_with(
    src: &str,
    args: &[(&str, Val)],
    host: &dyn Fn(&str, &[Val]) -> Option<Val>,
) -> u64 {
    u64_of(eval(src, args, host))
}

pub fn eval_u64_entry(src: &str, entry: &str, args: &[(&str, Val)]) -> u64 {
    u64_of(eval_named(src, Some(entry), args, &|_, _| None))
}

fn u64_of(value: Val) -> u64 {
    match value {
        Val::Int(value) => {
            u64::try_from(value).unwrap_or_else(|_| panic!("sample eval int {value}"))
        }
        other => panic!("sample eval expected an int, got {other:?}"),
    }
}

fn eval(src: &str, args: &[(&str, Val)], host: &dyn Fn(&str, &[Val]) -> Option<Val>) -> Val {
    run(src, None, args, host).0
}

fn eval_named(
    src: &str,
    entry: Option<&str>,
    args: &[(&str, Val)],
    host: &dyn Fn(&str, &[Val]) -> Option<Val>,
) -> Val {
    run(src, entry, args, host).0
}

fn run<'a>(
    src: &str,
    entry: Option<&str>,
    args: &[(&str, Val)],
    host: &'a dyn Fn(&str, &[Val]) -> Option<Val>,
) -> (Val, Ctx<'a>) {
    let funcs = functions(src);
    let func = match entry {
        Some(name) => funcs
            .get(name)
            .cloned()
            .unwrap_or_else(|| panic!("sample eval missing function {name}")),
        None => {
            let mut values = funcs.values().cloned();
            let func = values.next().expect("sample eval function");
            if values.next().is_some() {
                panic!("sample eval source has more than one function");
            }
            func
        }
    };
    let mut ctx = Ctx {
        scopes: vec![HashMap::new()],
        host,
        funcs,
        unsigned: std::collections::HashSet::new(),
        widths: HashMap::new(),
        structs: struct_map(src),
    };
    bind_file_consts(src, &mut ctx);
    for input in &func.sig.inputs {
        let syn::FnArg::Typed(typed) = input else {
            panic!("sample eval does not call methods");
        };
        let name = pat_ident(&typed.pat);
        if unsigned_type(&typed.ty) {
            ctx.unsigned.insert(name.to_string());
        }
        if let Some(width) = int_width(&typed.ty) {
            ctx.widths.insert(name.to_string(), width);
        }
        let value = args
            .iter()
            .find(|(arg, _)| *arg == name)
            .unwrap_or_else(|| panic!("sample eval missing argument {name}"))
            .1
            .clone();
        ctx.bind(name, value);
    }
    let value = match eval_block(&func.block, &mut ctx) {
        Flow::Next(value) | Flow::Return(value) => value,
        Flow::Break => panic!("break outside a loop"),
        Flow::Continue => panic!("continue outside a loop"),
    };
    (value, ctx)
}

fn functions(src: &str) -> HashMap<String, syn::ItemFn> {
    let mut map = HashMap::new();
    if let Ok(func) = syn::parse_str::<syn::ItemFn>(src) {
        map.insert(func.sig.ident.to_string(), func);
        return map;
    }
    let file: syn::File =
        syn::parse_str(src).unwrap_or_else(|err| panic!("sample eval parse: {err}"));
    for item in file.items {
        if let syn::Item::Fn(func) = item {
            map.insert(func.sig.ident.to_string(), func);
        }
    }
    if map.is_empty() {
        panic!("sample eval parse: no function");
    }
    map
}

pub fn eval_option_bytes(src: &str, entry: &str, args: &[(&str, Val)]) -> Option<Vec<u8>> {
    match eval_named(src, Some(entry), args, &|_, _| None) {
        Val::Bytes(data) => Some(data),
        Val::Opt(None) => None,
        Val::Opt(Some(value)) => Some(as_bytes(&value)),
        other => panic!("sample eval expected bytes or none, got {other:?}"),
    }
}

struct Ctx<'a> {
    scopes: Vec<HashMap<String, Val>>,
    host: &'a dyn Fn(&str, &[Val]) -> Option<Val>,
    funcs: HashMap<String, syn::ItemFn>,
    unsigned: std::collections::HashSet<String>,
    widths: HashMap<String, usize>,
    structs: HashMap<String, Vec<(String, String)>>,
}

impl Ctx<'_> {
    fn bind(&mut self, name: &str, value: Val) {
        self.scopes
            .last_mut()
            .expect("scope")
            .insert(name.to_string(), value);
    }

    fn set(&mut self, name: &str, value: Val) {
        for scope in self.scopes.iter_mut().rev() {
            if scope.contains_key(name) {
                scope.insert(name.to_string(), value);
                return;
            }
        }
        panic!("assignment to unknown {name}");
    }

    fn get(&self, name: &str) -> Option<Val> {
        for scope in self.scopes.iter().rev() {
            if let Some(value) = scope.get(name) {
                return Some(value.clone());
            }
        }
        None
    }
}

enum Flow {
    Next(Val),
    Return(Val),
    Break,
    Continue,
}

macro_rules! nextv {
    ($flow:expr) => {
        match $flow {
            Ok(value) => value,
            Err(other) => return other,
        }
    };
}

fn eval_block(block: &syn::Block, ctx: &mut Ctx<'_>) -> Flow {
    ctx.scopes.push(HashMap::new());
    let mut last = Val::Unit;
    for stmt in &block.stmts {
        match eval_stmt(stmt, ctx) {
            Flow::Next(value) => last = value,
            other => {
                ctx.scopes.pop();
                return other;
            }
        }
    }
    ctx.scopes.pop();
    Flow::Next(last)
}

fn eval_stmt(stmt: &syn::Stmt, ctx: &mut Ctx<'_>) -> Flow {
    match stmt {
        syn::Stmt::Local(local) => {
            let init = local.init.as_ref().expect("binding has a value");
            let Flow::Next(value) = eval_expr(&init.expr, ctx) else {
                return eval_expr(&init.expr, ctx);
            };
            bind_pat(&local.pat, &value, ctx);
            if let (syn::Pat::Ident(ident), Some((width, signed))) =
                (&local.pat, lit_suffix_width(&init.expr))
            {
                let name = ident.ident.to_string();
                ctx.widths.insert(name.clone(), width);
                if !signed {
                    ctx.unsigned.insert(name);
                }
            }
            Flow::Next(Val::Unit)
        }
        syn::Stmt::Expr(expr, _) => eval_expr(expr, ctx),
        syn::Stmt::Macro(mac) if is_ignored_macro(&mac.mac) => Flow::Next(Val::Unit),
        syn::Stmt::Item(syn::Item::Const(item)) => {
            let Flow::Next(value) = eval_expr(&item.expr, ctx) else {
                return eval_expr(&item.expr, ctx);
            };
            ctx.bind(&item.ident.to_string(), value);
            Flow::Next(Val::Unit)
        }
        syn::Stmt::Item(_) => Flow::Next(Val::Unit),
        other => panic!("unsupported statement {}", snippet(other)),
    }
}

fn eval_expr(expr: &syn::Expr, ctx: &mut Ctx<'_>) -> Flow {
    if cfg_gated(expr_attrs(expr)) {
        return Flow::Next(Val::Unit);
    }
    match expr {
        syn::Expr::Lit(lit) => Flow::Next(lit_val(&lit.lit)),
        syn::Expr::Path(path) => Flow::Next(path_val(&path.path, ctx)),
        syn::Expr::Paren(inner) => eval_expr(&inner.expr, ctx),
        syn::Expr::Reference(inner) => eval_expr(&inner.expr, ctx),
        syn::Expr::Block(block) => eval_block(&block.block, ctx),
        syn::Expr::Try(item) => match nextv!(take_next(eval_expr(&item.expr, ctx))) {
            Val::Opt(Some(inner)) => Flow::Next(*inner),
            Val::Opt(None) => Flow::Return(Val::Opt(None)),
            // `Err(...)` is `Name("err")`. `Ok(value)` is already unwrapped, so a
            // tuple, record, list, or byte string is a successful result.
            Val::Name(name) if name == "err" => Flow::Return(Val::Name("err".into())),
            other => Flow::Next(other),
        },
        syn::Expr::Return(ret) => {
            let value = match &ret.expr {
                Some(inner) => nextv!(take_next(eval_expr(inner, ctx))),
                None => Val::Unit,
            };
            Flow::Return(value)
        }
        syn::Expr::Break(_) => Flow::Break,
        syn::Expr::Continue(_) => Flow::Continue,
        syn::Expr::Unary(op) => {
            let value = nextv!(take_next(eval_expr(&op.expr, ctx)));
            match op.op {
                syn::UnOp::Not(_) => match value {
                    Val::Bool(flag) => Flow::Next(Val::Bool(!flag)),
                    Val::Int(bits) => Flow::Next(Val::Int(!bits)),
                    other => panic!("unsupported not {other:?}"),
                },
                syn::UnOp::Neg(_) => Flow::Next(Val::Int(-as_int(&value))),
                syn::UnOp::Deref(_) => Flow::Next(value),
                _ => panic!("unsupported unary"),
            }
        }
        syn::Expr::Binary(bin) => eval_binary(bin, ctx),
        syn::Expr::Assign(assign) => {
            let value = match eval_expr(&assign.right, ctx) {
                Flow::Next(value) => value,
                other => return other,
            };
            if let syn::Expr::Index(index) = &*assign.left {
                let name = expr_ident(&index.expr);
                let at = usize::try_from(as_int(&nextv!(take_next(eval_expr(&index.index, ctx)))))
                    .expect("index");
                let mut data = match ctx.get(&name) {
                    Some(Val::Bytes(data)) => data,
                    other => panic!("index assignment into {other:?}"),
                };
                let byte = u8::try_from(as_int(&value)).expect("assigned byte");
                *data.get_mut(at).unwrap_or_else(|| panic!("byte {at}")) = byte;
                ctx.set(&name, Val::Bytes(data));
                return Flow::Next(Val::Unit);
            }
            let name = assign_target(&assign.left);
            ctx.set(&name, value);
            Flow::Next(Val::Unit)
        }
        syn::Expr::Field(field) => {
            let base = nextv!(take_next(eval_expr(&field.base, ctx)));
            let syn::Member::Named(name) = &field.member else {
                panic!("tuple field");
            };
            Flow::Next(field_of(&base, &name.to_string()))
        }
        syn::Expr::Cast(cast) => {
            let value = nextv!(take_next(eval_expr(&cast.expr, ctx)));
            Flow::Next(cast_int(&value, &cast.ty))
        }
        syn::Expr::Index(index) => {
            let base = nextv!(take_next(eval_expr(&index.expr, ctx)));
            if let syn::Expr::Range(range) = &*index.index {
                Flow::Next(slice_bytes(&base, range, ctx))
            } else {
                let at = as_int(&nextv!(take_next(eval_expr(&index.index, ctx))));
                Flow::Next(index_val(&base, at))
            }
        }
        syn::Expr::Array(array) => {
            let mut items = Vec::new();
            for elem in &array.elems {
                items.push(nextv!(take_next(eval_expr(elem, ctx))));
            }
            Flow::Next(Val::List(items))
        }
        syn::Expr::Tuple(tuple) => {
            let mut items = Vec::new();
            for elem in &tuple.elems {
                items.push(nextv!(take_next(eval_expr(elem, ctx))));
            }
            Flow::Next(Val::Tuple(items))
        }
        syn::Expr::Repeat(repeat) => {
            let elem = nextv!(take_next(eval_expr(&repeat.expr, ctx)));
            let len = usize::try_from(as_int(&nextv!(take_next(eval_expr(&repeat.len, ctx)))))
                .expect("repeat length");
            let byte = u8::try_from(as_int(&elem)).expect("repeat byte");
            Flow::Next(Val::Bytes(vec![byte; len]))
        }
        syn::Expr::Range(range) => {
            let start = as_int(&nextv!(take_next(eval_expr(
                range.start.as_ref().expect("range start"),
                ctx
            ))));
            let end = as_int(&nextv!(take_next(eval_expr(
                range.end.as_ref().expect("range end"),
                ctx
            ))));
            let inclusive = matches!(range.limits, syn::RangeLimits::Closed(_));
            Flow::Next(Val::Name(format!("range:{start}:{end}:{inclusive}")))
        }
        syn::Expr::If(item) => eval_if(item, ctx),
        syn::Expr::While(item) => {
            loop {
                if !as_bool(&nextv!(take_next(eval_expr(&item.cond, ctx)))) {
                    break;
                }
                match eval_block(&item.body, ctx) {
                    Flow::Next(_) => {}
                    Flow::Continue => continue,
                    Flow::Break => break,
                    ret @ Flow::Return(_) => return ret,
                }
            }
            Flow::Next(Val::Unit)
        }
        syn::Expr::ForLoop(item) => eval_for(item, ctx),
        syn::Expr::Match(item) => eval_match(item, ctx),
        syn::Expr::MethodCall(call) if call.method == "copy_from_slice" => {
            if let syn::Expr::Path(path) = &*call.receiver {
                if path.path.segments.len() == 1 {
                    let name = path.path.segments[0].ident.to_string();
                    let source = as_bytes(&nextv!(take_next(eval_expr(&call.args[0], ctx))));
                    ctx.set(&name, Val::Bytes(source));
                    return Flow::Next(Val::Unit);
                }
            }
            copy_range(call, ctx)
        }
        syn::Expr::MethodCall(call) => lift(eval_method(call, ctx)),
        syn::Expr::Call(call) => lift(eval_call(call, ctx)),
        syn::Expr::Macro(mac) if mac.mac.path.is_ident("vec") => {
            let parsed: VecLit = syn::parse2(mac.mac.tokens.clone()).expect("vec!");
            let byte = u8::try_from(as_int(&nextv!(take_next(eval_expr(&parsed.item, ctx)))))
                .expect("vec byte");
            let len = match &parsed.count {
                Some(count) => usize::try_from(as_int(&nextv!(take_next(eval_expr(count, ctx)))))
                    .expect("vec length"),
                None => 1,
            };
            Flow::Next(Val::Bytes(vec![byte; len]))
        }
        syn::Expr::Macro(mac) if mac.mac.path.is_ident("matches") => {
            match eval_matches(&mac.mac, ctx) {
                Ok(value) => Flow::Next(Val::Bool(value)),
                Err(flow) => flow,
            }
        }
        syn::Expr::Macro(mac) if is_ignored_macro(&mac.mac) => Flow::Next(Val::Unit),
        syn::Expr::Struct(item) => {
            if item.rest.is_some() {
                panic!("struct update");
            }
            let mut fields = Vec::new();
            for field in &item.fields {
                let syn::Member::Named(name) = &field.member else {
                    panic!("tuple struct field");
                };
                let value = nextv!(take_next(eval_expr(&field.expr, ctx)));
                fields.push((name.to_string(), value));
            }
            Flow::Next(Val::Rec(fields))
        }
        other => panic!("unsupported expression {}", snippet(other)),
    }
}

fn eval_binary(bin: &syn::ExprBinary, ctx: &mut Ctx<'_>) -> Flow {
    if matches!(bin.op, syn::BinOp::And(_)) {
        let left = nextv!(take_next(eval_expr(&bin.left, ctx)));
        if !as_bool(&left) {
            return Flow::Next(Val::Bool(false));
        }
        let right = nextv!(take_next(eval_expr(&bin.right, ctx)));
        return Flow::Next(Val::Bool(as_bool(&right)));
    }
    if matches!(bin.op, syn::BinOp::Or(_)) {
        let left = nextv!(take_next(eval_expr(&bin.left, ctx)));
        if as_bool(&left) {
            return Flow::Next(Val::Bool(true));
        }
        let right = nextv!(take_next(eval_expr(&bin.right, ctx)));
        return Flow::Next(Val::Bool(as_bool(&right)));
    }
    let left = nextv!(take_next(eval_expr(&bin.left, ctx)));
    let right = nextv!(take_next(eval_expr(&bin.right, ctx)));
    let value = match bin.op {
        syn::BinOp::Eq(_) => Val::Bool(vals_eq(&left, &right)),
        syn::BinOp::Ne(_) => Val::Bool(!vals_eq(&left, &right)),
        syn::BinOp::Lt(_) => Val::Bool(as_int(&left) < as_int(&right)),
        syn::BinOp::Le(_) => Val::Bool(as_int(&left) <= as_int(&right)),
        syn::BinOp::Gt(_) => Val::Bool(as_int(&left) > as_int(&right)),
        syn::BinOp::Ge(_) => Val::Bool(as_int(&left) >= as_int(&right)),
        syn::BinOp::Add(_) => Val::Int(as_int(&left) + as_int(&right)),
        syn::BinOp::Sub(_) => Val::Int(as_int(&left) - as_int(&right)),
        syn::BinOp::Mul(_) => Val::Int(as_int(&left) * as_int(&right)),
        syn::BinOp::Div(_) => Val::Int(as_int(&left) / as_int(&right)),
        syn::BinOp::Rem(_) => Val::Int(as_int(&left) % as_int(&right)),
        syn::BinOp::BitAnd(_) => Val::Int(as_int(&left) & as_int(&right)),
        syn::BinOp::BitOr(_) => Val::Int(as_int(&left) | as_int(&right)),
        syn::BinOp::BitXor(_) => Val::Int(as_int(&left) ^ as_int(&right)),
        syn::BinOp::Shl(_) => Val::Int(as_int(&left) << as_int(&right)),
        syn::BinOp::Shr(_) => Val::Int(as_int(&left) >> as_int(&right)),
        syn::BinOp::ShrAssign(_) => {
            let name = assign_target(&bin.left);
            ctx.set(&name, Val::Int(as_int(&left) >> as_int(&right)));
            return Flow::Next(Val::Unit);
        }
        syn::BinOp::AddAssign(_) => {
            let name = assign_target(&bin.left);
            ctx.set(&name, Val::Int(as_int(&left) + as_int(&right)));
            return Flow::Next(Val::Unit);
        }
        syn::BinOp::BitOrAssign(_) => {
            let name = assign_target(&bin.left);
            ctx.set(&name, Val::Int(as_int(&left) | as_int(&right)));
            return Flow::Next(Val::Unit);
        }
        syn::BinOp::BitAndAssign(_) => {
            let name = assign_target(&bin.left);
            ctx.set(&name, Val::Int(as_int(&left) & as_int(&right)));
            return Flow::Next(Val::Unit);
        }
        _ => panic!("unsupported operator {}", snippet(&bin.op)),
    };
    Flow::Next(value)
}

fn eval_if(item: &syn::ExprIf, ctx: &mut Ctx<'_>) -> Flow {
    ctx.scopes.push(HashMap::new());
    let yes = match &*item.cond {
        syn::Expr::Let(binder) => {
            let value =
                take_next(eval_expr(&binder.expr, ctx)).unwrap_or_else(|_| panic!("if let"));
            pat_accepts(&binder.pat, &value, ctx)
        }
        other => as_bool(&take_next(eval_expr(other, ctx)).unwrap_or_else(|_| panic!("if"))),
    };
    let flow = if yes {
        // The then-block opens its own scope. Bindings from `if let` live beside it.
        let saved = ctx.scopes.last().cloned();
        let flow = eval_block(&item.then_branch, ctx);
        if let Some(scope) = saved {
            *ctx.scopes.last_mut().expect("if scope") = scope;
        }
        flow
    } else if let Some((_, else_expr)) = &item.else_branch {
        eval_expr(else_expr, ctx)
    } else {
        Flow::Next(Val::Unit)
    };
    ctx.scopes.pop();
    flow
}

fn eval_for(item: &syn::ExprForLoop, ctx: &mut Ctx<'_>) -> Flow {
    let range = take_next(eval_expr(&item.expr, ctx)).unwrap_or_else(|_| panic!("for range"));
    let values = match range {
        Val::Name(label) if label.starts_with("range:") => {
            let (start, end, inclusive) = parse_range(&label);
            let end = if inclusive { end + 1 } else { end };
            (start..end).map(Val::Int).collect()
        }
        Val::Iter(items) => items,
        Val::List(items) => items,
        Val::Bytes(data) => data
            .into_iter()
            .map(|byte| Val::Int(i128::from(byte)))
            .collect(),
        other => panic!("for loop expects a range or iterator, got {other:?}"),
    };
    for value in values {
        ctx.scopes.push(HashMap::new());
        bind_pat(&item.pat, &value, ctx);
        let flow = eval_block(&item.body, ctx);
        ctx.scopes.pop();
        match flow {
            Flow::Next(_) | Flow::Continue => {}
            Flow::Break => break,
            ret @ Flow::Return(_) => return ret,
        }
    }
    Flow::Next(Val::Unit)
}

fn eval_match(item: &syn::ExprMatch, ctx: &mut Ctx<'_>) -> Flow {
    let scrut = take_next(eval_expr(&item.expr, ctx)).unwrap_or_else(|_| panic!("match"));
    for arm in &item.arms {
        ctx.scopes.push(HashMap::new());
        if pat_accepts(&arm.pat, &scrut, ctx) {
            let guard_ok = match &arm.guard {
                None => true,
                Some((_, guard)) => as_bool(
                    &take_next(eval_expr(guard, ctx)).unwrap_or_else(|_| panic!("match guard")),
                ),
            };
            if guard_ok {
                let flow = eval_expr(&arm.body, ctx);
                ctx.scopes.pop();
                return flow;
            }
        }
        ctx.scopes.pop();
    }
    panic!("non-exhaustive match");
}

fn eval_method(call: &syn::ExprMethodCall, ctx: &mut Ctx<'_>) -> Result<Val, Flow> {
    let name = call.method.to_string();
    if name == "push" || name == "extend_from_slice" {
        let place = place_name(&call.receiver).unwrap_or_else(|| panic!("mutable {name}"));
        let current = ctx.get(&place).unwrap_or_else(|| panic!("missing {place}"));
        let args = eval_args(&call.args, ctx)?;
        if name == "extend_from_slice" {
            let mut data = as_bytes(&current);
            data.extend(as_bytes(&args[0]));
            ctx.set(&place, Val::Bytes(data));
            return Ok(Val::Unit);
        }
        match current {
            Val::List(mut items) => {
                items.push(args[0].clone());
                ctx.set(&place, Val::List(items));
            }
            Val::Bytes(mut data) => {
                if let Val::Int(byte) = &args[0] {
                    if let Ok(byte) = u8::try_from(*byte) {
                        data.push(byte);
                        ctx.set(&place, Val::Bytes(data));
                        return Ok(Val::Unit);
                    }
                }
                if data.is_empty() {
                    ctx.set(&place, Val::List(vec![args[0].clone()]));
                    return Ok(Val::Unit);
                }
                panic!("push {args:?} onto bytes");
            }
            other => panic!("push onto {other:?}"),
        }
        return Ok(Val::Unit);
    }
    let recv = take_next(eval_expr(&call.receiver, ctx))?;
    let name = call.method.to_string();
    if name == "to_le_bytes" || name == "to_be_bytes" {
        let mut data = le_bytes(as_int(&recv), le_width(&call.receiver, ctx));
        if name == "to_be_bytes" {
            data.reverse();
        }
        return Ok(Val::Bytes(data));
    }
    if let Some(value) = (ctx.host)(
        &name,
        &std::iter::once(recv.clone())
            .chain(eval_args(&call.args, ctx)?)
            .collect::<Vec<_>>(),
    ) {
        return Ok(value);
    }
    let args = eval_args(&call.args, ctx)?;
    Ok(match (recv, name.as_str()) {
        (Val::Bytes(data), "shl") if data.len() == 32 => {
            Val::Bytes(u256_shift(&data, as_int(&args[0]), true))
        }
        (Val::Bytes(data), "shr") if data.len() == 32 => {
            Val::Bytes(u256_shift(&data, as_int(&args[0]), false))
        }
        (Val::Bytes(data), "len") => Val::Int(data.len() as i128),
        (Val::List(data), "len") => Val::Int(data.len() as i128),
        (Val::Bytes(data), "is_empty") => Val::Bool(data.is_empty()),
        (Val::List(data), "is_empty") => Val::Bool(data.is_empty()),
        (Val::Bytes(data), "last") => {
            let last = data
                .last()
                .copied()
                .map(|byte| Box::new(Val::Int(i128::from(byte))));
            Val::Opt(last)
        }
        (Val::Bytes(data), "first") => {
            let first = data
                .first()
                .copied()
                .map(|byte| Box::new(Val::Int(i128::from(byte))));
            Val::Opt(first)
        }
        (Val::Opt(slot), "copied") => Val::Opt(slot),
        (Val::Bytes(data), "iter") => Val::Iter(
            data.into_iter()
                .map(|byte| Val::Int(i128::from(byte)))
                .collect(),
        ),
        (Val::List(items), "iter") => Val::Iter(items),
        (Val::Int(left), "div_ceil") => {
            let right = as_int(&args[0]);
            Val::Int(left.div_euclid(right) + i128::from(left.rem_euclid(right) != 0))
        }
        (Val::Bytes(data), "get") => {
            let index = as_int(&args[0]);
            match usize::try_from(index)
                .ok()
                .and_then(|index| data.get(index).copied())
            {
                Some(byte) => Val::Opt(Some(Box::new(Val::Int(i128::from(byte))))),
                None => Val::Opt(None),
            }
        }
        (Val::Int(left), "checked_add") => {
            let sum = left.checked_add(as_int(&args[0])).filter(|sum| {
                let Some(name) = place_name(&call.receiver) else {
                    return true;
                };
                let Some(width) = ctx.widths.get(&name).copied() else {
                    return true;
                };
                int_fits(*sum, width, !ctx.unsigned.contains(&name))
            });
            opt_int(sum)
        }
        (Val::Opt(slot), "ok_or_else") => match slot {
            Some(inner) => Val::Opt(Some(inner)),
            None => Val::Opt(None),
        },
        (Val::Opt(slot), "map_err") => match slot {
            Some(inner) => Val::Opt(Some(inner)),
            None => Val::Opt(None),
        },
        (Val::Bool(flag), "then_some") => {
            if flag {
                Val::Opt(Some(Box::new(args[0].clone())))
            } else {
                Val::Opt(None)
            }
        }
        (Val::Int(left), "min") => Val::Int(left.min(as_int(&args[0]))),
        (Val::Int(left), "saturating_add") => Val::Int(left.saturating_add(as_int(&args[0]))),
        (Val::Int(left), "saturating_sub") => {
            let right = as_int(&args[0]);
            let mut value = left.saturating_sub(right);
            if unsigned_receiver(&call.receiver, ctx) && value < 0 {
                value = 0;
            }
            Val::Int(value)
        }
        (Val::Int(left), "saturating_mul") => Val::Int(left.saturating_mul(as_int(&args[0]))),
        (Val::Int(left), "wrapping_sub") => Val::Int(left.wrapping_sub(as_int(&args[0]))),
        (Val::Int(left), "checked_sub") => opt_int(left.checked_sub(as_int(&args[0]))),
        (Val::Int(left), "checked_mul") => opt_int(left.checked_mul(as_int(&args[0]))),
        (Val::Opt(slot), "expect") => match slot.as_deref() {
            Some(inner) => inner.clone(),
            None => panic!("expect"),
        },
        (Val::Name(label), "contains") if label.starts_with("range:") => {
            let (start, end, inclusive) = parse_range(&label);
            let value = as_int(&deref(&args[0]));
            let inside = if inclusive {
                (start..=end).contains(&value)
            } else {
                (start..end).contains(&value)
            };
            Val::Bool(inside)
        }
        (Val::Name(text), "to_string") => Val::Name(text),
        (Val::Bytes(data), "to_vec") => Val::Bytes(data.clone()),
        (Val::Bytes(data), "as_slice") => Val::Bytes(data),
        (Val::Iter(items), "enumerate") => Val::Iter(
            items
                .into_iter()
                .enumerate()
                .map(|(index, item)| Val::Tuple(vec![Val::Int(i128::from(index as u32)), item]))
                .collect(),
        ),
        (Val::Opt(slot), "map") => match slot.as_deref() {
            None => Val::Opt(None),
            Some(inner) => Val::Opt(Some(Box::new(closure_value(inner, &args[0], ctx)?))),
        },
        (Val::Opt(slot), "is_some_and") => match slot.as_deref() {
            None => Val::Bool(false),
            Some(inner) => Val::Bool(as_bool(&closure_value(inner, &args[0], ctx)?)),
        },
        (Val::Iter(items), "all") => Val::Bool(closure_over(&items, &args[0], ctx, true)?),
        (Val::Iter(items), "any") => Val::Bool(closure_over(&items, &args[0], ctx, false)?),
        (other, name) => panic!("unsupported method {name} on {other:?}"),
    })
}

fn closure_value(item: &Val, closure: &Val, ctx: &mut Ctx<'_>) -> Result<Val, Flow> {
    let Val::Name(spec) = closure else {
        panic!("expected a closure");
    };
    let (name, body) = spec.split_once('\u{0}').expect("closure");
    let body: syn::Expr = syn::parse_str(body).expect("closure body");
    ctx.scopes.push(HashMap::new());
    ctx.bind(name, item.clone());
    let value = take_next(eval_expr(&body, ctx))?;
    ctx.scopes.pop();
    Ok(value)
}

fn closure_over(items: &[Val], closure: &Val, ctx: &mut Ctx<'_>, all: bool) -> Result<bool, Flow> {
    let Val::Name(spec) = closure else {
        panic!("expected a closure");
    };
    let (name, body) = spec.split_once('\u{0}').expect("closure");
    let body: syn::Expr = syn::parse_str(body).expect("closure body");
    for item in items {
        ctx.scopes.push(HashMap::new());
        ctx.bind(name, item.clone());
        let value = as_bool(&take_next(eval_expr(&body, ctx))?);
        ctx.scopes.pop();
        if all && !value {
            return Ok(false);
        }
        if !all && value {
            return Ok(true);
        }
    }
    Ok(all)
}

fn eval_call(call: &syn::ExprCall, ctx: &mut Ctx<'_>) -> Result<Val, Flow> {
    let syn::Expr::Path(path) = &*call.func else {
        panic!("unsupported call {}", snippet(&call.func));
    };
    let name = path_key(&path.path);
    if name == "Err" {
        return Ok(Val::Name("err".into()));
    }
    let args = eval_args(&call.args, ctx)?;
    if name == "Ok" {
        return Ok(args.into_iter().next().unwrap_or(Val::Unit));
    }
    if name.ends_with("::try_from") {
        let n = as_int(&args[0]);
        if n >= 0 && u64::try_from(n).is_ok() {
            return Ok(Val::Opt(Some(Box::new(Val::Int(n)))));
        }
        return Ok(Val::Opt(None));
    }
    if name == "Some" {
        return Ok(Val::Opt(Some(Box::new(
            args.into_iter().next().unwrap_or(Val::Unit),
        ))));
    }
    if name == "std::cmp::min" || name == "usize::min" || name == "cmp::min" {
        return Ok(Val::Int(as_int(&args[0]).min(as_int(&args[1]))));
    }
    if name.ends_with("::from_le_bytes") || name.ends_with("::from_be_bytes") {
        let Val::List(bytes) = &args[0] else {
            panic!("from_le_bytes argument");
        };
        let mut raw: Vec<i128> = bytes.iter().map(as_int).collect();
        if name.ends_with("::from_be_bytes") {
            raw.reverse();
        }
        let mut value = 0i128;
        for (shift, byte) in raw.iter().enumerate() {
            value |= byte << (8 * shift);
        }
        let width = raw.len() * 8;
        if name.starts_with('i') && width < 128 && value & (1i128 << (width - 1)) != 0 {
            value |= !((1i128 << width) - 1);
        }
        return Ok(Val::Int(value));
    }
    if name == "Vec::new" || name == "Vec::with_capacity" {
        return Ok(Val::Bytes(Vec::new()));
    }
    if name == "U256::zero" {
        return Ok(Val::Bytes(vec![0; 32]));
    }
    if name == "U256::one" {
        let mut bytes = vec![0; 32];
        bytes[0] = 1;
        return Ok(Val::Bytes(bytes));
    }
    if name == "U256::from_u32" {
        let value = as_int(&args[0]) as u32;
        let mut bytes = vec![0; 32];
        bytes[..4].copy_from_slice(&value.to_le_bytes());
        return Ok(Val::Bytes(bytes));
    }
    if let Some(func) = ctx.funcs.get(&name).cloned() {
        let places: Vec<Option<String>> = call.args.iter().map(place_name).collect();
        let (value, refs) = call_func(&func, &args, ctx)?;
        for (place, updated) in places.into_iter().zip(refs) {
            if let (Some(place), Some(updated)) = (place, updated) {
                ctx.set(&place, updated);
            }
        }
        return Ok(value);
    }
    if let Some(value) = (ctx.host)(&name, &args) {
        return Ok(value);
    }
    panic!("unsupported call {name}");
}

fn call_func(
    func: &syn::ItemFn,
    args: &[Val],
    ctx: &mut Ctx<'_>,
) -> Result<(Val, Vec<Option<Val>>), Flow> {
    ctx.scopes.push(HashMap::new());
    let mut supplied = args.iter();
    for input in &func.sig.inputs {
        let syn::FnArg::Typed(typed) = input else {
            panic!("sample eval does not call methods");
        };
        let name = pat_ident(&typed.pat);
        if unsigned_type(&typed.ty) {
            ctx.unsigned.insert(name.to_string());
        }
        if let Some(width) = int_width(&typed.ty) {
            ctx.widths.insert(name.to_string(), width);
        }
        let value = supplied
            .next()
            .cloned()
            .unwrap_or_else(|| panic!("sample eval missing argument {name}"));
        ctx.bind(name, value);
    }
    let flow = eval_block(&func.block, ctx);
    let refs = func
        .sig
        .inputs
        .iter()
        .map(|input| {
            let syn::FnArg::Typed(typed) = input else {
                return None;
            };
            if !mut_ref(&typed.ty) {
                return None;
            }
            let name = pat_ident(&typed.pat);
            Some(
                ctx.get(name)
                    .unwrap_or_else(|| panic!("missing mut {name}")),
            )
        })
        .collect();
    ctx.scopes.pop();
    match flow {
        Flow::Next(value) | Flow::Return(value) => Ok((value, refs)),
        other => Err(other),
    }
}

fn mut_ref(ty: &syn::Type) -> bool {
    matches!(ty, syn::Type::Reference(refer) if refer.mutability.is_some())
}

fn struct_map(src: &str) -> HashMap<String, Vec<(String, String)>> {
    let Ok(file) = syn::parse_str::<syn::File>(src) else {
        return HashMap::new();
    };
    let mut map = HashMap::new();
    for item in file.items {
        let syn::Item::Struct(item) = item else {
            continue;
        };
        let syn::Fields::Named(fields) = item.fields else {
            continue;
        };
        let rows = fields
            .named
            .into_iter()
            .filter_map(|field| {
                let name = field.ident?.to_string();
                Some((name, type_name(&field.ty)?))
            })
            .collect();
        map.insert(item.ident.to_string(), rows);
    }
    map
}

fn type_name(ty: &syn::Type) -> Option<String> {
    match ty {
        syn::Type::Path(path) => Some(path.path.segments.last()?.ident.to_string()),
        syn::Type::Reference(refer) => type_name(&refer.elem),
        _ => None,
    }
}

fn primitive_width(name: &str) -> Option<usize> {
    match name {
        "i8" | "u8" => Some(1),
        "i16" | "u16" => Some(2),
        "i32" | "u32" => Some(4),
        "i64" | "u64" | "isize" | "usize" => Some(8),
        "i128" | "u128" => Some(16),
        _ => None,
    }
}

/// Width of `value.parent.field.to_le_bytes()` from the struct that contains `parent`.
fn field_le_width(
    expr: &syn::Expr,
    structs: &HashMap<String, Vec<(String, String)>>,
) -> Option<usize> {
    let syn::Expr::Field(outer) = expr else {
        return None;
    };
    let syn::Member::Named(field) = &outer.member else {
        return None;
    };
    let syn::Expr::Field(inner) = &*outer.base else {
        return None;
    };
    let syn::Member::Named(parent) = &inner.member else {
        return None;
    };
    let field = field.to_string();
    let parent = parent.to_string();
    let mut found = None;
    for fields in structs.values() {
        for (name, ty) in fields {
            if name != &parent {
                continue;
            }
            let Some(nested) = structs.get(ty) else {
                continue;
            };
            for (nested_name, nested_ty) in nested {
                if nested_name != &field {
                    continue;
                }
                let Some(width) = primitive_width(nested_ty) else {
                    continue;
                };
                if found.is_some() && found != Some(width) {
                    return None;
                }
                found = Some(width);
            }
        }
    }
    found
}

fn int_width(ty: &syn::Type) -> Option<usize> {
    let syn::Type::Path(path) = ty else {
        return None;
    };
    match path
        .path
        .segments
        .last()
        .expect("type")
        .ident
        .to_string()
        .as_str()
    {
        "i8" | "u8" => Some(1),
        "i16" | "u16" => Some(2),
        "i32" | "u32" => Some(4),
        "i64" | "u64" | "isize" | "usize" => Some(8),
        "i128" | "u128" => Some(16),
        _ => None,
    }
}

fn eval_matches(mac: &syn::Macro, ctx: &mut Ctx<'_>) -> Result<bool, Flow> {
    let parsed: MatchesArgs = syn::parse2(mac.tokens.clone()).expect("matches!");
    let scrut = take_next(eval_expr(&parsed.scrut, ctx))?;
    Ok(pat_accepts(&parsed.pat, &scrut, ctx))
}

struct VecLit {
    item: syn::Expr,
    count: Option<syn::Expr>,
}

impl syn::parse::Parse for VecLit {
    fn parse(input: syn::parse::ParseStream<'_>) -> syn::Result<Self> {
        let item = input.parse()?;
        let count = if input.peek(syn::Token![;]) {
            input.parse::<syn::Token![;]>()?;
            Some(input.parse()?)
        } else {
            None
        };
        Ok(Self { item, count })
    }
}

struct MatchesArgs {
    scrut: syn::Expr,
    pat: syn::Pat,
}

impl syn::parse::Parse for MatchesArgs {
    fn parse(input: syn::parse::ParseStream<'_>) -> syn::Result<Self> {
        let scrut = input.parse()?;
        input.parse::<syn::Token![,]>()?;
        let pat = syn::Pat::parse_multi(input)?;
        Ok(Self { scrut, pat })
    }
}

fn eval_args(
    args: &syn::punctuated::Punctuated<syn::Expr, syn::Token![,]>,
    ctx: &mut Ctx<'_>,
) -> Result<Vec<Val>, Flow> {
    let mut out = Vec::new();
    for arg in args {
        if let syn::Expr::Closure(closure) = arg {
            let name = closure.inputs.first().map(pat_ident).unwrap_or_default();
            let body = snippet(&closure.body);
            out.push(Val::Name(format!("{name}\u{0}{body}")));
            continue;
        }
        out.push(take_next(eval_expr(arg, ctx))?);
    }
    Ok(out)
}

fn pat_accepts(pat: &syn::Pat, value: &Val, ctx: &mut Ctx<'_>) -> bool {
    match pat {
        syn::Pat::Wild(_) => true,
        syn::Pat::Lit(lit) => vals_eq(value, &lit_val(&lit.lit)),
        syn::Pat::Ident(ident) => {
            if let Some(constant) = named_int(&ident.ident.to_string()) {
                return vals_eq(value, &Val::Int(constant));
            }
            ctx.bind(&ident.ident.to_string(), value.clone());
            true
        }
        syn::Pat::Type(typed) => pat_accepts(&typed.pat, value, ctx),
        syn::Pat::Path(path) => {
            let name = path.path.segments.last().expect("pat").ident.to_string();
            if let Some(constant) = named_int(&name) {
                return vals_eq(value, &Val::Int(constant));
            }
            if let Val::Name(got) = value {
                got == &name
            } else {
                false
            }
        }
        syn::Pat::Or(or) => or.cases.iter().any(|case| pat_accepts(case, value, ctx)),
        syn::Pat::Tuple(tuple) => {
            let Val::Tuple(items) = value else {
                return false;
            };
            tuple.elems.len() == items.len()
                && tuple
                    .elems
                    .iter()
                    .zip(items)
                    .all(|(pat, item)| pat_accepts(pat, item, ctx))
        }
        syn::Pat::Range(range) => {
            let start = range_bound(range.start.as_ref().expect("range start"));
            let end = range_bound(range.end.as_ref().expect("range end"));
            let value = as_int(value);
            match range.limits {
                syn::RangeLimits::Closed(_) => (start..=end).contains(&value),
                syn::RangeLimits::HalfOpen(_) => (start..end).contains(&value),
            }
        }
        syn::Pat::TupleStruct(tuple)
            if tuple
                .path
                .segments
                .last()
                .is_some_and(|seg| seg.ident == "Some") =>
        {
            let Val::Opt(Some(inner)) = value else {
                return false;
            };
            let mut inner = inner.as_ref().clone();
            if let syn::Pat::Reference(refer) = &tuple.elems[0] {
                return pat_accepts(&refer.pat, &inner, ctx);
            }
            // `&last` may parse as a reference pattern inside Some.
            let _ = &mut inner;
            pat_accepts(&tuple.elems[0], &inner, ctx)
        }
        syn::Pat::Reference(refer) => pat_accepts(&refer.pat, value, ctx),
        syn::Pat::TupleStruct(tuple)
            if tuple
                .path
                .segments
                .last()
                .is_some_and(|seg| seg.ident == "Ok") =>
        {
            pat_accepts(&tuple.elems[0], value, ctx)
        }
        other => panic!("unsupported pattern {}", snippet(other)),
    }
}

fn bind_pat(pat: &syn::Pat, value: &Val, ctx: &mut Ctx<'_>) {
    if !pat_accepts(pat, value, ctx) {
        panic!("refutable binding {}", snippet(pat));
    }
}

fn range_bound(expr: &syn::Expr) -> i128 {
    match expr {
        syn::Expr::Lit(lit) => as_int(&lit_val(&lit.lit)),
        syn::Expr::Path(path) => {
            named_int(&path.path.segments.last().expect("bound").ident.to_string())
                .unwrap_or_else(|| panic!("unknown range bound"))
        }
        other => panic!("unsupported range bound {}", snippet(other)),
    }
}

fn parse_range(label: &str) -> (i128, i128, bool) {
    let mut parts = label.trim_start_matches("range:").split(':');
    let start: i128 = parts.next().expect("start").parse().expect("start");
    let end: i128 = parts.next().expect("end").parse().expect("end");
    let inclusive = parts.next().expect("limit") == "true";
    (start, end, inclusive)
}

fn lit_suffix_width(expr: &syn::Expr) -> Option<(usize, bool)> {
    let syn::Expr::Lit(lit) = expr else {
        return None;
    };
    let syn::Lit::Int(value) = &lit.lit else {
        return None;
    };
    match value.suffix() {
        "i8" => Some((1, true)),
        "u8" => Some((1, false)),
        "i16" => Some((2, true)),
        "u16" => Some((2, false)),
        "i32" => Some((4, true)),
        "u32" => Some((4, false)),
        "i64" => Some((8, true)),
        "u64" => Some((8, false)),
        _ => None,
    }
}

fn int_fits(value: i128, width: usize, signed: bool) -> bool {
    match (width, signed) {
        (1, true) => i8::try_from(value).is_ok(),
        (1, false) => u8::try_from(value).is_ok(),
        (2, true) => i16::try_from(value).is_ok(),
        (2, false) => u16::try_from(value).is_ok(),
        (4, true) => i32::try_from(value).is_ok(),
        (4, false) => u32::try_from(value).is_ok(),
        (8, true) => i64::try_from(value).is_ok(),
        (8, false) => u64::try_from(value).is_ok(),
        _ => true,
    }
}

fn lit_val(lit: &syn::Lit) -> Val {
    match lit {
        syn::Lit::Bool(value) => Val::Bool(value.value),
        syn::Lit::Int(value) => Val::Int(value.base10_parse::<i128>().expect("int")),
        syn::Lit::Str(value) => Val::Name(value.value()),
        other => panic!("unsupported literal {other:?}"),
    }
}

fn bind_file_consts(src: &str, ctx: &mut Ctx<'_>) {
    let Ok(file) = syn::parse_str::<syn::File>(src) else {
        return;
    };
    for item in file.items {
        let syn::Item::Const(item) = item else {
            continue;
        };
        let value = take_next(eval_expr(&item.expr, ctx))
            .unwrap_or_else(|_| panic!("const {}", item.ident));
        ctx.bind(&item.ident.to_string(), value);
    }
}

fn path_val(path: &syn::Path, ctx: &Ctx<'_>) -> Val {
    let name = path.segments.last().expect("path").ident.to_string();
    if path.segments.len() == 1 && name == "None" {
        return Val::Opt(None);
    }
    if let Some(value) = ctx.get(&name) {
        return value;
    }
    if path.segments.len() == 1 {
        if let Some(value) = named_int(&name) {
            return Val::Int(value);
        }
    }
    Val::Name(name)
}

fn named_int(name: &str) -> Option<i128> {
    if let Some(rest) = name.strip_prefix("OP_") {
        if let Ok(n) = rest.parse::<i128>() {
            if (1..=16).contains(&n) {
                return Some(0x50 + n);
            }
        }
    }
    Some(match name {
        "OP_0" | "OP_FALSE" => 0,
        "OP_PUSHDATA1" => 0x4c,
        "OP_PUSHDATA2" => 0x4d,
        "OP_PUSHDATA4" => 0x4e,
        "OP_1NEGATE" => 0x4f,
        "OP_RESERVED" => 0x50,
        "OP_1" => 0x51,
        "OP_16" => 0x60,
        "OP_NOP" => 0x61,
        "OP_DUP" => 0x76,
        "OP_EQUALVERIFY" => 0x88,
        "OP_HASH160" => 0xa9,
        "OP_EQUAL" => 0x87,
        "OP_CHECKSIG" => 0xac,
        "OP_CHECKSIGVERIFY" => 0xad,
        "OP_CHECKSIGADD" => 0xba,
        "OP_CHECKMULTISIG" => 0xae,
        "OP_CHECKMULTISIGVERIFY" => 0xaf,
        "LOCKTIME_THRESHOLD" => 500_000_000,
        "HALVING_INTERVAL" => 210_000,
        "INITIAL_SUBSIDY" => 5_000_000_000,
        "MAX_MONEY" => 2_100_000_000_000_000,
        "TAPROOT_ACTIVATION_MAINNET" => 709_632,
        "TAPROOT_ACTIVATION_TESTNET" => 2_011_968,
        "TAPROOT_SCRIPT_LENGTH" => 34,
        "TAPROOT_SCRIPT_PREFIX" => 0x51,
        "PUSH_32_BYTES" => 0x20,
        "PUSH_20_BYTES" => 0x14,
        _ => return None,
    })
}

fn le_width(expr: &syn::Expr, ctx: &Ctx<'_>) -> usize {
    let expr = match expr {
        syn::Expr::Paren(inner) => &*inner.expr,
        syn::Expr::Group(inner) => &*inner.expr,
        other => other,
    };
    if let syn::Expr::Path(path) = expr {
        if path.path.segments.len() == 1 {
            let name = path.path.segments[0].ident.to_string();
            if let Some(width) = ctx.widths.get(&name) {
                return *width;
            }
        }
    }
    if let Some(width) = field_le_width(expr, &ctx.structs) {
        return width;
    }
    let syn::Expr::Cast(cast) = expr else {
        panic!("to_le_bytes needs a cast, got {}", snippet(expr));
    };
    let syn::Type::Path(path) = &*cast.ty else {
        panic!("to_le_bytes type");
    };
    match path
        .path
        .segments
        .last()
        .expect("type")
        .ident
        .to_string()
        .as_str()
    {
        "i8" | "u8" => 1,
        "i16" | "u16" => 2,
        "i32" | "u32" => 4,
        "i64" | "u64" => 8,
        "i128" | "u128" => 16,
        other => panic!("to_le_bytes width {other}"),
    }
}

fn le_bytes(value: i128, width: usize) -> Vec<u8> {
    (value as u128).to_le_bytes()[..width].to_vec()
}

fn u256_shift(bytes: &[u8], shift: i128, left: bool) -> Vec<u8> {
    if !(0..256).contains(&shift) {
        return vec![0; 32];
    }
    let shift = shift as u32;
    let mut limbs = [0u64; 4];
    for (index, limb) in limbs.iter_mut().enumerate() {
        let start = index * 8;
        let mut word = [0u8; 8];
        word.copy_from_slice(&bytes[start..start + 8]);
        *limb = u64::from_le_bytes(word);
    }
    let word_shift = (shift / 64) as usize;
    let bit_shift = shift % 64;
    let mut result = [0u64; 4];
    if left {
        for index in 0..4 {
            if index + word_shift < 4 {
                result[index + word_shift] |= limbs[index] << bit_shift;
                if bit_shift > 0 && index + word_shift + 1 < 4 {
                    result[index + word_shift + 1] |= limbs[index] >> (64 - bit_shift);
                }
            }
        }
    } else if bit_shift == 0 {
        result[..(4 - word_shift)].copy_from_slice(&limbs[word_shift..4]);
    } else {
        for index in word_shift..4 {
            let mut word = limbs[index] >> bit_shift;
            if index + 1 < 4 {
                word |= limbs[index + 1] << (64 - bit_shift);
            }
            result[index - word_shift] = word;
        }
    }
    let mut out = vec![0u8; 32];
    for (index, limb) in result.iter().enumerate() {
        let start = index * 8;
        out[start..start + 8].copy_from_slice(&limb.to_le_bytes());
    }
    out
}

fn cast_int(value: &Val, ty: &syn::Type) -> Val {
    let value = as_int(value);
    let bits = match ty {
        syn::Type::Path(path) => path.path.segments.last().map(|seg| seg.ident.to_string()),
        _ => None,
    };
    let value = match bits.as_deref() {
        Some("u8") => value & 0xff,
        Some("u16") => value & 0xffff,
        Some("u32") => value & 0xffff_ffff,
        _ => value,
    };
    Val::Int(value)
}

fn index_val(base: &Val, index: i128) -> Val {
    let index = usize::try_from(index).unwrap_or_else(|_| panic!("index {index}"));
    match base {
        Val::Bytes(data) => Val::Int(i128::from(
            *data.get(index).unwrap_or_else(|| panic!("byte {index}")),
        )),
        Val::List(items) => items
            .get(index)
            .cloned()
            .unwrap_or_else(|| panic!("index {index}")),
        other => panic!("cannot index {other:?}"),
    }
}

fn vals_eq(left: &Val, right: &Val) -> bool {
    match (left, right) {
        (Val::Bool(a), Val::Bool(b)) => a == b,
        (Val::Int(a), Val::Int(b)) => a == b,
        (Val::Name(a), Val::Name(b)) => a == b,
        (Val::Bytes(a), Val::Bytes(b)) => a == b,
        (Val::Opt(None), Val::Opt(None)) => true,
        (Val::Opt(Some(a)), Val::Opt(Some(b))) => vals_eq(a, b),
        _ => false,
    }
}

fn as_bool(value: &Val) -> bool {
    match value {
        Val::Bool(value) => *value,
        other => panic!("expected bool, got {other:?}"),
    }
}

fn as_bytes(value: &Val) -> Vec<u8> {
    match value {
        Val::Bytes(data) => data.clone(),
        Val::List(items) => items
            .iter()
            .map(|item| u8::try_from(as_int(item)).expect("byte"))
            .collect(),
        other => panic!("expected bytes, got {other:?}"),
    }
}

fn slice_bytes(base: &Val, range: &syn::ExprRange, ctx: &mut Ctx<'_>) -> Val {
    let data = as_bytes(base);
    let read = |expr: &syn::Expr, ctx: &mut Ctx<'_>| -> i128 {
        match eval_expr(expr, ctx) {
            Flow::Next(value) => as_int(&value),
            _ => panic!("range bound"),
        }
    };
    let start = match &range.start {
        Some(expr) => usize::try_from(read(expr, ctx)).expect("start"),
        None => 0,
    };
    let mut end = match &range.end {
        Some(expr) => usize::try_from(read(expr, ctx)).expect("end"),
        None => data.len(),
    };
    if matches!(range.limits, syn::RangeLimits::Closed(_)) {
        end += 1;
    }
    Val::Bytes(
        data.get(start..end)
            .unwrap_or_else(|| panic!("slice {start}..{end}"))
            .to_vec(),
    )
}

fn as_int(value: &Val) -> i128 {
    match value {
        Val::Int(value) => *value,
        other => panic!("expected int, got {other:?}"),
    }
}

fn place_name(expr: &syn::Expr) -> Option<String> {
    match expr {
        syn::Expr::Path(path) if path.path.segments.len() == 1 => {
            Some(path.path.segments[0].ident.to_string())
        }
        syn::Expr::Reference(refer) => place_name(&refer.expr),
        syn::Expr::Paren(paren) => place_name(&paren.expr),
        syn::Expr::Group(group) => place_name(&group.expr),
        _ => None,
    }
}

fn unsigned_type(ty: &syn::Type) -> bool {
    let text = snippet(ty);
    ["u8", "u16", "u32", "u64", "u128", "usize", "Natural"]
        .iter()
        .any(|name| {
            text.split(|c: char| !c.is_ascii_alphanumeric())
                .any(|part| part == *name)
        })
}

fn unsigned_receiver(expr: &syn::Expr, ctx: &Ctx<'_>) -> bool {
    match expr {
        syn::Expr::Path(path) if path.path.segments.len() == 1 => ctx
            .unsigned
            .contains(&path.path.segments[0].ident.to_string()),
        syn::Expr::Paren(inner) => unsigned_receiver(&inner.expr, ctx),
        syn::Expr::Group(inner) => unsigned_receiver(&inner.expr, ctx),
        _ => false,
    }
}

fn field_of(value: &Val, name: &str) -> Val {
    let Val::Rec(fields) = value else {
        panic!("field {name} on {value:?}");
    };
    fields
        .iter()
        .find(|(field, _)| field == name)
        .map(|(_, inner)| inner.clone())
        .unwrap_or_else(|| panic!("missing field {name}"))
}

fn opt_int(value: Option<i128>) -> Val {
    match value {
        Some(value) => Val::Opt(Some(Box::new(Val::Int(value)))),
        None => Val::Opt(None),
    }
}

fn deref(value: &Val) -> Val {
    value.clone()
}

fn expr_ident(expr: &syn::Expr) -> String {
    match expr {
        syn::Expr::Path(path) if path.path.segments.len() == 1 => {
            path.path.segments[0].ident.to_string()
        }
        _ => panic!("assignment target {}", snippet(expr)),
    }
}

/// `offset += n` and `*offset += n` both write the local named `offset`.
fn assign_target(expr: &syn::Expr) -> String {
    match expr {
        syn::Expr::Unary(unary) if matches!(unary.op, syn::UnOp::Deref(_)) => {
            expr_ident(&unary.expr)
        }
        syn::Expr::Paren(inner) => assign_target(&inner.expr),
        other => expr_ident(other),
    }
}

fn pat_ident(pat: &syn::Pat) -> &str {
    match pat {
        syn::Pat::Ident(ident) => ident.ident.to_string().leak(),
        syn::Pat::Wild(_) => "_",
        syn::Pat::Type(typed) => pat_ident(&typed.pat),
        syn::Pat::Reference(refer) => pat_ident(&refer.pat),
        other => panic!("argument pattern {}", snippet(other)),
    }
}

fn path_key(path: &syn::Path) -> String {
    path.segments
        .iter()
        .map(|seg| seg.ident.to_string())
        .collect::<Vec<_>>()
        .join("::")
}

fn expr_attrs(expr: &syn::Expr) -> &[syn::Attribute] {
    match expr {
        syn::Expr::If(item) => &item.attrs,
        syn::Expr::While(item) => &item.attrs,
        syn::Expr::Block(item) => &item.attrs,
        _ => &[],
    }
}

fn cfg_gated(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| attr.path().is_ident("cfg"))
}

fn is_ignored_macro(mac: &syn::Macro) -> bool {
    mac.path.is_ident("debug_assert")
        || mac.path.is_ident("assert")
        || mac.path.is_ident("debug_assert_eq")
        || mac.path.is_ident("assert_eq")
}

fn snippet(value: &impl quote::ToTokens) -> String {
    quote::quote!(#value).to_string()
}

fn copy_range(call: &syn::ExprMethodCall, ctx: &mut Ctx<'_>) -> Flow {
    let syn::Expr::Index(index) = &*call.receiver else {
        panic!("copy_from_slice receiver");
    };
    let syn::Expr::Range(range) = &*index.index else {
        panic!("copy_from_slice range");
    };
    let name = expr_ident(&index.expr);
    let start = usize::try_from(as_int(&nextv!(take_next(eval_expr(
        range.start.as_ref().expect("range start"),
        ctx,
    )))))
    .expect("start");
    let mut end = usize::try_from(as_int(&nextv!(take_next(eval_expr(
        range.end.as_ref().expect("range end"),
        ctx,
    )))))
    .expect("end");
    if matches!(range.limits, syn::RangeLimits::Closed(_)) {
        end += 1;
    }
    let source = match nextv!(take_next(eval_expr(&call.args[0], ctx))) {
        Val::Bytes(data) => data,
        other => panic!("copy source {other:?}"),
    };
    let mut data = match ctx.get(&name) {
        Some(Val::Bytes(data)) => data,
        other => panic!("copy destination {other:?}"),
    };
    data.get_mut(start..end)
        .unwrap_or_else(|| panic!("range {start}..{end}"))
        .copy_from_slice(&source);
    ctx.set(&name, Val::Bytes(data));
    Flow::Next(Val::Unit)
}

fn lift(result: Result<Val, Flow>) -> Flow {
    match result {
        Ok(value) => Flow::Next(value),
        Err(flow) => flow,
    }
}

fn take_next(flow: Flow) -> Result<Val, Flow> {
    match flow {
        Flow::Next(value) => Ok(value),
        other => Err(other),
    }
}
