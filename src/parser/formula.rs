//! Formula AST shared by the Z3 clause and the Lean statement.
//!
//! A sentence that does not parse is not rewritten to `true`. A shape the
//! emitter does not handle is `unsupported` for that tool.

use crate::parser::spec_expr::{initial_subsidy, protocol_u64};

pub const UNSUPPORTED: &str = "unsupported";

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Formula {
    Lit(i64),
    Name(String),
    Call(String, Vec<Formula>),
    Floor(Box<Formula>),
    Not(Box<Formula>),
    And(Vec<Formula>),
    Or(Vec<Formula>),
    Implies(Box<Formula>, Box<Formula>),
    Cmp(Cmp, Box<Formula>, Box<Formula>),
    Arith(Arith, Box<Formula>, Box<Formula>),
    /// `∀ var ≥ bound: body` or `∀ var ≤ bound: body` over one integer parameter.
    BoundForall {
        var: String,
        cmp: Cmp,
        bound: Box<Formula>,
        body: Box<Formula>,
    },
    /// Unbounded `∀ var : body` that is not a single bound on the parameter.
    Forall {
        var: String,
        body: Box<Formula>,
    },
    Sum {
        var: String,
        lo: Box<Formula>,
        hi: Box<Formula>,
        body: Box<Formula>,
    },
    /// Piecewise definition. Each case is (condition, value). `otherwise` is the final value.
    /// `None` means the cases do not cover the domain, so the definition stays unlocked.
    Piecewise {
        scrutinee: Box<Formula>,
        cases: Vec<(Formula, Formula)>,
        otherwise: Option<Box<Formula>>,
    },
    /// Recursive definition. The induction principle depends on `kind`, not on the function name.
    Rec {
        name: String,
        var: String,
        head: Option<String>,
        base: Box<Formula>,
        step: Box<Formula>,
        kind: RecKind,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RecKind {
    Nat,
    List,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cmp {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Arith {
    Add,
    Sub,
    Mul,
    FloorDiv,
    TruncDiv,
    Mod,
    Pow,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EmitError {
    pub marker: &'static str,
    pub detail: String,
}

impl EmitError {
    fn unsupported(detail: impl Into<String>) -> Self {
        Self {
            marker: UNSUPPORTED,
            detail: detail.into(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Z3Clause {
    pub requires: String,
    pub ensures: String,
    /// Domain the clause ranges over. `u64` for a height parameter.
    pub domain: &'static str,
}

/// Normalize a spec sentence enough for the recursive descent below.
fn rewrite_frac(s: &str) -> String {
    let chars: Vec<char> = s.chars().collect();
    let mut out = String::new();
    let mut i = 0;
    while i < chars.len() {
        if chars[i..].starts_with(&['\\', 'f', 'r', 'a', 'c', '{']) {
            i += 6;
            let (num, nlen) = take_braced(&chars[i..]);
            i += nlen;
            if i < chars.len() && chars[i] == '{' {
                i += 1;
                let (den, dlen) = take_braced(&chars[i..]);
                i += dlen;
                out.push('(');
                out.push_str(&rewrite_frac(&num));
                out.push_str(")/(");
                out.push_str(&rewrite_frac(&den));
                out.push(')');
                continue;
            }
        }
        out.push(chars[i]);
        i += 1;
    }
    out
}

fn take_braced(chars: &[char]) -> (String, usize) {
    let mut depth = 1;
    let mut i = 0;
    let mut body = String::new();
    while i < chars.len() {
        if chars[i] == '{' {
            depth += 1;
        } else if chars[i] == '}' {
            depth -= 1;
            if depth == 0 {
                return (body, i + 1);
            }
        }
        body.push(chars[i]);
        i += 1;
    }
    (body, i)
}

fn rewrite_cases(s: &str) -> String {
    let begin = "\\begin{cases}";
    let end = "\\end{cases}";
    let mut out = String::new();
    let mut rest = s;
    while let Some(start) = rest.find(begin) {
        out.push_str(&rest[..start]);
        rest = &rest[start + begin.len()..];
        let Some(stop) = rest.find(end) else {
            out.push_str(begin);
            break;
        };
        let body = &rest[..stop];
        rest = &rest[stop + end.len()..];
        let mut arms = Vec::new();
        for row in body.split("\\\\") {
            let mut cols = row.split('&');
            let value = cols.next().unwrap_or("").trim().replace("\\gg", " >> ");
            let cond = cols
                .next()
                .unwrap_or("")
                .trim()
                .replace("\\text{if }", " ")
                .replace("\\text{if}", " ");
            if value.is_empty() {
                continue;
            }
            arms.push(format!("({cond}) => ({value})"));
        }
        out.push_str("piecewise(");
        out.push_str(&arms.join(", "));
        out.push(')');
    }
    out.push_str(rest);
    out
}

/// Replace `word` only where it stands alone, so `times` -> `*` leaves
/// identifiers such as `timestamp` or `blocktimes` intact. A word that starts
/// with a non-identifier character (a LaTeX command such as `\times`) only
/// needs the boundary after it.
fn replace_word(s: &str, word: &str, rep: &str) -> String {
    let is_ident = |c: char| c.is_ascii_alphanumeric() || c == '_';
    let check_before = word.chars().next().is_some_and(is_ident);
    let mut out = String::with_capacity(s.len());
    let mut rest = s;
    while let Some(pos) = rest.find(word) {
        let before = rest[..pos].chars().next_back().or(out.chars().next_back());
        let after = rest[pos + word.len()..].chars().next();
        out.push_str(&rest[..pos]);
        if (check_before && before.is_some_and(is_ident)) || after.is_some_and(is_ident) {
            out.push_str(word);
        } else {
            out.push_str(rep);
        }
        rest = &rest[pos + word.len()..];
    }
    out.push_str(rest);
    out
}

pub fn normalize(raw: &str) -> String {
    let mut s = rewrite_cases(raw.trim());
    s = rewrite_frac(&s);
    s = s.replace('$', "");
    // `\times` is the LaTeX operator; rewrite it before backslashes are stripped
    // so `a\times b` does not become the identifier `atimes`.
    s = replace_word(&s, "\\times", " * ");
    s = s.replace('\\', "");
    s = s.replace(['{', '}'], "");
    s = s.replace("text", "");
    s = s.replace('_', "");
    s = replace_word(&s, "times", "*");
    s = s.replace('×', "*");
    s = s.replace("cdot", "*");
    s = s.replace("geq", ">=");
    s = s.replace("leq", "<=");
    s = s.replace('≥', ">=");
    s = s.replace('≤', "<=");
    s = s.replace('≠', "!=");
    s = s.replace("neq", "!=");
    s = s.replace('∧', " && ");
    s = s.replace("land", " && ");
    s = s.replace('∨', " || ");
    s = s.replace("lor", " || ");
    s = s.replace("rightarrow", "->");
    s = s.replace("Rightarrow", "->");
    s = s.replace('→', "->");
    s = s.replace('⇒', "->");
    s = s.replace("implies", "->");
    s = s.replace("forall", "forall ");
    s = s.replace('∀', "forall ");
    s = s.replace("lfloor", "floor(");
    s = s.replace("rfloor", ")");
    s = s.replace('⌊', "floor(");
    s = s.replace('⌋', ")");
    s = s.replace(" gg ", " >> ");
    s = s.replace(">>", " >> ");
    s = strip_member_dots(&s);
    // Thousands separators inside numbers.
    let mut out = String::new();
    let chars: Vec<char> = s.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        if chars[i] == ','
            && i > 0
            && i + 1 < chars.len()
            && chars[i - 1].is_ascii_digit()
            && chars[i + 1].is_ascii_digit()
        {
            i += 1;
            continue;
        }
        out.push(chars[i]);
        i += 1;
    }
    out.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn strip_member_dots(s: &str) -> String {
    let chars: Vec<char> = s.chars().collect();
    let mut out = String::new();
    for (i, ch) in chars.iter().enumerate() {
        if *ch == '.'
            && i > 0
            && i + 1 < chars.len()
            && chars[i - 1].is_ascii_alphabetic()
            && chars[i + 1].is_ascii_alphabetic()
        {
            continue;
        }
        out.push(*ch);
    }
    out
}

pub fn parse_sentence(raw: &str) -> Option<Formula> {
    let norm = normalize(raw);
    if norm.is_empty() {
        return None;
    }
    let toks = tokenize(&norm);
    if toks.iter().any(|tok| matches!(tok, Tok::Semi)) {
        return parse_recursion(&toks);
    }
    let mut p = Parser { toks, i: 0 };
    let expr = p.parse_expr().ok()?;
    if p.peek().is_some() {
        return None;
    }
    Some(expr)
}

fn parse_recursion(toks: &[Tok]) -> Option<Formula> {
    let mut p = Parser {
        toks: toks.to_vec(),
        i: 0,
    };
    let base_eq = p.parse_cmp().ok()?;
    if !matches!(p.bump(), Some(Tok::Semi)) {
        return None;
    }
    let step_eq = p.parse_cmp().ok()?;
    if p.peek().is_some() {
        return None;
    }
    let (name, arg, base) = eq_call(base_eq)?;
    let (name2, arg2, step) = eq_call(step_eq)?;
    if name != name2 {
        return None;
    }
    if matches!(arg, Formula::Lit(0)) {
        let var = succ_var(&arg2)?;
        return Some(Formula::Rec {
            name,
            var,
            head: None,
            base: Box::new(base),
            step: Box::new(step),
            kind: RecKind::Nat,
        });
    }
    if matches!(&arg, Formula::Name(n) if n == "nil") {
        let (head, var) = cons_vars(&arg2)?;
        return Some(Formula::Rec {
            name,
            var,
            head: Some(head),
            base: Box::new(base),
            step: Box::new(step),
            kind: RecKind::List,
        });
    }
    None
}

fn eq_call(expr: Formula) -> Option<(String, Formula, Formula)> {
    let Formula::Cmp(Cmp::Eq, lhs, rhs) = expr else {
        return None;
    };
    let Formula::Call(name, mut args) = *lhs else {
        return None;
    };
    if args.len() != 1 {
        return None;
    }
    Some((name, args.remove(0), *rhs))
}

fn succ_var(arg: &Formula) -> Option<String> {
    let Formula::Arith(Arith::Add, left, right) = arg else {
        return None;
    };
    match (left.as_ref(), right.as_ref()) {
        (Formula::Name(var), Formula::Lit(1)) | (Formula::Lit(1), Formula::Name(var)) => {
            Some(var.clone())
        }
        _ => None,
    }
}

fn cons_vars(arg: &Formula) -> Option<(String, String)> {
    let Formula::Call(name, args) = arg else {
        return None;
    };
    if name != "cons" || args.len() != 2 {
        return None;
    }
    let Formula::Name(head) = &args[0] else {
        return None;
    };
    let Formula::Name(tail) = &args[1] else {
        return None;
    };
    Some((head.clone(), tail.clone()))
}

struct Parser {
    toks: Vec<Tok>,
    i: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Tok {
    Ident(String),
    Int(i64),
    Op(String),
    LParen,
    RParen,
    Comma,
    Colon,
    Semi,
}

fn tokenize(s: &str) -> Vec<Tok> {
    let mut toks = Vec::new();
    let b = s.as_bytes();
    let mut i = 0;
    while i < b.len() {
        if b[i].is_ascii_whitespace() {
            i += 1;
            continue;
        }
        if b[i] == b'(' {
            toks.push(Tok::LParen);
            i += 1;
            continue;
        }
        if b[i] == b')' {
            toks.push(Tok::RParen);
            i += 1;
            continue;
        }
        if b[i] == b',' {
            toks.push(Tok::Comma);
            i += 1;
            continue;
        }
        if b[i] == b':' {
            toks.push(Tok::Colon);
            i += 1;
            continue;
        }
        if b[i] == b';' {
            toks.push(Tok::Semi);
            i += 1;
            continue;
        }
        if b[i] == b'&' && i + 1 < b.len() && b[i + 1] == b'&' {
            toks.push(Tok::Op("&&".into()));
            i += 2;
            continue;
        }
        if b[i] == b'|' && i + 1 < b.len() && b[i + 1] == b'|' {
            toks.push(Tok::Op("||".into()));
            i += 2;
            continue;
        }
        if b[i] == b'-' && i + 1 < b.len() && b[i + 1] == b'>' {
            toks.push(Tok::Op("->".into()));
            i += 2;
            continue;
        }
        if b[i] == b'>' && i + 1 < b.len() && b[i + 1] == b'=' {
            toks.push(Tok::Op(">=".into()));
            i += 2;
            continue;
        }
        if b[i] == b'<' && i + 1 < b.len() && b[i + 1] == b'=' {
            toks.push(Tok::Op("<=".into()));
            i += 2;
            continue;
        }
        if b[i] == b'!' && i + 1 < b.len() && b[i + 1] == b'=' {
            toks.push(Tok::Op("!=".into()));
            i += 2;
            continue;
        }
        if b[i] == b'>' && i + 1 < b.len() && b[i + 1] == b'>' {
            toks.push(Tok::Op(">>".into()));
            i += 2;
            continue;
        }
        if b[i] == b'=' && i + 1 < b.len() && b[i + 1] == b'>' {
            toks.push(Tok::Op("=>".into()));
            i += 2;
            continue;
        }
        if b[i] == b'=' && i + 1 < b.len() && b[i + 1] == b'=' {
            toks.push(Tok::Op("==".into()));
            i += 2;
            continue;
        }
        if matches!(
            b[i],
            b'+' | b'-' | b'*' | b'/' | b'%' | b'=' | b'<' | b'>' | b'^'
        ) {
            toks.push(Tok::Op((b[i] as char).to_string()));
            i += 1;
            continue;
        }
        if b[i].is_ascii_digit() || (b[i] == b'-' && i + 1 < b.len() && b[i + 1].is_ascii_digit()) {
            let start = i;
            if b[i] == b'-' {
                i += 1;
            }
            while i < b.len() && b[i].is_ascii_digit() {
                i += 1;
            }
            if let Ok(n) = s[start..i].parse::<i64>() {
                toks.push(Tok::Int(n));
            }
            continue;
        }
        if b[i].is_ascii_alphabetic() || b[i] == b'_' {
            let start = i;
            i += 1;
            while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_') {
                i += 1;
            }
            toks.push(Tok::Ident(s[start..i].to_string()));
            continue;
        }
        i += 1;
    }
    toks
}

impl Parser {
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.i)
    }

    fn bump(&mut self) -> Option<Tok> {
        let t = self.toks.get(self.i).cloned();
        if t.is_some() {
            self.i += 1;
        }
        t
    }

    fn eat_op(&mut self, op: &str) -> bool {
        if matches!(self.peek(), Some(Tok::Op(s)) if s == op) {
            self.i += 1;
            true
        } else {
            false
        }
    }

    fn parse_expr(&mut self) -> Result<Formula, ()> {
        if matches!(self.peek(), Some(Tok::Ident(s)) if s == "forall") {
            self.bump();
            let Tok::Ident(var) = self.bump().ok_or(())? else {
                return Err(());
            };
            let mut vars = vec![var];
            while matches!(self.peek(), Some(Tok::Comma)) {
                self.bump();
                let Some(Tok::Ident(next)) = self.bump() else {
                    return Err(());
                };
                vars.push(next);
            }
            if matches!(self.peek(), Some(Tok::Ident(s)) if s == "in") {
                self.bump();
                if matches!(self.peek(), Some(Tok::Ident(_))) {
                    self.bump();
                }
                if matches!(self.peek(), Some(Tok::Comma)) {
                    self.bump();
                }
            }
            if vars.len() == 1 {
                if let Some(Tok::Op(op)) = self.peek().cloned() {
                    if matches!(op.as_str(), ">=" | "<=" | ">" | "<") {
                        self.bump();
                        let cmp = cmp_of(&op).ok_or(())?;
                        let bound = self.parse_sum()?;
                        if matches!(self.peek(), Some(Tok::Colon)) {
                            self.bump();
                        }
                        let body = self.parse_expr()?;
                        return Ok(Formula::BoundForall {
                            var: vars.remove(0),
                            cmp,
                            bound: Box::new(bound),
                            body: Box::new(body),
                        });
                    }
                }
            }
            if matches!(self.peek(), Some(Tok::Colon)) {
                self.bump();
            }
            let body = self.parse_expr()?;
            let mut wrapped = body;
            for var in vars.into_iter().rev() {
                wrapped = Formula::Forall {
                    var,
                    body: Box::new(wrapped),
                };
            }
            return Ok(wrapped);
        }
        self.parse_implies()
    }

    fn parse_implies(&mut self) -> Result<Formula, ()> {
        let mut left = self.parse_or()?;
        while self.eat_op("->") {
            let right = self.parse_or()?;
            left = Formula::Implies(Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_or(&mut self) -> Result<Formula, ()> {
        let mut left = self.parse_and()?;
        while self.eat_op("||") {
            let right = self.parse_and()?;
            left = match left {
                Formula::Or(mut xs) => {
                    xs.push(right);
                    Formula::Or(xs)
                }
                other => Formula::Or(vec![other, right]),
            };
        }
        Ok(left)
    }

    fn parse_and(&mut self) -> Result<Formula, ()> {
        let mut left = self.parse_cmp()?;
        while self.eat_op("&&") {
            let right = self.parse_cmp()?;
            left = match left {
                Formula::And(mut xs) => {
                    xs.push(right);
                    Formula::And(xs)
                }
                other => Formula::And(vec![other, right]),
            };
        }
        Ok(left)
    }

    fn parse_cmp(&mut self) -> Result<Formula, ()> {
        let left = self.parse_sum()?;
        let Some(Tok::Op(op)) = self.peek().cloned() else {
            return Ok(left);
        };
        if let Some(cmp) = cmp_of(&op) {
            self.bump();
            let right = self.parse_sum()?;
            let node = Formula::Cmp(cmp, Box::new(left), Box::new(right));
            if matches!(self.peek(), Some(Tok::Colon)) {
                self.bump();
                let rest = self.parse_expr()?;
                return Ok(Formula::Implies(Box::new(node), Box::new(rest)));
            }
            return Ok(node);
        }
        Ok(left)
    }

    fn parse_sum(&mut self) -> Result<Formula, ()> {
        let mut left = self.parse_product()?;
        loop {
            if self.eat_op("+") {
                let right = self.parse_product()?;
                left = Formula::Arith(Arith::Add, Box::new(left), Box::new(right));
            } else if self.eat_op("-") {
                let right = self.parse_product()?;
                left = Formula::Arith(Arith::Sub, Box::new(left), Box::new(right));
            } else {
                break;
            }
        }
        Ok(left)
    }

    fn parse_product(&mut self) -> Result<Formula, ()> {
        let mut left = self.parse_pow()?;
        loop {
            if self.eat_op("*") {
                let right = self.parse_pow()?;
                left = Formula::Arith(Arith::Mul, Box::new(left), Box::new(right));
            } else if self.eat_op("/") {
                let right = self.parse_pow()?;
                left = Formula::Arith(Arith::FloorDiv, Box::new(left), Box::new(right));
            } else if self.eat_op("%") {
                let right = self.parse_pow()?;
                left = Formula::Arith(Arith::Mod, Box::new(left), Box::new(right));
            } else {
                break;
            }
        }
        Ok(left)
    }

    fn parse_pow(&mut self) -> Result<Formula, ()> {
        let mut left = self.parse_unary()?;
        if self.eat_op("^") {
            let right = self.parse_unary()?;
            left = Formula::Arith(Arith::Pow, Box::new(left), Box::new(right));
        } else if self.eat_op(">>") {
            // Spec `>>` on a subsidy is floor division by a power of two.
            let right = self.parse_unary()?;
            let two = Formula::Lit(2);
            let pow = Formula::Arith(Arith::Pow, Box::new(two), Box::new(right));
            left = Formula::Arith(Arith::FloorDiv, Box::new(left), Box::new(pow));
        }
        Ok(left)
    }

    fn parse_unary(&mut self) -> Result<Formula, ()> {
        if self.eat_op("-") {
            let inner = self.parse_unary()?;
            return Ok(Formula::Arith(
                Arith::Sub,
                Box::new(Formula::Lit(0)),
                Box::new(inner),
            ));
        }
        self.parse_atom()
    }

    fn parse_atom(&mut self) -> Result<Formula, ()> {
        match self.bump() {
            Some(Tok::Int(n)) => Ok(Formula::Lit(n)),
            Some(Tok::Ident(name)) if name == "floor" => {
                if !matches!(self.bump(), Some(Tok::LParen)) {
                    return Err(());
                }
                let inner = self.parse_expr()?;
                if !matches!(self.bump(), Some(Tok::RParen)) {
                    return Err(());
                }
                Ok(Formula::Floor(Box::new(inner)))
            }
            Some(Tok::Ident(name)) if name == "piecewise" => self.parse_piecewise(),
            Some(Tok::Ident(name)) => {
                if matches!(self.peek(), Some(Tok::LParen)) {
                    self.bump();
                    let mut args = Vec::new();
                    if !matches!(self.peek(), Some(Tok::RParen)) {
                        loop {
                            args.push(self.parse_expr()?);
                            if matches!(self.peek(), Some(Tok::Comma)) {
                                self.bump();
                                continue;
                            }
                            break;
                        }
                    }
                    if !matches!(self.bump(), Some(Tok::RParen)) {
                        return Err(());
                    }
                    return Ok(Formula::Call(name, args));
                }
                Ok(Formula::Name(name))
            }
            Some(Tok::LParen) => {
                let inner = self.parse_expr()?;
                if !matches!(self.bump(), Some(Tok::RParen)) {
                    return Err(());
                }
                Ok(inner)
            }
            _ => Err(()),
        }
    }

    fn parse_piecewise(&mut self) -> Result<Formula, ()> {
        if !matches!(self.bump(), Some(Tok::LParen)) {
            return Err(());
        }
        let mut cases = Vec::new();
        let mut otherwise = None;
        if !matches!(self.peek(), Some(Tok::RParen)) {
            loop {
                if matches!(self.peek(), Some(Tok::Ident(s)) if s == "if") {
                    self.bump();
                }
                let cond = self.parse_cmp()?;
                if !self.eat_op("=>") {
                    return Err(());
                }
                let value = self.parse_cmp()?;
                if matches!(&cond, Formula::Name(name) if name == "otherwise") {
                    otherwise = Some(Box::new(value));
                } else {
                    cases.push((cond, value));
                }
                if matches!(self.peek(), Some(Tok::Comma)) {
                    self.bump();
                    continue;
                }
                break;
            }
        }
        if !matches!(self.bump(), Some(Tok::RParen)) {
            return Err(());
        }
        Ok(Formula::Piecewise {
            scrutinee: Box::new(Formula::Name("_".into())),
            cases,
            otherwise,
        })
    }
}

fn cmp_of(op: &str) -> Option<Cmp> {
    Some(match op {
        "<" => Cmp::Lt,
        "<=" => Cmp::Le,
        ">" => Cmp::Gt,
        ">=" => Cmp::Ge,
        "=" | "==" => Cmp::Eq,
        "!=" => Cmp::Ne,
        _ => return None,
    })
}

fn spec_value(name: &str) -> Option<i64> {
    if name == "INITIALSUBSIDY" || name == "INITIAL_SUBSIDY" {
        return i64::try_from(initial_subsidy()).ok();
    }
    let key = match name {
        "H" => "H",
        "C" => "C",
        "MAXMONEY" => "MAX_MONEY",
        other => other,
    };
    protocol_u64_opt(key)
}

fn protocol_u64_opt(name: &str) -> Option<i64> {
    // `protocol_u64` panics when the name is absent. Only known section-4 names.
    const KNOWN: &[&str] = &["H", "C", "MAX_MONEY", "W_MAX", "M_MAX"];
    if !KNOWN.contains(&name) {
        return None;
    }
    i64::try_from(protocol_u64(name)).ok()
}

/// Integer value of a closed spec expression. Names that are not spec constants stay symbolic.
pub fn eval_closed(expr: &Formula) -> Option<i64> {
    match expr {
        Formula::Lit(n) => Some(*n),
        Formula::Name(n) => spec_value(n),
        Formula::Arith(op, l, r) => {
            let l = eval_closed(l)?;
            let r = eval_closed(r)?;
            Some(match op {
                Arith::Add => l.checked_add(r)?,
                Arith::Sub => l.checked_sub(r)?,
                Arith::Mul => l.checked_mul(r)?,
                Arith::FloorDiv => floor_div(l, r)?,
                Arith::TruncDiv => trunc_div(l, r)?,
                Arith::Mod => l.checked_rem(r)?,
                Arith::Pow => pow_i64(l, r)?,
            })
        }
        Formula::Floor(inner) => eval_closed(inner),
        _ => None,
    }
}

fn floor_div(n: i64, d: i64) -> Option<i64> {
    if d == 0 {
        return None;
    }
    let q = n / d;
    let r = n % d;
    if r != 0 && (n < 0) != (d < 0) {
        Some(q - 1)
    } else {
        Some(q)
    }
}

fn trunc_div(n: i64, d: i64) -> Option<i64> {
    if d == 0 {
        return None;
    }
    Some(n / d)
}

fn pow_i64(base: i64, exp: i64) -> Option<i64> {
    if exp < 0 {
        return None;
    }
    let mut acc: i64 = 1;
    for _ in 0..exp {
        acc = acc.checked_mul(base)?;
    }
    Some(acc)
}

/// Defining equations regenerated from a definition sentence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Equations {
    pub cases: Vec<String>,
    pub exhaustiveness: String,
    pub disjointness: String,
}

impl Equations {
    pub fn combined(&self) -> String {
        let mut parts = self.cases.clone();
        parts.push(self.exhaustiveness.clone());
        parts.push(self.disjointness.clone());
        parts.join(" ∧ ")
    }

    /// The Lean file must contain each regenerated statement. A missing one leaves the definition unlocked.
    pub fn covered_by(&self, lean_src: &str) -> bool {
        let src = lean_src.split_whitespace().collect::<Vec<_>>().join(" ");
        self.cases
            .iter()
            .chain([&self.exhaustiveness, &self.disjointness])
            .all(|eq| src.contains(&eq.split_whitespace().collect::<Vec<_>>().join(" ")))
    }
}

/// One equation per piecewise case, plus exhaustiveness and disjointness.
/// The value uses floor division, not a shift. A missing `otherwise` does not cover the domain.
pub fn emit_equations(expr: &Formula) -> Result<Equations, EmitError> {
    let Formula::Cmp(Cmp::Eq, lhs, rhs) = expr else {
        return Err(EmitError::unsupported(
            "a definition equation is an equality",
        ));
    };
    let Formula::Call(name, args) = lhs.as_ref() else {
        return Err(EmitError::unsupported(
            "definition left side is not a function",
        ));
    };
    let Formula::Piecewise {
        cases, otherwise, ..
    } = rhs.as_ref()
    else {
        return Err(EmitError::unsupported("definition is not piecewise"));
    };
    let Some(otherwise) = otherwise else {
        return Err(EmitError::unsupported(
            "piecewise cases do not cover the domain",
        ));
    };
    if cases.is_empty() {
        return Err(EmitError::unsupported("piecewise has no case"));
    }
    let var = match args.first() {
        Some(Formula::Name(v)) => v.clone(),
        _ => return Err(EmitError::unsupported("definition parameter is not a name")),
    };
    let fname = lean_name(name);
    let mut conds = Vec::new();
    let mut case_strs = Vec::new();
    for (cond, value) in cases {
        let cond_s = emit_nat(cond)?;
        let value_s = emit_nat(value)?;
        conds.push(cond_s.clone());
        case_strs.push(format!(
            "∀ ({var} : Nat), ({cond_s}) → ({fname} {var} = {value_s})"
        ));
    }
    let negated = conds
        .iter()
        .map(|cond| format!("¬ ({cond})"))
        .collect::<Vec<_>>()
        .join(" ∧ ");
    let otherwise_s = emit_nat(otherwise)?;
    case_strs.push(format!(
        "∀ ({var} : Nat), ({negated}) → ({fname} {var} = {otherwise_s})"
    ));
    let cover = conds
        .iter()
        .cloned()
        .chain(std::iter::once(format!("({negated})")))
        .collect::<Vec<_>>()
        .join(" ∨ ");
    let mut disjoint = Vec::new();
    for cond in &conds {
        disjoint.push(format!("¬ (({cond}) ∧ ({negated}))"));
    }
    for i in 0..conds.len() {
        for j in (i + 1)..conds.len() {
            disjoint.push(format!("¬ (({}) ∧ ({}))", conds[i], conds[j]));
        }
    }
    Ok(Equations {
        cases: case_strs,
        exhaustiveness: format!("∀ ({var} : Nat), ({cover})"),
        disjointness: format!("∀ ({var} : Nat), ({})", disjoint.join(" ∧ ")),
    })
}

/// Base case, step case, and the induction principle for a recursive definition.
/// The principle is the one for that recursion shape. It is not written per function.
pub struct Induction {
    pub base: String,
    pub step: String,
    pub principle: String,
}

const NAT_PRINCIPLE: &str = "∀ (motive : Nat → Prop), motive 0 → (∀ (n : Nat), motive n → motive (n + 1)) → ∀ (n : Nat), motive n";
const LIST_PRINCIPLE: &str = "∀ (motive : List Nat → Prop), motive [] → (∀ (x : Nat) (xs : List Nat), motive xs → motive (x :: xs)) → ∀ (xs : List Nat), motive xs";

pub fn emit_induction(expr: &Formula) -> Result<Induction, EmitError> {
    let Formula::Rec {
        name,
        var,
        head,
        base,
        step,
        kind,
    } = expr
    else {
        return Err(EmitError::unsupported(
            "induction is emitted from a recursive definition",
        ));
    };
    let fname = lean_name(name);
    let base_s = emit_nat(base)?;
    let step_s = emit_nat(step)?;
    match kind {
        RecKind::Nat => Ok(Induction {
            base: format!("{fname} 0 = {base_s}"),
            step: format!("∀ ({var} : Nat), {fname} ({var} + 1) = {step_s}"),
            principle: NAT_PRINCIPLE.to_string(),
        }),
        RecKind::List => {
            let Some(head) = head else {
                return Err(EmitError::unsupported(
                    "list recursion has no head variable",
                ));
            };
            Ok(Induction {
                base: format!("{fname} [] = {base_s}"),
                step: format!(
                    "∀ ({head} : Nat) ({var} : List Nat), {fname} ({head} :: {var}) = {step_s}"
                ),
                principle: LIST_PRINCIPLE.to_string(),
            })
        }
    }
}

fn emit_nat(expr: &Formula) -> Result<String, EmitError> {
    match expr {
        Formula::Lit(n) => Ok(n.to_string()),
        Formula::Name(n) => Ok(lean_name(n)),
        Formula::Call(name, args) => {
            let args: Result<Vec<_>, _> = args.iter().map(emit_nat).collect();
            Ok(format!("{} {}", lean_name(name), args?.join(" ")))
        }
        Formula::Floor(inner) => emit_nat(inner),
        Formula::Not(inner) => Ok(format!("¬ ({})", emit_nat(inner)?)),
        Formula::Cmp(op, l, r) => Ok(format!(
            "{} {} {}",
            emit_nat(l)?,
            lean_cmp(*op),
            emit_nat(r)?
        )),
        Formula::Arith(Arith::FloorDiv, l, r) | Formula::Arith(Arith::TruncDiv, l, r) => {
            Ok(format!("({} / {})", emit_nat(l)?, emit_nat(r)?))
        }
        Formula::Arith(Arith::Pow, l, r) => Ok(format!("({} ^ {})", emit_nat(l)?, emit_nat(r)?)),
        Formula::Arith(op, l, r) => Ok(format!(
            "({} {} {})",
            emit_nat(l)?,
            lean_arith(*op),
            emit_nat(r)?
        )),
        _ => Err(EmitError::unsupported(
            "equation operand is not a natural-number term",
        )),
    }
}

/// Lean statement. Subtraction is `Int` subtraction. Floor division is `Int.fdiv`.
pub fn emit_lean(expr: &Formula) -> Result<String, EmitError> {
    match expr {
        Formula::Lit(n) => Ok(n.to_string()),
        Formula::Name(n) => Ok(lean_name(n)),
        Formula::Call(name, args) => {
            let args: Result<Vec<_>, _> = args.iter().map(emit_lean).collect();
            Ok(format!("{} {}", lean_name(name), args?.join(" ")))
        }
        Formula::Floor(inner) => {
            let inner = emit_lean(inner)?;
            Ok(format!("(Int.fdiv ({inner}) 1)"))
        }
        Formula::Not(inner) => Ok(format!("¬ ({})", emit_lean(inner)?)),
        Formula::And(xs) => join_lean(xs, "∧"),
        Formula::Or(xs) => join_lean(xs, "∨"),
        Formula::Implies(a, b) => Ok(format!("({} → {})", emit_lean(a)?, emit_lean(b)?)),
        Formula::Cmp(op, _l, r)
            if *op == Cmp::Eq && matches!(r.as_ref(), Formula::Piecewise { .. }) =>
        {
            let eqs = emit_equations(expr)?;
            Ok(eqs.combined())
        }
        Formula::Cmp(op, l, r) => Ok(format!(
            "({} {} {})",
            emit_lean(l)?,
            lean_cmp(*op),
            emit_lean(r)?
        )),
        Formula::Arith(Arith::Sub, l, r) => Ok(format!(
            "(({} : Int) - ({} : Int))",
            emit_lean(l)?,
            emit_lean(r)?
        )),
        Formula::Arith(Arith::FloorDiv, l, r) => Ok(format!(
            "(Int.fdiv ({} : Int) ({} : Int))",
            emit_lean(l)?,
            emit_lean(r)?
        )),
        Formula::Arith(Arith::TruncDiv, l, r) => Ok(format!(
            "(Int.tdiv ({} : Int) ({} : Int))",
            emit_lean(l)?,
            emit_lean(r)?
        )),
        Formula::Arith(Arith::Mod, l, r) => Ok(format!(
            "(Int.fmod ({} : Int) ({} : Int))",
            emit_lean(l)?,
            emit_lean(r)?
        )),
        Formula::Arith(op, l, r) => Ok(format!(
            "({} {} {})",
            emit_lean(l)?,
            lean_arith(*op),
            emit_lean(r)?
        )),
        Formula::BoundForall {
            var,
            cmp,
            bound,
            body,
        } => Ok(format!(
            "∀ ({} : Nat), {} {} {} → {}",
            var,
            var,
            lean_cmp(*cmp),
            emit_lean(bound)?,
            emit_lean(body)?
        )),
        Formula::Forall { var, body } => Ok(format!("∀ ({} : Nat), {}", var, emit_lean(body)?)),
        Formula::Rec { .. } => {
            let ind = emit_induction(expr)?;
            Ok(format!("{} ∧ {} ∧ {}", ind.base, ind.step, ind.principle))
        }
        Formula::Sum { var, lo, hi, body } => Ok(format!(
            "(Finset.sum (Finset.Icc ({}) ({})) (fun {} => {}))",
            emit_lean(lo)?,
            emit_lean(hi)?,
            var,
            emit_lean(body)?
        )),
        Formula::Piecewise { .. } => Err(EmitError::unsupported(
            "piecewise equations are emitted from the definition equality",
        )),
    }
}

fn join_lean(xs: &[Formula], op: &str) -> Result<String, EmitError> {
    let parts: Result<Vec<_>, _> = xs.iter().map(emit_lean).collect();
    Ok(format!("({})", parts?.join(&format!(" {op} "))))
}

fn lean_name(name: &str) -> String {
    match name {
        "GetBlockSubsidy" => "getBlockSubsidy".into(),
        "TotalSupply" => "totalSupply".into(),
        "INITIALSUBSIDY" => "initialSubsidy".into(),
        "MAXMONEY" => "maxMoney".into(),
        "CheckTransaction" => "checkTransaction".into(),
        "SighashBase" => "sighashBase".into(),
        other => other.to_string(),
    }
}

fn lean_cmp(op: Cmp) -> &'static str {
    match op {
        Cmp::Lt => "<",
        Cmp::Le => "≤",
        Cmp::Gt => ">",
        Cmp::Ge => "≥",
        Cmp::Eq => "=",
        Cmp::Ne => "≠",
    }
}

fn lean_arith(op: Arith) -> &'static str {
    match op {
        Arith::Add => "+",
        Arith::Sub => "-",
        Arith::Mul => "*",
        Arith::FloorDiv => "/",
        Arith::TruncDiv => "/",
        Arith::Mod => "%",
        Arith::Pow => "^",
    }
}

/// Z3 clause for a bounded universal over the function's integer parameter.
/// Any other shape is `unsupported` on the Z3 side.
pub fn emit_z3(expr: &Formula, param: &str) -> Result<Z3Clause, EmitError> {
    let Formula::BoundForall {
        cmp, bound, body, ..
    } = expr
    else {
        return Err(EmitError::unsupported(
            "Z3 clause is only a bounded universal over one integer parameter",
        ));
    };
    let Formula::Cmp(Cmp::Eq, call, rhs) = body.as_ref() else {
        return Err(EmitError::unsupported(
            "bounded universal body is not an equality",
        ));
    };
    if !matches!(call.as_ref(), Formula::Call(_, _)) {
        return Err(EmitError::unsupported("equality is not a function call"));
    }
    let bound_n = eval_closed(bound)
        .ok_or_else(|| EmitError::unsupported("bound does not evaluate from spec constants"))?;
    let rhs_n = eval_closed(rhs)
        .ok_or_else(|| EmitError::unsupported("right-hand side is not a spec constant"))?;
    let rel = match cmp {
        Cmp::Ge => ">=",
        Cmp::Le => "<=",
        Cmp::Gt => ">",
        Cmp::Lt => "<",
        Cmp::Eq | Cmp::Ne => {
            return Err(EmitError::unsupported(
                "bound comparison is not an inequality",
            ));
        }
    };
    Ok(Z3Clause {
        requires: format!("{param} {rel} {bound_n}"),
        ensures: format!("result == {rhs_n}"),
        domain: "u64",
    })
}

/// `floor(-7/2) = -4` under the emitted `Int.fdiv` statement.
pub fn floor_neg_seven_over_two() -> Result<String, EmitError> {
    let expr = Formula::Cmp(
        Cmp::Eq,
        Box::new(Formula::Arith(
            Arith::FloorDiv,
            Box::new(Formula::Lit(-7)),
            Box::new(Formula::Lit(2)),
        )),
        Box::new(Formula::Lit(-4)),
    );
    let lean = emit_lean(&expr)?;
    if !lean.contains("Int.fdiv") {
        return Err(EmitError::unsupported("floor did not emit Int.fdiv"));
    }
    if lean.contains("Int.tdiv") {
        return Err(EmitError::unsupported("floor emitted truncating division"));
    }
    let got = floor_div(-7, 2).ok_or_else(|| EmitError::unsupported("div0"))?;
    if got != -4 {
        return Err(EmitError::unsupported(format!("floor(-7/2) = {got}")));
    }
    Ok(lean)
}

/// A spec subtraction must mention `Int` subtraction, never truncating `Nat.sub`.
pub fn subtraction_is_int(expr: &Formula) -> Result<String, EmitError> {
    let lean = emit_lean(expr)?;
    if lean.contains("Nat.sub") || lean.contains("Nat.pred") {
        return Err(EmitError::unsupported("truncating Nat subtraction"));
    }
    if !lean.contains(": Int)") {
        return Err(EmitError::unsupported("subtraction was not emitted as Int"));
    }
    Ok(lean)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn theorem_6212_emits_both_sides() {
        if !crate::parser::spec_expr::spec_present() {
            return;
        }
        let raw = r"\forall h \geq 33 \times H: \text{GetBlockSubsidy}(h) = 0";
        let expr = parse_sentence(raw).expect("parse");
        let z3 = emit_z3(&expr, "height").expect("z3");
        assert_eq!(z3.requires, "height >= 6930000");
        assert_eq!(z3.ensures, "result == 0");
        assert_eq!(z3.domain, "u64");
        let lean = emit_lean(&expr).expect("lean");
        assert!(lean.contains("getBlockSubsidy"));
        assert!(lean.contains('∀'));
        assert!(!lean.contains("unsupported"));
    }

    #[test]
    fn subsidy_cases_emit_division_equations() {
        if !crate::parser::spec_expr::spec_present() {
            return;
        }
        let raw = r#"\text{GetBlockSubsidy}(h) = \begin{cases}
0 & \text{if } \lfloor h/H \rfloor \geq 64 \\
\text{INITIAL\_SUBSIDY} \gg \lfloor h/H \rfloor & \text{otherwise}
\end{cases}"#;
        let norm = normalize(raw);
        let expr = parse_sentence(raw).unwrap_or_else(|| panic!("parse\n{norm}"));
        let eqs = emit_equations(&expr).expect("equations");
        let joined = eqs.combined();
        assert!(joined.contains("getBlockSubsidy h = 0"), "{joined}");
        assert!(
            joined.contains("initialSubsidy / (2 ^ (h / H))"),
            "{joined}"
        );
        assert!(!joined.contains(">>>"), "{joined}");
        assert!(eqs.exhaustiveness.contains('∨'), "{}", eqs.exhaustiveness);
        assert!(eqs.disjointness.contains('¬'), "{}", eqs.disjointness);
        let lean_path = crate::parser::spec_expr::spec_checkout().join("lean/SpecLock/Defeq.lean");
        let lean = std::fs::read_to_string(&lean_path)
            .unwrap_or_else(|err| panic!("read {}: {err}", lean_path.display()));
        assert!(eqs.covered_by(&lean), "{joined}");
    }

    #[test]
    fn piecewise_without_otherwise_stays_unlocked() {
        let raw = r#"\text{GetBlockSubsidy}(h) = \begin{cases}
0 & \text{if } \lfloor h/H \rfloor \geq 64
\end{cases}"#;
        let expr = parse_sentence(raw).expect("parse");
        assert!(emit_equations(&expr).is_err());
    }

    #[test]
    fn theorem_621_parses_two_variables() {
        let raw = r"\forall h_1, h_2 \in \mathbb{N}, h_1 \leq h_2: \text{TotalSupply}(h_1) \leq \text{TotalSupply}(h_2)";
        let expr = parse_sentence(raw).expect("parse");
        let lean = emit_lean(&expr).expect("lean");
        assert!(lean.contains("totalSupply"));
        assert!(emit_z3(&expr, "h").is_err());
    }

    #[test]
    fn synthetic_bounded_universal_is_not_subsidy() {
        let expr = parse_sentence("forall x <= 7: otherFn(x) = 3").expect("parse");
        let z3 = emit_z3(&expr, "x").expect("z3");
        assert_eq!(z3.requires, "x <= 7");
        assert_eq!(z3.ensures, "result == 3");
        let lean = emit_lean(&expr).unwrap();
        assert!(lean.contains("otherFn"));
        assert!(!lean.contains("getBlockSubsidy"));
        assert!(!lean.contains('H'));
    }

    #[test]
    fn sighash_base_is_lean_only() {
        let raw = r"\forall byte: \text{SighashBase}(byte) = byte \% 32";
        let expr = parse_sentence(raw).expect("parse");
        let lean = emit_lean(&expr).expect("lean");
        assert!(lean.contains("sighashBase"), "{lean}");
        assert!(lean.contains("Int.fmod"), "{lean}");
        assert!(lean.contains("32"), "{lean}");
        assert!(emit_z3(&expr, "byte").is_err());
    }

    #[test]
    fn unbounded_forall_is_lean_only() {
        let expr = parse_sentence("forall h: TotalSupply(h) <= MAXMONEY").expect("parse");
        assert!(emit_z3(&expr, "h").is_err());
        assert!(emit_lean(&expr).unwrap().contains('∀'));
    }

    #[test]
    fn floor_of_negative_is_minus_four() {
        let lean = floor_neg_seven_over_two().unwrap();
        assert!(lean.contains("Int.fdiv"));
        assert!(lean.contains("-4"));
        assert_eq!(trunc_div(-7, 2), Some(-3));
    }

    #[test]
    fn subtraction_does_not_truncate_on_nat() {
        let expr = parse_sentence("a - b").unwrap();
        let lean = subtraction_is_int(&expr).unwrap();
        assert!(lean.contains(": Int"));
        let bad = "Nat.sub a b";
        assert!(bad.contains("Nat.sub"));
    }

    #[test]
    fn unparsed_sentence_is_none() {
        assert!(parse_sentence("this is prose without a formula").is_none());
    }

    #[test]
    fn recursion_emits_base_step_and_one_principle() {
        let supply = parse_sentence(
            r"\text{TotalSupply}(0) = \text{GetBlockSubsidy}(0); \text{TotalSupply}(h + 1) = \text{TotalSupply}(h) + \text{GetBlockSubsidy}(h + 1)",
        )
        .expect("parse");
        let supply = emit_induction(&supply).expect("induction");
        assert_eq!(supply.base, "totalSupply 0 = getBlockSubsidy 0");
        assert_eq!(
            supply.step,
            "∀ (h : Nat), totalSupply (h + 1) = (totalSupply h + getBlockSubsidy (h + 1))"
        );
        assert!(supply.principle.contains("motive 0"));
        assert!(supply.principle.contains("motive (n + 1)"));
        assert!(!supply.principle.contains("totalSupply"));
        assert!(emit_z3(
            &parse_sentence(
                r"\text{TotalSupply}(0) = \text{GetBlockSubsidy}(0); \text{TotalSupply}(h + 1) = \text{TotalSupply}(h) + \text{GetBlockSubsidy}(h + 1)",
            )
            .unwrap(),
            "h",
        )
        .is_err());

        let other =
            emit_induction(&parse_sentence("other(0) = 0; other(n + 1) = other(n) + 1").unwrap())
                .unwrap();
        assert_eq!(other.base, "other 0 = 0");
        assert_eq!(supply.principle, other.principle);

        let chain = emit_induction(
            &parse_sentence(
                "chainWork(nil) = 0; chainWork(cons(w, ws)) = chainWork(ws) + blockWork(w)",
            )
            .unwrap(),
        )
        .unwrap();
        let other_fold = emit_induction(
            &parse_sentence("otherFold(nil) = 1; otherFold(cons(a, as)) = otherFold(as)").unwrap(),
        )
        .unwrap();
        assert_eq!(chain.base, "chainWork [] = 0");
        assert!(chain.step.contains("chainWork (w :: ws)"));
        assert!(chain.step.contains("blockWork w"));
        assert!(!chain.principle.contains("chainWork"));
        assert_eq!(chain.principle, other_fold.principle);
        assert!(chain.principle.contains("motive []"));
        assert!(chain.principle.contains("x :: xs"));
    }

    #[test]
    fn sum_emits_finset() {
        let expr = parse_sentence("forall h: s = a + b").unwrap();
        assert!(matches!(expr, Formula::Forall { .. }));
        let summed = Formula::Sum {
            var: "i".into(),
            lo: Box::new(Formula::Lit(0)),
            hi: Box::new(Formula::Name("h".into())),
            body: Box::new(Formula::Call(
                "GetBlockSubsidy".into(),
                vec![Formula::Name("i".into())],
            )),
        };
        let lean = emit_lean(&summed).unwrap();
        assert!(lean.contains("Finset.sum"));
        assert!(emit_z3(&summed, "h").is_err());
    }

    /// `==` must tokenize as one comparison. Formulas from PROTOCOL.md §5.5 / BIP112.
    #[test]
    fn double_equals_formulas_parse() {
        for (raw, rhs) in [
            // F_CsvVersionBelowTwoFails
            ("$$result == false$$", "false"),
            // F_CsvDisableBitSkipsVersion
            ("$$result == true$$", "true"),
            // F_EvalSeqLocksTimeMet
            (r"$$result == true$$", "true"),
        ] {
            let expr = parse_sentence(raw).unwrap_or_else(|| panic!("parse {raw}"));
            match expr {
                Formula::Cmp(Cmp::Eq, l, r) => {
                    assert_eq!(*l, Formula::Name("result".into()), "{raw}");
                    assert!(
                        matches!(*r, Formula::Name(ref n) if n == rhs),
                        "{raw}: {r:?}"
                    );
                }
                other => panic!("{raw}: expected Eq, got {other:?}"),
            }
        }
    }

    /// F_HeaderTimestampAfterMtp / F_Bip94Timewarp: `timestamp` must survive
    /// the `times` -> `*` rewrite.
    #[test]
    fn timestamp_is_not_rewritten_as_times() {
        assert!(normalize("timestamp").contains("timestamp"));
        assert!(!normalize("timestamp").contains('*'));
        assert_eq!(
            normalize("a times b")
                .split_whitespace()
                .collect::<Vec<_>>(),
            ["a", "*", "b"]
        );
        assert!(normalize(r"a\times b").contains('*'));
        for raw in [
            "$$(timestamp > mtp) == result$$",
            "$$(timestamp + 600 >= parent_time) == result$$",
        ] {
            let expr = parse_sentence(raw).unwrap_or_else(|| panic!("parse {raw}"));
            let Formula::Cmp(Cmp::Eq, l, r) = expr else {
                panic!("{raw}: expected Eq");
            };
            assert_eq!(*r, Formula::Name("result".into()), "{raw}");
            assert!(format!("{l:?}").contains("timestamp"), "{raw}: {l:?}");
        }
    }
}
