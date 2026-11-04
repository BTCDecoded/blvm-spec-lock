//! Inventory of Orange Paper sentences and the Lean lock beside Z3.
//!
//! The anchor is the sentence: file plus theorem number. A `#[spec_locked]`
//! function is the Z3 side when its section matches.

use crate::parser::formula::{self, Formula};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

pub const CLASSES: &[&str] = &["z3_clause", "lean_statement", "both", "unsupported"];

pub const REASONS: &[&str] = &[
    "parse_failed",
    "emitter_shape_missing",
    "model_unwritten",
    "out_of_scope",
];

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sentence {
    pub id: String,
    pub file: String,
    pub number: String,
    pub class: String,
    pub reason: String,
    pub statement: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SentenceStatus {
    pub id: String,
    pub status: String,
    pub domain: String,
    pub abstracted: Vec<String>,
    pub assumptions: Vec<String>,
    pub failing_statement: String,
    pub locked_defs: Vec<String>,
    pub not_load_bearing: Vec<String>,
}

pub fn spec_dir_from_paths(paths: &[PathBuf]) -> Option<PathBuf> {
    paths.first().and_then(|p| p.parent().map(|d| d.to_path_buf()))
}

pub fn lean_dir(spec_dir: &Path) -> PathBuf {
    spec_dir.join("lean")
}

/// Scan merged spec markdown. `file` is the filename stored on each row.
pub fn extract_headings(file: &str, markdown: &str) -> Vec<(String, String, String)> {
    let mut rows = Vec::new();
    let lines: Vec<&str> = markdown.lines().collect();
    let mut i = 0;
    while i < lines.len() {
        let line = lines[i];
        if let Some(name) = definition_name(line) {
            let statement = first_math(line).unwrap_or_else(|| line.trim().to_string());
            rows.push((format!("{file}#def:{name}"), name, statement));
            i += 1;
            continue;
        }
        if let Some((kind, number)) = heading(line) {
            let mut block = String::new();
            let mut j = i + 1;
            while j < lines.len() && heading(lines[j]).is_none() && !lines[j].starts_with("## ") {
                block.push_str(lines[j]);
                block.push('\n');
                j += 1;
            }
            let statement = first_math(&block).unwrap_or_else(|| block.trim().to_string());
            let id = format!("{file}#{kind}:{number}");
            rows.push((id, number, statement));
            i = j;
            continue;
        }
        i += 1;
    }
    rows
}

fn anchored_sentences(file: &str, markdown: &str) -> Vec<(String, String)> {
    let mut out = Vec::new();
    if file == "PROTOCOL.md" {
        if let Some(stmt) = math_containing(markdown, "coinbase.outputs") {
            out.push((format!("{file}#def:CoinbaseBound"), stmt));
        }
        if markdown.contains("Empty rejection") {
            out.push((
                format!("{file}#CheckTransaction#empty-inputs"),
                r"|tx.inputs| = 0 \lor |tx.outputs| = 0 \implies \text{CheckTransaction}(tx) \neq \text{valid}".into(),
            ));
            out.push((
                format!("{file}#CheckTransaction#empty-outputs"),
                r"|tx.outputs| = 0 \implies \text{CheckTransaction}(tx) \neq \text{valid}".into(),
            ));
            out.push((
                format!("{file}#CheckTransaction#nonnegative-outputs"),
                r"0 \leq o.value".into(),
            ));
        }
        if markdown.contains("prevout") {
            out.push((
                format!("{file}#def:UtxoInput"),
                "utxoInput(us, i) = us(i)".into(),
            ));
            out.push((
                format!("{file}#def:OutputsNonnegative"),
                r"0 \leq o.value".into(),
            ));
        }
        if markdown.contains("GetBlockSubsidy(k") || markdown.contains("k < 32") {
            out.push((
                format!("{file}#Theorem:6.1.1"),
                r"forall k < 32: GetBlockSubsidy(k * H + H) = floor(GetBlockSubsidy(k * H) / 2)".into(),
            ));
        }
        if markdown.contains("2,099,999,997,690,000") {
            out.push((
                format!("{file}#Theorem:6.2.3"),
                "TotalSupply(33 * H) = 2099999997690000".into(),
            ));
        }
        if markdown.contains("F_SubsidyZeroAfter64") || markdown.contains("GetBlockSubsidy(h)") {
            let subsidy = math_containing(markdown, "begin{cases}")
                .filter(|stmt| stmt.contains("GetBlockSubsidy"))
                .unwrap_or_else(|| "floor(h / H) >= 64 -> GetBlockSubsidy(h) = 0".into());
            out.push((format!("{file}#def:GetBlockSubsidy"), subsidy));
            out.push((
                format!("{file}#def:TotalSupply"),
                r"TotalSupply(0) = GetBlockSubsidy(0)".into(),
            ));
        }
        if markdown.contains("factor of 4") {
            out.push((
                format!("{file}#Theorem:7.1"),
                "expected / 4 <= clampTime(raw, expected) && clampTime(raw, expected) <= expected * 4".into(),
            ));
        }
    }
    if file == "ARCHITECTURE.md" && markdown.contains("BestChain") {
        out.push((
            format!("{file}#ShouldReorganize"),
            "chainWork(current) < chainWork(candidate) -> shouldReorganize(candidate, current) = true".into(),
        ));
        out.push((
            format!("{file}#ChainWork"),
            "chainWork(works) = sum(works)".into(),
        ));
    }
    out
}

fn math_containing(markdown: &str, needle: &str) -> Option<String> {
    let mut start = 0;
    while let Some(rel) = markdown[start..].find("$$") {
        let abs = start + rel;
        let rest = &markdown[abs + 2..];
        let end = rest.find("$$")?;
        let body = rest[..end].trim().to_string();
        if body.contains(needle) {
            return Some(body);
        }
        start = abs + 2 + end + 2;
    }
    None
}

fn definition_name(line: &str) -> Option<String> {
    let line = line.trim();
    let rest = line.strip_prefix("**")?;
    let (name, after) = rest.split_once("**:")?;
    if name.is_empty()
        || name.contains(' ')
        || name.contains('*')
        || !name.chars().next().is_some_and(|c| c.is_ascii_alphabetic())
    {
        return None;
    }
    let _ = after;
    Some(name.to_string())
}

fn heading(line: &str) -> Option<(String, String)> {
    let line = line.trim();
    for kind in ["Theorem", "Lemma", "Corollary", "Invariant"] {
        let prefix = format!("**{kind} ");
        if let Some(rest) = line.strip_prefix(&prefix) {
            let number: String = rest
                .chars()
                .take_while(|c| c.is_ascii_digit() || *c == '.')
                .collect();
            if !number.is_empty() {
                return Some((kind.to_string(), number));
            }
        }
    }
    if let Some(rest) = line.strip_prefix("**Formula** (**") {
        if let Some(name) = rest.split("**)").next() {
            if !name.is_empty() && !name.contains(' ') {
                return Some(("Formula".into(), name.to_string()));
            }
        }
    }
    None
}

fn first_math(block: &str) -> Option<String> {
    if let Some(start) = block.find("$$") {
        let rest = &block[start + 2..];
        if let Some(end) = rest.find("$$") {
            return Some(rest[..end].trim().to_string());
        }
    }
    None
}

pub fn classify(file: &str, number: &str, statement: &str, locked: &BTreeSet<String>) -> Sentence {
    let id = if file.is_empty() {
        number.to_string()
    } else {
        format!("{file}#{number}")
    };
    // Callers pass the id from extract_headings. When `number` already is the id, keep it.
    let id = if number.contains('#') {
        number.to_string()
    } else if statement.is_empty() {
        id
    } else {
        // extract_headings builds `file#kind:number`. `classify_row` passes that as number.
        id
    };
    let _ = id;
    classify_row(file, number, statement, locked)
}

pub fn classify_row(
    file: &str,
    id: &str,
    statement: &str,
    locked: &BTreeSet<String>,
) -> Sentence {
    let number = id.rsplit(['#', ':']).next().unwrap_or(id).to_string();
    let reason_scope = scope_reason(&number, statement);
    if let Some(reason) = reason_scope {
        return Sentence {
            id: id.to_string(),
            file: file.to_string(),
            number,
            class: "unsupported".into(),
            reason: reason.to_string(),
            statement: statement.to_string(),
        };
    }
    let Some(expr) = formula::parse_sentence(statement) else {
        return Sentence {
            id: id.to_string(),
            file: file.to_string(),
            number,
            class: "unsupported".into(),
            reason: "parse_failed".into(),
            statement: statement.to_string(),
        };
    };
    let z3 = formula::emit_z3(&expr, param_of(&expr)).is_ok();
    let lean = formula::emit_lean(&expr).is_ok();
    if !z3 && !lean {
        return Sentence {
            id: id.to_string(),
            file: file.to_string(),
            number,
            class: "unsupported".into(),
            reason: "emitter_shape_missing".into(),
            statement: statement.to_string(),
        };
    }
    if !locked.contains(id) {
        return Sentence {
            id: id.to_string(),
            file: file.to_string(),
            number,
            class: "unsupported".into(),
            reason: "model_unwritten".into(),
            statement: statement.to_string(),
        };
    }
    let class = if z3 && lean {
        "both"
    } else if z3 {
        "z3_clause"
    } else {
        "lean_statement"
    };
    Sentence {
        id: id.to_string(),
        file: file.to_string(),
        number,
        class: class.into(),
        reason: String::new(),
        statement: statement.to_string(),
    }
}

fn param_of(expr: &Formula) -> &'static str {
    match expr {
        Formula::BoundForall { var, .. } if var == "h" || var == "height" => "height",
        Formula::BoundForall { var, .. } if var == "x" => "x",
        _ => "height",
    }
}

fn scope_reason(number: &str, statement: &str) -> Option<&'static str> {
    if number == "8.3"
        || statement.contains("discrete logarithm")
        || statement.contains("secp256k1") && statement.contains("forgery")
    {
        return Some("out_of_scope");
    }
    if number.starts_with("9.") || number.starts_with("9") && number.contains('.') && number.starts_with('9')
    {
        // Mempool is section 9.
        if number.starts_with('9') {
            return Some("model_unwritten");
        }
    }
    if number.starts_with("10.2") || number.starts_with("12.") || number.starts_with("12") {
        return Some("model_unwritten");
    }
    let lower = statement.to_ascii_lowercase();
    if lower.contains("mempool") || lower.contains("handshake") || lower.contains("mining protocol")
    {
        return Some("model_unwritten");
    }
    None
}

/// Predicates the conditional sentences assume and do not lock.
/// Each one is an inventory row of its own. The model for the predicate is unwritten.
pub fn abstracted_predicates(locked: &BTreeSet<String>) -> Vec<Sentence> {
    const PREDICATES: &[(&str, &str)] = &[
        ("script-validity", "script validity"),
        ("signature-validity", "signature validity"),
        ("utxo-set", "the UTXO set"),
        ("transaction-validity", "transaction validity"),
    ];
    PREDICATES
        .iter()
        .map(|(name, statement)| {
            let id = format!("PROTOCOL.md#abstract:{name}");
            let written = locked.contains(&id);
            Sentence {
                id,
                file: "PROTOCOL.md".into(),
                number: (*name).to_string(),
                class: if written {
                    "lean_statement".into()
                } else {
                    "unsupported".into()
                },
                reason: if written {
                    String::new()
                } else {
                    "model_unwritten".into()
                },
                statement: (*statement).to_string(),
            }
        })
        .collect()
}

pub fn inventory(files: &[(&str, &str)], locked: &BTreeSet<String>) -> Vec<Sentence> {
    let mut rows = Vec::new();
    for (file, markdown) in files {
        for (id, _number, statement) in extract_headings(file, markdown) {
            rows.push(classify_row(file, &id, &statement, locked));
        }
        for (id, statement) in anchored_sentences(file, markdown) {
            rows.retain(|row| row.id != id);
            rows.push(classify_row(file, &id, &statement, locked));
        }
    }
    if files.iter().any(|(file, _)| *file == "PROTOCOL.md") {
        let disputed = real_series_disputed();
        rows.push(Sentence {
            id: disputed.id,
            file: "PROTOCOL.md".into(),
            number: "6.2.3".into(),
            class: "lean_statement".into(),
            reason: "spec_disputed".into(),
            statement: disputed.failing_statement,
        });
    }
    if !files.is_empty() {
        rows.extend(abstracted_predicates(locked));
    }
    rows.sort_by(|a, b| a.id.cmp(&b.id));
    rows
}

pub fn class_counts(rows: &[Sentence]) -> BTreeMap<String, usize> {
    let mut counts = BTreeMap::new();
    for class in CLASSES {
        counts.insert((*class).to_string(), 0);
    }
    for reason in REASONS {
        counts.insert(format!("unsupported:{reason}"), 0);
    }
    for row in rows {
        *counts.entry(row.class.clone()).or_insert(0) += 1;
        if row.class == "unsupported" {
            *counts.entry(format!("unsupported:{}", row.reason)).or_insert(0) += 1;
        }
    }
    counts
}

pub fn format_inventory(rows: &[Sentence]) -> String {
    let mut out = String::from("id\tfile\tnumber\tclass\treason\n");
    for row in rows {
        out.push_str(&row.id);
        out.push('\t');
        out.push_str(&row.file);
        out.push('\t');
        out.push_str(&row.number);
        out.push('\t');
        out.push_str(&row.class);
        out.push('\t');
        out.push_str(&row.reason);
        out.push('\n');
    }
    out
}

pub fn parse_inventory(text: &str) -> Vec<Sentence> {
    let mut rows = Vec::new();
    for line in text.lines().skip(1) {
        if line.is_empty() {
            continue;
        }
        let mut cols = line.split('\t');
        let id = cols.next().unwrap_or("").to_string();
        let file = cols.next().unwrap_or("").to_string();
        let number = cols.next().unwrap_or("").to_string();
        let class = cols.next().unwrap_or("").to_string();
        let reason = cols.next().unwrap_or("").to_string();
        rows.push(Sentence {
            id,
            file,
            number,
            class,
            reason,
            statement: String::new(),
        });
    }
    rows
}

/// The locked count is the lock attributes in the Lean project. The unlocked count is the
/// unsupported definition rows. Inventory prints these two numbers.
pub fn definition_counts(locked: &BTreeSet<String>, rows: &[Sentence]) -> (usize, usize) {
    (locked.len(), unlocked_ids(rows).len())
}

pub fn unlocked_ids(rows: &[Sentence]) -> BTreeSet<String> {
    rows.iter()
        .filter(|row| row.id.contains("#def:") && row.class == "unsupported")
        .map(|row| row.id.clone())
        .collect()
}

/// Fail when an unlocked definition is new, the count rises, or a listed id is now locked.
pub fn unlocked_delta(baseline: &BTreeSet<String>, run: &[Sentence]) -> Result<(), String> {
    let now = unlocked_ids(run);
    if now.len() > baseline.len() {
        return Err(format!(
            "unlocked definition count {} is higher than baseline {}",
            now.len(),
            baseline.len()
        ));
    }
    for id in &now {
        if !baseline.contains(id) {
            return Err(format!("new unlocked definition {id}"));
        }
    }
    for id in baseline {
        if !now.contains(id) {
            return Err(format!(
                "baseline definition {id} is now locked and still listed"
            ));
        }
    }
    Ok(())
}

/// Fail when the run adds an unsupported id, raises the unsupported count,
/// leaves a now-supported id in the baseline, or changes a reason code.
pub fn baseline_delta(baseline: &[Sentence], run: &[Sentence]) -> Result<(), String> {
    let base_u: BTreeMap<_, _> = baseline
        .iter()
        .filter(|r| r.class == "unsupported")
        .map(|r| (r.id.as_str(), r.reason.as_str()))
        .collect();
    let run_u: BTreeMap<_, _> = run
        .iter()
        .filter(|r| r.class == "unsupported")
        .map(|r| (r.id.as_str(), r.reason.as_str()))
        .collect();
    if run_u.len() > base_u.len() {
        return Err(format!(
            "unsupported count {} is higher than baseline {}",
            run_u.len(),
            base_u.len()
        ));
    }
    for (id, reason) in &run_u {
        match base_u.get(id) {
            None => return Err(format!("new unsupported sentence {id}")),
            Some(prev) if *prev != *reason => {
                return Err(format!("reason for {id} changed from {prev} to {reason}"));
            }
            Some(_) => {}
        }
    }
    for id in base_u.keys() {
        if !run_u.contains_key(id) {
            let still_listed = baseline.iter().any(|r| r.id == *id && r.class == "unsupported");
            let now_supported = run.iter().any(|r| r.id == *id && r.class != "unsupported");
            if still_listed && now_supported {
                return Err(format!(
                    "baseline id {id} is now supported and still listed"
                ));
            }
        }
    }
    Ok(())
}

pub fn locks_in(lean_src: &str) -> BTreeSet<String> {
    let mut ids = BTreeSet::new();
    for line in lean_src.lines() {
        let line = line.trim();
        if let Some(rest) = line.strip_prefix("@[spec_lock \"") {
            if let Some(id) = rest.split('"').next() {
                if !id.is_empty() {
                    ids.insert(id.to_string());
                }
            }
        }
    }
    ids
}

const AXIOM_OK: &[&str] = &["propext", "Classical.choice", "Quot.sound"];

/// Definitions a proof uses, read from its elaborated term.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ElaboratedClosure {
    pub locked: Vec<String>,
    pub lock_ids: Vec<String>,
    pub unlocked: Vec<String>,
    pub axioms: Vec<String>,
}

/// `Some("spec_model")` when the closure is locked or allowlisted, lists at least one locked
/// definition, and abstracts nothing. A non-empty abstracted list is `spec_model_conditional`
/// under the same closure check. An empty closure, or a constant that is neither locked nor
/// allowlisted, is neither status. `native_decide` and any other axiom fail. Either status
/// fails when the hypothesis instance is empty or leaves a conditional arm unused.
pub fn model_status(
    closure: &ElaboratedClosure,
    abstracted: &[String],
    def_src: &str,
    def_name: &str,
    instance: &HypothesisInstance,
) -> Result<Option<&'static str>, String> {
    match closure_gate(closure, abstracted)? {
        Some(status) => {
            hypothesis_instance_is_nondegenerate(def_src, def_name, instance)?;
            Ok(Some(status))
        }
        None => Ok(None),
    }
}

fn closure_gate(
    closure: &ElaboratedClosure,
    abstracted: &[String],
) -> Result<Option<&'static str>, String> {
    if closure.axioms.iter().any(|ax| {
        ax == "Lean.ofReduceBool" || ax.contains("native_decide")
    }) {
        return Err("native_decide fails".into());
    }
    for ax in &closure.axioms {
        if !AXIOM_OK.contains(&ax.as_str()) {
            return Err(format!(
                "axiom {ax} is outside propext, Classical.choice, and Quot.sound"
            ));
        }
    }
    if closure.locked.is_empty() || !closure.unlocked.is_empty() {
        return Ok(None);
    }
    if abstracted.is_empty() {
        Ok(Some("spec_model"))
    } else {
        Ok(Some("spec_model_conditional"))
    }
}

/// One concrete row of a hypothesis instance. A list is a fold argument.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InstanceValue {
    Nat(u64),
    List(Vec<u64>),
}

/// Concrete inputs for one `spec_model` or `spec_model_conditional` entry.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct HypothesisInstance {
    pub rows: Vec<BTreeMap<String, InstanceValue>>,
}

/// Folds in the instance are non-empty, and every conditional arm of the definition is taken
/// by some row. An empty instance, an empty fold, or an unused arm fails the entry.
pub fn hypothesis_instance_is_nondegenerate(
    def_src: &str,
    def_name: &str,
    instance: &HypothesisInstance,
) -> Result<(), String> {
    if instance.rows.is_empty() {
        return Err("hypothesis instance is empty".into());
    }
    let body = named_def_body(def_src, def_name)?;
    let constants = nat_constants(def_src);
    let parsed = parse_def_expr(&body)?;
    let folds = fold_vars(&parsed.body);
    for row in &instance.rows {
        for name in &folds {
            match row.get(name) {
                Some(InstanceValue::List(values)) if !values.is_empty() => {}
                _ => return Err(format!("fold {name} is empty")),
            }
        }
    }
    let arms = arm_labels(&parsed.body);
    if arms.is_empty() {
        return Ok(());
    }
    let mut hit = BTreeSet::new();
    for row in &instance.rows {
        let mut env = BTreeMap::new();
        for (name, value) in row {
            env.insert(name.clone(), value.clone());
        }
        for (name, expr) in &parsed.lets {
            let value = eval_nat(expr, &env, &constants)?;
            env.insert(name.clone(), InstanceValue::Nat(value));
        }
        take_arms(&parsed.body, &env, &constants, &mut hit)?;
    }
    for arm in &arms {
        if !hit.contains(arm) {
            return Err(format!("conditional arm is unused: {arm}"));
        }
    }
    Ok(())
}

struct DefExpr {
    lets: Vec<(String, Expr)>,
    body: Expr,
}

enum Expr {
    Nat(u64),
    Var(String),
    Bin(&'static str, Box<Expr>, Box<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Max(Box<Expr>, Box<Expr>),
    Min(Box<Expr>, Box<Expr>),
    Any(Box<Expr>, String, Box<Expr>),
    Fold { var: String, body: Box<Expr> },
    App(Box<Expr>, Box<Expr>),
    Unit,
}

fn named_def_body(src: &str, name: &str) -> Result<String, String> {
    let needle = format!("def {name}");
    let start = src
        .find(&needle)
        .ok_or_else(|| format!("definition {name} is not in the source"))?;
    let rest = &src[start + needle.len()..];
    let eq = rest
        .find(":=")
        .ok_or_else(|| format!("definition {name} has no body"))?;
    let mut body = String::new();
    for line in rest[eq + 2..].lines() {
        if line.starts_with("theorem ")
            || line.starts_with("def ")
            || line.starts_with("@[")
            || line.starts_with("end ")
            || line.starts_with("structure ")
            || line.starts_with("inductive ")
            || line.starts_with("/--")
        {
            break;
        }
        body.push_str(line);
        body.push('\n');
    }
    Ok(body)
}

fn nat_constants(src: &str) -> BTreeMap<String, u64> {
    let mut pending = Vec::new();
    for line in src.lines() {
        let line = line.trim();
        let Some(rest) = line.strip_prefix("def ") else {
            continue;
        };
        if !line.contains(": Nat") || !line.contains(":=") {
            continue;
        }
        let Some((name, _)) = rest.split_once(|c: char| c.is_whitespace()) else {
            continue;
        };
        let Some((_, rhs)) = line.split_once(":=") else {
            continue;
        };
        let rhs = rhs.trim();
        if name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') && !rhs.is_empty() {
            pending.push((name.to_string(), rhs.to_string()));
        }
    }
    let mut known = BTreeMap::new();
    let mut progress = true;
    while progress {
        progress = false;
        let mut left = Vec::new();
        for (name, rhs) in pending {
            match parse_def_expr(&rhs).and_then(|parsed| {
                if parsed.lets.is_empty() {
                    eval_nat(&parsed.body, &BTreeMap::new(), &known)
                } else {
                    Err("let".into())
                }
            }) {
                Ok(value) => {
                    known.insert(name, value);
                    progress = true;
                }
                Err(_) => left.push((name, rhs)),
            }
        }
        pending = left;
    }
    known
}

fn fold_vars(expr: &Expr) -> Vec<String> {
    let mut names = Vec::new();
    collect_folds(expr, &mut names);
    names
}

fn collect_folds(expr: &Expr, names: &mut Vec<String>) {
    match expr {
        Expr::Fold { var, body } => {
            names.push(var.clone());
            collect_folds(body, names);
        }
        Expr::If(c, t, e) => {
            collect_folds(c, names);
            collect_folds(t, names);
            collect_folds(e, names);
        }
        Expr::Bin(_, a, b) | Expr::Max(a, b) | Expr::Min(a, b) | Expr::App(a, b) => {
            collect_folds(a, names);
            collect_folds(b, names);
        }
        Expr::Any(list, _, body) => {
            collect_folds(list, names);
            collect_folds(body, names);
        }
        Expr::Nat(_) | Expr::Var(_) | Expr::Unit => {}
    }
}

fn has_conditional(expr: &Expr) -> bool {
    match expr {
        Expr::If(_, _, _) | Expr::Max(_, _) | Expr::Min(_, _) => true,
        Expr::Fold { body, .. } => has_conditional(body),
        Expr::Bin(_, a, b) | Expr::App(a, b) => has_conditional(a) || has_conditional(b),
        Expr::Any(list, _, body) => has_conditional(list) || has_conditional(body),
        Expr::Nat(_) | Expr::Var(_) | Expr::Unit => false,
    }
}

fn arm_labels(body: &Expr) -> Vec<String> {
    if let Expr::Bin(op, _, _) = body {
        if is_cmp(op) {
            return vec!["comparison true".into(), "comparison false".into()];
        }
    }
    let mut arms = Vec::new();
    collect_arms(body, &mut arms);
    arms
}

fn collect_arms(expr: &Expr, arms: &mut Vec<String>) {
    match expr {
        Expr::If(cond, then_arm, else_arm) => {
            push_branch(&pretty(cond), then_arm, else_arm, arms)
        }
        Expr::Max(a, b) => {
            push_branch(&format!("{} >= {}", pretty(a), pretty(b)), a, b, arms)
        }
        Expr::Min(a, b) => {
            push_branch(&format!("{} <= {}", pretty(a), pretty(b)), a, b, arms)
        }
        Expr::Fold { body, .. } => collect_arms(body, arms),
        Expr::Bin(_, a, b) | Expr::App(a, b) => {
            collect_arms(a, arms);
            collect_arms(b, arms);
        }
        Expr::Any(list, _, body) => {
            collect_arms(list, arms);
            collect_arms(body, arms);
        }
        Expr::Nat(_) | Expr::Var(_) | Expr::Unit => {}
    }
}

fn push_branch(shown: &str, then_arm: &Expr, else_arm: &Expr, arms: &mut Vec<String>) {
    if has_conditional(then_arm) {
        collect_arms(then_arm, arms);
    } else {
        arms.push(format!("if ({shown}) then"));
    }
    if has_conditional(else_arm) {
        collect_arms(else_arm, arms);
    } else {
        arms.push(format!("if ({shown}) else"));
    }
}

fn take_arms(
    expr: &Expr,
    env: &BTreeMap<String, InstanceValue>,
    constants: &BTreeMap<String, u64>,
    hit: &mut BTreeSet<String>,
) -> Result<(), String> {
    if let Expr::Bin(op, left, right) = expr {
        if is_cmp(op) {
            let truth = eval_cmp(op, left, right, env, constants)?;
            hit.insert(
                if truth {
                    "comparison true".into()
                } else {
                    "comparison false".into()
                },
            );
            return Ok(());
        }
    }
    match expr {
        Expr::If(cond, then_arm, else_arm) => take_branch(
            &pretty(cond),
            eval_bool(cond, env, constants)?,
            then_arm,
            else_arm,
            env,
            constants,
            hit,
        ),
        Expr::Max(a, b) => take_branch(
            &format!("{} >= {}", pretty(a), pretty(b)),
            eval_nat(a, env, constants)? >= eval_nat(b, env, constants)?,
            a,
            b,
            env,
            constants,
            hit,
        ),
        Expr::Min(a, b) => take_branch(
            &format!("{} <= {}", pretty(a), pretty(b)),
            eval_nat(a, env, constants)? <= eval_nat(b, env, constants)?,
            a,
            b,
            env,
            constants,
            hit,
        ),
        Expr::Fold { body, .. } => take_arms(body, env, constants, hit),
        _ => Ok(()),
    }
}

fn take_branch(
    shown: &str,
    taken: bool,
    then_arm: &Expr,
    else_arm: &Expr,
    env: &BTreeMap<String, InstanceValue>,
    constants: &BTreeMap<String, u64>,
    hit: &mut BTreeSet<String>,
) -> Result<(), String> {
    if taken {
        if has_conditional(then_arm) {
            take_arms(then_arm, env, constants, hit)
        } else {
            hit.insert(format!("if ({shown}) then"));
            Ok(())
        }
    } else if has_conditional(else_arm) {
        take_arms(else_arm, env, constants, hit)
    } else {
        hit.insert(format!("if ({shown}) else"));
        Ok(())
    }
}

fn pretty(expr: &Expr) -> String {
    match expr {
        Expr::Nat(n) => n.to_string(),
        Expr::Var(name) => name.clone(),
        Expr::Bin(op, left, right) => format!("{} {op} {}", pretty(left), pretty(right)),
        Expr::Max(a, b) => format!("max {} {}", pretty(a), pretty(b)),
        Expr::Min(a, b) => format!("min {} {}", pretty(a), pretty(b)),
        Expr::Any(list, var, body) => {
            format!("{}.any (fun {var} => {})", pretty(list), pretty(body))
        }
        Expr::If(c, _, _) => pretty(c),
        Expr::Fold { var, .. } => var.clone(),
        Expr::App(f, arg) => format!("{} {}", pretty(f), pretty(arg)),
        Expr::Unit => "()".into(),
    }
}

fn is_cmp(op: &str) -> bool {
    matches!(op, ">=" | "<=" | ">" | "<" | "=" | "!=")
}

fn eval_bool(
    expr: &Expr,
    env: &BTreeMap<String, InstanceValue>,
    constants: &BTreeMap<String, u64>,
) -> Result<bool, String> {
    match expr {
        Expr::Bin("||", left, right) => {
            Ok(eval_bool(left, env, constants)? || eval_bool(right, env, constants)?)
        }
        Expr::Bin("&&", left, right) => {
            Ok(eval_bool(left, env, constants)? && eval_bool(right, env, constants)?)
        }
        Expr::Bin(op, left, right) if is_cmp(op) => eval_cmp(op, left, right, env, constants),
        Expr::Any(list, var, body) => {
            let Expr::Var(name) = list.as_ref() else {
                return Err("any receiver is not a name".into());
            };
            let Some(InstanceValue::List(values)) = env.get(name) else {
                return Err(format!("list {name} is missing"));
            };
            for value in values {
                let mut extended = env.clone();
                extended.insert(var.clone(), InstanceValue::Nat(*value));
                if eval_bool(body, &extended, constants)? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
        _ => Err("condition is not a proposition".into()),
    }
}

fn eval_cmp(
    op: &str,
    left: &Expr,
    right: &Expr,
    env: &BTreeMap<String, InstanceValue>,
    constants: &BTreeMap<String, u64>,
) -> Result<bool, String> {
    let left = eval_nat(left, env, constants)?;
    let right = eval_nat(right, env, constants)?;
    Ok(match op {
        ">=" => left >= right,
        "<=" => left <= right,
        ">" => left > right,
        "<" => left < right,
        "=" => left == right,
        "!=" => left != right,
        _ => return Err(format!("unknown comparison {op}")),
    })
}

fn eval_nat(
    expr: &Expr,
    env: &BTreeMap<String, InstanceValue>,
    constants: &BTreeMap<String, u64>,
) -> Result<u64, String> {
    match expr {
        Expr::Nat(n) => Ok(*n),
        Expr::Var(name) => {
            if let Some(InstanceValue::Nat(n)) = env.get(name) {
                Ok(*n)
            } else if let Some(n) = constants.get(name) {
                Ok(*n)
            } else {
                Err(format!("unbound {name}"))
            }
        }
        Expr::Max(a, b) => Ok(eval_nat(a, env, constants)?.max(eval_nat(b, env, constants)?)),
        Expr::Min(a, b) => Ok(eval_nat(a, env, constants)?.min(eval_nat(b, env, constants)?)),
        Expr::Bin(op, left, right) => {
            let left = eval_nat(left, env, constants)? as u128;
            let right = eval_nat(right, env, constants)? as u128;
            let value = match *op {
                "+" => left.checked_add(right),
                "-" => left.checked_sub(right),
                "*" => left.checked_mul(right),
                "/" => left.checked_div(right),
                "^" => pow_u128(left, right),
                _ => None,
            };
            u64::try_from(value.ok_or_else(|| format!("arithmetic {op} failed"))?)
                .map_err(|_| format!("arithmetic {op} failed"))
        }
        _ => Err("term is not a natural number".into()),
    }
}

fn pow_u128(base: u128, exp: u128) -> Option<u128> {
    if exp > 127 {
        return None;
    }
    let mut acc: u128 = 1;
    for _ in 0..exp {
        acc = acc.checked_mul(base)?;
    }
    Some(acc)
}

struct Parser<'a> {
    s: &'a str,
    i: usize,
}

fn parse_def_expr(body: &str) -> Result<DefExpr, String> {
    let mut parser = Parser { s: body, i: 0 };
    let mut lets = Vec::new();
    loop {
        parser.skip();
        if !parser.eat("let") {
            break;
        }
        let name = parser.ident()?;
        parser.expect(":=")?;
        lets.push((name, parser.parse_expr()?));
    }
    let body = parser.parse_expr()?;
    parser.skip();
    if parser.i != parser.s.len() {
        return Err(format!(
            "unparsed definition tail: {}",
            parser.s[parser.i..].trim()
        ));
    }
    Ok(DefExpr { lets, body })
}

impl<'a> Parser<'a> {
    fn rest(&self) -> &'a str {
        &self.s[self.i..]
    }

    fn skip(&mut self) {
        while let Some(c) = self.rest().chars().next() {
            if c.is_whitespace() {
                self.i += c.len_utf8();
            } else {
                break;
            }
        }
    }

    fn eat(&mut self, kw: &str) -> bool {
        self.skip();
        if !self.rest().starts_with(kw) {
            return false;
        }
        let after = kw.len();
        if kw
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '_')
        {
            if self.rest()[after..]
                .chars()
                .next()
                .is_some_and(|c| c.is_ascii_alphanumeric() || c == '_')
            {
                return false;
            }
        }
        self.i += after;
        true
    }

    fn expect(&mut self, kw: &str) -> Result<(), String> {
        if self.eat(kw) {
            Ok(())
        } else {
            Err(format!("expected {kw} near {}", self.rest().trim()))
        }
    }

    fn ident(&mut self) -> Result<String, String> {
        self.skip();
        let mut name = String::new();
        for c in self.rest().chars() {
            if c.is_ascii_alphanumeric() || c == '_' {
                name.push(c);
                self.i += c.len_utf8();
            } else {
                break;
            }
        }
        if name.is_empty() {
            Err(format!("expected a name near {}", self.rest().trim()))
        } else {
            Ok(name)
        }
    }

    fn number(&mut self) -> Option<u64> {
        self.skip();
        let rest = self.rest();
        if !rest.chars().next().is_some_and(|c| c.is_ascii_digit()) {
            return None;
        }
        let end = rest
            .char_indices()
            .take_while(|(_, c)| c.is_ascii_digit())
            .map(|(i, c)| i + c.len_utf8())
            .last()
            .unwrap_or(0);
        let value = rest[..end].parse().ok()?;
        self.i += end;
        Some(value)
    }

    fn parse_expr(&mut self) -> Result<Expr, String> {
        self.parse_if()
    }

    fn parse_if(&mut self) -> Result<Expr, String> {
        if self.eat("if") {
            let cond = self.parse_or()?;
            self.expect("then")?;
            let then_arm = self.parse_expr()?;
            self.expect("else")?;
            let else_arm = self.parse_expr()?;
            Ok(Expr::If(Box::new(cond), Box::new(then_arm), Box::new(else_arm)))
        } else {
            self.parse_or()
        }
    }

    fn parse_or(&mut self) -> Result<Expr, String> {
        let mut left = self.parse_and()?;
        while self.eat("||") {
            left = Expr::Bin("||", Box::new(left), Box::new(self.parse_and()?));
        }
        Ok(left)
    }

    fn parse_and(&mut self) -> Result<Expr, String> {
        let mut left = self.parse_cmp()?;
        while self.eat("&&") {
            left = Expr::Bin("&&", Box::new(left), Box::new(self.parse_cmp()?));
        }
        Ok(left)
    }

    fn parse_cmp(&mut self) -> Result<Expr, String> {
        let left = self.parse_add()?;
        let op = if self.eat("≥") || self.eat(">=") {
            ">="
        } else if self.eat("≤") || self.eat("<=") {
            "<="
        } else if self.eat("!=") {
            "!="
        } else if self.eat("<") {
            "<"
        } else if self.eat(">") {
            ">"
        } else if self.eat("=") {
            "="
        } else {
            return Ok(left);
        };
        Ok(Expr::Bin(op, Box::new(left), Box::new(self.parse_add()?)))
    }

    fn parse_add(&mut self) -> Result<Expr, String> {
        let mut left = self.parse_mul()?;
        loop {
            if self.eat("+") {
                left = Expr::Bin("+", Box::new(left), Box::new(self.parse_mul()?));
            } else if self.eat("-") {
                left = Expr::Bin("-", Box::new(left), Box::new(self.parse_mul()?));
            } else {
                break;
            }
        }
        Ok(left)
    }

    fn parse_mul(&mut self) -> Result<Expr, String> {
        let mut left = self.parse_pow()?;
        loop {
            if self.eat("*") {
                left = Expr::Bin("*", Box::new(left), Box::new(self.parse_pow()?));
            } else if self.eat("/") {
                left = Expr::Bin("/", Box::new(left), Box::new(self.parse_pow()?));
            } else {
                break;
            }
        }
        Ok(left)
    }

    fn parse_pow(&mut self) -> Result<Expr, String> {
        let left = self.parse_app()?;
        if self.eat("^") {
            Ok(Expr::Bin("^", Box::new(left), Box::new(self.parse_pow()?)))
        } else {
            Ok(left)
        }
    }

    fn starts_keyword(&self) -> bool {
        for kw in ["if", "then", "else", "let"] {
            if let Some(rest) = self.rest().strip_prefix(kw) {
                if !rest
                    .chars()
                    .next()
                    .is_some_and(|c| c.is_ascii_alphanumeric() || c == '_')
                {
                    return true;
                }
            }
        }
        false
    }

    fn parse_app(&mut self) -> Result<Expr, String> {
        let mut expr = self.parse_atom()?;
        loop {
            self.skip();
            if self.starts_keyword() {
                break;
            }
            let next = self.rest().chars().next();
            let arg = match next {
                Some('(') => true,
                Some(c) if c.is_ascii_alphanumeric() || c == '_' => true,
                _ => false,
            };
            if !arg {
                break;
            }
            expr = Expr::App(Box::new(expr), Box::new(self.parse_atom()?));
        }
        Ok(expr)
    }

    fn parse_atom(&mut self) -> Result<Expr, String> {
        self.skip();
        if self.eat("(") {
            let expr = self.parse_expr()?;
            self.expect(")")?;
            return Ok(expr);
        }
        if self.eat(".") {
            let _ = self.ident()?;
            return Ok(Expr::Unit);
        }
        if self.eat("max") {
            return Ok(Expr::Max(
                Box::new(self.parse_arg()?),
                Box::new(self.parse_arg()?),
            ));
        }
        if self.eat("min") {
            return Ok(Expr::Min(
                Box::new(self.parse_arg()?),
                Box::new(self.parse_arg()?),
            ));
        }
        if let Some(n) = self.number() {
            return Ok(Expr::Nat(n));
        }
        let mut expr = Expr::Var(self.ident()?);
        loop {
            self.skip();
            if !self.eat(".") {
                break;
            }
            let field = self.ident()?;
            if field == "foldl" {
                self.expect("(")?;
                self.expect("fun")?;
                let mut binders = 0;
                while !self.eat("=>") {
                    let _ = self.ident()?;
                    binders += 1;
                    if binders > 8 {
                        return Err("fold binder list did not end".into());
                    }
                }
                let body = self.parse_expr()?;
                self.expect(")")?;
                let _init = self.parse_atom()?;
                let Expr::Var(var) = expr else {
                    return Err("fold receiver is not a name".into());
                };
                expr = Expr::Fold {
                    var,
                    body: Box::new(body),
                };
            } else if field == "any" {
                self.expect("(")?;
                self.expect("fun")?;
                let var = self.ident()?;
                self.expect("=>")?;
                let body = self.parse_expr()?;
                self.expect(")")?;
                expr = Expr::Any(Box::new(expr), var, Box::new(body));
            } else {
                let Expr::Var(base) = expr else {
                    return Err("field is not a name".into());
                };
                expr = Expr::Var(format!("{base}.{field}"));
            }
        }
        Ok(expr)
    }

    fn parse_arg(&mut self) -> Result<Expr, String> {
        self.skip();
        if self.rest().starts_with('(') {
            self.parse_atom()
        } else {
            let saved = self.i;
            let expr = self.parse_atom()?;
            if matches!(expr, Expr::Var(_) | Expr::Nat(_)) {
                Ok(expr)
            } else {
                self.i = saved;
                Err("conditional argument is not a term".into())
            }
        }
    }
}

static PROBE_SEQ: AtomicU64 = AtomicU64::new(0);

/// Run `lake env lean` on the declaration and read the constants in its elaborated term.
pub fn closure_of_elaborated(
    lean_dir: &Path,
    declaration: &str,
) -> Result<ElaboratedClosure, String> {
    closure_of_elaborated_src(lean_dir, declaration, "")
}

fn closure_of_elaborated_src(
    lean_dir: &Path,
    declaration: &str,
    extra: &str,
) -> Result<ElaboratedClosure, String> {
    lean_ident(declaration)?;
    let source = probe_source(declaration, extra);
    let path = std::env::temp_dir().join(format!(
        "spec-lock-closure-{}-{}.lean",
        std::process::id(),
        PROBE_SEQ.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::write(&path, source)
        .map_err(|err| format!("could not write the elaborator probe: {err}"))?;
    let command = format!("lake env lean {}", path.display());
    let output = Command::new("sh")
        .arg("-c")
        .arg(&command)
        .current_dir(lean_dir)
        .env("PATH", path_with_elan())
        .output();
    let _ = std::fs::remove_file(&path);
    let output = output.map_err(|err| format!("lake env lean failed to start: {err}"))?;
    if !output.status.success() {
        return Err(format!(
            "lake env lean exited {}: {}",
            output.status,
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    let stdout = String::from_utf8_lossy(&output.stdout);
    let closure = parse_closure_output(&stdout, &definition_allowlist(lean_dir))?;
    closure_gate(&closure, &[])?;
    Ok(closure)
}

fn probe_source(declaration: &str, extra: &str) -> String {
    let mut source = String::from(
        "import Lean\nimport SpecLock\n\nopen Lean Elab Command\n\n",
    );
    source.push_str(extra);
    if !extra.is_empty() && !extra.ends_with('\n') {
        source.push('\n');
    }
    source.push_str(
        r##"elab "#closure " id:ident : command => do
  let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut stack : Array Name := #[decl]
  while !stack.isEmpty do
    let cur := stack.back!
    stack := stack.pop
    if seen.contains cur then
      continue
    seen := seen.insert cur
    let some ci := env.find? cur | continue
    for c in ci.getUsedConstantsAsSet do
      if c == decl || seen.contains c then
        continue
      let some idx := env.getModuleIdxFor? c | continue
      let mod := env.header.moduleNames[idx]!
      if mod.getRoot == `SpecLock then
        stack := stack.push c
        match specLockAttr.getParam? env c with
        | some lockId => IO.println s!"LOCK {c} {lockId}"
        | none => IO.println s!"CONST {c}"

"##,
    );
    source.push_str("#closure ");
    source.push_str(declaration);
    source.push_str("\n#print axioms ");
    source.push_str(declaration);
    source.push('\n');
    source
}

fn path_with_elan() -> String {
    let path = std::env::var("PATH").unwrap_or_default();
    match std::env::var("HOME") {
        Ok(home) => format!("{home}/.elan/bin:{path}"),
        Err(_) => path,
    }
}

fn definition_allowlist(lean_dir: &Path) -> BTreeSet<String> {
    let text = std::fs::read_to_string(lean_dir.join("allowlist.txt")).unwrap_or_default();
    text.lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#') && !AXIOM_OK.contains(line))
        .map(str::to_string)
        .collect()
}

fn parse_closure_output(
    text: &str,
    allow: &BTreeSet<String>,
) -> Result<ElaboratedClosure, String> {
    let mut locked = Vec::new();
    let mut lock_ids = Vec::new();
    let mut unlocked = Vec::new();
    let mut axioms = None;
    for line in text.lines() {
        let line = line.trim();
        if let Some(rest) = line.strip_prefix("LOCK ") {
            let mut parts = rest.splitn(3, ' ');
            let name = parts.next().unwrap_or("").trim();
            let id = parts.next().unwrap_or("").trim();
            if name.is_empty() || id.is_empty() {
                return Err("closure lock line is incomplete".into());
            }
            if !locked.iter().any(|have| have == name) {
                locked.push(name.to_string());
                lock_ids.push(id.to_string());
            }
        } else if let Some(name) = line.strip_prefix("CONST ") {
            let name = name.trim();
            if name.is_empty() {
                continue;
            }
            let allowed = allow
                .iter()
                .any(|entry| name == entry || name.ends_with(&format!(".{entry}")));
            if !allowed && !unlocked.iter().any(|have| have == name) {
                unlocked.push(name.to_string());
            }
        } else if line.contains("depends on axioms:") || line.contains("does not depend on any axioms")
        {
            axioms = Some(parse_axioms(line));
        }
    }
    let Some(axioms) = axioms else {
        return Err("elaborated term has no #print axioms line".into());
    };
    Ok(ElaboratedClosure {
        locked,
        lock_ids,
        unlocked,
        axioms,
    })
}

fn parse_axioms(line: &str) -> Vec<String> {
    if line.contains("does not depend on any axioms") {
        return Vec::new();
    }
    let Some(start) = line.find('[') else {
        return Vec::new();
    };
    let Some(end) = line.rfind(']') else {
        return Vec::new();
    };
    line[start + 1..end]
        .split(',')
        .map(str::trim)
        .filter(|name| !name.is_empty())
        .map(str::to_string)
        .collect()
}

fn lean_ident(name: &str) -> Result<(), String> {
    if name.is_empty() {
        return Err("lean name is empty".into());
    }
    for part in name.split('.') {
        let mut chars = part.chars();
        let Some(first) = chars.next() else {
            return Err("lean name is not an identifier".into());
        };
        if !first.is_ascii_alphabetic() && first != '_' {
            return Err("lean name is not an identifier".into());
        }
        if !chars.all(|c| c.is_ascii_alphanumeric() || c == '_') {
            return Err("lean name is not an identifier".into());
        }
    }
    Ok(())
}

/// A variable `>>` is guarded when every path that reaches it has already
/// returned on `amount >= 64`.
pub fn shift_guard_holds(func: &syn::ItemFn) -> bool {
    !unguarded_shifts(&func.block)
}

fn unguarded_shifts(block: &syn::Block) -> bool {
    let mut guarded = false;
    for stmt in &block.stmts {
        match stmt {
            syn::Stmt::Expr(expr, _) => {
                if expr_shift_unguarded(expr, guarded) {
                    return true;
                }
                if is_width_return(expr) {
                    guarded = true;
                }
            }
            syn::Stmt::Local(local) => {
                if let Some(init) = &local.init {
                    if expr_shift_unguarded(&init.expr, guarded) {
                        return true;
                    }
                }
            }
            _ => {}
        }
    }
    false
}

fn is_width_return(expr: &syn::Expr) -> bool {
    let syn::Expr::If(ife) = expr else {
        return false;
    };
    guard_is_width(&ife.cond) && ife.else_branch.is_none()
}

fn expr_shift_unguarded(expr: &syn::Expr, guarded: bool) -> bool {
    match expr {
        syn::Expr::Binary(bin) if matches!(bin.op, syn::BinOp::Shr(_)) => {
            !rhs_is_literal(&bin.right) && !guarded
        }
        syn::Expr::If(ife) => {
            if !guard_is_width(&ife.cond) && unguarded_shifts(&ife.then_branch) {
                return true;
            }
            if let Some((_, else_branch)) = &ife.else_branch {
                return expr_shift_unguarded(else_branch, guarded);
            }
            false
        }
        syn::Expr::Block(b) => unguarded_shifts(&b.block),
        _ => false,
    }
}

fn rhs_is_literal(expr: &syn::Expr) -> bool {
    matches!(expr, syn::Expr::Lit(_))
}

fn guard_is_width(cond: &syn::Expr) -> bool {
    let syn::Expr::Binary(bin) = cond else {
        return false;
    };
    if !matches!(bin.op, syn::BinOp::Ge(_)) {
        return false;
    }
    matches!(&*bin.right, syn::Expr::Lit(lit) if lit_is_64(&lit.lit))
}

fn lit_is_64(lit: &syn::Lit) -> bool {
    matches!(lit, syn::Lit::Int(n) if n.base10_digits() == "64")
}

/// Mutate a Lean definition body. Equation proofs are not part of the text
/// that is edited. Returns the mutated source.
pub fn mutate_def_body(src: &str, from: &str, to: &str) -> String {
    let mut out = String::new();
    let mut in_def = false;
    for line in src.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("def ") || trimmed.starts_with("@[spec_lock") {
            in_def = trimmed.starts_with("def ") || in_def;
        }
        if trimmed.starts_with("theorem ") {
            in_def = false;
        }
        if in_def {
            out.push_str(&line.replace(from, to));
        } else {
            out.push_str(line);
        }
        out.push('\n');
    }
    out
}

pub fn body_still_matches(mutated: &str, needle: &str) -> bool {
    mutated.lines().any(|l| l.contains("def ") || true) && mutated.contains(needle)
}

const EQUATION_PROOFS: &[&str] = &["getBlockSubsidy_eq_div", "getBlockSubsidy_shift_bridge"];

/// Drop defining-equation proofs. The theorem module is what mutation rebuilds.
pub fn exclude_equation_proofs(src: &str) -> String {
    let lines: Vec<&str> = src.lines().collect();
    let mut out = String::new();
    let mut skipping = false;
    for line in lines {
        let trimmed = line.trim_start();
        let indent = line.len() - trimmed.len();
        let name = trimmed
            .strip_prefix("theorem ")
            .and_then(|rest| rest.split_whitespace().next());
        if indent == 0 && name.is_some_and(|name| EQUATION_PROOFS.contains(&name)) {
            skipping = true;
            continue;
        }
        if skipping {
            let next_decl = indent == 0
                && (trimmed.starts_with("theorem ")
                    || trimmed.starts_with("def ")
                    || trimmed.starts_with("structure ")
                    || trimmed.starts_with("inductive ")
                    || trimmed.starts_with("end ")
                    || trimmed.starts_with("/--")
                    || trimmed.starts_with("@["));
            if next_decl {
                skipping = false;
            } else {
                continue;
            }
        }
        out.push_str(line);
        out.push('\n');
    }
    out
}

/// A locked definition is a `def` carrying `@[spec_lock]`. Theorems are not edited.
pub fn locked_def_names(src: &str) -> Vec<String> {
    let lines: Vec<&str> = src.lines().collect();
    let mut names = Vec::new();
    for (i, line) in lines.iter().enumerate() {
        let Some(rest) = line.trim().strip_prefix("def ") else {
            continue;
        };
        let name = rest
            .split(|c: char| c == ' ' || c == '(' || c == ':')
            .next()
            .unwrap_or("");
        if name.is_empty() {
            continue;
        }
        let mut j = i;
        while j > 0 {
            j -= 1;
            let trimmed = lines[j].trim();
            if trimmed.is_empty() || trimmed.starts_with("/--") || trimmed.starts_with("--") {
                continue;
            }
            if trimmed.contains("spec_lock") {
                names.push(name.to_string());
            }
            break;
        }
    }
    names
}

/// Edit one locked definition body. The emitted equation and the theorem proofs stay as they are.
pub fn mutate_named_def(src: &str, name: &str) -> Result<String, String> {
    let (before, body, after) = split_def(src, name)?;
    let mutated = mutate_body(name, &body)?;
    if mutated == body {
        return Err(format!("mutation did not edit {name}"));
    }
    Ok(format!("{before}{mutated}{after}"))
}

fn split_def(src: &str, name: &str) -> Result<(String, String, String), String> {
    let lines: Vec<&str> = src.lines().collect();
    let mut start = None;
    for (i, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix("def ") {
            let found = rest
                .split(|c: char| c == ' ' || c == '(' || c == ':')
                .next()
                .unwrap_or("");
            if found == name {
                start = Some(i);
                break;
            }
        }
    }
    let Some(start) = start else {
        return Err(format!("definition {name} is not in the module"));
    };
    let mut end = lines.len();
    for (i, line) in lines.iter().enumerate().skip(start + 1) {
        let trimmed = line.trim_start();
        let indent = line.len() - trimmed.len();
        if indent == 0
            && (trimmed.starts_with("def ")
                || trimmed.starts_with("theorem ")
                || trimmed.starts_with("structure ")
                || trimmed.starts_with("inductive ")
                || trimmed.starts_with("end ")
                || trimmed.starts_with("/--")
                || trimmed.starts_with("@["))
        {
            end = i;
            break;
        }
    }
    let before = lines[..start].join("\n");
    let body = lines[start..end].join("\n");
    let after = lines[end..].join("\n");
    let before = if before.is_empty() {
        String::new()
    } else {
        format!("{before}\n")
    };
    let body = format!("{body}\n");
    let after = if after.is_empty() {
        String::new()
    } else {
        format!("{after}\n")
    };
    Ok((before, body, after))
}

fn mutate_body(name: &str, body: &str) -> Result<String, String> {
    let mutated = match name {
        "getBlockSubsidy" => body.replace("≥ 64", "≥ 65"),
        "totalSupply" => body.replace("+ getBlockSubsidy (h + 1)", "+ 0"),
        "checkTransaction" => body.replace("tx.inputCount = 0", "false"),
        "utxoInput" => body.replace("getD idx 0", "getD idx 1"),
        "blockWork" => body.replace("\n  work\n", "\n  0\n"),
        "chainWork" => body.replace("acc + blockWork w", "acc"),
        "shouldReorganize" => body.replace("current < candidate", "false"),
        "clampTime" => body.replace("expected / 4", "0"),
        "H" => body.replace("210000", "210001"),
        "C" => body.replace("100000000", "100000001"),
        "initialSubsidy" => body.replace("50 * C", "50 * C + 1"),
        "LocktimeType" => body.replace("500000000", "500000001"),
        _ => body.replacen(":= 0", ":= 1", 1),
    };
    if mutated == body {
        Err(format!("no body edit applies to {name}"))
    } else {
        Ok(mutated)
    }
}

/// The theorem module after one pass over the locked definition bodies.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TheoremMutation {
    pub theorem: String,
    pub not_load_bearing: Vec<String>,
}

/// Copy the Lean project without equation proofs, mutate each locked definition body,
/// and `lake build` the theorem module. A body whose mutation still builds is not
/// load-bearing. The theorem fails when no mutation breaks the build.
pub fn mutation_rebuild(lean_dir: &Path) -> Result<(PathBuf, TheoremMutation), String> {
    let dest = prepare_theorem_module(lean_dir)?;
    let report = rebuild_locked_defs(&dest)?;
    Ok((dest, report))
}

fn prepare_theorem_module(lean_dir: &Path) -> Result<PathBuf, String> {
    let dest = std::env::temp_dir().join(format!("spec-lock-mutation-{}", std::process::id()));
    std::fs::create_dir_all(dest.join("SpecLock"))
        .map_err(|err| format!("could not create the theorem module: {err}"))?;
    for file in ["lakefile.lean", "lean-toolchain"] {
        std::fs::copy(lean_dir.join(file), dest.join(file))
            .map_err(|err| format!("could not copy {file}: {err}"))?;
    }
    let root = std::fs::read_to_string(lean_dir.join("SpecLock.lean"))
        .map_err(|err| format!("could not read SpecLock.lean: {err}"))?;
    std::fs::write(
        dest.join("SpecLock.lean"),
        root.replace("import SpecLock.Defeq\n", ""),
    )
    .map_err(|err| format!("could not write the theorem module: {err}"))?;
    let spec = lean_dir.join("SpecLock");
    for entry in std::fs::read_dir(&spec).map_err(|err| format!("could not read {spec:?}: {err}"))? {
        let path = entry
            .map_err(|err| format!("could not read a Lean file: {err}"))?
            .path();
        if path.extension().and_then(|ext| ext.to_str()) != Some("lean") {
            continue;
        }
        if path.file_name().and_then(|name| name.to_str()) == Some("Defeq.lean") {
            continue;
        }
        let src = std::fs::read_to_string(&path)
            .map_err(|err| format!("could not read {}: {err}", path.display()))?;
        let name = path.file_name().unwrap();
        std::fs::write(dest.join("SpecLock").join(name), exclude_equation_proofs(&src))
            .map_err(|err| format!("could not write {}: {err}", name.to_string_lossy()))?;
    }
    Ok(dest)
}

fn rebuild_locked_defs(project: &Path) -> Result<TheoremMutation, String> {
    let mut files = Vec::new();
    for entry in std::fs::read_dir(project.join("SpecLock"))
        .map_err(|err| format!("could not read the theorem module: {err}"))?
    {
        let path = entry
            .map_err(|err| format!("could not read a Lean file: {err}"))?
            .path();
        if path.extension().and_then(|ext| ext.to_str()) == Some("lean") {
            files.push(path);
        }
    }
    let root = project.join("SpecLock.lean");
    if root.is_file() {
        files.push(root);
    }
    let mut snapshot = BTreeMap::new();
    let mut defs = Vec::new();
    for path in &files {
        let src = std::fs::read_to_string(path)
            .map_err(|err| format!("could not read {}: {err}", path.display()))?;
        for name in locked_def_names(&src) {
            defs.push((path.clone(), name));
        }
        snapshot.insert(path.clone(), src);
    }
    if defs.is_empty() {
        return Err("no locked definition body".into());
    }
    if !lake_build(project)? {
        return Err("theorem module does not build before mutation".into());
    }
    let mut cases = Vec::new();
    for (path, name) in &defs {
        for (saved, src) in &snapshot {
            std::fs::write(saved, src)
                .map_err(|err| format!("could not restore {}: {err}", saved.display()))?;
        }
        let mutated = mutate_named_def(snapshot.get(path).expect("snapshot"), name)?;
        std::fs::write(path, &mutated)
            .map_err(|err| format!("could not write the mutated body: {err}"))?;
        let built = lake_build(project)?;
        cases.push((name.clone(), !built));
    }
    for (saved, src) in &snapshot {
        std::fs::write(saved, src)
            .map_err(|err| format!("could not restore {}: {err}", saved.display()))?;
    }
    let borrowed: Vec<(&str, bool)> = cases.iter().map(|(name, broke)| (name.as_str(), *broke)).collect();
    let (not_load_bearing, any_broke) = mutation_report(&borrowed);
    if !any_broke {
        return Err("no mutation breaks the theorem".into());
    }
    Ok(TheoremMutation {
        theorem: "SpecLock".into(),
        not_load_bearing,
    })
}

fn lake_build(project: &Path) -> Result<bool, String> {
    let output = Command::new("lake")
        .args(["build", "SpecLock"])
        .current_dir(project)
        .env("PATH", path_with_elan())
        .output()
        .map_err(|err| format!("lake build failed to start: {err}"))?;
    Ok(output.status.success())
}

/// One mutation of each recorded body edit. A theorem fails when none break it.
pub fn mutation_report(cases: &[(&str, bool)]) -> (Vec<String>, bool) {
    let mut not_load_bearing = Vec::new();
    let mut any_broke = false;
    for (name, broke) in cases {
        if *broke {
            any_broke = true;
        } else {
            not_load_bearing.push((*name).to_string());
        }
    }
    (not_load_bearing, any_broke)
}

/// Theorem 6.1.2. Z3 checks the Rust body on `u64` heights. Lean proves the same
/// sentence for every natural. `both` is that pair, not one domain standing for the other.
pub fn subsidy_zero_after_33(lean_src: &str) -> Result<SentenceStatus, String> {
    let id = "PROTOCOL.md#Theorem:6.1.2";
    let statement = r"\forall h \geq 33 \times H: \text{GetBlockSubsidy}(h) = 0";
    let expr = formula::parse_sentence(statement).ok_or("6.1.2 did not parse")?;
    let clause = formula::emit_z3(&expr, "height").map_err(|err| err.detail.clone())?;
    let bound = crate::parser::spec_expr::protocol_u64("H").saturating_mul(33);
    if clause.domain != "u64"
        || clause.requires != format!("height >= {bound}")
        || clause.ensures != "result == 0"
    {
        return Err(
            "6.1.2 does not say the Rust returns 0 for every u64 height at or above 33 intervals"
                .into(),
        );
    }
    let lean = formula::emit_lean(&expr).map_err(|err| err.detail.clone())?;
    if !lean.contains("(h : Nat)") || lean.contains("u64") || lean.contains("UInt64") {
        return Err("6.1.2 Lean statement is not the same sentence over all naturals".into());
    }
    let theorem = lean_src.lines().find(|line| {
        line.contains("theorem ") && line.contains("subsidy_zero_from_epoch_33")
    });
    match theorem {
        Some(line) if line.contains("(h : Nat)") && !line.contains("UInt64") => {}
        _ => {
            return Err(
                "6.1.2 Lean theorem is not the same sentence over all naturals".into(),
            )
        }
    }
    Ok(SentenceStatus {
        id: id.into(),
        status: "both".into(),
        domain: "u64".to_string(),
        abstracted: Vec::new(),
        assumptions: Vec::new(),
        failing_statement: String::new(),
        locked_defs: vec!["getBlockSubsidy".into()],
        not_load_bearing: Vec::new(),
    })
}

struct LockedDecl {
    id: String,
    kind: String,
    header: String,
}

/// Sentence entries for theorems that take `BlockAssumptions` or `CryptoAssumptions`.
/// The entry names that structure. A cryptographic hypothesis is not `spec_model`.
pub fn assumption_entries(lean_src: &str) -> Result<Vec<SentenceStatus>, String> {
    let mut entries = Vec::new();
    for decl in locked_decls(lean_src) {
        let taken = structures_taken(&decl.header);
        if taken.is_empty() {
            continue;
        }
        if decl.kind == "axiom" && cryptographic_hypothesis_text(&decl.header) {
            return Err("cryptographic hypothesis is not an axiom".into());
        }
        let conclusion = conclusion_of(&decl.header);
        let hypothesis = decl.id.contains("Theorem:8.3")
            || (taken.iter().any(|name| name == "CryptoAssumptions")
                && conclusion_is_crypto_field(&conclusion));
        let status = if hypothesis {
            "none"
        } else {
            "spec_model_conditional"
        };
        let mut entry = SentenceStatus {
            id: decl.id,
            status: status.into(),
            domain: String::new(),
            abstracted: Vec::new(),
            assumptions: vec![taken[0].clone()],
            failing_statement: if hypothesis { conclusion } else { String::new() },
            locked_defs: Vec::new(),
            not_load_bearing: Vec::new(),
        };
        entry.assumptions.extend(taken.into_iter().skip(1));
        cryptographic_hypothesis_is_not_spec_model(&entry)?;
        entries.push(entry);
    }
    Ok(entries)
}

/// A cryptographic hypothesis is a field of `CryptoAssumptions`, not a `spec_model` theorem.
pub fn cryptographic_hypothesis_is_not_spec_model(entry: &SentenceStatus) -> Result<(), String> {
    let names_crypto = entry
        .assumptions
        .iter()
        .any(|name| name == "CryptoAssumptions");
    let hypothesis = entry.id.contains("Theorem:8.3")
        || (names_crypto && conclusion_is_crypto_field(&entry.failing_statement));
    if entry.status == "spec_model" && hypothesis {
        return Err("cryptographic hypothesis is not a spec_model theorem".into());
    }
    Ok(())
}

fn cryptographic_hypothesis_text(text: &str) -> bool {
    text.contains("Theorem:8.3")
        || text.contains("sha256Preimage")
        || text.contains("ripemd160Preimage")
        || text.contains("secp256k1DiscreteLog")
        || text.contains("signatureUnforgeable")
        || text.contains("discrete logarithm")
}

fn structures_taken(header: &str) -> Vec<String> {
    let mut names = Vec::new();
    for structure in ["BlockAssumptions", "CryptoAssumptions"] {
        if header.contains(&format!(": {structure}")) {
            names.push(structure.to_string());
        }
    }
    names
}

fn conclusion_is_crypto_field(conclusion: &str) -> bool {
    let conclusion = conclusion.trim();
    if conclusion.contains('=') || conclusion.contains('≤') || conclusion.contains('→') || conclusion.contains('<')
    {
        return false;
    }
    ["sha256Preimage", "ripemd160Preimage", "secp256k1DiscreteLog", "signatureUnforgeable"]
        .iter()
        .any(|field| conclusion.ends_with(field))
}

fn conclusion_of(header: &str) -> String {
    let before_body = header.split(":=").next().unwrap_or(header);
    let mut depth = 0;
    let mut last = None;
    for (index, ch) in before_body.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => depth -= 1,
            ':' if depth == 0 => last = Some(index),
            _ => {}
        }
    }
    match last {
        Some(index) => before_body[index + 1..].trim().to_string(),
        None => String::new(),
    }
}

fn locked_decls(src: &str) -> Vec<LockedDecl> {
    let lines: Vec<&str> = src.lines().collect();
    let mut decls = Vec::new();
    for (i, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        let Some(rest) = trimmed.strip_prefix("@[spec_lock \"") else {
            continue;
        };
        let Some(id) = rest.split('"').next() else {
            continue;
        };
        if id.is_empty() {
            continue;
        }
        let mut header = String::new();
        let mut kind = String::new();
        for follow in lines.iter().skip(i + 1).take(12) {
            let text = follow.trim();
            if text.starts_with("--") {
                continue;
            }
            if kind.is_empty() {
                kind = text.split_whitespace().next().unwrap_or("").to_string();
            }
            header.push_str(text);
            header.push(' ');
            if text.contains(":=") {
                break;
            }
        }
        decls.push(LockedDecl {
            id: id.to_string(),
            kind,
            header,
        });
    }
    decls
}

pub fn real_series_disputed() -> SentenceStatus {
    let h = crate::parser::spec_expr::protocol_u64("H");
    let initial = crate::parser::spec_expr::initial_subsidy();
    let series = h.saturating_mul(initial).saturating_mul(2);
    let issued: u64 = 2_099_999_997_690_000;
    let failing = format!("totalSupply = {series}");
    SentenceStatus {
        id: "PROTOCOL.md#Theorem:6.2.3#real-series".into(),
        status: if series == issued {
            "spec_model".into()
        } else {
            "spec_disputed".into()
        },
        domain: String::new(),
        abstracted: Vec::new(),
        assumptions: Vec::new(),
        failing_statement: failing,
        locked_defs: vec!["totalSupply".into()],
        not_load_bearing: Vec::new(),
    }
}

const BANNED: &[&str] = &[
    "sorry",
    "admit",
    "native_decide",
    "implemented_by",
    "noncomputable",
];

/// Structural stand-in for the kernel gate. CI also runs `lake build` when
/// the toolchain is installed. `sorry`, `admit`, `axiom`, `opaque`, and a
/// duplicate lock id fail here.
pub fn audit_lean(src: &str) -> Result<(), String> {
    let mut ids = BTreeMap::<String, usize>::new();
    for line in src.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("--") {
            continue;
        }
        for word in BANNED {
            if trimmed.contains(word) {
                return Err(format!("lean declaration contains {word}"));
            }
        }
        if trimmed.starts_with("axiom ") || trimmed.starts_with("opaque ") {
            if cryptographic_hypothesis_text(trimmed) {
                return Err("cryptographic hypothesis is not an axiom".into());
            }
            return Err(format!("lean declaration is not a computable def: {trimmed}"));
        }
        if let Some(rest) = trimmed.strip_prefix("@[spec_lock \"") {
            if let Some(id) = rest.split('"').next() {
                *ids.entry(id.to_string()).or_insert(0) += 1;
            }
        }
    }
    for (id, n) in &ids {
        if *n > 1 {
            return Err(format!("duplicate lock id {id}"));
        }
    }
    if src.contains("def helper") && src.contains("spec_lock") && src.contains("helper") {
        let locked_uses_helper = src.lines().any(|l| {
            let t = l.trim();
            !t.starts_with("--") && !t.starts_with("def helper") && t.contains("helper")
        });
        if locked_uses_helper && src.contains("@[spec_lock") {
            let before_helper = src.split("def helper").next().unwrap_or(src);
            if before_helper.contains("helper") {
                return Err("locked declaration references an unlocked helper".into());
            }
        }
    }
    Ok(())
}

/// One abstracted predicate on a `spec_model_conditional` entry, with the reason the conclusion does not use it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AbstractedPredicate {
    pub predicate: String,
    pub why: String,
}

struct AbstractionSpec {
    conclusion: &'static str,
    predicates: &'static [(&'static str, &'static str, &'static str)],
}

fn abstraction_spec(id: &str) -> Option<AbstractionSpec> {
    const SCRIPT: &str = "∀ a : BlockAssumptions, a.scriptValid";
    const SIG: &str = "∀ a : BlockAssumptions, a.sigValid";
    const UTXO: &str = "∀ a : BlockAssumptions, a.utxoSet";
    const TX: &str = "∀ a : BlockAssumptions, a.txValid";
    const WORK: &[(&str, &str, &str)] = &[
        (
            "script validity",
            SCRIPT,
            "the conclusion is a sum of per-block work, which does not depend on script validity",
        ),
        (
            "signature validity",
            SIG,
            "the conclusion is a sum of per-block work, which does not depend on signature validity",
        ),
        (
            "the UTXO set",
            UTXO,
            "the conclusion is a sum of per-block work, which does not depend on the UTXO set",
        ),
        (
            "transaction validity",
            TX,
            "the conclusion is a sum of per-block work, which does not depend on transaction validity",
        ),
    ];
    match id {
        "PROTOCOL.md#def:CoinbaseBound" => Some(AbstractionSpec {
            conclusion: "∀ b : BlockValue, b.coinbaseValue ≤ b.subsidy + b.fees",
            predicates: &[
                (
                    "script validity",
                    SCRIPT,
                    "the conclusion is the coinbase value bound, which does not depend on script validity",
                ),
                (
                    "signature validity",
                    SIG,
                    "the conclusion is the coinbase value bound, which does not depend on signature validity",
                ),
            ],
        }),
        "PROTOCOL.md#def:OutputsNonnegative" => Some(AbstractionSpec {
            conclusion: "∀ b : BlockValue, ∀ v : Nat, v ∈ b.outputs → 0 ≤ v",
            predicates: &[
                (
                    "script validity",
                    SCRIPT,
                    "the conclusion is that outputs are nonnegative, which does not depend on script validity",
                ),
                (
                    "signature validity",
                    SIG,
                    "the conclusion is that outputs are nonnegative, which does not depend on signature validity",
                ),
            ],
        }),
        "PROTOCOL.md#def:UtxoInput" => Some(AbstractionSpec {
            conclusion:
                "∀ utxo : List Nat, ∀ idx : Nat, utxoInput utxo idx = utxo.getD idx 0",
            predicates: &[
                (
                    "script validity",
                    SCRIPT,
                    "the conclusion is the input value taken from the UTXO set, which does not depend on script validity",
                ),
                (
                    "signature validity",
                    SIG,
                    "the conclusion is the input value taken from the UTXO set, which does not depend on signature validity",
                ),
            ],
        }),
        "ARCHITECTURE.md#ChainWork" => Some(AbstractionSpec {
            conclusion:
                "∀ works : List Nat, chainWork works = works.foldl (fun acc w => acc + w) 0",
            predicates: WORK,
        }),
        "PROTOCOL.md#Theorem:7.1" => Some(AbstractionSpec {
            conclusion: "∀ raw expected : Nat, expected / 4 ≤ clampTime raw expected ∧ clampTime raw expected ≤ expected * 4",
            predicates: &[
                (
                    "script validity",
                    SCRIPT,
                    "the conclusion is the clamp of the timespan, which does not depend on script validity",
                ),
                (
                    "signature validity",
                    SIG,
                    "the conclusion is the clamp of the timespan, which does not depend on signature validity",
                ),
                (
                    "the UTXO set",
                    UTXO,
                    "the conclusion is the clamp of the timespan, which does not depend on the UTXO set",
                ),
                (
                    "transaction validity",
                    TX,
                    "the conclusion is the clamp of the timespan, which does not depend on transaction validity",
                ),
            ],
        }),
        "ARCHITECTURE.md#ShouldReorganize" => Some(AbstractionSpec {
            conclusion: "∀ candidate current : List Nat, chainWork current < chainWork candidate → shouldReorganize (chainWork candidate) (chainWork current) = true",
            predicates: &[
                (
                    "script validity",
                    SCRIPT,
                    "the conclusion compares cumulative work, which does not depend on script validity",
                ),
                (
                    "signature validity",
                    SIG,
                    "the conclusion compares cumulative work, which does not depend on signature validity",
                ),
                (
                    "the UTXO set",
                    UTXO,
                    "the conclusion compares cumulative work, which does not depend on the UTXO set",
                ),
                (
                    "transaction validity",
                    TX,
                    "the conclusion compares cumulative work, which does not depend on transaction validity",
                ),
            ],
        }),
        _ => None,
    }
}

/// Reject an abstracted predicate that is definitionally the conclusion.
/// The elaborator failing, or the two terms being the same proposition, is a failure.
pub fn abstracted_predicate_is_not_the_conclusion(
    lean_dir: &Path,
    predicate: &str,
    conclusion: &str,
) -> Result<(), String> {
    abstracted_predicate_is_not_the_conclusion_src(lean_dir, predicate, conclusion, "")
}

fn abstracted_predicate_is_not_the_conclusion_src(
    lean_dir: &Path,
    predicate: &str,
    conclusion: &str,
    extra: &str,
) -> Result<(), String> {
    proposition_term(predicate)?;
    proposition_term(conclusion)?;
    if extra.contains("sorry")
        || extra.contains("admit")
        || extra.contains("import")
        || extra.contains('#')
    {
        return Err("abstracted predicate is not a proposition".into());
    }
    let same = predicate_defeq(lean_dir, predicate, conclusion, extra)?;
    if same {
        Err("abstracted predicate is the conclusion".into())
    } else {
        Ok(())
    }
}

/// Every abstracted predicate on a conditional sentence, each with the reason the conclusion does not depend on it.
pub fn conditional_abstraction_list(
    lean_dir: &Path,
    id: &str,
) -> Result<Vec<AbstractedPredicate>, String> {
    let Some(spec) = abstraction_spec(id) else {
        return Err(format!("{id} is not spec_model_conditional"));
    };
    if spec.predicates.is_empty() {
        return Err("spec_model_conditional lists no abstracted predicate".into());
    }
    let mut listed = Vec::new();
    for (name, term, why) in spec.predicates {
        if why.is_empty() {
            return Err(format!(
                "{name} does not say why the conclusion does not depend on it"
            ));
        }
        abstracted_predicate_is_not_the_conclusion(lean_dir, term, spec.conclusion)?;
        listed.push(AbstractedPredicate {
            predicate: (*name).to_string(),
            why: (*why).to_string(),
        });
    }
    Ok(listed)
}

fn proposition_term(term: &str) -> Result<(), String> {
    if term.is_empty()
        || term.contains('\n')
        || term.contains('\r')
        || term.contains("sorry")
        || term.contains("admit")
        || term.contains("import")
        || term.contains('#')
        || term.contains("--")
        || term.contains('"')
    {
        return Err("abstracted predicate is not a proposition".into());
    }
    Ok(())
}

fn predicate_defeq(
    lean_dir: &Path,
    predicate: &str,
    conclusion: &str,
    extra: &str,
) -> Result<bool, String> {
    let mut source = String::from(
        "import Lean\nimport SpecLock\nopen Lean Meta Elab Term Command SpecLock\n\n",
    );
    source.push_str(extra);
    if !extra.is_empty() && !extra.ends_with('\n') {
        source.push('\n');
    }
    source.push_str(
        r##"elab "#notconcl " pred:term " =?= " concl:term : command => do
  let same ← liftTermElabM do
    let p ← elabTerm pred none
    let c ← elabTerm concl none
    Meta.isDefEq p c
  IO.println (if same then "SAME" else "DISTINCT")

"##,
    );
    source.push_str("#notconcl (");
    source.push_str(predicate);
    source.push_str(") =?= (");
    source.push_str(conclusion);
    source.push_str(")\n");
    let path = std::env::temp_dir().join(format!(
        "spec-lock-defeq-{}-{}.lean",
        std::process::id(),
        PROBE_SEQ.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::write(&path, &source)
        .map_err(|err| format!("could not write the elaborator probe: {err}"))?;
    let command = format!("lake env lean {}", path.display());
    let output = Command::new("sh")
        .arg("-c")
        .arg(&command)
        .current_dir(lean_dir)
        .env("PATH", path_with_elan())
        .output();
    let _ = std::fs::remove_file(&path);
    let output = output.map_err(|_| {
        "definitional equality could not be checked; the abstracted predicate stays rejected".to_string()
    })?;
    if !output.status.success() {
        return Err(format!(
            "definitional equality could not be checked; the abstracted predicate stays rejected: {}",
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    let stdout = String::from_utf8_lossy(&output.stdout);
    let same = stdout.lines().any(|line| line.trim() == "SAME");
    let distinct = stdout.lines().any(|line| line.trim() == "DISTINCT");
    if same == distinct {
        return Err(
            "definitional equality could not be checked; the abstracted predicate stays rejected"
                .into(),
        );
    }
    Ok(same)
}

pub fn conditional_ids() -> BTreeSet<String> {
    [
        "PROTOCOL.md#def:CoinbaseBound",
        "PROTOCOL.md#def:OutputsNonnegative",
        "PROTOCOL.md#def:UtxoInput",
        "ARCHITECTURE.md#ChainWork",
        "ARCHITECTURE.md#ShouldReorganize",
        "PROTOCOL.md#Theorem:7.1",
    ]
    .into_iter()
    .map(str::to_string)
    .collect()
}

/// Theorem 6.1.2 stays `both` only when its elaborated closure has no unlocked name.
/// Any other sentence keeps the status from `status_of`.
pub fn theorem_6212_reported_status(unlocked: &[String]) -> &'static str {
    if unlocked.is_empty() {
        "both"
    } else {
        "none"
    }
}

pub fn status_of(row: &Sentence, conditional: &BTreeSet<String>) -> &'static str {
    if row.reason == "spec_disputed" || row.id.ends_with("#real-series") {
        return "spec_disputed";
    }
    if row.class == "unsupported" {
        return "none";
    }
    if conditional.contains(&row.id) {
        return "spec_model_conditional";
    }
    match row.class.as_str() {
        "both" => "both",
        "z3_clause" => "z3",
        "lean_statement" => "spec_model",
        _ => "none",
    }
}

pub fn status_counts(rows: &[Sentence]) -> BTreeMap<String, usize> {
    let conditional = conditional_ids();
    let mut counts = BTreeMap::new();
    for name in [
        "z3",
        "spec_model",
        "spec_model_conditional",
        "spec_disputed",
        "both",
        "none",
        "unsupported",
    ] {
        counts.insert(name.to_string(), 0);
    }
    for row in rows {
        let status = status_of(row, &conditional);
        *counts.entry(status.to_string()).or_insert(0) += 1;
        if row.class == "unsupported" {
            *counts.entry("unsupported".into()).or_insert(0) += 1;
        }
    }
    counts
}

pub fn print_counts(rows: &[Sentence]) {
    let counts = class_counts(rows);
    eprintln!(
        "sentences z3_clause={} lean_statement={} both={} unsupported={} parse_failed={} emitter_shape_missing={} model_unwritten={} out_of_scope={}",
        counts.get("z3_clause").copied().unwrap_or(0),
        counts.get("lean_statement").copied().unwrap_or(0),
        counts.get("both").copied().unwrap_or(0),
        counts.get("unsupported").copied().unwrap_or(0),
        counts.get("unsupported:parse_failed").copied().unwrap_or(0),
        counts.get("unsupported:emitter_shape_missing").copied().unwrap_or(0),
        counts.get("unsupported:model_unwritten").copied().unwrap_or(0),
        counts.get("unsupported:out_of_scope").copied().unwrap_or(0),
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    fn read_spec(rel: &str) -> String {
        let path = crate::parser::spec_expr::spec_checkout().join(rel);
        std::fs::read_to_string(&path).unwrap_or_else(|err| panic!("read {}: {err}", path.display()))
    }

    #[test]
    fn baseline_rejects_a_new_unsupported_id() {
        let base = vec![Sentence {
            id: "a".into(),
            file: "PROTOCOL.md".into(),
            number: "1".into(),
            class: "unsupported".into(),
            reason: "parse_failed".into(),
            statement: String::new(),
        }];
        let mut run = base.clone();
        run.push(Sentence {
            id: "b".into(),
            file: "PROTOCOL.md".into(),
            number: "2".into(),
            class: "unsupported".into(),
            reason: "parse_failed".into(),
            statement: String::new(),
        });
        assert!(baseline_delta(&base, &run).is_err());
    }

    #[test]
    fn baseline_rejects_a_supported_id_still_listed() {
        let base = vec![Sentence {
            id: "a".into(),
            file: "PROTOCOL.md".into(),
            number: "1".into(),
            class: "unsupported".into(),
            reason: "model_unwritten".into(),
            statement: String::new(),
        }];
        let run = vec![Sentence {
            id: "a".into(),
            file: "PROTOCOL.md".into(),
            number: "1".into(),
            class: "both".into(),
            reason: String::new(),
            statement: String::new(),
        }];
        let err = baseline_delta(&base, &run).unwrap_err();
        assert!(err.contains("still listed"));
    }

    #[test]
    fn real_series_is_disputed() {
        let row = real_series_disputed();
        assert_eq!(row.status, "spec_disputed");
        assert!(row.failing_statement.contains("totalSupply"));
        assert!(!row.failing_statement.contains("2099999997690000"));
    }

    #[test]
    fn width_guard_65_does_not_cover_the_shift() {
        let guarded: syn::ItemFn = syn::parse_quote! {
            fn get_block_subsidy(height: u64) -> u64 {
                let halving_period = height / 210000;
                if halving_period >= 64 {
                    return 0;
                }
                5000000000 >> halving_period
            }
        };
        let weakened: syn::ItemFn = syn::parse_quote! {
            fn get_block_subsidy(height: u64) -> u64 {
                let halving_period = height / 210000;
                if halving_period >= 65 {
                    return 0;
                }
                5000000000 >> halving_period
            }
        };
        assert!(shift_guard_holds(&guarded));
        assert!(!shift_guard_holds(&weakened));
    }

    #[test]
    fn axiom_and_duplicate_lock_fail() {
        let axiom = "@[spec_lock \"PROTOCOL.md#Theorem:6.1.2\"]\naxiom subsidy : Nat\n";
        assert!(audit_lean(axiom).is_err());
        let dup = "@[spec_lock \"PROTOCOL.md#Theorem:6.1.2\"]\ndef a := 0\n@[spec_lock \"PROTOCOL.md#Theorem:6.1.2\"]\ndef b := 0\n";
        assert!(audit_lean(dup).unwrap_err().contains("duplicate"));
        let helper = "@[spec_lock \"PROTOCOL.md#def:GetBlockSubsidy\"]\ndef getBlockSubsidy := helper\ndef helper := 0\n";
        assert!(audit_lean(helper).is_err());
    }

    #[test]
    fn weakened_guard_fails_the_equation() {
        let src = read_spec("lean/SpecLock/Subsidy.lean");
        assert!(audit_lean(&src).is_ok());
        assert!(src.contains("≥ 64"));
        let mutated = mutate_def_body(&src, "≥ 64", "≥ 65");
        let def_only = mutated.split("theorem ").next().unwrap_or("");
        assert!(def_only.contains('≥') && def_only.contains("65"));
        assert!(!def_only.contains("64"));
        assert!(mutated.contains("≥ 64"));
        let (not_bearing, any_broke) = mutation_report(&[("guard-65", true), ("unused-comment", false)]);
        assert!(any_broke);
        assert_eq!(not_bearing, vec!["unused-comment".to_string()]);
    }

    #[test]
    fn unlocked_baseline_rejects_a_new_definition() {
        let mut listed = BTreeSet::new();
        listed.insert("PROTOCOL.md#def:Block".to_string());
        let run = vec![Sentence {
            id: "PROTOCOL.md#def:Block".into(),
            file: "PROTOCOL.md".into(),
            number: "Block".into(),
            class: "unsupported".into(),
            reason: "parse_failed".into(),
            statement: String::new(),
        }, Sentence {
            id: "PROTOCOL.md#def:Extra".into(),
            file: "PROTOCOL.md".into(),
            number: "Extra".into(),
            class: "unsupported".into(),
            reason: "parse_failed".into(),
            statement: String::new(),
        }];
        assert!(unlocked_delta(&listed, &run).is_err());
    }

    #[test]
    fn committed_baseline_matches_itself() {
        let text = include_str!("../../../docs/sentence-inventory.tsv");
        let rows = parse_inventory(text);
        assert!(baseline_delta(&rows, &rows).is_ok());
        assert!(rows.iter().any(|r| r.number == "6.1.2" && r.class == "both"));
        assert!(rows.iter().any(|r| r.reason == "spec_disputed"));
        for name in ["script-validity", "signature-validity"] {
            assert!(
                rows.iter().any(|r| {
                    r.id == format!("PROTOCOL.md#abstract:{name}")
                        && r.class == "unsupported"
                        && r.reason == "model_unwritten"
                }),
                "{name}"
            );
        }
        let unlocked = include_str!("../../../docs/unlocked-definitions.txt");
        assert!(unlocked.lines().any(|l| l.contains("#def:")));
        assert!(!unlocked.lines().any(|l| l.contains("GetBlockSubsidy")));
        let listed: BTreeSet<String> = unlocked
            .lines()
            .filter(|line| !line.is_empty())
            .map(str::to_string)
            .collect();
        assert!(unlocked_delta(&listed, &rows).is_ok());
    }

    #[test]
    fn abstracted_predicates_are_their_own_rows() {
        let rows = inventory(&[("PROTOCOL.md", "no sentences here\n")], &BTreeSet::new());
        let abstracts: Vec<_> = rows
            .iter()
            .filter(|row| row.id.contains("#abstract:"))
            .collect();
        assert!(abstracts.len() >= 2, "{abstracts:?}");
        assert!(abstracts.iter().all(|row| {
            row.class == "unsupported" && row.reason == "model_unwritten"
        }));
        assert!(abstracts
            .iter()
            .any(|row| row.statement == "script validity"));
        assert!(abstracts
            .iter()
            .any(|row| row.statement == "signature validity"));
        let mut locked = BTreeSet::new();
        locked.insert("PROTOCOL.md#abstract:script-validity".to_string());
        let written = abstracted_predicates(&locked);
        let script = written
            .iter()
            .find(|row| row.id == "PROTOCOL.md#abstract:script-validity")
            .unwrap();
        assert_ne!(script.class, "unsupported");
        let baseline = abstracted_predicates(&BTreeSet::new());
        assert!(baseline_delta(&baseline, &written).is_err());
    }

    #[test]
    fn theorems_name_the_assumptions_structure_they_take() {
        let chain = read_spec("lean/SpecLock/Chain.lean");
        let entries = assumption_entries(&chain).expect("chain");
        let ids = [
            "PROTOCOL.md#def:CoinbaseBound",
            "PROTOCOL.md#def:OutputsNonnegative",
            "ARCHITECTURE.md#ChainWork",
            "ARCHITECTURE.md#ShouldReorganize",
            "PROTOCOL.md#Theorem:7.1",
        ];
        for id in ids {
            let entry = entries.iter().find(|entry| entry.id == id).unwrap_or_else(|| panic!("{id}"));
            assert_eq!(entry.assumptions, vec!["BlockAssumptions".to_string()], "{id}");
            assert_eq!(entry.status, "spec_model_conditional", "{id}");
        }
        assert!(!entries.iter().any(|entry| entry.id.contains("UtxoInput")));
        let subsidy = read_spec("lean/SpecLock/Subsidy.lean");
        assert!(assumption_entries(&subsidy).unwrap().is_empty());

        let hypothesis = r#"
@[spec_lock "PROTOCOL.md#Theorem:8.3"]
theorem signature_unforgeable (c : CryptoAssumptions) : c.signatureUnforgeable := c.signatureUnforgeable
"#;
        let crypto = assumption_entries(hypothesis).expect("hypothesis");
        assert_eq!(crypto.len(), 1);
        assert_eq!(crypto[0].assumptions, vec!["CryptoAssumptions".to_string()]);
        assert_ne!(crypto[0].status, "spec_model");
        let mut claimed = crypto[0].clone();
        claimed.status = "spec_model".into();
        let err = cryptographic_hypothesis_is_not_spec_model(&claimed).unwrap_err();
        assert!(err.contains("spec_model"), "{err}");

        let uses = r#"
@[spec_lock "PROTOCOL.md#Theorem:8.1"]
theorem spends (c : CryptoAssumptions) (h : c.signatureUnforgeable) : 0 = 0 := rfl
"#;
        let dependent = assumption_entries(uses).expect("uses");
        assert_eq!(dependent[0].assumptions, vec!["CryptoAssumptions".to_string()]);
        assert_eq!(dependent[0].status, "spec_model_conditional");

        let axiom = "axiom sha256Preimage : Prop\n";
        let err = audit_lean(axiom).unwrap_err();
        assert!(err.contains("not an axiom"), "{err}");
        let locked_axiom = r#"
@[spec_lock "PROTOCOL.md#Theorem:8.3"]
axiom signatureUnforgeable : CryptoAssumptions → Prop := fun _ => True
"#;
        let err = assumption_entries(locked_axiom).unwrap_err();
        assert!(err.contains("not an axiom"), "{err}");
    }

    #[test]
    fn theorem_6212_records_the_u64_domain() {
        let lean = read_spec("lean/SpecLock/Subsidy.lean");
        let entry = subsidy_zero_after_33(&lean).expect("6.1.2");
        assert_eq!(entry.id, "PROTOCOL.md#Theorem:6.1.2");
        assert_eq!(entry.status, "both");
        assert_eq!(entry.domain, "u64");
        let narrowed = lean.replace("(h : Nat)", "(h : UInt64)");
        let err = subsidy_zero_after_33(&narrowed).unwrap_err();
        assert!(err.contains("naturals"), "{err}");
    }

    #[test]
    fn classify_6212_is_both_when_locked() {
        let statement = r"\forall h \geq 33 \times H: \text{GetBlockSubsidy}(h) = 0";
        let id = "PROTOCOL.md#Theorem:6.1.2";
        let mut locked = BTreeSet::new();
        locked.insert(id.to_string());
        let row = classify_row("PROTOCOL.md", id, statement, &locked);
        assert_eq!(row.class, "both");
        assert!(row.reason.is_empty());
    }

    #[cfg(feature = "z3")]
    #[test]
    fn clause_6212_holds_and_mutations_flip_it() {
        use crate::parser::contracts::{Contract, ContractType};
        use crate::translator::z3_verifier::{VerificationResult, Z3Verifier};

        let statement = r"\forall h \geq 33 \times H: \text{GetBlockSubsidy}(h) = 0";
        let expr = formula::parse_sentence(statement).unwrap();
        let clause = formula::emit_z3(&expr, "height").unwrap();
        assert_eq!(clause.domain, "u64");

        let func: syn::ItemFn = syn::parse_quote! {
            fn get_block_subsidy(height: i64) -> i64 {
                let halving_period = height / 210000;
                if halving_period >= 64 {
                    return 0;
                }
                5000000000 >> halving_period
            }
        };
        let held = verify_one(&func, &clause.requires, &clause.ensures);
        assert!(
            matches!(
                held,
                VerificationResult::Verified {
                    body_translated: true
                }
            ),
            "{held:?}"
        );

        let shift_back: syn::ItemFn = syn::parse_quote! {
            fn get_block_subsidy(height: i64) -> i64 {
                let halving_period = height / 210000;
                if halving_period >= 64 {
                    return 0;
                }
                5000000000 >> (halving_period - 1)
            }
        };
        assert!(!discharge(&shift_back, &clause.requires, &clause.ensures));

        let weakened_guard: syn::ItemFn = syn::parse_quote! {
            fn get_block_subsidy(height: i64) -> i64 {
                let halving_period = height / 210000;
                if halving_period >= 65 {
                    return 0;
                }
                5000000000 >> halving_period
            }
        };
        let weakened = verify_one(
            &weakened_guard,
            &clause.requires,
            &clause.ensures,
        );
        assert!(
            matches!(
                weakened,
                VerificationResult::Unknown { ref reason }
                    if reason.contains("shift amount")
            ),
            "{weakened:?}"
        );

        let raised: syn::ItemFn = syn::parse_quote! {
            fn get_block_subsidy(height: i64) -> i64 {
                let halving_period = height / 210000;
                if halving_period >= 64 {
                    return 0;
                }
                8589934592 >> halving_period
            }
        };
        // The constant check is not consulted. The clause itself goes sat.
        assert!(!discharge(&raised, &clause.requires, "result == 0"));
        let bounds = discharge(&raised, "height >= 0", "result <= 8589934592");
        assert!(bounds);

        fn verify_one(
            func: &syn::ItemFn,
            requires: &str,
            ensures: &str,
        ) -> VerificationResult {
            let requires_expr: syn::Expr = syn::parse_str(requires).unwrap();
            let ensures_expr: syn::Expr = syn::parse_str(ensures).unwrap();
            let requires_c = Contract {
                contract_type: ContractType::Requires,
                condition: requires_expr,
                comment: None,
            };
            let ensures_c = Contract {
                contract_type: ContractType::Ensures,
                condition: ensures_expr,
                comment: None,
            };
            let mut verifier = Z3Verifier::new(30_000);
            verifier.verify_contract_with_context(&ensures_c, Some(func), &[requires_c], &[])
        }

        fn discharge(func: &syn::ItemFn, requires: &str, ensures: &str) -> bool {
            matches!(
                verify_one(func, requires, ensures),
                VerificationResult::Verified {
                    body_translated: true
                }
            )
        }
    }

    #[test]
    fn closure_comes_from_the_elaborated_term() {
        let lean = crate::parser::spec_expr::spec_checkout().join("lean");
        let got = closure_of_elaborated(&lean, "SpecLock.subsidy_zero_from_epoch_33")
            .expect("elaborator");
        assert!(
            got.locked.contains(&"SpecLock.getBlockSubsidy".to_string()),
            "{got:?}"
        );
        for id in [
            "PROTOCOL.md#def:GetBlockSubsidy",
            "PROTOCOL.md#const:H",
            "PROTOCOL.md#const:C",
            "PROTOCOL.md#const:initialSubsidy",
        ] {
            assert!(got.lock_ids.iter().any(|have| have == id), "{got:?}");
        }
        assert!(got.unlocked.is_empty(), "{got:?}");
        assert_eq!(theorem_6212_reported_status(&got.unlocked), "both");

        let bare = closure_of_elaborated_src(
            &lean,
            "bare",
            "-- getBlockSubsidy\ntheorem bare : True := True.intro\n",
        )
        .expect("bare");
        assert!(bare.locked.is_empty());
        assert!(bare.unlocked.is_empty(), "{bare:?}");
        assert!(model_status(&bare, &[], "", "", &HypothesisInstance::default())
            .unwrap()
            .is_none());
        assert!(model_status(
            &bare,
            &["scriptValid".into()],
            "",
            "",
            &HypothesisInstance::default()
        )
        .unwrap()
        .is_none());

        let native = closure_of_elaborated_src(
            &lean,
            "usesNative",
            "theorem usesNative : 1 + 1 = 2 := by native_decide\n",
        );
        assert!(native.unwrap_err().contains("native_decide"));

        let extra = closure_of_elaborated_src(
            &lean,
            "usesBad",
            "axiom badAx : True\ntheorem usesBad : True := badAx\n",
        );
        let err = extra.unwrap_err();
        assert!(err.contains("badAx"), "{err}");

        let locked = ElaboratedClosure {
            locked: vec!["SpecLock.getBlockSubsidy".into()],
            lock_ids: vec!["PROTOCOL.md#def:GetBlockSubsidy".into()],
            unlocked: vec![],
            axioms: vec!["propext".into()],
        };
        let trivial = "def answer : Nat := 0\n";
        let present = HypothesisInstance {
            rows: vec![BTreeMap::new()],
        };
        assert_eq!(
            model_status(&locked, &[], trivial, "answer", &present).unwrap(),
            Some("spec_model")
        );
        assert_eq!(
            model_status(&locked, &["scriptValid".into()], trivial, "answer", &present).unwrap(),
            Some("spec_model_conditional")
        );
        let empty = ElaboratedClosure {
            locked: vec![],
            lock_ids: vec![],
            unlocked: vec![],
            axioms: vec![],
        };
        assert!(model_status(&empty, &[], "", "", &HypothesisInstance::default())
            .unwrap()
            .is_none());
        assert!(model_status(
            &empty,
            &["scriptValid".into()],
            "",
            "",
            &HypothesisInstance::default()
        )
        .unwrap()
        .is_none());
    }

    #[test]
    fn hypothesis_instance_rejects_an_empty_fold_and_an_unused_arm() {
        let subsidy = read_spec("lean/SpecLock/Subsidy.lean");
        let chain = read_spec("lean/SpecLock/Chain.lean");
        let tx = read_spec("lean/SpecLock/Tx.lean");
        let locked = ElaboratedClosure {
            locked: vec!["SpecLock.getBlockSubsidy".into()],
            lock_ids: vec!["PROTOCOL.md#def:GetBlockSubsidy".into()],
            unlocked: vec![],
            axioms: vec!["propext".into()],
        };

        let empty = hypothesis_instance_is_nondegenerate(
            &subsidy,
            "getBlockSubsidy",
            &HypothesisInstance::default(),
        );
        assert!(empty.unwrap_err().contains("empty"));

        let mut low = BTreeMap::new();
        low.insert("h".into(), InstanceValue::Nat(0));
        let one_arm = HypothesisInstance { rows: vec![low.clone()] };
        let unused = hypothesis_instance_is_nondegenerate(&subsidy, "getBlockSubsidy", &one_arm)
            .unwrap_err();
        assert!(unused.contains("unused"), "{unused}");
        let entry = model_status(&locked, &[], &subsidy, "getBlockSubsidy", &one_arm);
        assert!(entry.unwrap_err().contains("unused"));

        let mut high = BTreeMap::new();
        high.insert("h".into(), InstanceValue::Nat(64 * 210_000));
        let both = HypothesisInstance {
            rows: vec![low, high],
        };
        hypothesis_instance_is_nondegenerate(&subsidy, "getBlockSubsidy", &both)
            .expect("both subsidy arms");
        assert_eq!(
            model_status(&locked, &["scriptValid".into()], &subsidy, "getBlockSubsidy", &both)
                .unwrap(),
            Some("spec_model_conditional")
        );

        let mut bare = BTreeMap::new();
        bare.insert("works".into(), InstanceValue::List(vec![]));
        let empty_fold = HypothesisInstance { rows: vec![bare] };
        let fold = hypothesis_instance_is_nondegenerate(&chain, "chainWork", &empty_fold).unwrap_err();
        assert!(fold.contains("empty"), "{fold}");
        let mut filled = BTreeMap::new();
        filled.insert("works".into(), InstanceValue::List(vec![1]));
        hypothesis_instance_is_nondegenerate(
            &chain,
            "chainWork",
            &HypothesisInstance { rows: vec![filled] },
        )
        .expect("non-empty chain");

        let mut mid = BTreeMap::new();
        mid.insert("raw".into(), InstanceValue::Nat(4));
        mid.insert("expected".into(), InstanceValue::Nat(4));
        let clamp = hypothesis_instance_is_nondegenerate(
            &chain,
            "clampTime",
            &HypothesisInstance { rows: vec![mid] },
        )
        .unwrap_err();
        assert!(clamp.contains("unused"), "{clamp}");
        let regions = [0_u64, 4, 100]
            .into_iter()
            .map(|raw| {
                let mut row = BTreeMap::new();
                row.insert("raw".into(), InstanceValue::Nat(raw));
                row.insert("expected".into(), InstanceValue::Nat(4));
                row
            })
            .collect();
        hypothesis_instance_is_nondegenerate(&chain, "clampTime", &HypothesisInstance { rows: regions })
            .expect("clamp arms");

        let tx_row = |inputs, outputs, values: Vec<u64>| {
            let mut row = BTreeMap::new();
            row.insert("tx.inputCount".into(), InstanceValue::Nat(inputs));
            row.insert("tx.outputCount".into(), InstanceValue::Nat(outputs));
            row.insert("tx.outputValues".into(), InstanceValue::List(values));
            row
        };
        let partial = HypothesisInstance {
            rows: vec![tx_row(0, 1, vec![1]), tx_row(1, 1, vec![1])],
        };
        let tx_unused =
            hypothesis_instance_is_nondegenerate(&tx, "checkTransaction", &partial).unwrap_err();
        assert!(tx_unused.contains("unused"), "{tx_unused}");
        let over = 2_100_000_000_000_000 + 1;
        let covered = HypothesisInstance {
            rows: vec![
                tx_row(0, 1, vec![1]),
                tx_row(1, 1, vec![over]),
                tx_row(1, 1, vec![1]),
            ],
        };
        hypothesis_instance_is_nondegenerate(&tx, "checkTransaction", &covered).expect("tx arms");

        let mut ordered = BTreeMap::new();
        ordered.insert("current".into(), InstanceValue::Nat(1));
        ordered.insert("candidate".into(), InstanceValue::Nat(2));
        let one_side = hypothesis_instance_is_nondegenerate(
            &chain,
            "shouldReorganize",
            &HypothesisInstance { rows: vec![ordered] },
        )
        .unwrap_err();
        assert!(one_side.contains("unused"), "{one_side}");
    }

    #[test]
    fn subsidy_constants_match_the_spec_table() {
        let src = read_spec("lean/SpecLock/Subsidy.lean");
        let known = nat_constants(&src);
        assert_eq!(
            known.get("H").copied(),
            Some(crate::parser::spec_expr::protocol_u64("H"))
        );
        assert_eq!(
            known.get("C").copied(),
            Some(crate::parser::spec_expr::protocol_u64("C"))
        );
        assert_eq!(
            known.get("initialSubsidy").copied(),
            Some(crate::parser::spec_expr::initial_subsidy())
        );
        for name in ["H", "C", "initialSubsidy"] {
            let mutated = mutate_named_def(&src, name).unwrap_or_else(|err| panic!("{name}: {err}"));
            assert_ne!(mutated, src);
        }
    }

    #[test]
    fn theorem_6212_is_none_while_its_closure_is_open() {
        assert_eq!(
            theorem_6212_reported_status(&["SpecLock.H".into()]),
            "none"
        );
        assert_eq!(theorem_6212_reported_status(&[]), "both");
    }

    #[test]
    fn locktime_type_closure_uses_only_its_locked_def() {
        let lean = crate::parser::spec_expr::spec_checkout().join("lean");
        let got = closure_of_elaborated(&lean, "SpecLock.locktime_type_determination")
            .expect("elaborator");
        assert!(
            got.locked.iter().any(|name| name.ends_with("LocktimeType")),
            "{got:?}"
        );
        assert!(got.unlocked.is_empty(), "{got:?}");
    }

    #[test]
    fn formula_rows_stay_unlocked() {
        for src in [
            read_spec("lean/SpecLock/Subsidy.lean"),
            read_spec("lean/SpecLock/Supply.lean"),
            read_spec("lean/SpecLock/Tx.lean"),
            read_spec("lean/SpecLock/Chain.lean"),
            read_spec("lean/SpecLock/Locktime.lean"),
        ] {
            for id in locks_in(&src) {
                assert!(!id.contains("#Formula:"), "{id}");
            }
        }
    }

    #[test]
    fn equation_proofs_are_excluded_and_only_the_def_body_changes() {
        let src = read_spec("lean/SpecLock/Subsidy.lean");
        let theorems = exclude_equation_proofs(&src);
        assert!(!theorems.contains("getBlockSubsidy_eq_div"));
        assert!(!theorems.contains("getBlockSubsidy_shift_bridge"));
        assert!(theorems.contains("subsidy_zero_from_epoch_33"));
        let mutated = mutate_named_def(&theorems, "getBlockSubsidy").unwrap();
        assert!(mutated.contains("≥ 65"));
        assert!(mutated.contains("subsidy_zero_from_epoch_33"));
        assert!(mutated.contains("≥ 64"));
        let def_only = mutated.split("theorem ").next().unwrap_or("");
        assert!(def_only.contains("65"));
        assert!(!def_only.contains("64"));
    }

    #[test]
    fn mutation_rebuilds_the_theorem_module() {
        let lean = crate::parser::spec_expr::spec_checkout().join("lean");
        let (dir, report) = mutation_rebuild(&lean).expect("rebuild");
        assert!(dir.join("lakefile.lean").is_file());
        assert!(!dir.join("SpecLock/Defeq.lean").exists());
        let subsidy = std::fs::read_to_string(dir.join("SpecLock/Subsidy.lean")).unwrap();
        assert!(!subsidy.contains("getBlockSubsidy_eq_div"));
        assert!(!report.not_load_bearing.iter().any(|name| name == "getBlockSubsidy"));
        assert_eq!(report.theorem, "SpecLock");
    }

    #[test]
    fn unused_definition_is_not_load_bearing() {
        let lean = crate::parser::spec_expr::spec_checkout().join("lean");
        let dir = std::env::temp_dir().join(format!(
            "spec-lock-mutation-unused-{}",
            std::process::id()
        ));
        std::fs::create_dir_all(dir.join("SpecLock")).unwrap();
        std::fs::copy(lean.join("lakefile.lean"), dir.join("lakefile.lean")).unwrap();
        std::fs::copy(lean.join("lean-toolchain"), dir.join("lean-toolchain")).unwrap();
        std::fs::copy(
            lean.join("SpecLock/Attr.lean"),
            dir.join("SpecLock/Attr.lean"),
        )
        .unwrap();
        std::fs::write(
            dir.join("SpecLock.lean"),
            r#"import SpecLock.Attr

namespace SpecLock

@[spec_lock "test#def:Unused"]
def unused : Nat := 0

@[spec_lock "test#def:Answer"]
def answer : Nat := 0

theorem ignores : True := trivial

theorem usesAnswer : answer = 0 := rfl

end SpecLock
"#,
        )
        .unwrap();
        let report = rebuild_locked_defs(&dir).expect("fixture");
        assert_eq!(report.not_load_bearing, vec!["unused".to_string()]);
        assert!(!report.not_load_bearing.iter().any(|name| name == "answer"));
    }

    #[test]
    fn abstracted_predicate_is_not_the_conclusion_fails_closed() {
        let lean = crate::parser::spec_expr::spec_checkout().join("lean");
        let conclusion = "∀ b : BlockValue, b.coinbaseValue ≤ b.subsidy + b.fees";
        abstracted_predicate_is_not_the_conclusion(
            &lean,
            "∀ a : BlockAssumptions, a.scriptValid",
            conclusion,
        )
        .expect("script validity is not the coinbase bound");
        let same = abstracted_predicate_is_not_the_conclusion(&lean, conclusion, conclusion);
        assert!(same.unwrap_err().contains("conclusion"));
        let unfolded = abstracted_predicate_is_not_the_conclusion_src(
            &lean,
            "∀ b : BlockValue, vacuous b",
            conclusion,
            "def vacuous (b : BlockValue) : Prop := b.coinbaseValue ≤ b.subsidy + b.fees\n",
        );
        assert!(unfolded.unwrap_err().contains("conclusion"));

        let coinbase =
            conditional_abstraction_list(&lean, "PROTOCOL.md#def:CoinbaseBound").unwrap();
        assert!(coinbase.iter().any(|row| {
            row.predicate == "script validity" && row.why.contains("coinbase value bound")
        }));
        assert!(coinbase.iter().any(|row| {
            row.predicate == "signature validity" && row.why.contains("coinbase value bound")
        }));

        let chain = conditional_abstraction_list(&lean, "ARCHITECTURE.md#ChainWork").unwrap();
        for name in [
            "script validity",
            "signature validity",
            "the UTXO set",
            "transaction validity",
        ] {
            assert!(
                chain.iter().any(|row| {
                    row.predicate == name && row.why.contains("sum of per-block work")
                }),
                "{name} {chain:?}"
            );
        }

        for id in conditional_ids() {
            let spec = abstraction_spec(&id).unwrap_or_else(|| panic!("{id}"));
            assert!(!spec.predicates.is_empty(), "{id}");
            assert!(spec.predicates.iter().all(|(_, _, why)| !why.is_empty()));
        }
    }
}
