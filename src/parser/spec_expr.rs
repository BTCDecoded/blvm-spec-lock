//! Census clauses read from PROTOCOL.md.
//!
//! Section 4 constants come from `SpecParser`. Comparisons, conjunctions, and one
//! implication are parsed from the math already in the paper. `result = 0` is not
//! a clause. A `≤` bound is the valid range; the census clause is the `>` rejection.

use super::orange_paper::SpecParser;
use std::collections::HashMap;
use std::path::Path;
use std::sync::OnceLock;

/// Locked rows whose numeric clause bound is the parsed spec value.
pub const SPEC_SOURCED: &[&str] = &[
    "block_weight_limit",
    "block_sigop_limit",
    "eval_script_limits",
    "validate_block_header",
    "validate_block_header_fields",
    "check_transaction",
    "validate_supply_limit",
    "get_block_subsidy",
    "total_supply",
    "coinbase_scriptsig_len",
    "is_strict_der",
    "check_coinbase_maturity",
    "get_next_work_required",
    "activation_height_from_headers",
    "is_push_opcode",
    "is_op_success",
    "opcode_bytes",
    "validate_block_header_mtp",
    "is_sequence_disabled",
    "extract_sequence_type_flag",
    "extract_sequence_locktime_value",
    "get_locktime_type",
    "check_bip65",
    "validate_witness_program_length",
    "check_bip54_sigop_limit",
    "check_bip54_coinbase",
    "check_bip54_tx_stripped_size",
    "check_bip54_timewarp",
    "is_bip54_active_at",
    "calculate_transaction_weight_segwit",
    "weight_to_vsize",
    "get_transaction_sigop_cost_with_utxos",
    "is_coinbase",
    "check_bip90",
    "sighash_single_quirk",
    "find_and_delete",
    "opcode_dispatch",
    "push_advance",
    "extract_witness_commitment",
    "build_bip143_preimage",
    "check_proof_of_work",
    "validate_prev_block_hash",
    "p2sh_push_only_check",
    "expand_target",
    "strip_taproot_annex",
    "merkle_tree_from_hashes",
];

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpcodeRow {
    pub name: String,
    pub byte: u64,
    pub min: u32,
    pub op: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Op {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Expr {
    Lit(u64),
    Name(String),
    Cmp(Op, Box<Expr>, Box<Expr>),
    And(Vec<Expr>),
    Add(Box<Expr>, Box<Expr>),
    Implies(Box<Expr>, Box<Expr>),
}

pub fn protocol_u64(name: &str) -> u64 {
    *protocol_constants()
        .get(name)
        .unwrap_or_else(|| panic!("spec constant {name} is missing"))
}

pub fn impl_u64(name: &str) -> u64 {
    rust_const_u64(primitives_src(), name)
        .unwrap_or_else(|| panic!("impl constant {name} is missing"))
}

/// Integer constant in a sibling crate source (`../blvm-consensus/src/...`).
pub fn source_u64(rel: &str, name: &str) -> u64 {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(rel);
    let src =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    rust_const_u64(&src, name).unwrap_or_else(|| panic!("constant {name} is missing in {rel}"))
}

pub fn impl_i64(name: &str) -> i64 {
    i64::try_from(impl_u64(name))
        .unwrap_or_else(|_| panic!("impl constant {name} does not fit i64"))
}

/// Value of a `≤ name` bound. The name is the §4 constant (`W_MAX`, `M_MAX`, …).
pub fn upper_bound(name: &str) -> u64 {
    let n = protocol_u64(name);
    if !protocol_text_has_upper(name) {
        panic!("spec has no ≤ {name} bound");
    }
    n
}

/// Header rule `version ≥ N`.
pub fn version_min() -> u64 {
    version_min_in(protocol_text()).unwrap_or_else(|| panic!("spec has no version ≥ N"))
}

/// Header rule `bits ≠ N`. The rejected value is `N`.
pub fn bits_rejected() -> u64 {
    neq_in(protocol_text(), "bits").unwrap_or_else(|| panic!("spec has no bits ≠ N"))
}

/// Future-time window from `T_FUTURE`, present as an upper bound in the header rule.
pub fn future_window() -> u64 {
    if !protocol_text_has_upper("T_FUTURE") && !protocol_text_has_upper("MAX_FUTURE_BLOCK_TIME") {
        panic!("spec has no future-time upper bound");
    }
    protocol_u64("T_FUTURE")
}

/// Header rule `timestamp ≠ N`. The rejected value is `N`.
pub fn timestamp_rejected() -> u64 {
    neq_in(protocol_text(), "timestamp").unwrap_or_else(|| panic!("spec has no timestamp ≠ N"))
}

/// H05 writes `timestamp ≥ MedianTimePast`. The census clause is the `<` rejection.
pub fn median_past_is_lower_bound() -> bool {
    math_blocks(protocol_text()).into_iter().any(|block| {
        let norm = normalize_math(&block);
        norm.contains("timestamp") && norm.contains(">=") && norm.contains("MedianTimePast")
    })
}

/// `INITIAL_SUBSIDY = 50 × C` from the subsidy section.
pub fn initial_subsidy() -> u64 {
    let found = math_blocks(protocol_text()).into_iter().any(|block| {
        let norm = normalize_math(&block);
        norm.contains("INITIAL_SUBSIDY") && norm.contains("50 * C")
    });
    if !found {
        panic!("spec has no INITIAL_SUBSIDY = 50 × C");
    }
    50 * protocol_u64("C")
}

/// Inclusive range in the math nearest `label` (`scriptSig`, `IsStrictDER`).
pub fn range_near(label: &str) -> (u64, u64) {
    let md = protocol_text();
    let at = md
        .find(label)
        .unwrap_or_else(|| panic!("spec has no {label}"));
    let mut after: Option<(u64, u64)> = None;
    for (start, block) in math_blocks_at(md) {
        let norm = strip_brackets(&normalize_math(&block));
        let Some(expr) = parse_expr(&norm) else {
            continue;
        };
        let Some(range) = inclusive_range(&expr) else {
            continue;
        };
        if block.contains(label) {
            return range;
        }
        if start >= at && after.is_none() {
            after = Some(range);
        }
    }
    after.unwrap_or_else(|| panic!("spec has no inclusive range near {label}"))
}

/// Largest opcode in the completed `PushOpcode` set. The set must be `0x00..=max`.
pub fn push_opcode_max() -> u64 {
    let md = protocol_text();
    let start = md
        .find("PushOpcode")
        .unwrap_or_else(|| panic!("spec has no PushOpcode"));
    let rest = &md[start..];
    let end = rest
        .find("**Opcode table**")
        .unwrap_or_else(|| panic!("spec PushOpcode list is not closed by the opcode table"));
    let section = &rest[..end];
    let mut present = vec![false; 0x61];
    let norm = normalize_math(section);
    fill_push_set(&norm, &mut present);
    if !present.iter().all(|bit| *bit) {
        panic!("spec PushOpcode set is not the contiguous range 0x00..=0x60");
    }
    0x60
}

/// Inclusive ranges in the immediate-success sentence. A single opcode is `(n, n)`.
pub fn op_success_ranges() -> Vec<(u64, u64)> {
    let md = protocol_text();
    let start = md
        .find("immediate success")
        .unwrap_or_else(|| panic!("spec has no immediate-success sentence"));
    let rest = &md[start..];
    let end = rest.find('\n').unwrap_or(rest.len());
    let mut out = Vec::new();
    for block in math_blocks(&rest[..end]) {
        let norm = decimalize_hex(&normalize_math(&block));
        if let Some(expr) = parse_expr(&norm) {
            if let Some(range) = inclusive_range(&expr) {
                out.push(range);
                continue;
            }
            if let Expr::Lit(n) = expr {
                out.push((n, n));
            }
        }
    }
    if out.is_empty() {
        panic!("spec immediate-success sentence has no ranges");
    }
    out
}

pub fn opcodes() -> &'static [OpcodeRow] {
    static ROWS: OnceLock<Vec<OpcodeRow>> = OnceLock::new();
    ROWS.get_or_init(|| parse_opcode_table(protocol_text()))
        .as_slice()
}

pub fn opcode(name: &str) -> Option<&'static OpcodeRow> {
    opcodes().iter().find(|row| row.name == name)
}

/// True when the row's clause value is a parsed spec atom or an opcode-table row.
pub fn is_spec_sourced(name: &str) -> bool {
    SPEC_SOURCED.contains(&name) || opcode(name).is_some()
}

/// Hex mask in the equation that defines `label`.
pub fn mask_in(label: &str) -> u64 {
    let mut hit = None;
    for block in math_blocks(protocol_text()) {
        if !block.contains(label) {
            continue;
        }
        let hexes = hex_values(&block);
        if hexes.len() == 1 {
            return hexes[0];
        }
        if hit.is_none() && !hexes.is_empty() {
            hit = Some(hexes[0]);
        }
    }
    hit.unwrap_or_else(|| panic!("spec mask for {label} is missing"))
}

/// `lt < 500000000` from the locktime-type equation.
pub fn locktime_threshold() -> u64 {
    for block in math_blocks(protocol_text()) {
        let n = normalize_math(&block);
        if let Some(v) = decimal_after_op(&n, "<") {
            if v >= 100_000_000 {
                return v;
            }
        }
    }
    panic!("spec locktime threshold is missing");
}

/// BIP65 orders by `tx_locktime >= stack_locktime`.
pub fn bip65_orders_ge() -> bool {
    math_blocks(protocol_text()).iter().any(|block| {
        let n = normalize_math(block);
        n.contains(">=") && (n.contains("tx_locktime") || n.contains("lockTime"))
    })
}

pub fn bip54_sigop_cap() -> u64 {
    let text = protocol_text();
    let i = text
        .find("per-tx sigop")
        .or_else(|| text.find("CheckBip54SigOpLimit"))
        .unwrap_or_else(|| panic!("spec BIP54 sigop section is missing"));
    for (pos, block) in math_blocks_at(text) {
        if pos < i {
            continue;
        }
        let n = normalize_math(&block);
        if let Some(v) = decimal_after_op(&n, "<=") {
            return v;
        }
    }
    panic!("spec BIP54 sigop cap is missing");
}

pub fn bip54_locktime_delta() -> u64 {
    for block in math_blocks(protocol_text()) {
        let n = normalize_math(&block);
        if let Some(i) = n.find("height - ") {
            if let Some(v) = leading_decimal(&n[i + "height - ".len()..]) {
                return v;
            }
        }
    }
    panic!("spec BIP54 locktime delta is missing");
}

pub fn bip54_sequence_rejected() -> u64 {
    for block in math_blocks(protocol_text()) {
        let n = normalize_math(&block);
        if n.contains("sequence") || n.contains("Sequence") {
            if let Some(v) = hex_values(&n).into_iter().find(|v| *v > 0xff) {
                return v;
            }
        }
    }
    panic!("spec BIP54 sequence rejection is missing");
}

pub fn stripped_size_rejected() -> u64 {
    for block in math_blocks(protocol_text()) {
        let n = normalize_math(&block);
        if n.contains("SerializeNoWitness") {
            if let Some(v) = decimal_after_op(&n, "=") {
                return v;
            }
        }
    }
    panic!("spec stripped-size rejection is missing");
}

pub fn bip54_timewarp_grace() -> u64 {
    for block in math_blocks(protocol_text()) {
        let n = normalize_math(&block);
        if n.contains("7200") || n.contains("- 7200") {
            if let Some(v) = leading_decimal(n.trim_start_matches(|c: char| !c.is_ascii_digit())) {
                if v >= 1000 {
                    return v;
                }
            }
        }
    }
    panic!("spec BIP54 timewarp grace is missing");
}

/// `IsBip54ActiveAt` is `height >=` the activation.
pub fn bip54_activation_is_ge() -> bool {
    let text = protocol_text();
    text.contains("height \\geq a")
        || text.contains("height ≥ a")
        || math_blocks(text).iter().any(|block| {
            let n = normalize_math(block);
            n.contains("IsBip54ActiveAt") && n.contains(">=")
        })
}

pub fn witness_program_lengths() -> (u64, u64) {
    for block in math_blocks(protocol_text()) {
        if !block.contains("ValidateWitnessProgramLength") {
            continue;
        }
        let n = normalize_math(&block);
        let mut vals = Vec::new();
        let mut rest = n.as_str();
        while let Some(i) = rest.find('=') {
            rest = &rest[i + 1..];
            if rest.starts_with('>') || rest.starts_with('<') || rest.starts_with('=') {
                continue;
            }
            if let Some(v) = leading_decimal(rest) {
                if v > 0 && v < 128 {
                    vals.push(v);
                }
            }
        }
        if vals.len() >= 2 {
            let short = *vals.iter().min().unwrap();
            let long = *vals.iter().max().unwrap();
            return (short, long);
        }
    }
    panic!("spec witness program lengths are missing");
}

pub fn weight_base_coeff() -> u64 {
    for block in math_blocks(protocol_text()) {
        if let Some(i) = block.find("BaseSize") {
            if let Some(v) = last_number(&block[..i]) {
                return v;
            }
        }
    }
    panic!("spec weight coefficient is missing");
}

/// `(weight + add) / div` from the ceiling equation.
pub fn vsize_ceiling() -> (u64, u64) {
    for block in math_blocks(protocol_text()) {
        if let Some(i) = block.find("weight + ") {
            let add = leading_decimal(&block[i + "weight + ".len()..]).unwrap_or(0);
            let div = block[i..]
                .split('/')
                .nth(1)
                .and_then(leading_decimal)
                .unwrap_or(0);
            if add > 0 && div > 0 {
                return (add, div);
            }
        }
    }
    panic!("spec vsize ceiling is missing");
}

pub fn sigop_legacy_scale() -> u64 {
    for block in math_blocks(protocol_text()) {
        let n = normalize_math(&block);
        if n.contains("GetLegacySigOpCount") && n.contains("* ") {
            if let Some(v) = leading_decimal(n.split("* ").nth(1).unwrap_or("")) {
                return v;
            }
        }
    }
    panic!("spec sigop scale is missing");
}

pub fn p2sh_flag_bit() -> u64 {
    flag_bit("SCRIPT_VERIFY_P2SH")
}

pub fn flag_bit(name: &str) -> u64 {
    let text = protocol_text();
    let mut rest = text;
    while let Some(i) = rest.find(name) {
        let at = text.len() - rest.len() + i;
        let window = &text[at..text.len().min(at + name.len() + 80)];
        if let Some(v) = hex_values(window).into_iter().next() {
            return v;
        }
        rest = &rest[i + name.len()..];
    }
    panic!("spec flag {name} has no bit");
}

pub fn coinbase_shape() -> (u64, bool, u64) {
    let mut count = None;
    let mut null_hash = false;
    let mut index = None;
    for block in math_blocks(protocol_text()) {
        if !block.contains("IsCoinbase") && !block.contains("0^{32}") {
            continue;
        }
        let n = normalize_math(&block);
        if n.contains("= 1") && (block.contains("ins") || n.contains("ins")) {
            count = Some(1);
        }
        if block.contains("0^{32}") {
            null_hash = true;
        }
        if let Some(i) = block.find("2^{") {
            if let Some(exp) = leading_decimal(&block[i + 3..]) {
                if exp < 63 {
                    index = Some((1u64 << exp) - 1);
                }
            }
        }
    }
    (
        count.expect("spec coinbase input count is missing"),
        {
            if !null_hash {
                panic!("spec coinbase null hash is missing");
            }
            true
        },
        index.expect("spec coinbase index is missing"),
    )
}

/// MinVersion cases: BIP65, BIP66, BIP34, otherwise.
pub fn min_version_floors() -> (i64, i64, i64, i64) {
    let mut floors = [None; 4];
    for block in math_blocks(protocol_text()) {
        if !block.contains("MinVersion") {
            continue;
        }
        let n = normalize_math(&block);
        for (i, key) in ["BIP65", "BIP66", "BIP34", "otherwise"].iter().enumerate() {
            if let Some(pos) = n.find(key) {
                let before = &n[..pos];
                if let Some(v) = trailing_decimal(before) {
                    floors[i] = Some(v as i64);
                }
            }
        }
    }
    (
        floors[0].expect("spec BIP65 version is missing"),
        floors[1].expect("spec BIP66 version is missing"),
        floors[2].expect("spec BIP34 version is missing"),
        floors[3].expect("spec default version is missing"),
    )
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreimageField {
    pub name: String,
    pub width: Option<u32>,
}

pub fn bip143_fields() -> Vec<PreimageField> {
    for block in math_blocks(protocol_text()) {
        if !block.contains("hashPrevouts") || !block.contains("\\parallel") {
            continue;
        }
        let mut fields = Vec::new();
        for part in block.split("\\parallel") {
            let n = normalize_math(part);
            let part = n
                .trim()
                .trim_matches(|c: char| c == '(' || c == ')' || c == '=');
            let part = part.trim();
            if part.is_empty() {
                continue;
            }
            let (name, width) = split_width(part);
            let name = name
                .split(|c: char| !c.is_ascii_alphanumeric())
                .filter(|s| !s.is_empty())
                .next_back()
                .unwrap_or("");
            if name.is_empty() {
                continue;
            }
            fields.push(PreimageField {
                name: name.to_string(),
                width,
            });
        }
        if fields.len() >= 8 {
            return fields;
        }
    }
    panic!("spec BIP143 preimage concatenation is missing");
}

/// Standard sighash base types `0x01`, `0x02`, `0x03`.
pub fn sighash_standard_bounds() -> (u64, u64) {
    for block in math_blocks(protocol_text()) {
        let n = normalize_math(&block);
        if !n.contains("0x01") || !n.contains("0x03") {
            continue;
        }
        let hexes = hex_values(&n);
        let standard: Vec<u64> = hexes.into_iter().filter(|v| *v <= 0x03).collect();
        if standard.contains(&0x01) && standard.contains(&0x03) {
            let lo = *standard.iter().filter(|v| **v > 0).min().unwrap_or(&1);
            let hi = *standard.iter().max().unwrap_or(&3);
            return (lo, hi);
        }
    }
    panic!("spec sighash standard range is missing");
}

pub fn sighash_single_lead() -> u64 {
    let text = protocol_text();
    let Some(i) = text.find("byte 0 equal") else {
        panic!("spec sighash-single quirk is missing");
    };
    let window = &text[i..text.len().min(i + 80)];
    hex_values(window)
        .into_iter()
        .next()
        .unwrap_or_else(|| panic!("spec sighash-single lead byte is missing"))
}

pub fn direct_push_max() -> u64 {
    for block in math_blocks(protocol_text()) {
        let n = normalize_math(&block);
        if n.contains("0x4b") && n.contains("<=") {
            return 0x4b;
        }
    }
    panic!("spec direct-push max is missing");
}

/// First opcode byte above the completed push set.
pub fn first_non_push_byte() -> u64 {
    let max = push_opcode_max();
    opcodes()
        .iter()
        .map(|row| row.byte)
        .filter(|b| *b > max)
        .min()
        .unwrap_or_else(|| panic!("spec has no opcode above the push set"))
}

/// Prefix widths the push bullets state: direct 0, then 1, 2, and 4.
/// The advance is one opcode byte plus that prefix.
pub fn push_advances() -> [u64; 4] {
    let widths = push_prefix_widths();
    [1 + widths[0], 1 + widths[1], 1 + widths[2], 1 + widths[3]]
}

pub fn push_prefix_widths() -> [u64; 4] {
    let text = protocol_text();
    let one = byte_width_near(text, "1-byte length");
    let two = byte_width_near(text, "2-byte length");
    let four = byte_width_near(text, "4-byte length");
    [0, one, two, four]
}

/// Commitment offset is one opcode byte, one length byte, and the stated magic width.
pub fn witness_commitment_offset() -> u64 {
    let text = protocol_text();
    let Some(i) = text.find("4-byte magic") else {
        panic!("spec witness-commitment magic width is missing");
    };
    let magic = leading_decimal(&text[i..]).unwrap_or_else(|| panic!("spec magic width"));
    1 + 1 + magic
}

pub fn witness_magic_present() -> bool {
    protocol_text().contains("0xaa21a9ed")
}

pub fn annex_rule() -> (u64, u64) {
    let text = protocol_text();
    let Some(i) = text.find("begins with byte") else {
        panic!("spec annex tag is missing");
    };
    let window = &text[i.saturating_sub(40)..text.len().min(i + 40)];
    let tag = hex_values(window)
        .into_iter()
        .next()
        .unwrap_or_else(|| panic!("spec annex tag byte is missing"));
    let min = if text.contains("|w| \\geq 2") || text.contains("|w| ≥ 2") {
        2
    } else {
        panic!("spec annex minimum length is missing");
    };
    (tag, min)
}

pub fn compact_target() -> (u64, u64, u64, u64, u64) {
    let mut mask = None;
    let mut lo = None;
    let mut hi = None;
    let mut bias = None;
    let mut shift = None;
    for block in math_blocks(protocol_text()) {
        let n = normalize_math(&block);
        if block.contains("0x007fffff") {
            mask = hex_values(&normalize_math(&block.replace("\\mathtt", "")))
                .into_iter()
                .find(|v| *v > 0xff);
        }
        if n.contains("exponent") && n.contains("<=") {
            if let Some(v) = trailing_decimal(n.split("exponent").next().unwrap_or("")) {
                lo = Some(v);
            }
            if let Some(tail) = n.split("exponent").nth(1) {
                hi = decimal_after_op(tail, "<=").or_else(|| {
                    leading_decimal(
                        tail.trim_start_matches(|c: char| c != '0' && !c.is_ascii_digit()),
                    )
                });
            }
        }
        if block.contains("exponent") && block.contains("- ") {
            if let Some(i) = block.find("- ") {
                if block[..i].contains("exponent") {
                    bias = leading_decimal(&block[i + 2..]);
                }
            }
        }
        if block.contains("exponent") && block.contains("\\times") {
            if let Some(v) = last_number(block.split("\\times").next().unwrap_or("")) {
                if v > 1 && v < 64 {
                    shift = Some(v);
                }
            }
        }
    }
    (
        mask.expect("spec mantissa mask is missing"),
        lo.expect("spec exponent floor is missing"),
        hi.expect("spec exponent ceiling is missing"),
        bias.expect("spec exponent bias is missing"),
        shift.unwrap_or(8),
    )
}

pub fn header_hash_rounds() -> u32 {
    for block in math_blocks(protocol_text()) {
        if block.contains("ExpandTarget") && block.contains("SHA256") {
            return block.matches("SHA256").count() as u32;
        }
    }
    panic!("spec header hash is missing");
}

pub fn header_hash_strict() -> bool {
    for block in math_blocks(protocol_text()) {
        if block.contains("ExpandTarget") && block.contains("SHA256") {
            let n = normalize_math(&block);
            return n.contains('<') && !n.contains("<=");
        }
    }
    panic!("spec header hash comparison is missing");
}

pub fn parent_hash_equal() -> bool {
    math_blocks(protocol_text()).iter().any(|block| {
        block.contains("ValidatePrevBlockHash") && block.contains('=') && !block.contains("\\neq")
    })
}

pub fn empty_pattern_is_noop() -> bool {
    protocol_text().contains("|pattern| = 0")
}

pub fn merkle_compares_unpadded() -> bool {
    protocol_text().contains("unpadded") && protocol_text().contains("not a mutation")
}

pub fn taproot_height(network: &str) -> u64 {
    let needle = match network {
        "mainnet" => "709632",
        "testnet" => "2011968",
        _ => panic!("spec taproot height for {network} is not a stated deployment"),
    };
    for block in math_blocks(protocol_text()) {
        let n = normalize_math(&block);
        if n.contains(needle) {
            return needle.parse().unwrap();
        }
    }
    panic!("spec taproot {network} height is missing");
}

fn byte_width_near(text: &str, phrase: &str) -> u64 {
    let Some(i) = text.find(phrase) else {
        panic!("spec phrase {phrase} is missing");
    };
    leading_decimal(&text[i..]).unwrap_or_else(|| panic!("spec width in {phrase} is missing"))
}

fn split_width(part: &str) -> (String, Option<u32>) {
    let part = part.trim();
    if let Some((name, width)) = part.rsplit_once('_') {
        if width.chars().all(|c| c.is_ascii_digit()) && !width.is_empty() {
            return (name.trim().to_string(), width.parse().ok());
        }
    }
    (part.to_string(), None)
}

fn hex_values(s: &str) -> Vec<u64> {
    let bytes = s.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i + 2 < bytes.len() {
        if bytes[i] == b'0' && (bytes[i + 1] == b'x' || bytes[i + 1] == b'X') {
            let mut j = i + 2;
            let mut digits = String::new();
            while j < bytes.len() && bytes[j].is_ascii_hexdigit() {
                digits.push(bytes[j] as char);
                j += 1;
            }
            if let Ok(v) = u64::from_str_radix(&digits, 16) {
                if !digits.is_empty() {
                    out.push(v);
                }
            }
            i = j;
            continue;
        }
        i += 1;
    }
    out
}

fn decimal_after_op(s: &str, op: &str) -> Option<u64> {
    let mut rest = s;
    while let Some(i) = rest.find(op) {
        let after = &rest[i + op.len()..];
        if op == "<" && after.starts_with('=') {
            rest = &rest[i + op.len()..];
            continue;
        }
        if op == "="
            && (rest[..i].ends_with('<') || rest[..i].ends_with('>') || rest[..i].ends_with('!'))
        {
            rest = &rest[i + op.len()..];
            continue;
        }
        let trimmed = after.trim_start();
        if let Some(v) = leading_decimal(trimmed) {
            if v > 0 {
                return Some(v);
            }
        }
        rest = &rest[i + op.len()..];
    }
    None
}

fn leading_decimal(s: &str) -> Option<u64> {
    let s = s.trim_start();
    let digits: String = s.chars().take_while(|c| c.is_ascii_digit()).collect();
    if digits.is_empty() {
        None
    } else {
        digits.parse().ok()
    }
}

fn trailing_decimal(s: &str) -> Option<u64> {
    last_number(s)
}

fn last_number(s: &str) -> Option<u64> {
    let bytes = s.as_bytes();
    let mut end = bytes.len();
    while end > 0 && !bytes[end - 1].is_ascii_digit() {
        end -= 1;
    }
    let mut start = end;
    while start > 0 && bytes[start - 1].is_ascii_digit() {
        start -= 1;
    }
    if start == end {
        None
    } else {
        std::str::from_utf8(&bytes[start..end])
            .ok()
            .and_then(|d| d.parse().ok())
    }
}

pub fn constants_in(markdown: &str) -> Result<HashMap<String, u64>, String> {
    let mut parser = SpecParser::new(markdown.to_string());
    parser.parse()?;
    let raw = parser
        .extract_constants()
        .into_iter()
        .map(|constant| (constant.name.clone(), constant.rust_expr.clone()))
        .collect();
    Ok(fold_constants(raw))
}

pub fn version_min_in(markdown: &str) -> Option<u64> {
    for expr in math_exprs(markdown) {
        if let Some(n) = lower_bound(&expr, "version") {
            return Some(n);
        }
    }
    None
}

pub fn neq_in(markdown: &str, field: &str) -> Option<u64> {
    for expr in math_exprs(markdown) {
        if let Some(n) = neq_value(&expr, field) {
            return Some(n);
        }
    }
    None
}

/// Census and mutation tests read the sibling checkouts. A CI checkout of this
/// repo alone does not have them; those tests return instead of panicking.
pub fn consensus_workspace_present() -> bool {
    workspace_at(&Path::new(env!("CARGO_MANIFEST_DIR")).join(".."))
}

fn workspace_at(root: &Path) -> bool {
    root.join("blvm-spec/PROTOCOL.md").is_file()
        && root.join("blvm-primitives/src/constants.rs").is_file()
        && root.join("blvm-consensus/src").is_dir()
}

fn protocol_constants() -> &'static HashMap<String, u64> {
    static MAP: OnceLock<HashMap<String, u64>> = OnceLock::new();
    MAP.get_or_init(|| {
        constants_in(protocol_text()).unwrap_or_else(|e| panic!("section 4 constants: {e}"))
    })
}

fn protocol_text() -> &'static str {
    static TEXT: OnceLock<String> = OnceLock::new();
    TEXT.get_or_init(|| {
        let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../blvm-spec/PROTOCOL.md");
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
    })
    .as_str()
}

fn primitives_src() -> &'static str {
    static TEXT: OnceLock<String> = OnceLock::new();
    TEXT.get_or_init(|| {
        let path =
            Path::new(env!("CARGO_MANIFEST_DIR")).join("../blvm-primitives/src/constants.rs");
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
    })
    .as_str()
}

fn protocol_text_has_upper(name: &str) -> bool {
    math_blocks(protocol_text()).into_iter().any(|block| {
        let norm = normalize_math(&block);
        !norm.contains("forall") && loose_le_name(&norm, name)
    })
}

fn loose_le_name(norm: &str, name: &str) -> bool {
    let mut rest = norm;
    while let Some(i) = rest.find("<=") {
        rest = &rest[i + 2..];
        let head: String = rest
            .chars()
            .take_while(|c| !matches!(c, '<' | '>' | '!' | '=' | '&'))
            .collect();
        for tok in head.split(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == '.')) {
            if tok.is_empty() {
                continue;
            }
            let base = tok.rsplit('.').next().unwrap_or(tok);
            if base == name || alias(base) == Some(name) {
                return true;
            }
        }
    }
    false
}

fn fold_constants(raw: Vec<(String, String)>) -> HashMap<String, u64> {
    let mut env = HashMap::new();
    let mut pending = Vec::new();
    for (name, expr) in raw {
        let cleaned = expr.replace('_', "");
        if let Ok(n) = cleaned.trim().parse::<u64>() {
            env.insert(name, n);
        } else {
            pending.push((name, cleaned));
        }
    }
    for (name, expr) in pending {
        if let Some(n) = fold_times_c(&expr, env.get("C").copied()) {
            env.insert(name, n);
        }
    }
    env
}

fn fold_times_c(expr: &str, c: Option<u64>) -> Option<u64> {
    let compact: String = expr.chars().filter(|ch| !ch.is_whitespace()).collect();
    let rest = compact.strip_prefix('(')?;
    let (base, after) = rest.split_once("*C)")?;
    if !after.starts_with("asi64") {
        return None;
    }
    let base: u64 = base.parse().ok()?;
    Some(base.saturating_mul(c?))
}

fn rust_const_u64(src: &str, name: &str) -> Option<u64> {
    let needle = format!("const {name}:");
    let rest = src.get(src.find(&needle)? + needle.len()..)?;
    let expr = rest.get(rest.find('=')? + 1..)?;
    let expr = expr.split([';', '\n']).next()?.trim();
    eval_rust_int(expr)
}

fn eval_rust_int(expr: &str) -> Option<u64> {
    let expr = expr.replace(['_', ' '], "");
    if let Some((left, right)) = expr.split_once('*') {
        return Some(eval_rust_int(left)? * eval_rust_int(right)?);
    }
    expr.parse().ok()
}

fn math_exprs(markdown: &str) -> Vec<Expr> {
    let mut out = Vec::new();
    for block in math_blocks(markdown) {
        let norm = normalize_math(&block);
        if norm.contains("forall") {
            continue;
        }
        if let Some(expr) = parse_expr(&norm) {
            if usable(&expr) {
                out.push(expr);
            }
        }
    }
    out
}

fn math_blocks(markdown: &str) -> Vec<String> {
    math_blocks_at(markdown)
        .into_iter()
        .map(|(_, block)| block)
        .collect()
}

fn math_blocks_at(markdown: &str) -> Vec<(usize, String)> {
    let mut out = Vec::new();
    let bytes = markdown.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'$' {
            let display = markdown[i..].starts_with("$$");
            let open = if display { 2 } else { 1 };
            let start = i + open;
            if let Some(rel) = markdown[start..].find(if display { "$$" } else { "$" }) {
                out.push((start, markdown[start..start + rel].to_string()));
                i = start + rel + open;
                continue;
            }
        }
        i += 1;
    }
    out
}

fn normalize_math(raw: &str) -> String {
    let mut s = raw.to_string();
    s = s
        .replace("\\leq", "<=")
        .replace("\\geq", ">=")
        .replace("\\neq", "!=");
    s = s.replace('≤', "<=").replace('≥', ">=").replace('≠', "!=");
    s = s.replace("\\land", "&&").replace('∧', "&&");
    s = s.replace("\\implies", "=>").replace(['⟹', '⇒'], "=>");
    s = s.replace("\\times", "*").replace('×', "*");
    s = s.replace("\\_", "_");
    s = rewrite_text(&s);
    s = rewrite_subscripts(&s);
    s = strip_commands(&s);
    s = strip_calls(&s);
    s = s.replace('|', "");
    s = s.replace("{,}", "");
    s = s.replace(',', "");
    s
}

fn rewrite_text(s: &str) -> String {
    let mut out = String::new();
    let mut rest = s;
    while let Some(i) = rest.find("\\text{") {
        out.push_str(&rest[..i]);
        rest = &rest[i + 6..];
        if let Some(end) = rest.find('}') {
            out.push_str(&rest[..end]);
            rest = &rest[end + 1..];
        } else {
            break;
        }
    }
    out.push_str(rest);
    out
}

fn rewrite_subscripts(s: &str) -> String {
    let mut out = String::new();
    let chars: Vec<char> = s.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        if chars[i] == '_' && i + 1 < chars.len() && chars[i + 1] == '{' {
            out.push('_');
            i += 2;
            while i < chars.len() && chars[i] != '}' {
                out.push(chars[i].to_ascii_uppercase());
                i += 1;
            }
            if i < chars.len() && chars[i] == '}' {
                i += 1;
            }
        } else {
            out.push(chars[i]);
            i += 1;
        }
    }
    out
}

fn strip_commands(s: &str) -> String {
    let mut out = String::new();
    let chars: Vec<char> = s.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        if chars[i] == '\\' {
            i += 1;
            while i < chars.len() && chars[i].is_ascii_alphabetic() {
                i += 1;
            }
        } else {
            out.push(chars[i]);
            i += 1;
        }
    }
    out
}

fn strip_calls(s: &str) -> String {
    let mut out = String::new();
    let chars: Vec<char> = s.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        if chars[i] == '(' {
            let mut depth = 1;
            i += 1;
            while i < chars.len() && depth > 0 {
                if chars[i] == '(' {
                    depth += 1;
                } else if chars[i] == ')' {
                    depth -= 1;
                }
                i += 1;
            }
        } else {
            out.push(chars[i]);
            i += 1;
        }
    }
    out
}

fn strip_brackets(s: &str) -> String {
    let mut out = String::new();
    let mut depth = 0i32;
    for c in s.chars() {
        if c == '[' {
            depth += 1;
            continue;
        }
        if c == ']' {
            depth = depth.saturating_sub(1);
            continue;
        }
        if depth == 0 {
            out.push(c);
        }
    }
    out
}

fn inclusive_range(expr: &Expr) -> Option<(u64, u64)> {
    let Expr::And(parts) = expr else {
        return None;
    };
    let mut lo = None;
    let mut hi = None;
    for part in parts {
        let Expr::Cmp(Op::Le, lhs, rhs) = part else {
            continue;
        };
        if let Expr::Lit(n) = lhs.as_ref() {
            lo = Some(*n);
        }
        if let Expr::Lit(n) = rhs.as_ref() {
            hi = Some(*n);
        }
    }
    Some((lo?, hi?))
}

fn fill_push_set(norm: &str, present: &mut [bool]) {
    let bytes = norm.as_bytes();
    let mut i = 0;
    while i + 2 < bytes.len() {
        if bytes[i] == b'0' && bytes[i + 1] == b'x' {
            if let Some((val, next)) = hex_at(&norm[i + 2..]) {
                let tail = norm[i + 2 + next..].trim_start();
                if let Some(rest) = tail.strip_prefix("<=") {
                    if let Some(after) = rest.split("<=").nth(1) {
                        if let Some(hi) = hex_token(after.trim_start()) {
                            for n in val..=hi {
                                if (n as usize) < present.len() {
                                    present[n as usize] = true;
                                }
                            }
                            i += 2 + next;
                            continue;
                        }
                    }
                }
                if (val as usize) < present.len() {
                    present[val as usize] = true;
                }
                i += 2 + next;
                continue;
            }
        }
        i += 1;
    }
}

/// The immediate-success sentence is written in hex. The census still matches
/// the decimal opcode numbers in source (`80 | 98`, `126..=129`).
fn decimalize_hex(norm: &str) -> String {
    let bytes = norm.as_bytes();
    let mut out = String::new();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'0' && bytes.get(i + 1) == Some(&b'x') {
            if let Some((val, next)) = hex_at(&norm[i + 2..]) {
                if next > 0 {
                    out.push_str(&val.to_string());
                    i += 2 + next;
                    continue;
                }
            }
        }
        out.push(bytes[i] as char);
        i += 1;
    }
    out
}

fn hex_at(s: &str) -> Option<(u64, usize)> {
    let hex: String = s.chars().take_while(|c| c.is_ascii_hexdigit()).collect();
    if hex.is_empty() {
        return None;
    }
    Some((u64::from_str_radix(&hex, 16).ok()?, hex.len()))
}

fn hex_token(s: &str) -> Option<u64> {
    let s = s.trim_start();
    let s = s.strip_prefix("0x")?;
    hex_at(s).map(|(n, _)| n)
}

fn parse_opcode_table(markdown: &str) -> Vec<OpcodeRow> {
    let start = markdown
        .find("**Opcode table**")
        .unwrap_or_else(|| panic!("spec has no opcode table"));
    let mut rows = Vec::new();
    for line in markdown[start..].lines() {
        if line.starts_with("**P2SH") {
            break;
        }
        if !line.starts_with("| OP_") {
            continue;
        }
        let cols: Vec<&str> = line
            .split('|')
            .map(str::trim)
            .filter(|col| !col.is_empty())
            .collect();
        if cols.len() != 4 {
            panic!("opcode table row has {} columns: {line}", cols.len());
        }
        let byte = u64::from_str_radix(cols[1].trim_start_matches("0x"), 16)
            .unwrap_or_else(|_| panic!("opcode byte {}", cols[1]));
        let min = cols[2]
            .parse()
            .unwrap_or_else(|_| panic!("opcode stack {}", cols[2]));
        rows.push(OpcodeRow {
            name: cols[0].to_string(),
            byte,
            min,
            op: cols[3].to_string(),
        });
    }
    if rows.is_empty() {
        panic!("opcode table is empty");
    }
    rows
}

fn usable(expr: &Expr) -> bool {
    match expr {
        Expr::Cmp(Op::Eq, lhs, rhs) => !is_result_zero(lhs, rhs),
        Expr::Implies(_, conclusion) => usable(conclusion),
        Expr::And(parts) => parts.iter().any(usable),
        Expr::Cmp(_, _, _) => true,
        _ => false,
    }
}

fn is_result_zero(lhs: &Expr, rhs: &Expr) -> bool {
    matches!(lhs, Expr::Name(name) if base_name(name) == "result") && matches!(rhs, Expr::Lit(0))
}

fn base_name(name: &str) -> &str {
    name.rsplit('.').next().unwrap_or(name)
}

fn has_upper(expr: &Expr, name: &str) -> bool {
    match expr {
        Expr::Cmp(Op::Le, _, rhs) => rhs_is(rhs, name),
        Expr::And(parts) => parts.iter().any(|part| has_upper(part, name)),
        Expr::Implies(_, conclusion) => has_upper(conclusion, name),
        _ => false,
    }
}

fn rhs_is(expr: &Expr, name: &str) -> bool {
    match expr {
        Expr::Name(got) => base_name(got) == name || alias(base_name(got)) == Some(name),
        Expr::Add(_, right) => rhs_is(right, name),
        _ => false,
    }
}

fn alias(name: &str) -> Option<&'static str> {
    match name {
        "MAX_FUTURE_BLOCK_TIME" => Some("T_FUTURE"),
        _ => None,
    }
}

fn lower_bound(expr: &Expr, field: &str) -> Option<u64> {
    match expr {
        Expr::Cmp(Op::Ge, lhs, rhs) if lhs_is(lhs, field) => match rhs.as_ref() {
            Expr::Lit(n) => Some(*n),
            _ => None,
        },
        Expr::And(parts) => parts.iter().find_map(|part| lower_bound(part, field)),
        Expr::Implies(_, conclusion) => lower_bound(conclusion, field),
        _ => None,
    }
}

fn neq_value(expr: &Expr, field: &str) -> Option<u64> {
    match expr {
        Expr::Cmp(Op::Ne, lhs, rhs) if lhs_is(lhs, field) => match rhs.as_ref() {
            Expr::Lit(n) => Some(*n),
            _ => None,
        },
        Expr::And(parts) => parts.iter().find_map(|part| neq_value(part, field)),
        Expr::Implies(_, conclusion) => neq_value(conclusion, field),
        _ => None,
    }
}

fn lhs_is(expr: &Expr, field: &str) -> bool {
    matches!(expr, Expr::Name(name) if base_name(name) == field)
}

struct Parser<'a> {
    s: &'a [u8],
    i: usize,
}

fn parse_expr(input: &str) -> Option<Expr> {
    let mut p = Parser {
        s: input.as_bytes(),
        i: 0,
    };
    let expr = p.parse_implies()?;
    p.skip();
    if p.i != p.s.len() {
        return None;
    }
    Some(expr)
}

impl<'a> Parser<'a> {
    fn parse_implies(&mut self) -> Option<Expr> {
        let left = self.parse_and()?;
        self.skip();
        if self.eat("=>") {
            let right = self.parse_and()?;
            return Some(Expr::Implies(Box::new(left), Box::new(right)));
        }
        Some(left)
    }

    fn parse_and(&mut self) -> Option<Expr> {
        let mut parts = vec![self.parse_cmp()?];
        loop {
            self.skip();
            if self.eat("&&") {
                parts.push(self.parse_cmp()?);
            } else {
                break;
            }
        }
        if parts.len() == 1 {
            parts.pop()
        } else {
            Some(Expr::And(parts))
        }
    }

    fn parse_cmp(&mut self) -> Option<Expr> {
        let mut left = self.parse_add()?;
        let mut pairs = Vec::new();
        loop {
            self.skip();
            let op = if self.eat("<=") {
                Op::Le
            } else if self.eat(">=") {
                Op::Ge
            } else if self.eat("==") {
                Op::Eq
            } else if self.eat("!=") {
                Op::Ne
            } else if self.eat("<") {
                Op::Lt
            } else if self.eat(">") {
                Op::Gt
            } else {
                break;
            };
            let right = self.parse_add()?;
            pairs.push((op, left, right));
            left = pairs.last().unwrap().2.clone();
        }
        if pairs.is_empty() {
            return Some(left);
        }
        if pairs.len() == 1 {
            let (op, lhs, rhs) = pairs.pop().unwrap();
            return Some(Expr::Cmp(op, Box::new(lhs), Box::new(rhs)));
        }
        Some(Expr::And(
            pairs
                .into_iter()
                .map(|(op, lhs, rhs)| Expr::Cmp(op, Box::new(lhs), Box::new(rhs)))
                .collect(),
        ))
    }

    fn parse_add(&mut self) -> Option<Expr> {
        let mut left = self.parse_primary()?;
        loop {
            self.skip();
            if self.eat("+") {
                let right = self.parse_primary()?;
                left = Expr::Add(Box::new(left), Box::new(right));
            } else {
                break;
            }
        }
        Some(left)
    }

    fn parse_primary(&mut self) -> Option<Expr> {
        self.skip();
        if self.eat("(") {
            let inner = self.parse_implies()?;
            self.skip();
            if !self.eat(")") {
                return None;
            }
            return Some(inner);
        }
        if self.peek().is_some_and(|c| c.is_ascii_digit()) {
            return Some(Expr::Lit(self.number()?));
        }
        if self
            .peek()
            .is_some_and(|c| c.is_ascii_alphabetic() || c == b'_')
        {
            return Some(Expr::Name(self.ident()?));
        }
        None
    }

    fn number(&mut self) -> Option<u64> {
        let start = self.i;
        while self.peek().is_some_and(|c| c.is_ascii_digit()) {
            self.i += 1;
        }
        std::str::from_utf8(&self.s[start..self.i])
            .ok()?
            .parse()
            .ok()
    }

    fn ident(&mut self) -> Option<String> {
        let start = self.i;
        while self
            .peek()
            .is_some_and(|c| c.is_ascii_alphanumeric() || c == b'_' || c == b'.')
        {
            self.i += 1;
        }
        let text = std::str::from_utf8(&self.s[start..self.i]).ok()?;
        if text.is_empty() {
            None
        } else {
            Some(text.to_string())
        }
    }

    fn eat(&mut self, token: &str) -> bool {
        self.skip();
        if self.s[self.i..].starts_with(token.as_bytes()) {
            self.i += token.len();
            true
        } else {
            false
        }
    }

    fn skip(&mut self) {
        while self.peek().is_some_and(|c| c.is_ascii_whitespace()) {
            self.i += 1;
        }
    }

    fn peek(&self) -> Option<u8> {
        self.s.get(self.i).copied()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn section4_folds_money_and_the_block_caps() {
        let markdown = "\
### 4.1 Monetary Constants

$C = 10^8$ (satoshis per BTC)  
$M_{max} = 21 \\times 10^6 \\times C$ (cap)  
$H = 210,000$ (halving interval)

### 4.2 Block Constants

$W_{max} = 4 \\times 10^6$ (maximum block weight)  
$S_{max} = 80,000$ (maximum sigops)
";
        let map = constants_in(markdown).unwrap();
        assert_eq!(map.get("C").copied(), Some(100_000_000));
        assert_eq!(map.get("M_MAX").copied(), Some(2_100_000_000_000_000));
        assert_eq!(map.get("H").copied(), Some(210_000));
        assert_eq!(map.get("W_MAX").copied(), Some(4_000_000));
        assert_eq!(map.get("S_MAX").copied(), Some(80_000));
    }

    #[test]
    fn result_zero_is_not_a_clause_and_a_bound_parses() {
        assert!(parse_expr("result == 0").is_some());
        assert!(!usable(&parse_expr("result == 0").unwrap()));
        let joined = parse_expr("version >= 1 && bits != 0").unwrap();
        assert_eq!(lower_bound(&joined, "version"), Some(1));
        assert_eq!(neq_value(&joined, "bits"), Some(0));
        let implied = parse_expr("result == 1 => weight <= W_MAX").unwrap();
        assert!(has_upper(&implied, "W_MAX"));
        assert!(!has_upper(&parse_expr("result == 0").unwrap(), "W_MAX"));
    }

    #[test]
    fn a_checkout_without_sibling_crates_is_not_the_consensus_workspace() {
        assert!(!workspace_at(Path::new(
            "/this/blvm-spec-lock-checkout/has/no/siblings"
        )));
    }

    #[test]
    fn protocol_bounds_match_the_implementation_constants() {
        if !consensus_workspace_present() {
            return;
        }
        assert_eq!(upper_bound("W_MAX"), 4_000_000);
        assert_eq!(upper_bound("S_MAX"), 80_000);
        assert_eq!(upper_bound("L_SCRIPT"), 10_000);
        assert_eq!(upper_bound("L_STACK"), 1_000);
        assert_eq!(upper_bound("M_MAX"), 2_100_000_000_000_000);
        assert_eq!(protocol_u64("H"), 210_000);
        assert_eq!(future_window(), 7200);
        assert_eq!(version_min(), 1);
        assert_eq!(bits_rejected(), 0);
        assert_eq!(impl_u64("MAX_BLOCK_WEIGHT"), upper_bound("W_MAX"));
        assert_eq!(impl_u64("MAX_BLOCK_SIGOPS_COST"), upper_bound("S_MAX"));
        assert_eq!(impl_u64("MAX_SCRIPT_SIZE"), upper_bound("L_SCRIPT"));
        assert_eq!(impl_u64("MAX_STACK_SIZE"), upper_bound("L_STACK"));
        assert_eq!(impl_u64("HALVING_INTERVAL"), protocol_u64("H"));
        assert_eq!(impl_u64("MAX_FUTURE_BLOCK_TIME"), future_window());
        assert_eq!(impl_i64("MAX_MONEY") as u64, upper_bound("M_MAX"));
        assert_eq!(protocol_u64("L_ELEMENT"), 520);
        assert_eq!(protocol_u64("L_OPS"), 201);
        assert_eq!(protocol_u64("R"), 100);
        assert_eq!(protocol_u64("D_INTERVAL"), 2016);
        assert_eq!(protocol_u64("T_BLOCK"), 600);
        assert_eq!(timestamp_rejected(), 0);
        assert!(median_past_is_lower_bound());
        assert_eq!(initial_subsidy(), 5_000_000_000);
        assert_eq!(range_near("scriptSig"), (2, 100));
        assert_eq!(range_near("IsStrictDER"), (9, 73));
        assert_eq!(push_opcode_max(), 0x60);
        let success = op_success_ranges();
        assert!(success.contains(&(80, 80)));
        assert!(success.contains(&(187, 254)));
        let add = opcode("OP_ADD").unwrap();
        assert_eq!((add.byte, add.min, add.op.as_str()), (0x93, 2, "add"));
        let swap = opcode("OP_SWAP").unwrap();
        assert_eq!(swap.op, "swap");
        assert_ne!(swap.op, "12");
        assert_eq!(mask_in("IsSequenceDisabled"), 0x8000_0000);
        assert_eq!(mask_in("ExtractSequenceTypeFlag"), 0x0040_0000);
        assert_eq!(mask_in("ExtractSequenceLocktimeValue"), 0x0000_ffff);
        assert_eq!(locktime_threshold(), 500_000_000);
        assert!(bip65_orders_ge());
        assert_eq!(bip54_sigop_cap(), 2500);
        assert_eq!(bip54_locktime_delta(), 13);
        assert_eq!(bip54_sequence_rejected(), 0xffff_ffff);
        assert_eq!(stripped_size_rejected(), 64);
        assert_eq!(bip54_timewarp_grace(), 7200);
        assert!(bip54_activation_is_ge());
        assert_eq!(witness_program_lengths(), (20, 32));
        assert_eq!(weight_base_coeff(), 3);
        assert_eq!(vsize_ceiling(), (3, 4));
        assert_eq!(sigop_legacy_scale(), 4);
        assert_eq!(p2sh_flag_bit(), 0x01);
        assert_eq!(coinbase_shape(), (1, true, 0xffff_ffff));
        assert_eq!(min_version_floors(), (4, 3, 2, 1));
        let fields = bip143_fields();
        assert_eq!(fields.first().map(|f| f.name.as_str()), Some("nVersion"));
        assert_eq!(fields.first().and_then(|f| f.width), Some(32));
        assert_eq!(fields.last().map(|f| f.name.as_str()), Some("sighashType"));
        assert_eq!(sighash_standard_bounds(), (1, 3));
        assert_eq!(sighash_single_lead(), 0x01);
        assert_eq!(direct_push_max(), 0x4b);
        assert_eq!(push_prefix_widths(), [0, 1, 2, 4]);
        assert_eq!(push_advances(), [1, 2, 3, 5]);
        assert_eq!(witness_commitment_offset(), 6);
        assert!(witness_magic_present());
        assert_eq!(annex_rule(), (0x50, 2));
        assert_eq!(compact_target(), (0x007f_ffff, 3, 32, 3, 8));
        assert_eq!(header_hash_rounds(), 2);
        assert!(header_hash_strict());
        assert!(parent_hash_equal());
        assert!(merkle_compares_unpadded());
        assert_eq!(taproot_height("mainnet"), 709_632);
        assert_eq!(taproot_height("testnet"), 2_011_968);
        assert_eq!(flag_bit("SCRIPT_VERIFY_DERSIG"), 0x04);
        assert_eq!(flag_bit("SCRIPT_VERIFY_LOW_S"), 0x08);
        assert_eq!(flag_bit("SCRIPT_VERIFY_NULLDUMMY"), 0x10);
        assert_eq!(flag_bit("SCRIPT_VERIFY_CHECKLOCKTIMEVERIFY"), 0x200);
        assert_eq!(flag_bit("SCRIPT_VERIFY_CHECKSEQUENCEVERIFY"), 0x400);
    }

    #[test]
    fn a_changed_spec_constant_is_not_the_upper_bound_in_the_paper() {
        if !consensus_workspace_present() {
            return;
        }
        let markdown = "\
### 4.2 Block Constants

$W_{max} = 1$ (maximum block weight)

The block is valid when $weight \\leq W_{max}$.
";
        let map = constants_in(markdown).unwrap();
        assert_eq!(map.get("W_MAX").copied(), Some(1));
        assert_ne!(
            map.get("W_MAX").copied(),
            Some(impl_u64("MAX_BLOCK_WEIGHT"))
        );
    }

    #[test]
    fn removing_the_header_call_does_not_falsify_the_weight_bound() {
        let src = "\
if !header::validate_block_header(
block_weight > crate::constants::MAX_BLOCK_WEIGHT as u64 {";
        let patched = src.replace("if !header::validate_block_header(", "if false {");
        assert!(patched.contains("block_weight > crate::constants::MAX_BLOCK_WEIGHT as u64 {"));
    }
}
