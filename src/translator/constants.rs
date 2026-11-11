//! Integer values for well-known Bitcoin consensus constants.
//!
//! Always compiled (not gated on the `z3` feature) so drift comparison
//! and a `--no-default-features` build resolve the same names.

/// Parse a decimal or `0x` hex integer token, ignoring `_` separators.
pub(crate) fn int_token(expr: &str) -> Option<i64> {
    let expr = expr.trim();
    if let Some(hex) = expr.strip_prefix("0x").or_else(|| expr.strip_prefix("0X")) {
        return i64::try_from(u64::from_str_radix(hex, 16).ok()?).ok();
    }
    expr.replace('_', "").parse().ok()
}

/// Resolve common Bitcoin consensus constants
/// Returns the constant value if known, None otherwise
pub(crate) fn resolve_constant(name: &str) -> Option<i64> {
    match name {
        // Economic constants (from blvm-consensus/src/constants.rs)
        "INITIAL_SUBSIDY" => Some(50_0000_0000), // 50 BTC in satoshis
        "MAX_MONEY" => Some(2_100_000_000_000_000), // 21M BTC in satoshis
        "HALVING_INTERVAL" => Some(210_000),
        "LOCKTIME_THRESHOLD" => Some(500_000_000),
        "SATOSHIS_PER_BTC" => Some(100_000_000),

        // Transaction constants
        "MAX_BLOCK_SIZE" => Some(1_000_000), // 1MB
        "MAX_TX_SIZE" => Some(100_000),      // Conservative limit

        // Script constants
        "MAX_SCRIPT_SIZE" => Some(10_000),
        "MAX_STACK_SIZE" => Some(1000),

        // Script opcodes (blvm-primitives/src/opcodes.rs)
        "OP_1" => Some(0x51),  // 81
        "OP_16" => Some(0x60), // 96
        name if name.starts_with("OP_") => prim_opcode(name),

        // SegWit program lengths (blvm-primitives/src/constants.rs)
        "SEGWIT_P2WPKH_LENGTH" => Some(20),
        "SEGWIT_P2WSH_LENGTH" => Some(32),
        "TAPROOT_PROGRAM_LENGTH" => Some(32),

        // Taproot activation heights (blvm-primitives/src/constants.rs)
        "TAPROOT_ACTIVATION_MAINNET" => Some(709_632),
        "TAPROOT_ACTIVATION_TESTNET" => Some(2_011_968),
        "TAPROOT_ACTIVATION_REGTEST" => Some(0),

        // Read from the primitive source. Final sequence is `0xffffffff`.
        "SEQUENCE_FINAL" => {
            if crate::parser::spec_expr::consensus_workspace_present() {
                Some(crate::parser::spec_expr::impl_u64("SEQUENCE_FINAL") as i64)
            } else {
                None
            }
        }
        // Read from the primitive source. The clause uses the spec's R.
        "COINBASE_MATURITY" => {
            if crate::parser::spec_expr::consensus_workspace_present() {
                Some(crate::parser::spec_expr::impl_u64("COINBASE_MATURITY") as i64)
            } else {
                None
            }
        }

        _ => sourced_const_i64(name),
    }
}

/// A `const` in the opcode or consensus sources, including one alias such as `OP_1`.
pub(crate) fn sourced_const_i64(name: &str) -> Option<i64> {
    if let Some(value) = prim_opcode(name) {
        return Some(value);
    }
    if !crate::parser::spec_expr::consensus_workspace_present() {
        return None;
    }
    const FILES: &[&str] = &[
        "../blvm-primitives/src/constants.rs",
        "../blvm-consensus/src/constants.rs",
        "../blvm-consensus/src/taproot.rs",
    ];
    for rel in FILES {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(rel);
        let Ok(src) = std::fs::read_to_string(path) else {
            continue;
        };
        let needle = format!("const {name}:");
        let Some(at) = src.find(&needle) else {
            continue;
        };
        let rest = &src[at + needle.len()..];
        let Some(eq) = rest.find('=') else {
            continue;
        };
        let expr = rest[eq + 1..].split([';', '\n']).next()?.trim();
        if let Some(value) = int_token(expr) {
            return Some(value);
        }
        if expr
            .chars()
            .all(|ch| ch.is_ascii_alphanumeric() || ch == '_')
        {
            if let Some(value) = prim_opcode(expr) {
                return Some(value);
            }
        }
    }
    None
}

pub(crate) fn prim_opcode(name: &str) -> Option<i64> {
    if !crate::parser::spec_expr::consensus_workspace_present() {
        return None;
    }
    let path =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../blvm-primitives/src/opcodes.rs");
    let src = std::fs::read_to_string(path).ok()?;
    let needle = format!("const {name}:");
    let rest = src.get(src.find(&needle)? + needle.len()..)?;
    let expr = rest
        .get(rest.find('=')? + 1..)?
        .split([';', '\n'])
        .next()?
        .trim();
    let value = if let Some(hex) = expr.strip_prefix("0x").or_else(|| expr.strip_prefix("0X")) {
        u64::from_str_radix(hex, 16).ok()?
    } else {
        expr.parse().ok()?
    };
    i64::try_from(value).ok()
}
