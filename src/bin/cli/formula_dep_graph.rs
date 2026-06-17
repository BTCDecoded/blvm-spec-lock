//! **F_* → F_*** edges among **defined** formulas (**`Depends on`**), for **list-formulas** diagnostics.

use crate::parser::orange_paper::FormulaSpec;
use std::collections::HashMap;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Color {
    White,
    Gray,
    Black,
}

fn canonical_cycle_rotation(cycle: Vec<String>) -> Vec<String> {
    let n = cycle.len();
    if n <= 1 {
        return cycle;
    }
    (0..n)
        .map(|r| {
            cycle[r..]
                .iter()
                .chain(&cycle[..r])
                .cloned()
                .collect::<Vec<_>>()
        })
        .min()
        .unwrap_or(cycle)
}

/// Directed edges: **`F_u` → `F_v`** when **`u.depends_on`** contains **`v`** and both exist in **`formulas`**.
pub fn find_formula_id_cycles(formulas: &HashMap<String, FormulaSpec>) -> Vec<Vec<String>> {
    let mut color: HashMap<String, Color> =
        formulas.keys().map(|k| (k.clone(), Color::White)).collect();

    let mut stack: Vec<String> = Vec::new();
    let mut raw_cycles: Vec<Vec<String>> = Vec::new();

    for start in formulas.keys().cloned().collect::<Vec<_>>() {
        if color.get(&start).copied().unwrap_or(Color::White) == Color::White {
            visit_dfs(&start, formulas, &mut color, &mut stack, &mut raw_cycles);
        }
    }

    let mut out: Vec<Vec<String>> = raw_cycles
        .into_iter()
        .map(canonical_cycle_rotation)
        .collect();
    out.sort();
    out.dedup();
    out
}

fn visit_dfs(
    u: &str,
    formulas: &HashMap<String, FormulaSpec>,
    color: &mut HashMap<String, Color>,
    stack: &mut Vec<String>,
    cycles: &mut Vec<Vec<String>>,
) {
    match color.get(u).copied().unwrap_or(Color::White) {
        Color::Black => return,
        Color::Gray => return,
        Color::White => {}
    }

    *color.get_mut(u).expect("vertex in map") = Color::Gray;
    stack.push(u.to_string());

    if let Some(f) = formulas.get(u) {
        for dep in &f.depends_on {
            if !dep.starts_with("F_") {
                continue;
            }
            if !formulas.contains_key(dep) {
                continue;
            }
            let v = dep.as_str();
            match color.get(v).copied().unwrap_or(Color::White) {
                Color::White => {
                    visit_dfs(v, formulas, color, stack, cycles);
                }
                Color::Gray => {
                    if let Some(pos) = stack.iter().position(|x| x == v) {
                        let c: Vec<_> = stack[pos..].to_vec();
                        if !c.is_empty() {
                            cycles.push(c);
                        }
                    }
                }
                Color::Black => {}
            }
        }
    }

    stack.pop();
    *color.get_mut(u).expect("vertex in map") = Color::Black;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::orange_paper::FormulaSpec;
    use std::collections::HashMap;

    fn formula(id: &str, deps: &[&str]) -> FormulaSpec {
        FormulaSpec {
            id: id.to_string(),
            section: "1.0".into(),
            latex_body: "true".into(),
            raw_markdown: String::new(),
            depends_on: deps.iter().map(|d| (*d).to_string()).collect(),
        }
    }

    #[test]
    fn canonical_cycle_picks_lexicographic_rotation() {
        let c = vec!["F_B".into(), "F_C".into(), "F_A".into()];
        assert_eq!(canonical_cycle_rotation(c), vec!["F_A", "F_B", "F_C"]);
    }

    #[test]
    fn detects_simple_two_cycle() {
        let mut formulas = HashMap::new();
        formulas.insert("F_A".into(), formula("F_A", &["F_B"]));
        formulas.insert("F_B".into(), formula("F_B", &["F_A"]));
        let c = find_formula_id_cycles(&formulas);
        assert_eq!(c, vec![vec!["F_A".to_string(), "F_B".to_string()]]);
    }

    #[test]
    fn dag_has_no_cycles() {
        let mut formulas = HashMap::new();
        formulas.insert("F_Root".into(), formula("F_Root", &[]));
        formulas.insert("F_Leaf".into(), formula("F_Leaf", &["F_Root"]));
        assert!(find_formula_id_cycles(&formulas).is_empty());
    }
}
