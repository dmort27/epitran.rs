//! Defines WFSTs for implementing the rules in an Epitran processor file (as
//! parsed by the `ruleparse`` module).

use anyhow::Result;
// use itertools::{concat, Itertools};
use rustfst::algorithms::compose::compose;
use rustfst::algorithms::{concat::concat, rm_epsilon::rm_epsilon, tr_sort, union::union};
use rustfst::fst_impls::VectorFst;
use rustfst::fst_traits::{CoreFst, ExpandedFst, MutableFst};
use rustfst::prelude::*;
use rustfst::utils::{acceptor, transducer};
use rustfst::DrawingConfig;
use std::char;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::collections::HashSet;
use std::process::Command;
use std::sync::Arc;

use crate::ruleparse::{rule, rule_no_env, rule_with_comment, RegexAST, RewriteRule, Statement};

#[derive(Debug, Clone, Copy)]
enum LabelColor {
    White,
    Gray,
    Black,
}

#[derive(Debug, Clone, Copy)]
enum Action {
    Enter,
    Exit,
}

/// Return a symbol table based on a specified unicode range (our Σ).
pub fn unicode_symbol_table() -> Arc<SymbolTable> {
    let mut symt = SymbolTable::new();
    symt.add_symbol("#");
    (1..0xFFFF)
        .map(|i| char::from_u32(i))
        .filter_map(|i| i)
        .filter(|&c| c != '#')
        .for_each(|i| {
            let _ = symt.add_symbol(i);
        });
    Arc::new(symt)
}

/// Compile an Epitran script as a WFST.
///
/// # Arguments
///
/// * statements - a vector of `Statement`s
///
/// # Returns
///
/// An WFST corresponding to the script
pub fn compile_script(statements: Vec<Statement>) -> Result<VectorFst<TropicalWeight>> {
    let symt = unicode_symbol_table();
    let mut fst = universal_acceptor(symt.clone())?;
    let mut macros: HashMap<String, RegexAST> = HashMap::new();
    for statement in statements {
        match statement {
            Statement::Comment => (),
            Statement::MacroDef((mac, def)) => {
                macros.insert(mac, def).unwrap();
                ()
            }
            Statement::Rule(rule) => {
                let fst2 = rule_fst(symt.clone(), &macros, rule)?;
                fst = compose(fst.clone(), fst2)?;
                ()
            }
        }
    }
    Ok(fst)
}

/// Returns a WFST representing a rule.
///
/// # Arguments
///
/// * symt - A symbol table
/// * macros - macros
/// * rule - A rewrite rule
///
/// # Returns
///
/// A WFST corresponding to a rewrite rule
fn rule_fst(
    symt: Arc<SymbolTable>,
    macros: &HashMap<String, RegexAST>,
    rule: RewriteRule,
) -> Result<VectorFst<TropicalWeight>> {
    println!("--- rule={:?}", rule);

    let mut fst = VectorFst::<TropicalWeight>::new();
    fst.set_input_symbols(symt.clone());
    fst.set_output_symbols(symt.clone());
    let q0 = fst.add_state();
    fst.set_start(0)?;
    let q1 = fst.add_state();
    fst.set_final(q1, 0.0)?;
    fst.emplace_tr(q0, 0, 0, 0.0, q1)?;

    // Compute core (L[S->T]R)

    let src_fst: VectorFst<TropicalWeight> =
        output_to_epsilons(node_fst(symt.clone(), macros, rule.source).unwrap());
    let tgt_fst: VectorFst<TropicalWeight> =
        input_to_epsilons(node_fst(symt.clone(), macros, rule.target).unwrap());
    let left_fst: VectorFst<TropicalWeight> = node_fst(symt.clone(), macros, rule.left).unwrap();
    let right_fst: VectorFst<TropicalWeight> = node_fst(symt.clone(), macros, rule.right).unwrap();
    let univ_acc: VectorFst<TropicalWeight> = universal_acceptor(symt.clone()).unwrap();

    println!("--- left_fst={:?}", left_fst);
    println!("--- right_fst={:?}", right_fst);

    let _ = concat(&mut fst, &left_fst);
    let _ = concat(&mut fst, &src_fst);
    let _ = concat(&mut fst, &tgt_fst);
    let _ = concat(&mut fst, &right_fst);
    let _ = concat(&mut fst, &univ_acc);

    let first_state: u32 = 0;
    let last_state: u32 = (fst.num_states() - 1) as u32;

    let _ = fst.emplace_tr(last_state, 0, 0, 0.0, first_state);
    let _ = fst.emplace_tr(first_state, 0, 0, 10.0, last_state);
    let _ = fst.set_final(last_state, 0.0);

    let mut root: VectorFst<TropicalWeight> = universal_acceptor(symt.clone()).unwrap();

    let _ = concat(&mut root, &fst);

    let _ = root.set_start(0);

    let _ = root.draw(
        "root_fst.dot",
        &DrawingConfig {
            vertical: false,
            size: (Some((10.0, 10.0))),
            title: ("Source FST before adding root".to_string()),
            portrait: (true),
            ranksep: (None),
            nodesep: (None),
            fontsize: (12),
            acceptor: (false),
            show_weight_one: (true),
            print_weight: (true),
        },
    );
    Command::new("dot")
        .args(["-Tpdf", "-oroot_fst.pdf", "root_fst.dot"])
        .spawn()
        .expect("Could not run dot on dot file \"fst.dot\".");

    Command::new("open")
        .arg("root_fst.pdf")
        .spawn()
        .expect("Could not open \"root_fst.pdf\".");

    let _ = rm_epsilon(&mut root);

    Ok(root)
}

fn output_to_epsilons(fst: VectorFst<TropicalWeight>) -> VectorFst<TropicalWeight> {
    let mut fst2 = fst.clone();
    for state in fst2.states_iter() {
        let trs: Vec<Tr<TropicalWeight>> = fst2.pop_trs(state).unwrap_or_default().clone();
        for tr in trs.iter() {
            fst2.emplace_tr(state, tr.ilabel, 0, tr.weight, tr.nextstate)
                .unwrap();
        }
    }
    fst2
}

fn input_to_epsilons(fst: VectorFst<TropicalWeight>) -> VectorFst<TropicalWeight> {
    let mut fst2 = fst.clone();
    // println!("In input_to_epsilons, fst2.num_states={:?}", fst2.num_states());
    // println!("In input_to_epsilons, fst2.start()={:?}", fst2.start());
    for state in fst2.states_iter() {
        let trs: Vec<Tr<TropicalWeight>> = fst2.pop_trs(state).unwrap_or_default().clone();
        for tr in trs.iter() {
            fst2.emplace_tr(state, 0, tr.olabel, tr.weight, tr.nextstate)
                .unwrap();
        }
    }
    fst2
}

fn add_univ_acc_to_right(
    symt: Arc<SymbolTable>,
    mut fst: VectorFst<TropicalWeight>,
) -> VectorFst<TropicalWeight> {
    let fst2: VectorFst<TropicalWeight> = universal_acceptor(symt).unwrap();
    let _ = concat(&mut fst, &fst2);
    let _ = rm_epsilon(&mut fst);
    fst
}

fn add_univ_acc_to_left(
    symt: Arc<SymbolTable>,
    fst: VectorFst<TropicalWeight>,
) -> VectorFst<TropicalWeight> {
    let mut fst2: VectorFst<TropicalWeight> = universal_acceptor(symt).unwrap();
    let _ = concat(&mut fst2, &fst);
    let _ = rm_epsilon(&mut fst2);
    fst2
}

/// Return an fst that will accept any string s ∈ Σ*
pub fn universal_acceptor(symt: Arc<SymbolTable>) -> Result<VectorFst<TropicalWeight>> {
    let mut fst = VectorFst::<TropicalWeight>::new();
    fst.set_input_symbols(symt.clone());
    fst.set_output_symbols(symt.clone());
    let q0 = fst.add_state();
    fst.set_start(q0)?;
    fst.set_final(q0, 0.0)?;
    for (label, symbol) in symt.iter().filter(|(l, s)| *s != "<eps>".to_string()) {
        fst.add_tr(q0, Tr::new(label, label, 10.0, q0))?;
    }
    Ok(fst)
}

fn node_fst(
    symt: Arc<SymbolTable>,
    macros: &HashMap<String, RegexAST>,
    node: RegexAST,
) -> Result<VectorFst<TropicalWeight>> {
    let mut fst: VectorFst<TropicalWeight> = fst![0 => 0];
    fst.set_input_symbols(symt.clone());
    fst.set_output_symbols(symt.clone());
    // let last_final_state = 1;

    match node {
        RegexAST::Epsilon => (),
        RegexAST::Group(nodes) => {
            for node2 in nodes {
                let fst2 = node_fst(symt.clone(), macros, node2).unwrap();
                let _ = concat(&mut fst, &fst2);
            }
        }
        RegexAST::Boundary => {
            let bnd_label = symt.get_label("#>").unwrap();
            let fst2: VectorFst<TropicalWeight> = fst![bnd_label];
            let _ = concat(&mut fst, &fst2);
        }
        RegexAST::Char(c) => {
            let label = symt
                .get_label(c.to_string())
                .expect("Could not find label for symbol {c.to_string()}");
            let fst2: VectorFst<TropicalWeight> = fst![label => label; 0.0];
            concat(&mut fst, &fst2)?;
            // println!("char fst={:#?}", fst);
            // rm_epsilon(&mut fst)?;
            // let last_final_state = fst.final_states_iter().max().unwrap();
        }
        RegexAST::Disjunction(nodes) => {
            let mut fst2: VectorFst<TropicalWeight> = VectorFst::<TropicalWeight>::new();
            let q0 = fst.add_state();
            let q1 = fst.add_state();
            let _ = fst.emplace_tr(q0, 0, 0, TropicalWeight::zero(), q1);
            for node in nodes {
                let case_fst = node_fst(symt.clone(), macros, node)?;
                let _ = union(&mut fst2, &case_fst);
            }
            let _ = concat(&mut fst, &fst2);
        }
        RegexAST::Class(nodes) => {
            let mut fst2: VectorFst<TropicalWeight> = VectorFst::<TropicalWeight>::new();
            let q0 = fst.add_state();
            let q1 = fst.add_state();
            let _ = fst.emplace_tr(q0, 0, 0, TropicalWeight::zero(), q1);
            for node in nodes {
                let case_fst = node_fst(symt.clone(), macros, node)?;
                let _ = union(&mut fst2, &case_fst);
            }
            let _ = concat(&mut fst, &fst2);
        }
        _ => (),
    }

    let _ = rm_epsilon(&mut fst);

    Ok(fst)
}

// pub fn universal_acceptor(symt: Arc<SymbolTable>) -> Result<VectorFst<TropicalWeight>> {
//     let mut fst: VectorFst<TropicalWeight> = fst![0 => 0];
//     fst.emplace_tr(0, 0, 0, 0.0, 1)?;
//     for (label, _) in symt.iter().filter(|(_, s)| *s != "#") {
//         let fst2: VectorFst<TropicalWeight> = fst![label => label];
//         let _ = union(&mut fst, &fst2);
//     }
//     Ok(fst)
// }

/// Returns true if the wFST has a cycle. Otherwise, it returns false.
pub fn is_cyclic(fst: VectorFst<TropicalWeight>) -> bool {
    let fst = fst.clone();
    let mut stack: Vec<(Action, StateId)> = Vec::new();
    // println!("num states={}", fst.num_states());
    // println!("start state={:?}", fst.start());
    match fst.start() {
        Some(s) => stack.push((Action::Enter, s)),
        _ => panic!("wFST lacks a start state. Aborting."),
    }
    let mut state = vec![LabelColor::White; fst.num_states()];
    while !stack.is_empty() {
        match stack.pop() {
            Some((Action::Exit, v)) => state[v as usize] = LabelColor::Black,
            Some((Action::Enter, v)) => {
                state[v as usize] = LabelColor::Gray;
                stack.push((Action::Exit, v));
                for tr in fst
                    .get_trs(v)
                    .unwrap_or_else(|e| panic!("State {} not present in wFST: {}", v, e))
                    .iter()
                {
                    let n = tr.nextstate;
                    match state[n as usize] {
                        LabelColor::Gray => return true,
                        LabelColor::White => stack.push((Action::Enter, n)),
                        _ => (),
                    }
                }
            }
            _ => (),
        }
    }
    false
}

// Returns the start state of an FST. Surely, there is a better way of doing this.
fn _get_start(fst: VectorFst<TropicalWeight>) -> Result<StateId> {
    for q in fst.states_iter() {
        if fst.is_start(q) {
            return Ok(q);
        }
    }
    panic!("FST has no start state!")
}

/// Convert a string to a linear automaton
pub fn string_to_linear_automaton(symt: Arc<SymbolTable>, s: &str) -> VectorFst<TropicalWeight> {
    let symt = symt.clone();
    let labels: Vec<u32> = s
        .chars()
        .filter_map(|c| symt.get_label(c.to_string()))
        .collect();
    acceptor(&labels, TropicalWeight::one())
}

/// Apply a wFST to a string input
///
/// # Examples
///
/// Basic usage:
/// ```
/// # use std::sync::Arc;
/// # use rustfst::prelude::*;
/// # use rustfst::utils::transducer;
/// # use parserule::rulefst::{apply_fst_to_string};
/// let symt = Arc::new(symt!["a", "b", "c", "d"]);
/// let fst = fst![1, 2 => 3, 4];
/// let input = "ab".to_string();
/// let expected_output = fst![1, 2 => 3, 4];
/// assert_eq!(apply_fst_to_string(symt, fst, input).unwrap(), expected_output);
/// ```
pub fn apply_fst_to_string(
    symt: Arc<SymbolTable>,
    mut fst: VectorFst<TropicalWeight>,
    input: String,
) -> Result<VectorFst<TropicalWeight>> {
    let symt: Arc<SymbolTable> = symt.clone();
    let mut acc = string_to_linear_automaton(symt, &input);
    acc.set_symts_from_fst(&fst);
    // println!("acc={:?}", acc);
    // println!("fst={:?}", fst);

    tr_sort(&mut acc, OLabelCompare {});
    tr_sort(&mut fst, ILabelCompare {});

    let composed_fst: VectorFst<TropicalWeight> = compose(acc, fst).unwrap();
    // println!("composed_fst={:?}", composed_fst);

    let _ = composed_fst.draw(
        "composed_fst.dot",
        &DrawingConfig {
            vertical: false,
            size: (Some((5.0, 5.0))),
            title: ("Simple Rule".to_string()),
            portrait: (true),
            ranksep: (None),
            nodesep: (None),
            fontsize: (12),
            acceptor: (false),
            show_weight_one: (true),
            print_weight: (true),
        },
    );

    Ok(composed_fst)
}

/// Decode each of the paths through the output labels of a wFST as a vector of (weight, string) tuples
///
/// # Examples
///
/// Basic usage
///
/// ```
/// # use std::sync::Arc;
/// # use parserule::rulefst::{decode_paths_through_fst};
/// # use rustfst::fst_impls::VectorFst;
/// # use rustfst::prelude::*;
/// # use rustfst::utils::{acceptor, transducer};
/// let symt: Arc<SymbolTable> = Arc::new(symt!["a", "b", "c", "d"]);
/// let mut fst: VectorFst<TropicalWeight> = fst![1, 2, 1 => 3, 4, 3; 0.1];
/// fst.set_input_symbols(symt.clone());
/// fst.set_output_symbols(symt.clone());
/// assert_eq!(decode_paths_through_fst(symt, fst), vec![(TropicalWeight::from(0.1), "cdc".to_string())]);
/// ```

pub fn decode_paths_through_fst(
    symt: Arc<SymbolTable>,
    fst: VectorFst<TropicalWeight>,
) -> Vec<(TropicalWeight, String)> {
    let symt: Arc<SymbolTable> = symt.clone();
    let paths: Vec<_> = fst.string_paths_iter().unwrap().collect();
    let mut outputs: Vec<(TropicalWeight, String)> = paths
        .iter()
        .map(|p| (*p.weight(), decode_path(symt.clone(), p.clone())))
        .collect();
    outputs.sort_unstable_by(|(w1, _), (w2, _)| w1.partial_cmp(w2).unwrap());
    println!("\n*** outputs={:?}", outputs);
    outputs
}

fn decode_path(symt: Arc<SymbolTable>, path: StringPath<TropicalWeight>) -> String {
    let symt = symt.clone();
    path.olabels()
        .iter()
        .map(|&l| symt.get_symbol(l).unwrap())
        .map(|s| s.to_string())
        .collect::<Vec<String>>()
        .join("")
}

/// Apply a wFST to a string, yielding a string
///
/// # Examples
///
/// ```
/// # use std::sync::Arc;
/// # use parserule::rulefst::test_apply;
/// # use rustfst::fst_impls::VectorFst;
/// # use rustfst::prelude::*;
/// # use rustfst::utils::{acceptor, transducer};
/// let symt: Arc<SymbolTable> = Arc::new(symt!["a", "b", "c", "d"]);
/// let mut fst: VectorFst<TropicalWeight> = fst![1, 2, 1 => 3, 4, 3; 0.1];
/// fst.set_input_symbols(symt.clone());
/// fst.set_output_symbols(symt.clone());
/// let input = "aba".to_string();
/// assert_eq!(test_apply(symt, fst, input), "cdc".to_string());
/// ```
pub fn test_apply(symt: Arc<SymbolTable>, fst: VectorFst<TropicalWeight>, input: String) -> String {
    let composed_fst = apply_fst_to_string(symt.clone(), fst, input).unwrap();
    let mut outputs = decode_paths_through_fst(symt.clone(), composed_fst);
    if let Some((best_weight, best_string)) = outputs.first() {
        best_string.clone()
    } else {
        "".to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_char1() {
        let symt = unicode_symbol_table();
        // let symt = Arc::new(symt!["#", "a", "b", "c"]);
        let macros = HashMap::new();
        let fst = node_fst(symt, &macros, RegexAST::Char('a')).unwrap();
        let paths: Vec<_> = fst.paths_iter().collect();
        assert_eq!(paths.len(), 1);
    }

    #[test]
    fn test_simple_rule() {
        // let symt = unicode_symbol_table();
        let symt = Arc::new(symt!["#", "a", "e"]);
        let macros: &HashMap<String, RegexAST> = &HashMap::new();
        let (_, rewrite_rule) = rule_no_env("a -> e").unwrap();
        // println!("rewrite_rule = {:?}", rewrite_rule);
        let fst: VectorFst<TropicalWeight> =
            rule_fst(symt.clone(), macros, rewrite_rule).expect("Something");
        // println!("fst.num_states()={:?}", fst.num_states());
        // println!("fst={:#?}", fst);
        // let _ = fst.draw(
        //     "simple_rule.dot",
        //     &DrawingConfig {
        //         vertical: false,
        //         size: (Some((5.0, 5.0))),
        //         title: ("Simple Rule".to_string()),
        //         portrait: (false),
        //         ranksep: (None),
        //         nodesep: (None),
        //         fontsize: (12),
        //         acceptor: (false),
        //         show_weight_one: (true),
        //         print_weight: (true),
        //     },
        // );
        assert_eq!(test_apply(symt, fst, "#a#".to_string()), "#e#".to_string());
    }

    #[test]
    fn test_multiple_application() {
        // let symt = unicode_symbol_table();
        let symt = Arc::new(symt!["#", "a", "e"]);
        let macros: &HashMap<String, RegexAST> = &HashMap::new();
        let (_, rewrite_rule) = rule_no_env("a -> e").unwrap();
        // println!("rewrite_rule = {:?}", rewrite_rule);
        let fst: VectorFst<TropicalWeight> =
            rule_fst(symt.clone(), macros, rewrite_rule).expect("Something");
        // println!("fst.num_states()={:?}", fst.num_states());
        // println!("fst={:?}", fst);
        assert_eq!(
            test_apply(symt, fst, "#aa#".to_string()),
            "#ee#".to_string()
        );
    }

    #[test]
    fn test_rule_with_context() {
        // let symt = unicode_symbol_table();
        let symt = Arc::new(symt!["#", "a", "b", "p"]);
        let macros: &HashMap<String, RegexAST> = &HashMap::new();
        let (_, rewrite_rule) = rule("p -> b / a _ a").unwrap();
        // println!("rewrite_rule = {:?}", rewrite_rule);
        let fst: VectorFst<TropicalWeight> =
            rule_fst(symt.clone(), macros, rewrite_rule).expect("Something");
        // println!("fst.num_states()={:?}", fst.num_states());
        // println!("fst={:?}", fst);
        assert_eq!(
            test_apply(symt, fst, "#apa#".to_string()),
            "#aba#".to_string()
        );
    }

    #[test]
    fn test_multiple_application_with_context() {
        // let symt = unicode_symbol_table();
        let symt = Arc::new(symt!["#", "a", "b", "p"]);
        let macros: &HashMap<String, RegexAST> = &HashMap::new();
        let (_, rewrite_rule) = rule("p -> b / a _ a").unwrap();
        // println!("rewrite_rule = {:?}", rewrite_rule);
        let fst: VectorFst<TropicalWeight> =
            rule_fst(symt.clone(), macros, rewrite_rule).expect("Something");
        // println!("fst.num_states()={:?}", fst.num_states());
        // println!("fst={:?}", fst);
        assert_eq!(
            test_apply(symt, fst, "#apaapa#".to_string()),
            "#abaaba#".to_string()
        );
    }

    #[test]
    fn test_rule_disjunction() {
        let symt = Arc::new(symt!["#", "a", "b", "p", "i"]);
        let macros: &HashMap<String, RegexAST> = &HashMap::new();
        let (_, rewrite_rule) = rule("(p|b) -> i / a _ ").unwrap();
        let fst: VectorFst<TropicalWeight> =
            rule_fst(symt.clone(), macros, rewrite_rule).expect("Something");
        assert_eq!(
            test_apply(symt, fst, "#apab#".to_string()),
            "#aiai#".to_string()
        );
    }

    #[test]
    fn test_rule_class() {
        let symt = Arc::new(symt!["#", "a", "b", "p", "i"]);
        let macros: &HashMap<String, RegexAST> = &HashMap::new();
        let (_, rewrite_rule) = rule("a -> i / [pb] _ ").unwrap();
        let fst: VectorFst<TropicalWeight> =
            rule_fst(symt.clone(), macros, rewrite_rule).expect("Something");
        assert_eq!(
            test_apply(symt, fst, "#pabaaa#".to_string()),
            "#pibiaa#".to_string()
        );
    }

    #[test]
    fn test_concat() {
        let mut fst1 = VectorFst::<TropicalWeight>::new();
        let q0 = fst1.add_state();
        let _ = fst1.set_start(q0);
        let q1 = fst1.add_state();
        let _ = fst1.set_final(q1, 0.0);
        let _ = fst1.emplace_tr(q0, 0, 0, 0.0, q1);
        let fst2: VectorFst<TropicalWeight> = fst![1 => 2; 0.0];
        let _ = concat(&mut fst1, &fst2);
        assert_eq!(fst1, fst![0, 0, 1 => 0, 0, 2; 0.0])
    }

    #[test]
    fn test_rm_epsilon() {
        let mut fst1 = VectorFst::<TropicalWeight>::new();
        let q0 = fst1.add_state();
        let _ = fst1.set_start(q0);
        let q1 = fst1.add_state();
        let _ = fst1.set_final(q1, 0.0);
        let _ = fst1.emplace_tr(q0, 0, 0, 0.0, q1);
        let fst2: VectorFst<TropicalWeight> = fst![1, 3 => 2, 4; 0.0];
        let _ = concat(&mut fst1, &fst2);
        let _ = rm_epsilon(&mut fst1);
        assert_eq!(fst1, fst![1, 3 => 2, 4; 0.0])
    }

    #[test]
    fn test_node_fst() {
        let symt = Arc::new(symt!["a", "b", "c", "d"]);
        let macros: HashMap<String, RegexAST> = HashMap::new();
        let input = RegexAST::Char('a');
        let mut fst: VectorFst<TropicalWeight> = fst![1 => 1; 0.0];
        fst.set_input_symbols(symt.clone());
        fst.set_output_symbols(symt.clone());
        assert_eq!(node_fst(symt, &macros, input).unwrap(), fst);
    }
}
