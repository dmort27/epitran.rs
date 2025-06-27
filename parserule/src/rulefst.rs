//! Defines WFSTs for implementing the rules in an Epitran processor file (as
//! parsed by the `ruleparse`` module).

// cSpell:disable

use anyhow::Result;
use rustfst::algorithms::compose::compose;
use rustfst::algorithms::{
    add_super_final_state, closure::closure, concat::concat, minimize_with_config, MinimizeConfig, push_weights,
    rm_epsilon::rm_epsilon, tr_sort, union::union, ReweightType,
    determinize::{determinize_with_config, DeterminizeConfig, DeterminizeType},
};
use rustfst::fst_impls::VectorFst;
use rustfst::fst_traits::{CoreFst, ExpandedFst, MutableFst};
use rustfst::prelude::*;
use rustfst::utils::{acceptor, transducer};
// use rustfst::DrawingConfig;
use std::char;
use std::cmp::Ordering;
use std::collections::HashMap;
// use std::process::Command;
use std::sync::Arc;

use crate::ruleparse::{RegexAST, RewriteRule, Statement};

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

// fn is_cyclic(fst: &VectorFst<TropicalWeight>) -> bool {
//     top_sort(&mut fst.clone()).is_err()
// }

/// Return a symbol table based on a specified unicode range (our Σ).
pub fn unicode_symbol_table() -> Arc<SymbolTable> {
    let mut symt = SymbolTable::new();
    symt.add_symbol("#");
    (1..0xFFFF)
        .map(char::from_u32)
        .flatten()
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
pub fn compile_script(
    symt: Arc<SymbolTable>,
    statements: Vec<Statement>,
) -> Result<VectorFst<TropicalWeight>> {
    // let symt = unicode_symbol_table();
    let mut fst = universal_acceptor(symt.clone())?;
    let mut macros: HashMap<String, RegexAST> = HashMap::new();
    for statement in statements {
        match statement {
            Statement::Comment => (),
            Statement::MacroDef((mac, def)) => {
                macros.insert(mac, def).unwrap_or(RegexAST::Epsilon);
            }
            Statement::Rule(rule) => {
                let mut fst2 = rule_fst(symt.clone(), &macros, rule.clone())
                    .inspect_err(|e| {
                        println!(
                            "Failed to build rule {:?} having macros {:?}: {}",
                            rule, macros, e
                        )
                    })
                    .unwrap_or(VectorFst::<TropicalWeight>::new());
                tr_sort(&mut fst, OLabelCompare {});
                tr_sort(&mut fst2, ILabelCompare {});
                fst = compose(fst.clone(), fst2)?;
                rm_epsilon(&mut fst).unwrap();
                // let mut fst: VectorFst<TropicalWeight> = determinize_with_config(
                //     &fst,
                //     DeterminizeConfig { 
                //         delta: 1e-6,
                //         det_type: DeterminizeType::DeterminizeFunctional
                //     })?;
                push_weights(&mut fst, ReweightType::ReweightToInitial)?;
                minimize_with_config(&mut fst, MinimizeConfig { delta: 1e-7, allow_nondet: (true) })?;
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
    fst.set_final(q1, TropicalWeight::one())?;
    fst.emplace_tr(q0, 0, 0, TropicalWeight::one(), q1)?;

    // Compute core (L[S->T]R)

    let src_fst: VectorFst<TropicalWeight> =
        output_to_epsilons(node_fst(symt.clone(), macros, rule.source)?);
    let tgt_fst: VectorFst<TropicalWeight> =
        input_to_epsilons(node_fst(symt.clone(), macros, rule.target)?);
    let left_fst: VectorFst<TropicalWeight> = node_fst(symt.clone(), macros, rule.left)?;
    let right_fst: VectorFst<TropicalWeight> = node_fst(symt.clone(), macros, rule.right)?;
    let univ_acc: VectorFst<TropicalWeight> = universal_acceptor(symt.clone())?;

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

    let mut root: VectorFst<TropicalWeight> = universal_acceptor(symt.clone())?;

    let _ = concat(&mut root, &fst);

    let _ = root.set_start(0);

    // let _ = root.draw(
    //     "root_fst.dot",
    //     &DrawingConfig {
    //         vertical: false,
    //         size: (Some((10.0, 10.0))),
    //         title: ("Source FST before adding root".to_string()),
    //         portrait: (true),
    //         ranksep: (None),
    //         nodesep: (None),
    //         fontsize: (12),
    //         acceptor: (false),
    //         show_weight_one: (true),
    //         print_weight: (true),
    //     },
    // );
    // Command::new("dot")
    //     .args(["-Tpdf", "-oroot_fst.pdf", "root_fst.dot"])
    //     .spawn()
    //     .expect("Could not run dot on dot file \"fst.dot\".");

    // Command::new("open")
    //     .arg("root_fst.pdf")
    //     .spawn()
    //     .expect("Could not open \"root_fst.pdf\".");

    rm_epsilon(&mut root).unwrap_or_else(|e| println!("{e}: Cannot remove epsilons."));
    minimize_with_config(&mut root, MinimizeConfig { delta: 1e-7, allow_nondet: (true) }).unwrap_or_else(|e| println!("{e}: Could not minimize wFST. Proceeding"));

    Ok(root)
}

fn output_to_epsilons(fst: VectorFst<TropicalWeight>) -> VectorFst<TropicalWeight> {
    let mut fst2 = fst.clone();
    for state in fst2.states_iter() {
        let trs: Vec<Tr<TropicalWeight>> = fst2.pop_trs(state).unwrap_or_default().clone();
        for tr in trs.iter() {
            fst2.emplace_tr(state, tr.ilabel, 0, tr.weight, tr.nextstate)
                .inspect_err(|e| {
                    println!(
                        "{e}: Cannot emplace transition from {state} to {}.",
                        tr.nextstate
                    )
                })
                .unwrap_or(());
        }
    }
    fst2
}

fn input_to_epsilons(fst: VectorFst<TropicalWeight>) -> VectorFst<TropicalWeight> {
    let mut fst2 = fst.clone();
    for state in fst2.states_iter() {
        let trs: Vec<Tr<TropicalWeight>> = fst2.pop_trs(state).unwrap_or_default().clone();
        for tr in trs.iter() {
            fst2.emplace_tr(state, 0, tr.olabel, tr.weight, tr.nextstate)
                .inspect_err(|e| {
                    println!(
                        "{e}: Cannot emplace transition from {state} to {}.",
                        tr.nextstate
                    )
                })
                .unwrap_or(());
        }
    }
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
    for (label, _) in symt.iter().filter(|(_, s)| *s != "<eps>") {
        fst.add_tr(q0, Tr::new(label, label, 10.0, q0))?;
    }
    Ok(fst)
}

/// Interpret an RegexAST node as a wFST
fn node_fst(
    symt: Arc<SymbolTable>,
    macros: &HashMap<String, RegexAST>,
    node: RegexAST,
) -> Result<VectorFst<TropicalWeight>> {
    let mut fst: VectorFst<TropicalWeight> = fst![0 => 0];
    fst.set_input_symbols(symt.clone());
    fst.set_output_symbols(symt.clone());

    match node {
        // Interpret an Epsilon node (leaves `fst` unchanged, since it already includes an epsilon transition).
        RegexAST::Epsilon => (),

        // Interpret a group (a sequence of nodes)
        RegexAST::Group(nodes) => {
            for node2 in nodes {
                let fst2 = node_fst(symt.clone(), macros, node2)?;
                let _ = concat(&mut fst, &fst2);
            }
        }

        // Interpret a boundary symbol.
        RegexAST::Boundary => {
            let bnd_label = symt.get_label("#").unwrap_or(1);
            let fst2: VectorFst<TropicalWeight> = fst![bnd_label];
            let _ = concat(&mut fst, &fst2);
        }

        // Interpret a character.
        RegexAST::Char(c) => {
            let label = symt.get_label(c.to_string()).unwrap_or(0);
            let fst2: VectorFst<TropicalWeight> = fst![label => label; 0.0];
            concat(&mut fst, &fst2)?;
        }

        // Interpret a disjunction (a set of mutually-exclusive sequences).
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

        // Interpret a character class (a set of characters any of which match the expression).
        RegexAST::Class(class) => {
            let mut fst2: VectorFst<TropicalWeight> = VectorFst::<TropicalWeight>::new();
            let q0 = fst2.add_state();
            let _ = fst2.set_start(q0);
            let q1: u32 = fst2.add_state();
            let _ = fst2.set_final(q1, 0.0);
            let _ = fst2.emplace_tr(q1, 0, 0, TropicalWeight::zero(), q1);
            class
                .iter()
                .map(|s| {
                    symt.get_label(s).unwrap_or_else(|| {
                        println!("Symbol {s} is not in symbol table.");
                        0
                    })
                })
                .for_each(|l| {
                    fst2.emplace_tr(q0, l, l, TropicalWeight::one(), q1)
                        .unwrap();
                });
            let _ = concat::concat(&mut fst, &fst2);
        }

        // Interpret the complement of a character class (a set of characters none of which match the expression).
        RegexAST::ClassComplement(mut class) => {
            let mut fst2: VectorFst<TropicalWeight> = VectorFst::<TropicalWeight>::new();
            let q0 = fst2.add_state();
            let _ = fst2.set_start(q0);
            let q1: u32 = fst2.add_state();
            let _ = fst2.set_final(q1, 0.0);
            let _ = class.insert("#".to_string());
            let _ = class.insert("<eps>".to_string());
            symt.iter()
                .filter(|(_, s)| !class.contains(*s))
                .for_each(|(l, _)| {
                    fst2.emplace_tr(q0, l, l, TropicalWeight::one(), q1)
                        .unwrap();
                });
            let _ = concat::concat(&mut fst, &fst2);
        }

        // Interpret a Kleene star.
        RegexAST::Star(node) => {
            let mut fst2 = node_fst(symt, macros, *node)?;
            closure(&mut fst2, closure::ClosureType::ClosureStar);
            concat(&mut fst, &fst2)
                .unwrap_or_else(|e| println!("{e}: Couldn't concatenate wFSTs."));
        }

        // Interpret a Kleene plus.
        RegexAST::Plus(node) => {
            let mut fst2 = node_fst(symt, macros, *node)?;
            closure(&mut fst2, closure::ClosureType::ClosurePlus);
            concat(&mut fst, &fst2)
                .unwrap_or_else(|e| println!("{e}: Couldn't concatenate wFSTs."));
        }

        // Interpret an optional node
        RegexAST::Option(node) => {
            let mut fst2: VectorFst<TropicalWeight> = node_fst(symt, macros, *node)?;
            let start_state = fst2.start().unwrap_or_else(|| {
                println!("wFST does not have start state.");
                0
            });
            let final_state = add_super_final_state(&mut fst2);
            fst2.emplace_tr(start_state, 0, 0, 0.0, final_state)
                .unwrap_or_else(|e| println!("{e}: Could not add transition."));
            concat(&mut fst, &fst2)
                .unwrap_or_else(|e| println!("{e}: Could not concatenate wFSTs."));
        }

        // Interpret a macro
        RegexAST::Macro(macro_key) => {
            let macro_node = macros.get(&macro_key).unwrap_or_else(|| {
                println!("Macro {macro_key} not defined!");
                &RegexAST::Epsilon
            });
            let fst2 = node_fst(symt, macros, macro_node.clone())?;
            concat(&mut fst, &fst2)
                .unwrap_or_else(|e| println!("{e}: Could not concatenate wFSTs."));
        }

        RegexAST::Comment => (),
    }

    let _ = rm_epsilon(&mut fst);
    let mut fst = determinize_with_config(
        &fst,
        DeterminizeConfig { 
            delta: 1e-6,
            det_type: DeterminizeType::DeterminizeFunctional
        })?;
    push_weights(&mut fst, ReweightType::ReweightToInitial)?;
    minimize_with_config(&mut fst, MinimizeConfig { delta: 1e-7, allow_nondet: (true) })?;

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
pub fn is_cyclic(fst: &VectorFst<TropicalWeight>) -> bool {
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

    let composed_fst: VectorFst<TropicalWeight> = compose(acc, fst)?;
    // println!("composed_fst={:?}", composed_fst);

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
    mut fst: VectorFst<TropicalWeight>,
) -> Vec<(TropicalWeight, String)> {
    let symt: Arc<SymbolTable> = symt.clone();
    fst.set_input_symbols(symt.clone());
    fst.set_output_symbols(symt.clone());
    let paths: Vec<_> = fst
        .string_paths_iter()
        .inspect_err(|e| println!("{e}: error iterating over paths."))
        .unwrap()
        .collect();
    let mut outputs: Vec<(TropicalWeight, String)> = paths
        .iter()
        .map(|p| (*p.weight(), decode_path(symt.clone(), p.clone())))
        .collect();
    outputs.sort_unstable_by(|(w1, _), (w2, _)| w1.partial_cmp(w2).unwrap_or(Ordering::Equal));
    println!("\n*** outputs={:?}", outputs);
    outputs
}

fn decode_path(symt: Arc<SymbolTable>, path: StringPath<TropicalWeight>) -> String {
    let symt = symt.clone();
    path.olabels()
        .iter()
        .map(|&l| symt.get_symbol(l).unwrap_or(""))
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
/// # use parserule::rulefst::apply_fst;
/// # use rustfst::fst_impls::VectorFst;
/// # use rustfst::prelude::*;
/// # use rustfst::utils::{acceptor, transducer};
/// let symt: Arc<SymbolTable> = Arc::new(symt!["a", "b", "c", "d"]);
/// let mut fst: VectorFst<TropicalWeight> = fst![1, 2, 1 => 3, 4, 3; 0.1];
/// fst.set_input_symbols(symt.clone());
/// fst.set_output_symbols(symt.clone());
/// let input = "aba".to_string();
/// assert_eq!(apply_fst(symt, fst, input), "cdc".to_string());
/// ```
pub fn apply_fst(symt: Arc<SymbolTable>, fst: VectorFst<TropicalWeight>, input: String) -> String {
    let composed_fst = apply_fst_to_string(symt.clone(), fst.clone(), input.clone())
        .unwrap_or_else(|e| {
            println!("{e}: Couldn't apply wFST {:?} to string {:?}.", fst, input);
            VectorFst::<TropicalWeight>::new()
        });
    if is_cyclic(&composed_fst) {
        panic!("Transducer resulting from applying composing input string was cyclic.")
    }
    let outputs = decode_paths_through_fst(symt.clone(), composed_fst);
    if let Some((_, best_string)) = outputs.first() {
        best_string.clone()
    } else {
        "".to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ruleparse::{parse_script, rule, rule_no_env};

    #[test]
    fn test_compile_script_basic() {
        let (script, syms) = parse_script("::seg:: = [abcdefghijklmnopqrstuvwxyzñ']\n[1234] -> {14} / #(::seg::)+ _ \n[23] -> {4} / _ ").unwrap();
        let mut inner_symt = symt!["#"];
        inner_symt.add_symbols(syms);
        let symt = Arc::new(inner_symt);
        println!("script={:?}", script);
        let fst = compile_script(symt.clone(), script).unwrap_or_else(|e| {
            println!("{e}: Could not compile script.");
            VectorFst::<TropicalWeight>::new()
        });
        let result = apply_fst(symt.clone(), fst, "#ni1hao3#".to_string());
        assert_eq!(result, "#ni{14}hao{4}#".to_string());
    }

    #[test]
    fn test_compile_script_basic_with_comment() {
        let symt = Arc::new(symt!["p", "b", "a", "i"]);
        let (script, _syms) = parse_script(
            "::voi::=(b|a|i)\n% The rules start here:\np -> b / (::voi::) _ (::voi::)",
        )
        .unwrap();
        println!("script={:?}", script);
        let fst = compile_script(symt.clone(), script).unwrap();
        let result = apply_fst(symt.clone(), fst, "apbppi".to_string());
        assert_eq!(result, "abbppi".to_string());
    }

    fn evaluate_rule(symt: Arc<SymbolTable>, rule_str: &str, input: &str, output: &str) {
        let macros: &HashMap<String, RegexAST> = &HashMap::new();
        let (_, (rewrite_rule, _syms)) = rule(rule_str).unwrap();
        let fst: VectorFst<TropicalWeight> = rule_fst(symt.clone(), macros, rewrite_rule).unwrap();
        assert_eq!(
            apply_fst(symt.clone(), fst, input.to_string()),
            output.to_string()
        )
    }

    #[test]
    fn test_kleene_star1() {
        evaluate_rule(
            Arc::new(symt!["#", "<g>", "</g>", "a", "b", "c", "d"]),
            "a -> b / cd* _ ",
            "cddda",
            "cdddb",
        )
    }

    #[test]
    fn test_kleene_star2() {
        evaluate_rule(
            Arc::new(symt!["#", "<g>", "</g>", "a", "b", "c", "d"]),
            "a -> b / cd* _ ",
            "ca",
            "cb",
        )
    }

    #[test]
    fn test_kleene_star3() {
        evaluate_rule(
            Arc::new(symt!["#", "<g>", "</g>", "a", "b", "c", "d"]),
            "a -> b / cd* _ ",
            "ddda",
            "ddda",
        )
    }

    #[test]
    fn test_kleene_plus3() {
        evaluate_rule(
            Arc::new(symt!["#", "<g>", "</g>", "a", "b", "c", "d"]),
            "a -> b / cd+ _ ",
            "cda",
            "cdb",
        )
    }

    #[test]
    fn test_kleene_plus4() {
        evaluate_rule(
            Arc::new(symt!["#", "<g>", "</g>", "a", "b", "c", "d"]),
            "a -> b / cd+ _ ",
            "ca",
            "ca",
        )
    }

    #[test]
    fn test_kleene_plus5() {
        evaluate_rule(
            Arc::new(symt!["#", "<g>", "</g>", "a", "b", "c", "d"]),
            "a -> b / (cd)+ _ ",
            "cdcdcda",
            "cdcdcdb",
        )
    }

    #[test]
    fn test_kleene_plus6() {
        evaluate_rule(
            Arc::new(symt!["#", "<g>", "</g>", "a", "b", "c", "d"]),
            "a -> b / (cd)+ _ ",
            "cdcdca",
            "cdcdca",
        )
    }

    #[test]
    fn test_option1() {
        evaluate_rule(
            Arc::new(symt!["#", "<g>", "</g>", "a", "b", "c", "d"]),
            "a -> b / cd? _ ",
            "cda",
            "cdb",
        )
    }

    #[test]
    fn test_option2() {
        evaluate_rule(
            Arc::new(symt!["#", "<g>", "</g>", "a", "b", "c", "d"]),
            "a -> b / cd? _ ",
            "ca",
            "cb",
        )
    }

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
        let symt = Arc::new(symt!["#", "<g>", "</g>", "a", "e"]);
        let macros: &HashMap<String, RegexAST> = &HashMap::new();
        let (_, (rewrite_rule, _syms)) = rule_no_env("a -> e").unwrap();
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
        assert_eq!(apply_fst(symt, fst, "#a#".to_string()), "#e#".to_string());
    }

    #[test]
    fn test_multiple_application() {
        // let symt = unicode_symbol_table();
        let symt = Arc::new(symt!["#", "<g>", "</g>", "a", "e"]);
        let macros: &HashMap<String, RegexAST> = &HashMap::new();
        let (_, (rewrite_rule, _syms)) = rule_no_env("a -> e").unwrap();
        // println!("rewrite_rule = {:?}", rewrite_rule);
        let fst: VectorFst<TropicalWeight> =
            rule_fst(symt.clone(), macros, rewrite_rule).expect("Something");
        // println!("fst.num_states()={:?}", fst.num_states());
        // println!("fst={:?}", fst);
        assert_eq!(apply_fst(symt, fst, "#aa#".to_string()), "#ee#".to_string());
    }

    #[test]
    fn test_rule_with_context() {
        // let symt = unicode_symbol_table();
        let symt = Arc::new(symt!["#", "<g>", "</g>", "a", "b", "p"]);
        let macros: &HashMap<String, RegexAST> = &HashMap::new();
        let (_, (rewrite_rule, _syms)) = rule("p -> b / a _ a").unwrap();
        // println!("rewrite_rule = {:?}", rewrite_rule);
        let fst: VectorFst<TropicalWeight> =
            rule_fst(symt.clone(), macros, rewrite_rule).expect("Something");
        // println!("fst.num_states()={:?}", fst.num_states());
        // println!("fst={:?}", fst);
        assert_eq!(
            apply_fst(symt, fst, "#apa#".to_string()),
            "#aba#".to_string()
        );
    }

    #[test]
    fn test_multiple_application_with_context() {
        // let symt = unicode_symbol_table();
        let symt = Arc::new(symt!["#", "<g>", "</g>", "a", "b", "p"]);
        let macros: &HashMap<String, RegexAST> = &HashMap::new();
        let (_, (rewrite_rule, _syms)) = rule("p -> b / a _ a").unwrap();
        // println!("rewrite_rule = {:?}", rewrite_rule);
        let fst: VectorFst<TropicalWeight> =
            rule_fst(symt.clone(), macros, rewrite_rule).expect("Something");
        // println!("fst.num_states()={:?}", fst.num_states());
        // println!("fst={:?}", fst);
        assert_eq!(
            apply_fst(symt, fst, "#apaapa#".to_string()),
            "#abaaba#".to_string()
        );
    }

    #[test]
    fn test_rule_disjunction() {
        let symt = Arc::new(symt!["#", "<g>", "</g>", "a", "b", "p", "i"]);
        let macros: &HashMap<String, RegexAST> = &HashMap::new();
        let (_, (rewrite_rule, _syms)) = rule("(p|b) -> i / a _ ").unwrap();
        let fst: VectorFst<TropicalWeight> =
            rule_fst(symt.clone(), macros, rewrite_rule).expect("Something");
        assert_eq!(
            apply_fst(symt, fst, "#apab#".to_string()),
            "#aiai#".to_string()
        );
    }

    #[test]
    fn test_rule_class() {
        let symt = Arc::new(symt!["#", "<g>", "</g>", "a", "b", "p", "i"]);
        let macros: &HashMap<String, RegexAST> = &HashMap::new();
        let (_, (rewrite_rule, _syms)) = rule("a -> i / [pb] _ ").unwrap();
        let fst: VectorFst<TropicalWeight> =
            rule_fst(symt.clone(), macros, rewrite_rule).expect("Something");
        assert_eq!(
            apply_fst(symt, fst, "#pabaaa#".to_string()),
            "#pibiaa#".to_string()
        );
    }

    #[test]
    fn test_rule_complement_class() {
        let symt = Arc::new(symt!["#", "<g>", "</g>", "a", "b", "p", "i"]);
        let macros: &HashMap<String, RegexAST> = &HashMap::new();
        let (_, (rewrite_rule, _syms)) = rule("a -> i / [^pb] _ ").unwrap();
        let fst: VectorFst<TropicalWeight> =
            rule_fst(symt.clone(), macros, rewrite_rule).expect("Something");
        assert_eq!(
            apply_fst(symt, fst, "#pabaa#".to_string()),
            "#pabai#".to_string()
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
        let symt = Arc::new(symt!["#", "<g>", "</g>", "a", "b", "c", "d"]);
        let macros: HashMap<String, RegexAST> = HashMap::new();
        let input = RegexAST::Char('a');
        let mut fst: VectorFst<TropicalWeight> = fst![4 => 4; 0.0];
        fst.set_input_symbols(symt.clone());
        fst.set_output_symbols(symt.clone());
        assert_eq!(node_fst(symt, &macros, input).unwrap(), fst);
    }
}
