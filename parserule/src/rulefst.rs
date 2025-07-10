//! Defines WFSTs for implementing the rules in an Epitran processor file (as
//! parsed by the `ruleparse`` module).

// cSpell:disable

use anyhow::Result;
use rustfst::algorithms::compose::compose;
use rustfst::algorithms::{
    add_super_final_state,
    closure::{closure, ClosureType},
    concat::concat,
    shortest_path, tr_sort,
    union::union,
};
// Explicitly import VectorFst to avoid conflicts
use rustfst::fst_impls::VectorFst;
use rustfst::fst_traits::{CoreFst, ExpandedFst, MutableFst};
use rustfst::prelude::*;
use rustfst::utils::{acceptor, transducer};
// use rustfst::DrawingConfig;
use std::char;
use std::cmp::Ordering;
// Explicitly import HashMap to avoid conflicts
use std::collections::HashMap;
// use std::process::Command;
// Explicitly import Arc to avoid conflicts
use std::sync::Arc;

use colored::Colorize;

use crate::ruleparse::{RegexAST, RewriteRule, Statement};
use crate::utils::optimize_fst;

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
pub fn unicode_symbol_table() -> Result<Arc<SymbolTable>> {
    let mut symt = SymbolTable::new();
    symt.add_symbol("#");
    for code_point in 1..0xFFFF {
        if let Some(c) = char::from_u32(code_point) {
            if c != '#' {
                symt.add_symbol(c);
            }
        }
    }
    Ok(Arc::new(symt))
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
                            "Failed to build rule {rule:?} having macros {macros:?}: {e}"
                        )
                    })
                    .unwrap_or(VectorFst::<TropicalWeight>::new());
                optimize_fst(&mut fst, 1e-7).unwrap_or(());
                tr_sort(&mut fst, OLabelCompare {});
                tr_sort(&mut fst2, ILabelCompare {});
                fst = compose(fst.clone(), fst2)?;
                // rm_epsilon(&mut fst).unwrap_or_else(|e| {
                //     println!("Warning: Could not remove epsilons from rule FST: {}", e);
                // });
                // let mut fst: VectorFst<TropicalWeight> = determinize_with_config(
                //     &fst,
                //     DeterminizeConfig {
                //         delta: 1e-6,
                //         det_type: DeterminizeType::DeterminizeFunctional
                //     })?;
                // push_weights(&mut fst, ReweightType::ReweightToInitial)?;
                // minimize_with_config(
                //     &mut fst,
                //     MinimizeConfig {
                //         delta: 1e-7,
                //         allow_nondet: (true),
                //     },
                // )?;
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
pub fn rule_fst(
    symt: Arc<SymbolTable>,
    macros: &HashMap<String, RegexAST>,
    rule: RewriteRule,
) -> Result<VectorFst<TropicalWeight>> {
    
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
    let left_fst = match rule.left {
        RegexAST::Epsilon => {
            let mut inner_fst = universal_acceptor(symt.clone())?;
            closure(&mut inner_fst, ClosureType::ClosureStar);
            inner_fst
        }
        _ => node_fst(symt.clone(), macros, rule.left)?,
    };
    let right_fst = match rule.right {
        RegexAST::Epsilon => {
            let mut inner_fst = universal_acceptor(symt.clone())?;
            closure(&mut inner_fst, ClosureType::ClosureStar);
            inner_fst
        }
        _ => node_fst(symt.clone(), macros, rule.right)?,
    };
    let univ_acc: VectorFst<TropicalWeight> = universal_acceptor(symt.clone())?;

    concat(&mut fst, &left_fst)?;
    concat(&mut fst, &src_fst)?;
    concat(&mut fst, &tgt_fst)?;
    concat(&mut fst, &right_fst)?;
    concat(&mut fst, &univ_acc)?;

    let first_state: u32 = 0;
    let last_state: u32 = (fst.num_states() - 1) as u32;

    fst.emplace_tr(last_state, 0, 0, 0.0, first_state)?;
    fst.emplace_tr(first_state, 0, 0, 10.0, last_state)?;
    fst.set_final(last_state, 0.0)?;

    let mut root: VectorFst<TropicalWeight> = universal_acceptor(symt.clone())?;

    concat(&mut root, &fst)?;

    root.set_start(0)?;

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

    // rm_epsilon(&mut root).unwrap_or_else(|e| println!("{e}: Cannot remove epsilons."));
    // minimize_with_config(
    //     &mut root,
    //     MinimizeConfig {
    //         delta: 1e-7,
    //         allow_nondet: (true),
    //     },
    // )?;
    // .unwrap_or_else(|e| println!("{e}: Could not minimize wFST. Proceeding"));
    optimize_fst(&mut root, 1e-6).unwrap_or(());

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
                concat(&mut fst, &fst2)?;
            }
        }

        // Interpret a boundary symbol.
        RegexAST::Boundary => {
            let bnd_label = symt.get_label("#").unwrap_or(1);
            let fst2: VectorFst<TropicalWeight> = fst![bnd_label];
            concat(&mut fst, &fst2)?;
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
            fst.emplace_tr(q0, 0, 0, TropicalWeight::zero(), q1)?;
            for node in nodes {
                let case_fst = node_fst(symt.clone(), macros, node)?;
                union(&mut fst2, &case_fst)?;
            }
            concat(&mut fst, &fst2)?;
        }

        // Interpret a character class (a set of characters any of which match the expression).
        RegexAST::Class(class) => {
            let mut fst2: VectorFst<TropicalWeight> = VectorFst::<TropicalWeight>::new();
            let q0 = fst2.add_state();
            fst2.set_start(q0)?;
            let q1: u32 = fst2.add_state();
            fst2.set_final(q1, 0.0)?;
            fst2.emplace_tr(q1, 0, 0, TropicalWeight::zero(), q1)?;
            for s in class.iter() {
                let l = symt.get_label(s).unwrap_or_else(|| {
                    eprintln!(
                        "Warning: Symbol '{}' is not in symbol table, using epsilon",
                        s.red()
                    );
                    0
                });
                fst2.emplace_tr(q0, l, l, TropicalWeight::one(), q1)?;
            }
            concat::concat(&mut fst, &fst2)?;
        }

        // Interpret the complement of a character class (a set of characters none of which match the expression).
        RegexAST::ClassComplement(mut class) => {
            let mut fst2: VectorFst<TropicalWeight> = VectorFst::<TropicalWeight>::new();
            let q0 = fst2.add_state();
            fst2.set_start(q0)?;
            let q1: u32 = fst2.add_state();
            fst2.set_final(q1, 0.0)?;
            class.insert("#".to_string());
            class.insert("<eps>".to_string());
            for (l, s) in symt.iter() {
                if !class.contains(s) {
                    fst2.emplace_tr(q0, l, l, TropicalWeight::one(), q1)?;
                }
            }
            concat::concat(&mut fst, &fst2)?;
        }

        // Interpret a Kleene star.
        RegexAST::Star(node) => {
            let mut fst2 = node_fst(symt, macros, *node)?;
            closure(&mut fst2, closure::ClosureType::ClosureStar);
            concat(&mut fst, &fst2)?;
        }

        // Interpret a Kleene plus.
        RegexAST::Plus(node) => {
            let mut fst2 = node_fst(symt, macros, *node)?;
            closure(&mut fst2, closure::ClosureType::ClosurePlus);
            concat(&mut fst, &fst2)?;
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

    // rm_epsilon(&mut fst).unwrap_or_else(|e| {
    //     eprintln!("Warning: Could not remove epsilon transitions: {}", e);
    // });
    // let mut fst = determinize_with_config(
    //     &fst,
    //     DeterminizeConfig {
    //         delta: 1e-6,
    //         det_type: DeterminizeType::DeterminizeFunctional,
    //     },
    // )?;
    // push_weights(&mut fst, ReweightType::ReweightToInitial)?;
    // minimize_with_config(
    //     &mut fst,
    //     MinimizeConfig {
    //         delta: 1e-7,
    //         allow_nondet: (true),
    //     },
    // )?;

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
        None => {
            eprintln!("{}", "wFST lacks start state. Assuming 0.".red());
            stack.push((Action::Enter, 0));
        }
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
                    .unwrap_or_else(|e| panic!("State {v} not present in wFST: {e}"))
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
/// # use rustfst::fst_impls::VectorFst;
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
    fst: VectorFst<TropicalWeight>,
    input: String,
) -> Result<VectorFst<TropicalWeight>> {
    // Convert input string to a linear automaton
    let mut acc = string_to_linear_automaton(symt.clone(), &input);
    acc.set_symts_from_fst(&fst);

    // Sort transitions for efficient composition
    tr_sort(&mut acc, OLabelCompare {});

    // We should assume that `fst` is already sorted by output labels.
    // tr_sort(&mut fst, ILabelCompare {});

    // Compose input automaton with the rule FST
    let composed_fst = compose(acc, fst)?;

    // Optionally, optimize the composed FST if you will decode paths or apply further operations
    // optimize_fst(&mut composed_fst, 1e-6).unwrap_or(());

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
/// # use std::collections::HashMap;
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
    // Need proper error handling here.
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
    println!("\n*** outputs={outputs:?}");
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
/// # use std::collections::HashMap;
/// # use rustfst::utils::{acceptor, transducer};
/// let symt: Arc<SymbolTable> = Arc::new(symt!["a", "b", "c", "d"]);
/// let mut fst: VectorFst<TropicalWeight> = fst![1, 2, 1 => 3, 4, 3; 0.1];
/// fst.set_input_symbols(symt.clone());
/// fst.set_output_symbols(symt.clone());
/// let input = "aba".to_string();
/// assert_eq!(apply_fst(symt, fst, input), "cdc".to_string());
/// ```
// pub fn apply_fst(symt: Arc<SymbolTable>, fst: VectorFst<TropicalWeight>, input: String) -> String {
//     let composed_fst = apply_fst_to_string(symt.clone(), fst.clone(), input.clone())
//         .unwrap_or_else(|e| {
//             println!("{e}: Couldn't apply wFST {:?} to string {:?}.", fst, input);
//             VectorFst::<TropicalWeight>::new()
//         });
//     if is_cyclic(&composed_fst) {
//         panic!("Transducer resulting from applying composing input string was cyclic.")
//     }
//     let outputs = decode_paths_through_fst(symt.clone(), composed_fst);
//     if let Some((_, best_string)) = outputs.first() {
//         best_string.clone()
//     } else {
//         "".to_string()
//     }
// }
pub fn apply_fst(symt: Arc<SymbolTable>, fst: VectorFst<TropicalWeight>, input: String) -> String {
    let mut composed_fst: VectorFst<TropicalWeight> =
        apply_fst_to_string(symt.clone(), fst.clone(), input.clone()).unwrap_or_else(|e| {
            println!("{e}: Couldn't apply wFST {fst:?} to string {input:?}.");
            VectorFst::<TropicalWeight>::new()
        });
    if is_cyclic(&composed_fst) {
        panic!("Transducer resulting from applying composing input string was cyclic.")
    };
    composed_fst.set_input_symbols(symt.clone());
    composed_fst.set_output_symbols(symt.clone());

    let shortest: VectorFst<TropicalWeight> = shortest_path(&composed_fst).unwrap();

    shortest
        .string_paths_iter()
        .unwrap()
        .collect::<Vec<StringPath<TropicalWeight>>>()[0]
        .olabels()
        .iter()
        .map(|l| symt.get_symbol(*l).unwrap_or_else(|| {
            eprintln!("Label {l} not found in Symbol Table while decoding path. Using empty string.");
            ""
        }))
        .collect::<String>()
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustfst::algorithms::rm_epsilon::rm_epsilon;
    use crate::ruleparse::{parse_script, rule, rule_no_env};

    // #[test]
    // fn test_compile_script_basic() {
    //     let (_, (script, syms)) = parse_script("::seg:: = [abcdefghijklmnopqrstuvwxyzñ']\n[1234] -> {14} / #(::seg::)+ _ \n[23] -> {4} / _ ").expect("Failed to parse script in test");
    //     let mut inner_symt = symt!["#"];
    //     inner_symt.add_symbols(syms);
    //     let symt = Arc::new(inner_symt);
    //     println!("script={:?}", script);
    //     let fst = compile_script(symt.clone(), script).unwrap_or_else(|e| {
    //         println!("{e}: Could not compile script.");
    //         VectorFst::<TropicalWeight>::new()
    //     });
    //     let result = apply_fst(symt.clone(), fst, "#ni1hao3#".to_string());
    //     assert_eq!(result, "#ni{14}hao{4}#".to_string());
    // }

    #[test]
    fn test_compile_script_basic_with_comment() {
        let symt = Arc::new(symt!["p", "b", "a", "i"]);
        let (_, (script, _syms)) = parse_script(
            "::voi::=(b|a|i)\n% The rules start here:\np -> b / (::voi::) _ (::voi::)",
        )
        .expect("Failed to parse script in test");
        let fst = compile_script(symt.clone(), script).expect("Failed to compile script in test");
        let result = apply_fst(symt.clone(), fst, "apbppi".to_string());
        assert_eq!(result, "abbppi".to_string());
    }

    fn evaluate_rule(symt: Arc<SymbolTable>, rule_str: &str, input: &str, output: &str) {
        let macros: &HashMap<String, RegexAST> = &HashMap::new();
        let (_, (rewrite_rule, _syms)) = rule(rule_str).expect("Failed to parse rule in test");
        let fst: VectorFst<TropicalWeight> = rule_fst(symt.clone(), macros, rewrite_rule)
            .expect("Failed to create rule FST in test");
        // 1optimize_fst(&mut fst, 1e-5).expect("Could not optimize FST in test");
        assert_eq!(
            apply_fst(symt.clone(), fst, input.to_string()),
            output.to_string()
        )
    }

    #[test]
    fn test_kleene_star1() {
        evaluate_rule(
            Arc::new(symt!["#", "a", "b", "c", "d"]),
            "a -> b / cd* _ ",
            "cddda",
            "cdddb",
        )
    }

    #[test]
    fn test_kleene_star2() {
        evaluate_rule(
            Arc::new(symt!["#", "a", "b", "c", "d"]),
            "a -> b / cd* _ ",
            "ca",
            "cb",
        )
    }

    #[test]
    fn test_kleene_star3() {
        evaluate_rule(
            Arc::new(symt!["#", "a", "b", "c", "d"]),
            "a -> b / cd* _ ",
            "ddda",
            "ddda",
        )
    }

    #[test]
    fn test_kleene_plus3() {
        evaluate_rule(
            Arc::new(symt!["#", "a", "b", "c", "d"]),
            "a -> b / cd+ _ ",
            "cda",
            "cdb",
        )
    }

    #[test]
    fn test_kleene_plus4() {
        evaluate_rule(
            Arc::new(symt!["#", "a", "b", "c", "d"]),
            "a -> b / cd+ _ ",
            "ca",
            "ca",
        )
    }

    #[test]
    fn test_kleene_plus5() {
        evaluate_rule(
            Arc::new(symt!["#", "a", "b", "c", "d"]),
            "a -> b / (cd)+ _ ",
            "cdcdcda",
            "cdcdcdb",
        )
    }

    #[test]
    fn test_kleene_plus6() {
        evaluate_rule(
            Arc::new(symt!["#", "a", "b", "c", "d"]),
            "a -> b / (cd)+ _ ",
            "cdcdca",
            "cdcdca",
        )
    }

    #[test]
    fn test_option1() {
        evaluate_rule(
            Arc::new(symt!["#", "a", "b", "c", "d"]),
            "a -> b / cd? _ ",
            "cda",
            "cdb",
        )
    }

    #[test]
    fn test_option2() {
        evaluate_rule(
            Arc::new(symt!["#", "a", "b", "c", "d"]),
            "a -> b / cd? _ ",
            "ca",
            "cb",
        )
    }

    #[test]
    fn test_simple_rule() {
        // let symt = unicode_symbol_table();
        let symt = Arc::new(symt!["#", "a", "e"]);
        let macros: &HashMap<String, RegexAST> = &HashMap::new();
        let (_, (rewrite_rule, _syms)) =
            rule_no_env("a -> e").expect("Failed to parse rule_no_env in test");
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
        let symt = Arc::new(symt!["#", "a", "e"]);
        let macros: &HashMap<String, RegexAST> = &HashMap::new();
        let (_, (rewrite_rule, _syms)) =
            rule_no_env("a -> e").expect("Failed to parse rule_no_env in test");
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
        let symt = Arc::new(symt!["#", "a", "b", "p"]);
        let macros: &HashMap<String, RegexAST> = &HashMap::new();
        let (_, (rewrite_rule, _syms)) =
            rule("p -> b / a _ a").expect("Failed to parse rule in test");
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
        let symt = Arc::new(symt!["#", "a", "b", "p"]);
        let macros: &HashMap<String, RegexAST> = &HashMap::new();
        let (_, (rewrite_rule, _syms)) =
            rule("p -> b / a _ a").expect("Failed to parse rule in test");
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
        let symt = Arc::new(symt!["#", "a", "b", "p", "i"]);
        let macros: &HashMap<String, RegexAST> = &HashMap::new();
        let (_, (rewrite_rule, _syms)) =
            rule("(p|b) -> i / a _ ").expect("Failed to parse rule in test");
        let fst: VectorFst<TropicalWeight> =
            rule_fst(symt.clone(), macros, rewrite_rule).expect("Something");
        assert_eq!(
            apply_fst(symt, fst, "#apab#".to_string()),
            "#aiai#".to_string()
        );
    }

    #[test]
    fn test_rule_class() {
        let symt = Arc::new(symt!["#", "a", "b", "p", "i"]);
        let macros: &HashMap<String, RegexAST> = &HashMap::new();
        let (_, (rewrite_rule, _syms)) =
            rule("a -> i / [pb] _ ").expect("Failed to parse rule in test");
        let fst: VectorFst<TropicalWeight> =
            rule_fst(symt.clone(), macros, rewrite_rule).expect("Something");
        assert_eq!(
            apply_fst(symt, fst, "#pabaaa#".to_string()),
            "#pibiaa#".to_string()
        );
    }

    #[test]
    fn test_rule_complement_class() {
        let symt = Arc::new(symt!["#", "a", "b", "p", "i"]);
        let macros: &HashMap<String, RegexAST> = &HashMap::new();
        let (_, (rewrite_rule, _syms)) =
            rule("a -> i / [^pb] _ ").expect("Failed to parse rule in test");
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
        fst1.set_start(q0)
            .expect("Failed to set start state in test");
        let q1 = fst1.add_state();
        fst1.set_final(q1, 0.0)
            .expect("Failed to set final state in test");
        fst1.emplace_tr(q0, 0, 0, 0.0, q1)
            .expect("Failed to add transition in test");
        let fst2: VectorFst<TropicalWeight> = fst![1 => 2; 0.0];
        concat(&mut fst1, &fst2).expect("Failed to concatenate FSTs in test");
        assert_eq!(fst1, fst![0, 0, 1 => 0, 0, 2; 0.0])
    }

    #[test]
    fn test_rm_epsilon() {
        let mut fst1 = VectorFst::<TropicalWeight>::new();
        let q0 = fst1.add_state();
        fst1.set_start(q0)
            .expect("Failed to set start state in test");
        let q1 = fst1.add_state();
        fst1.set_final(q1, 0.0)
            .expect("Failed to set final state in test");
        fst1.emplace_tr(q0, 0, 0, 0.0, q1)
            .expect("Failed to add transition in test");
        let fst2: VectorFst<TropicalWeight> = fst![1, 3 => 2, 4; 0.0];
        concat(&mut fst1, &fst2).expect("Failed to concatenate FSTs in test");
        rm_epsilon(&mut fst1).expect("Failed to remove epsilon transitions in test");
        assert_eq!(fst1, fst![1, 3 => 2, 4; 0.0])
    }
}
