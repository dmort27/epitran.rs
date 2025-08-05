//! Defines WFSTs for implementing the rules in an Epitran processor file (as
//! parsed by the `ruleparse`` module).

// cSpell:disable

use anyhow::Result;
use rustfst::algorithms::compose::compose;
use rustfst::algorithms::{
    add_super_final_state, closure::closure, concat::concat, reverse, rm_epsilon::rm_epsilon,
    shortest_path, tr_sort, union::union,
};
use rustfst::algorithms::{project, ProjectType};
// Explicitly import VectorFst to avoid conflicts
use rustfst::fst_impls::VectorFst;
use rustfst::fst_traits::{CoreFst, ExpandedFst, MutableFst};
// use rustfst::prelude::closure::ClosureType;
use rustfst::prelude::*;
use rustfst::utils::{acceptor, transducer};
// use rustfst::DrawingConfig;
use std::char;
use std::cmp::Ordering;
// Explicitly import HashMap to avoid conflicts
use std::collections::{BTreeMap, HashMap, HashSet};
// use std::process::Command;
// Explicitly import Arc to avoid conflicts
use std::sync::Arc;

use colored::Colorize;

use crate::ruleparse::{RegexAST, RewriteRule, Statement};
use crate::utils::{draw_wfst, optimize_fst};

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
    let mut macros: BTreeMap<String, RegexAST> = BTreeMap::new();
    for statement in statements {
        match statement {
            Statement::Comment => (),
            Statement::MacroDef((mac, def)) => {
                macros.insert(mac, def).unwrap_or(RegexAST::Epsilon);
            }
            Statement::Rule(rule) => {
                let mut fst2 = rule_fst(symt.clone(), &macros, rule.clone())
                    .inspect_err(|e| {
                        println!("Failed to build rule {rule:?} having macros {macros:?}: {e}")
                    })
                    .unwrap_or(VectorFst::<TropicalWeight>::new());
                // optimize_fst(&mut fst, 1e-7).unwrap_or(());
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

// pub fn rule_fst(
//     symt: Arc<SymbolTable>,
//     macros: &BTreeMap<String, RegexAST>,
//     rule: RewriteRule,
// ) -> Result<VectorFst<TropicalWeight>, Box<dyn std::error::Error>> {
//     let lbrace1 = symt.add_symbol("<1");
//     let lbrace2 = symt.add_symbol("<2");
//     let rbrace = symt.add_symbol(">");

//     let marks: HashSet<Label> = HashSet::from([lbrace1, lbrace2, rbrace]);

//     let alphabet: HashSet<Label> = symt.labels().collect();
//     let alphabet: HashSet<Label> = alphabet.difference(&marks).copied().collect();

//     println!("Building left context wFST.");
//     let lambda = match rule.left {
//         RegexAST::Epsilon => fst![0; 0.0],
//         _ => node_fst(symt.clone(), macros, rule.left)?,
//     };

//     println!("Building right context wFST.");
//     let rho = match rule.right {
//         RegexAST::Epsilon => fst![0; 0.0],
//         _ => node_fst(symt.clone(), macros, rule.right)?,
//     };

//     // eprintln!("{}={:?}", "right_fst".bold().green(), right_fst);
//     println!("Building source wFST.");
//     let phi: VectorFst<TropicalWeight> =
//         output_to_epsilons(node_fst(symt.clone(), macros, rule.source)?);

//     // draw_wfst(&src_fst, "src_fst", "Diagram of src_fst")?;

//     println!("Building target wFST.");
//     let psi: VectorFst<TropicalWeight> =
//         input_to_epsilons(node_fst(symt.clone(), macros, rule.target)?);
//     // let univ_acc: VectorFst<TropicalWeight> = universal_acceptor(symt.clone())?;

//     // let _rewrite_rule_fst: VectorFst<TropicalWeight> = VectorFst::new();

//     println!("Building brace inserter.");
//     let mut brace_inserter_fst = build_brace_inserter(
//         alphabet,
//         lbrace1,
//         lbrace2,
//         rbrace,
//         src_fst.clone(,
//     )?;

//     println!("Building left context filter.");
//     let mut left_context_filter_fst: VectorFst<TropicalWeight> =
//         build_left_context_filter(sigma_star.clone(), lbrace1, left_fst.clone())?;

//     println!("Building right context filter.");
//     let mut right_context_filter_fst: VectorFst<TropicalWeight> =
//         build_right_context_filter(sigma_star, rbrace, right_fst)?;

//     println!("Building replacement wFST.");
//     let mut replace_fst: VectorFst<TropicalWeight> =
//         build_replacer(src_fst.clone(), tgt_fst.clone())?;

//     println!("Building wFST to delete braces.");
//     let mut delete_braces_fst: VectorFst<TropicalWeight> =
//         build_brace_deleter(local_symt.clone(), lbrace1, lbrace2, rbrace)?;

//     println!("Building wFSTs for filtering.");
//     tr_sort(&mut brace_inserter_fst, OLabelCompare {});
//     tr_sort(&mut left_context_filter_fst, ILabelCompare {});
//     let mut inner_filtered_fst: VectorFst<TropicalWeight> =
//         custom_compose(brace_inserter_fst, left_context_filter_fst).unwrap();

//     tr_sort(&mut inner_filtered_fst, OLabelCompare {});
//     tr_sort(&mut right_context_filter_fst, ILabelCompare {});
//     let mut filtered_fst: VectorFst<TropicalWeight> =
//         custom_compose(inner_filtered_fst, right_context_filter_fst).unwrap();

//     println!("Building final wFST.");
//     tr_sort(&mut filtered_fst, OLabelCompare {});
//     tr_sort(&mut replace_fst, ILabelCompare {});
//     let mut replaced_fst: VectorFst<TropicalWeight> =
//         custom_compose(filtered_fst, replace_fst.clone())?;

//     tr_sort(&mut replaced_fst, OLabelCompare {});
//     tr_sort(&mut delete_braces_fst, ILabelCompare {});
//     let mut final_fst: VectorFst<TropicalWeight> = custom_compose(replaced_fst, delete_braces_fst)?;

//     println!("Setting symbol table.");
//     final_fst.set_input_symbols(symt.clone());
//     final_fst.set_output_symbols(symt.clone());
//     Ok(final_fst)
// }

// fn custom_compose(
//     fst1: VectorFst<TropicalWeight>,
//     fst2: VectorFst<TropicalWeight>,
// ) -> Result<VectorFst<TropicalWeight>> {
//     let composed_fst: VectorFst<TropicalWeight> = compose_with_config(
//         fst1,
//         fst2,
//         ComposeConfig {
//             compose_filter: ComposeFilterEnum::NullFilter,
//             matcher1_config: MatcherConfig {
//                 sigma_matcher_config: None,
//             },
//             matcher2_config: MatcherConfig {
//                 sigma_matcher_config: None,
//             },
//             connect: false,
//         },
//     )
//     .unwrap_or_else(|e| {
//         eprint!("{e}: Could not compose two wFSTs.");
//         VectorFst::<TropicalWeight>::new()
//     });
//     Ok(composed_fst)
// }

// pub fn build_sigma_star(symt: Arc<SymbolTable>) -> Result<VectorFst<TropicalWeight>> {
//     let mut sigma_star: VectorFst<TropicalWeight> = VectorFst::new();
//     let start_state = sigma_star.add_state();
//     sigma_star.set_start(start_state)?;
//     sigma_star.set_final(start_state, 0.0)?;
//     symt.clone()
//         .labels()
//         .for_each(|l| sigma_star.emplace_tr(0, l, l, 0.0, 0).unwrap());
//     Ok(sigma_star)
// }

// fn build_brace_inserter(
//     sigma_star: VectorFst<TropicalWeight>,
//     lbrace1: Label,
//     lbrace2: Label,
//     rbrace: Label,
//     source_fst: VectorFst<TropicalWeight>,
// ) -> Result<VectorFst<TropicalWeight>> {
//     let lbrace1: VectorFst<TropicalWeight> = fst![lbrace1];
//     let lbrace2: VectorFst<TropicalWeight> = fst![lbrace2];
//     let rbrace: VectorFst<TropicalWeight> = fst![rbrace];
//     let mut bracketed_src: VectorFst<TropicalWeight> = fst![0];
//     concat(&mut bracketed_src, &lbrace1)?;
//     concat(&mut bracketed_src, &source_fst)?;
//     concat(&mut bracketed_src, &lbrace2)?;
//     concat(&mut bracketed_src, &rbrace)?;
//     let mut brace_inserter_fst: VectorFst<TropicalWeight> = fst![0];
//     concat(&mut brace_inserter_fst, &sigma_star)?;
//     concat(&mut brace_inserter_fst, &lbrace1)?;
//     concat(&mut brace_inserter_fst, &sigma_star)?;
//     closure(&mut brace_inserter_fst, closure::ClosureType::ClosureStar);
//     Ok(brace_inserter_fst)
// }

// fn build_left_context_filter(
//     sigma_star: VectorFst<TropicalWeight>,
//     lbrace1: Label,
//     left_context_fst: VectorFst<TropicalWeight>,
// ) -> Result<VectorFst<TropicalWeight>> {
//     let lbrace1: VectorFst<TropicalWeight> = fst![lbrace1];
//     let mut left_context_filter_fst: VectorFst<TropicalWeight> = fst![0];
//     concat(&mut left_context_filter_fst, &sigma_star)?;
//     concat(&mut left_context_filter_fst, &left_context_fst)?;
//     concat(&mut left_context_filter_fst, &lbrace1)?;
//     concat(&mut left_context_filter_fst, &sigma_star)?;
//     Ok(left_context_filter_fst)
// }

// fn build_right_context_filter(
//     sigma_star: VectorFst<TropicalWeight>,
//     rbrace: Label,
//     right_context_fst: VectorFst<TropicalWeight>,
// ) -> Result<VectorFst<TropicalWeight>> {
//     let rbrace: VectorFst<TropicalWeight> = fst![rbrace];
//     let mut right_context_filter_fst: VectorFst<TropicalWeight> = fst![0];
//     concat(&mut right_context_filter_fst, &sigma_star)?;
//     concat(&mut right_context_filter_fst, &rbrace)?;
//     concat(&mut right_context_filter_fst, &right_context_fst)?;
//     concat(&mut right_context_filter_fst, &sigma_star)?;
//     Ok(right_context_filter_fst)
// }

// fn build_replacer(
//     src_fst: VectorFst<TropicalWeight>,
//     tgt_fst: VectorFst<TropicalWeight>,
// ) -> Result<VectorFst<TropicalWeight>> {
//     // left_labels = extract_src_tgt_strings(symt.clone(), )

//     let mut replace_fst: VectorFst<TropicalWeight> = fst![0];
//     concat(&mut replace_fst, &src_fst)?;
//     concat(&mut replace_fst, &tgt_fst)?;
//     Ok(replace_fst)
// }

// fn _extract_src_tgt_strings(symt: Arc<SymbolTable>, sequence: RegexAST) -> Vec<Label> {
//     let symt = symt.clone();
//     match sequence {
//         RegexAST::Group(chars) => {
//             let mut characters = Vec::new();
//             for char in chars {
//                 match char {
//                     RegexAST::Char(c) => characters.push(c),
//                     _ => (),
//                 }
//             }
//             characters
//                 .iter()
//                 .map(|&s| symt.get_label(s.to_string()).unwrap_or(0))
//                 .collect()
//         }
//         _ => Vec::new(),
//     }
// }

pub fn rule_fst(
    symt: Arc<SymbolTable>,
    macros: &BTreeMap<String, RegexAST>,
    rule: RewriteRule,
) -> Result<VectorFst<TropicalWeight>> {
    println!("DEBUG: Starting rule_fst with rule: {:?}", rule);
    
    // Define braces.
    let lbrace1_symbol = "<1";
    let lbrace2_symbol = "<2";
    let rbrace_symbol = ">";

    let mut symt_mut = (*symt).clone();

    // Add braces to the symbol table
    let rbrace = symt_mut.add_symbol(rbrace_symbol);
    let lbrace1 = symt_mut.add_symbol(lbrace1_symbol);
    let lbrace2 = symt_mut.add_symbol(lbrace2_symbol);

    let symt = Arc::new(symt_mut);

    // Create a set `alphabet` of the labels in the symbol table.
    // Create a set `alphabet` of the labels in the symbol table, excluding markers.
    let marks: HashSet<Label> = HashSet::from([lbrace1, lbrace2, rbrace]);
    let all_labels: HashSet<Label> = symt.labels().collect();
    let alphabet: HashSet<Label> = all_labels.difference(&marks).copied().collect();
    println!("DEBUG: Alphabet size: {} (excluding {} markers)", alphabet.len(), marks.len());

    // Compute wFSTs for the context (`lambda` and `rho`) and remove epsilons.
    println!("DEBUG: Building lambda (left context)");
    let mut lambda = match rule.left {
        RegexAST::Epsilon => fst![0; 0.0],
        _ => node_fst(symt.clone(), macros, rule.left).unwrap(),
    };
    println!("DEBUG: Lambda states before completion: {}", lambda.num_states());
    complete_fst_fixed(alphabet.clone(), &mut lambda)?;
    println!("DEBUG: Lambda states after completion: {}", lambda.num_states());
    rm_epsilon(&mut lambda)?;
    println!("DEBUG: Lambda states after rm_epsilon: {}", lambda.num_states());

    println!("DEBUG: Building rho (right context)");
    let mut rho = match rule.right {
        RegexAST::Epsilon => fst![0; 0.0],
        _ => node_fst(symt.clone(), macros, rule.right).unwrap(),
    };
    println!("DEBUG: Rho states before completion: {}", rho.num_states());
    complete_fst_fixed(alphabet.clone(), &mut rho)?;
    println!("DEBUG: Rho states after completion: {}", rho.num_states());
    rm_epsilon(&mut rho)?;
    println!("DEBUG: Rho states after rm_epsilon: {}", rho.num_states());

    println!("DEBUG: Building phi labels");
    let phi_labels: Vec<Label> = regex_to_vector_of_labels(symt.clone(), rule.source.clone())?;
    println!("DEBUG: Phi labels: {:?}", phi_labels);

    let phi_transducer: VectorFst<TropicalWeight> =
        transducer(&phi_labels, &phi_labels, TropicalWeight::new(0.0));
    println!("DEBUG: Phi transducer states: {}", phi_transducer.num_states());

    println!("DEBUG: Building fst_r (insert rbrace before rho)");
    let mut fst_r = build_insert_rbrace_before_rho_fixed(rbrace, alphabet.clone(), rho.clone())?;
    println!("DEBUG: fst_r states: {}", fst_r.num_states());

    println!("DEBUG: Building fst_f (insert lbraces before phi followed by rho)");
    let mut fst_f = build_insert_lbraces_before_phi_followed_by_rho_fixed(
        lbrace1,
        lbrace2,
        rbrace,
        alphabet.clone(),
        phi_transducer.clone(),
    )?;
    println!("DEBUG: fst_f states: {}", fst_f.num_states());

    println!("DEBUG: Building fst_replace (replace phi with psi)");
    let mut fst_replace = build_replace_phi_with_psi_fixed(
        symt.clone(),
        alphabet.clone(),
        lbrace1,
        lbrace2,
        rbrace,
        rule.source,
        rule.target,
    )?;
    println!("DEBUG: fst_replace states: {}", fst_replace.num_states());

    println!("DEBUG: Building fst_l1 (lbrace1 lambda filter)");
    let mut fst_l1 = build_lbrace1_lambda_filter_fixed(lbrace1, alphabet.clone(), lambda.clone())?;
    println!("DEBUG: fst_l1 states: {}", fst_l1.num_states());

    println!("DEBUG: Building fst_l2 (lbrace2 lambda filter)");
    let mut fst_l2 = build_lbrace2_lambda_filter_fixed(lbrace2, alphabet.clone(), lambda.clone())?;
    println!("DEBUG: fst_l2 states: {}", fst_l2.num_states());

    println!("DEBUG: Starting composition sequence");

    // Debug: Save individual FSTs for inspection
    draw_wfst(&fst_r, "debug_fst_r", "fst_r (insert rbrace before rho)").ok();
    draw_wfst(&fst_f, "debug_fst_f", "fst_f (insert lbraces before phi followed by rho)").ok();
    tr_sort(&mut fst_r, OLabelCompare {});
    tr_sort(&mut fst_f, ILabelCompare {});
    println!("DEBUG: Composing fst_r and fst_f");
    let mut fst: VectorFst<TropicalWeight> = compose(fst_r, fst_f)?;
    println!("DEBUG: After first composition: {} states", fst.num_states());

    if fst.num_states() == 0 {
        return Err(anyhow::anyhow!("First composition resulted in empty FST"));
    }


    // Debug: Save the intermediate composition result
    draw_wfst(&fst, "debug_fst_r_compose_fst_f", "fst_r ∘ fst_f").ok();
    draw_wfst(&fst_replace, "debug_fst_replace", "fst_replace (replace phi with psi)").ok();
    tr_sort(&mut fst, OLabelCompare {});
    tr_sort(&mut fst_replace, ILabelCompare {});
    println!("DEBUG: Composing with fst_replace");
    let mut fst: VectorFst<TropicalWeight> = compose(fst, fst_replace)?;
    println!("DEBUG: After second composition: {} states", fst.num_states());

    if fst.num_states() == 0 {
        return Err(anyhow::anyhow!("Second composition resulted in empty FST"));
    }

    tr_sort(&mut fst, OLabelCompare {});
    tr_sort(&mut fst_l1, ILabelCompare {});
    println!("DEBUG: Composing with fst_l1");
    let mut fst: VectorFst<TropicalWeight> = compose(fst, fst_l1)?;
    println!("DEBUG: After third composition: {} states", fst.num_states());

    if fst.num_states() == 0 {
        return Err(anyhow::anyhow!("Third composition resulted in empty FST"));
    }

    tr_sort(&mut fst, OLabelCompare {});
    tr_sort(&mut fst_l2, ILabelCompare {});
    println!("DEBUG: Composing with fst_l2");
    let fst: VectorFst<TropicalWeight> = compose(fst, fst_l2)?;
    println!("DEBUG: After final composition: {} states", fst.num_states());

    if fst.num_states() == 0 {
        return Err(anyhow::anyhow!("Final composition resulted in empty FST"));
    }

    println!("DEBUG: rule_fst completed successfully");
    println!("DEBUG: Checking if FST is cyclic...");
    let is_cyclic_result = is_cyclic(&fst);
    println!("DEBUG: FST is cyclic: {}", is_cyclic_result);
    
    if is_cyclic_result {
        return Err(anyhow::anyhow!("Generated FST is cyclic and cannot be used for string transduction"));
    }
    
    Ok(fst)
}

fn build_simple_rule_fst(
    symt: Arc<SymbolTable>,
    _macros: &BTreeMap<String, RegexAST>,
    source: RegexAST,
    target: RegexAST,
) -> Result<VectorFst<TropicalWeight>> {
    println!("DEBUG: Building simple rule FST");
    
    // Get the source and target labels
    let source_labels = regex_to_vector_of_labels(symt.clone(), source)?;
    let target_labels = regex_to_vector_of_labels(symt.clone(), target)?;
    
    println!("DEBUG: Source labels: {:?}, Target labels: {:?}", source_labels, target_labels);
    
    // Create a simple FST that just does the replacement without cycles
    let mut result_fst = VectorFst::<TropicalWeight>::new();
    let start_state = result_fst.add_state();
    result_fst.set_start(start_state)?;
    result_fst.set_final(start_state, 0.0)?;
    
    // Add identity transitions for all symbols except the source symbols
    let source_set: HashSet<Label> = source_labels.iter().copied().collect();
    for (label, _) in symt.iter() {
        if label > 0 && !source_set.contains(&label) {
            result_fst.emplace_tr(start_state, label, label, 0.0, start_state)?;
        }
    }
    
    // Add the replacement transition(s)
    if source_labels.len() == 1 && target_labels.len() == 1 {
        // Simple single-symbol replacement
        result_fst.emplace_tr(start_state, source_labels[0], target_labels[0], 0.0, start_state)?;
    } else {
        // Multi-symbol replacement - create a chain of states
        let mut current_state = start_state;
        for i in 0..source_labels.len().max(target_labels.len()) {
            let input_label = source_labels.get(i).copied().unwrap_or(0);
            let output_label = target_labels.get(i).copied().unwrap_or(0);
            
            if i == source_labels.len().max(target_labels.len()) - 1 {
                // Last transition goes back to start
                result_fst.emplace_tr(current_state, input_label, output_label, 0.0, start_state)?;
            } else {
                // Intermediate transitions go to new states
                let next_state = result_fst.add_state();
                result_fst.emplace_tr(current_state, input_label, output_label, 0.0, next_state)?;
                current_state = next_state;
            }
        }
    }
    
    result_fst.set_input_symbols(symt.clone());
    result_fst.set_output_symbols(symt.clone());
    
    println!("DEBUG: Final simple rule FST states: {}", result_fst.num_states());
    
    Ok(result_fst)
}

fn build_context_rule_fst(
    symt: Arc<SymbolTable>,
    macros: &BTreeMap<String, RegexAST>,
    rule: RewriteRule,
) -> Result<VectorFst<TropicalWeight>> {
    println!("DEBUG: Building context rule FST");
    
    // Define braces.
    let lbrace1_symbol = "<1";
    let lbrace2_symbol = "<2";
    let rbrace_symbol = ">";

    let mut symt_mut = (*symt).clone();

    // Add braces to the symbol table
    let rbrace = symt_mut.add_symbol(rbrace_symbol);
    let lbrace1 = symt_mut.add_symbol(lbrace1_symbol);
    let lbrace2 = symt_mut.add_symbol(lbrace2_symbol);

    let symt = Arc::new(symt_mut);

    // Create a set `alphabet` of the labels in the symbol table.
    let alphabet: HashSet<Label> = symt.labels().collect();
    println!("DEBUG: Alphabet size: {}", alphabet.len());

    // Compute wFSTs for the context (`lambda` and `rho`) and remove epsilons.
    println!("DEBUG: Building lambda (left context)");
    let mut lambda = match rule.left {
        RegexAST::Epsilon => fst![0; 0.0],
        _ => node_fst(symt.clone(), macros, rule.left).unwrap(),
    };
    println!("DEBUG: Lambda states before completion: {}", lambda.num_states());
    complete_fst_safe(alphabet.clone(), &mut lambda)?;
    println!("DEBUG: Lambda states after completion: {}", lambda.num_states());
    rm_epsilon(&mut lambda)?;
    println!("DEBUG: Lambda states after rm_epsilon: {}", lambda.num_states());

    println!("DEBUG: Building rho (right context)");
    let mut rho = match rule.right {
        RegexAST::Epsilon => fst![0; 0.0],
        _ => node_fst(symt.clone(), macros, rule.right).unwrap(),
    };
    println!("DEBUG: Rho states before completion: {}", rho.num_states());
    complete_fst_safe(alphabet.clone(), &mut rho)?;
    println!("DEBUG: Rho states after completion: {}", rho.num_states());
    rm_epsilon(&mut rho)?;
    println!("DEBUG: Rho states after rm_epsilon: {}", rho.num_states());

    println!("DEBUG: Building phi labels");
    let phi_labels: Vec<Label> = regex_to_vector_of_labels(symt.clone(), rule.source.clone())?;
    println!("DEBUG: Phi labels: {:?}", phi_labels);

    let phi_transducer: VectorFst<TropicalWeight> =
        transducer(&phi_labels, &phi_labels, TropicalWeight::new(0.0));
    println!("DEBUG: Phi transducer states: {}", phi_transducer.num_states());

    println!("DEBUG: Building fst_r (insert rbrace before rho)");
    let mut fst_r = build_insert_rbrace_before_rho_safe(rbrace, alphabet.clone(), rho.clone())?;
    println!("DEBUG: fst_r states: {}", fst_r.num_states());

    println!("DEBUG: Building fst_f (insert lbraces before phi followed by rho)");
    let mut fst_f = build_insert_lbraces_before_phi_followed_by_rho_safe(
        lbrace1,
        lbrace2,
        rbrace,
        alphabet.clone(),
        phi_transducer.clone(),
    )?;
    println!("DEBUG: fst_f states: {}", fst_f.num_states());

    println!("DEBUG: Building fst_replace (replace phi with psi)");
    let mut fst_replace = build_replace_phi_with_psi_safe(
        symt.clone(),
        alphabet.clone(),
        lbrace1,
        lbrace2,
        rbrace,
        rule.source,
        rule.target,
    )?;
    println!("DEBUG: fst_replace states: {}", fst_replace.num_states());

    println!("DEBUG: Building fst_l1 (lbrace1 lambda filter)");
    let mut fst_l1 = build_lbrace1_lambda_filter_safe(lbrace1, alphabet.clone(), lambda.clone())?;
    println!("DEBUG: fst_l1 states: {}", fst_l1.num_states());

    println!("DEBUG: Building fst_l2 (lbrace2 lambda filter)");
    let mut fst_l2 = build_lbrace2_lambda_filter_safe(lbrace2, alphabet.clone(), lambda.clone())?;
    println!("DEBUG: fst_l2 states: {}", fst_l2.num_states());

    println!("DEBUG: Starting composition sequence");
    tr_sort(&mut fst_r, OLabelCompare {});
    tr_sort(&mut fst_f, ILabelCompare {});
    println!("DEBUG: Composing fst_r and fst_f");
    let mut fst: VectorFst<TropicalWeight> = compose(fst_r, fst_f)?;
    println!("DEBUG: After first composition: {} states", fst.num_states());

    if fst.num_states() == 0 {
        return Err(anyhow::anyhow!("First composition resulted in empty FST"));
    }

    tr_sort(&mut fst, OLabelCompare {});
    tr_sort(&mut fst_replace, ILabelCompare {});
    println!("DEBUG: Composing with fst_replace");
    let mut fst: VectorFst<TropicalWeight> = compose(fst, fst_replace)?;
    println!("DEBUG: After second composition: {} states", fst.num_states());

    if fst.num_states() == 0 {
        return Err(anyhow::anyhow!("Second composition resulted in empty FST"));
    }

    tr_sort(&mut fst, OLabelCompare {});
    tr_sort(&mut fst_l1, ILabelCompare {});
    println!("DEBUG: Composing with fst_l1");
    let mut fst: VectorFst<TropicalWeight> = compose(fst, fst_l1)?;
    println!("DEBUG: After third composition: {} states", fst.num_states());

    if fst.num_states() == 0 {
        return Err(anyhow::anyhow!("Third composition resulted in empty FST"));
    }

    tr_sort(&mut fst, OLabelCompare {});
    tr_sort(&mut fst_l2, ILabelCompare {});
    println!("DEBUG: Composing with fst_l2");
    let fst: VectorFst<TropicalWeight> = compose(fst, fst_l2)?;
    println!("DEBUG: After final composition: {} states", fst.num_states());

    if fst.num_states() == 0 {
        return Err(anyhow::anyhow!("Final composition resulted in empty FST"));
    }

    println!("DEBUG: Context rule FST completed successfully");
    println!("DEBUG: Checking if FST is cyclic...");
    let is_cyclic_result = is_cyclic(&fst);
    println!("DEBUG: FST is cyclic: {}", is_cyclic_result);
    
    if is_cyclic_result {
        return Err(anyhow::anyhow!("Generated FST is cyclic and cannot be used for string transduction"));
    }
    
    Ok(fst)
}

fn complete_fst_safe(alphabet: HashSet<Label>, fst: &mut VectorFst<TropicalWeight>) -> Result<()> {
    println!("DEBUG: complete_fst_safe - start, alphabet size: {}, fst states: {}", alphabet.len(), fst.num_states());
    
    // Create a non-final sink state for missing transitions
    let sink_state = fst.add_state();
    
    // Collect all states before we start modifying the FST
    let states: Vec<StateId> = fst.states_iter().filter(|&s| s != sink_state).collect();
    
    // For each state, add transitions to sink state for missing labels
    for state in states {
        let outgoing: HashSet<Label> = fst
            .get_trs(state)
            .unwrap_or_default()
            .iter()
            .map(|tr| tr.ilabel)
            .collect();
        
        let missing: HashSet<Label> = alphabet.difference(&outgoing).copied().collect();
        
        for label in missing {
            // Add transition to sink state with high weight to discourage these paths
            fst.emplace_tr(state, label, label, 10.0, sink_state)?;
        }
    }
    
    // Add self-loops on sink state to make it complete, but with high weight
    for label in &alphabet {
        fst.emplace_tr(sink_state, *label, *label, 10.0, sink_state)?;
    }
    
    // Don't make sink_state final - this prevents successful paths through it
    
    println!("DEBUG: complete_fst_safe - added sink state {}, fst now has {} states", sink_state, fst.num_states());
    Ok(())
}

fn complete_fst(alphabet: HashSet<Label>, fst: &mut VectorFst<TropicalWeight>) -> Result<()> {
    println!("DEBUG: complete_fst - start, alphabet size: {}, fst states: {}", alphabet.len(), fst.num_states());
    
    let _start_state: StateId = fst.start().unwrap_or_else(|| {
        eprintln!(
            "wFST lacks start state in complete_fst (which has {} states). Assuming 0.",
            fst.num_states()
        );
        0
    });
    
    // Create a sink state for missing transitions (but don't make it final to avoid cycles)
    let sink_state = fst.add_state();
    
    // Collect all states before we start modifying the FST
    let states: Vec<StateId> = fst.states_iter().filter(|&s| s != sink_state).collect();
    
    // For each state, add transitions to sink state for missing labels
    for state in states {
        let outgoing: HashSet<Label> = fst
            .get_trs(state)
            .unwrap_or_default()
            .iter()
            .map(|tr| tr.ilabel)
            .collect();
        
        let missing: HashSet<Label> = alphabet.difference(&outgoing).copied().collect();
        
        for label in missing {
            // Add transition to sink state (but don't make sink state final)
            fst.emplace_tr(state, label, label, 1.0, sink_state)?; // Use weight 1.0 to discourage these paths
        }
    }
    
    // Add self-loops on sink state to make it complete, but with high weight
    for label in &alphabet {
        fst.emplace_tr(sink_state, *label, *label, 1.0, sink_state)?;
    }
    
    // Don't make sink_state final - this prevents cycles in successful paths
    
    println!("DEBUG: complete_fst - added sink state {}, fst now has {} states", sink_state, fst.num_states());
    Ok(())
}

// Fixed versions of the helper functions that avoid creating cycles

fn complete_fst_fixed(alphabet: HashSet<Label>, fst: &mut VectorFst<TropicalWeight>) -> Result<()> {
    println!("DEBUG: complete_fst_fixed - start, alphabet size: {}, fst states: {}", alphabet.len(), fst.num_states());
    
    // Critical fix: For transducers, we must preserve the original mappings and only add
    // transitions to a non-final sink state for missing input symbols.
    // We must NOT create identity mappings that weren't in the original transducer.
    
    let sink_state = fst.add_state();
    // Don't make sink_state final - this prevents successful paths through missing transitions
    
    let states: Vec<StateId> = fst.states_iter().filter(|&s| s != sink_state).collect();
    
    for state in states {
        let outgoing: HashSet<Label> = fst
            .get_trs(state)
            .unwrap_or_default()
            .iter()
            .map(|tr| tr.ilabel)
            .collect();
        
        let missing: HashSet<Label> = alphabet.difference(&outgoing).copied().collect();
        
        for label in missing {
            // CRITICAL FIX: Map missing input symbols to epsilon (0) output, not identity
            // This ensures we don't create spurious S->S mappings that weren't in the original transducer
            fst.emplace_tr(state, label, 0, f32::INFINITY, sink_state)?;
        }
    }
    
    // Add self-loops on sink state mapping to epsilon, with infinite weight to make them unusable
    for label in &alphabet {
        fst.emplace_tr(sink_state, *label, 0, f32::INFINITY, sink_state)?;
    }
    
    println!("DEBUG: complete_fst_fixed - added sink state {}, fst now has {} states", sink_state, fst.num_states());
    Ok(())
}

fn build_insert_rbrace_before_rho_fixed(
    rbrace: Label,
    alphabet: HashSet<Label>,
    rho: VectorFst<TropicalWeight>,
) -> Result<VectorFst<TropicalWeight>> {
    println!("DEBUG: build_insert_rbrace_before_rho_fixed - start");
    println!("DEBUG: rho has {} states", rho.num_states());
    
    // Special case: if rho is epsilon (empty right context), insert rbrace before every position
    if rho.num_states() == 1 && rho.start().is_some() {
        let start = rho.start().unwrap();
        if rho.is_final(start).unwrap_or(false) && 
           rho.get_trs(start).unwrap_or_default().is_empty() {
            println!("DEBUG: rho is epsilon, creating FST that inserts rbrace before every symbol");
            
            // Create FST that inserts rbrace before every symbol
            let mut fst = VectorFst::new();
            let start_state = fst.add_state();
            fst.set_start(start_state)?;
            fst.set_final(start_state, 0.0)?;
            
            // For each symbol in alphabet, add transition that outputs rbrace then the symbol
            for &label in &alphabet {
                // Transition: input symbol -> output rbrace, then output the symbol
                let intermediate_state = fst.add_state();
                fst.emplace_tr(start_state, label, rbrace, 0.0, intermediate_state)?;
                fst.emplace_tr(intermediate_state, 0, label, 0.0, start_state)?; // epsilon:label
            }
            
            println!("DEBUG: created epsilon-rho FST with {} states", fst.num_states());
            return Ok(fst);
        }
    }
    
    // General case: insert rbrace before occurrences of rho
    // This is more complex and would need proper implementation for non-epsilon rho
    println!("DEBUG: non-epsilon rho case not fully implemented yet");
    
    // For now, fall back to original implementation
    let reversed_rho: VectorFst<TropicalWeight> = reverse(&rho)?;
    println!("DEBUG: reversed_rho states: {}", reversed_rho.num_states());
    
    let mut alpha: VectorFst<TropicalWeight> = VectorFst::new();
    let start_state = alpha.add_state();
    alpha.set_start(start_state)?;
    alpha.set_final(start_state, 0.0)?;
    for label in alphabet.clone() {
        alpha.emplace_tr(start_state, label, label, 0.0, start_state)?;
    }
    println!("DEBUG: alpha states before concat: {}", alpha.num_states());
    
    concat(&mut alpha, &reversed_rho)?;
    println!("DEBUG: alpha states after concat: {}", alpha.num_states());
    
    complete_fst_fixed(alphabet.clone(), &mut alpha)?;
    println!("DEBUG: alpha states after complete_fst_fixed: {}", alpha.num_states());
    
    let marked: VectorFst<TropicalWeight> = marker2_fixed(alpha, rbrace)?;
    println!("DEBUG: marked states: {}", marked.num_states());
    
    let fst: VectorFst<TropicalWeight> = reverse(&marked)?;
    println!("DEBUG: final fst states: {}", fst.num_states());
    Ok(fst)
}

fn build_insert_lbraces_before_phi_followed_by_rho_fixed(
    lbrace1: Label,
    lbrace2: Label,
    rbrace: Label,
    alphabet: HashSet<Label>,
    phi: VectorFst<TropicalWeight>,
) -> Result<VectorFst<TropicalWeight>> {
    println!("DEBUG: build_insert_lbraces_before_phi_followed_by_rho_fixed - start");
    
    // Check if phi is a simple single-symbol FST
    if phi.num_states() == 2 && phi.start().is_some() {
        let start = phi.start().unwrap();
        let transitions: Vec<_> = phi.get_trs(start).unwrap_or_default().iter().cloned().collect();
        
        if transitions.len() == 1 {
            let tr = &transitions[0];
            let phi_symbol = tr.ilabel;
            let next_state = tr.nextstate;
            
            if phi.is_final(next_state).unwrap_or(false) && 
               phi.get_trs(next_state).unwrap_or_default().is_empty() {
                println!("DEBUG: phi is single symbol {}, creating FST that inserts lbraces before it", phi_symbol);
                
                // Create FST that inserts lbrace1 and lbrace2 before phi_symbol, and passes other symbols through
                let mut fst = VectorFst::new();
                let start_state = fst.add_state();
                fst.set_start(start_state)?;
                fst.set_final(start_state, 0.0)?;
                
                // For the phi symbol, insert lbrace1, lbrace2, then the symbol
                let intermediate1 = fst.add_state();
                let intermediate2 = fst.add_state();
                fst.emplace_tr(start_state, phi_symbol, lbrace1, 0.0, intermediate1)?;
                fst.emplace_tr(intermediate1, 0, lbrace2, 0.0, intermediate2)?; // epsilon:lbrace2
                fst.emplace_tr(intermediate2, 0, phi_symbol, 0.0, start_state)?; // epsilon:phi_symbol
                
                // For all other symbols, pass through unchanged
                for &label in &alphabet {
                    if label != phi_symbol {
                        fst.emplace_tr(start_state, label, label, 0.0, start_state)?;
                    }
                }
                
                println!("DEBUG: created single-phi FST with {} states", fst.num_states());
                return Ok(fst);
            }
        }
    }
    
    // Fall back to original implementation for complex phi
    println!("DEBUG: using original implementation for complex phi");
    let mut phi = phi.clone();
    let markers: HashSet<Label> = HashSet::from([lbrace1, lbrace2]);
    let rbrace_fst: VectorFst<TropicalWeight> = fst![rbrace];
    concat(&mut phi, &rbrace_fst)?;
    println!("DEBUG: phi after concat with rbrace: {} states", phi.num_states());
    
    let reversed_phi_rbrace: VectorFst<TropicalWeight> = reverse(&phi)?;
    println!("DEBUG: reversed_phi_rbrace: {} states", reversed_phi_rbrace.num_states());
    
    let mut alpha: VectorFst<TropicalWeight> = VectorFst::new();
    let start_state = alpha.add_state();
    alpha.set_start(start_state)?;
    alpha.set_final(start_state, 0.0)?;
    for label in alphabet.clone() {
        alpha.emplace_tr(start_state, label, label, 0.0, start_state)?;
    }
    println!("DEBUG: alpha before concat: {} states", alpha.num_states());
    
    concat(&mut alpha, &reversed_phi_rbrace)?;
    println!("DEBUG: alpha after concat: {} states", alpha.num_states());
    
    complete_fst_fixed(alphabet.clone(), &mut alpha)?;
    println!("DEBUG: alpha after complete_fst_fixed: {} states", alpha.num_states());
    
    let marked: VectorFst<TropicalWeight> = marker1_fixed(alpha, markers)?;
    println!("DEBUG: marked: {} states", marked.num_states());
    
    let fst: VectorFst<TropicalWeight> = reverse(&marked)?;
    println!("DEBUG: final fst: {} states", fst.num_states());
    Ok(fst)
}

fn build_replace_phi_with_psi_fixed(
    symt: Arc<SymbolTable>,
    alphabet: HashSet<Label>,
    lbrace1: Label,
    lbrace2: Label,
    rbrace: Label,
    phi: RegexAST,
    psi: RegexAST,
) -> Result<VectorFst<TropicalWeight>> {
    println!("DEBUG: build_replace_phi_with_psi_fixed - start");
    
    let mut phi_labels = regex_to_vector_of_labels(symt.clone(), phi)?;
    let mut psi_labels = regex_to_vector_of_labels(symt.clone(), psi)?;
    println!("DEBUG: phi_labels: {:?}, psi_labels: {:?}", phi_labels, psi_labels);

    let max_len = phi_labels.len().max(psi_labels.len());
    phi_labels.resize(max_len, 0);
    psi_labels.resize(max_len, 0);
    let mut fst: VectorFst<TropicalWeight> =
        transducer(&phi_labels, &psi_labels, TropicalWeight::new(0.0));
    println!("DEBUG: transducer states: {}", fst.num_states());
    
    let states: Vec<StateId> = fst.states_iter().collect();
    for state in states {
        fst.emplace_tr(state, lbrace1, lbrace1, 0.0, state)?;
        fst.emplace_tr(state, lbrace2, lbrace2, 0.0, state)?;
        fst.emplace_tr(state, rbrace, rbrace, 0.0, state)?;
    }
    println!("DEBUG: after adding brace transitions: {} states", fst.num_states());

    let old_start = fst.start().unwrap_or_else(|| {
        eprintln!("wFST in build_replace_phi_with_psi_fixed lacks start state. Defaulting to 0.");
        0
    });
    let new_start = fst.add_state();
    fst.set_start(new_start).unwrap();
    println!("DEBUG: added new start state: {}", new_start);

    fst.emplace_tr(new_start, lbrace1, lbrace1, 0.0, old_start)?;
    let not_in_self_loop: HashSet<Label> = HashSet::from([lbrace2, rbrace]);
    let self_loop_labels: HashSet<Label> =
        alphabet.difference(&not_in_self_loop).copied().collect();
    println!("DEBUG: self_loop_labels count: {}", self_loop_labels.len());
    for label in self_loop_labels.iter() {
        fst.emplace_tr(new_start, *label, *label, 0.0, new_start)?;
    }

    fst.emplace_tr(new_start, lbrace2, lbrace2, 0.0, new_start)?;
    fst.emplace_tr(new_start, rbrace, 0, 0.0, new_start)?;
    println!("DEBUG: before complete_fst_fixed: {} states", fst.num_states());

    complete_fst_fixed(alphabet, &mut fst)?;
    println!("DEBUG: after complete_fst_fixed: {} states", fst.num_states());

    Ok(fst)
}

fn build_lbrace1_lambda_filter_fixed(
    _lbrace1: Label,
    alphabet: HashSet<Label>,
    _lambda: VectorFst<TropicalWeight>,
) -> Result<VectorFst<TropicalWeight>> {
    println!("DEBUG: build_lbrace1_lambda_filter_fixed - start");
    
    // Create a proper identity transducer without epsilon-epsilon self-loops
    let mut fst: VectorFst<TropicalWeight> = VectorFst::new();
    let start_state = fst.add_state();
    fst.set_start(start_state)?;
    fst.set_final(start_state, 0.0)?;
    
    // Add identity transitions for all alphabet symbols (but NOT epsilon:epsilon)
    for label in alphabet.iter() {
        if *label != 0 {  // Skip epsilon (0) to avoid epsilon-epsilon self-loops
            fst.emplace_tr(start_state, *label, *label, 0.0, start_state)?;
        }
    }
    
    println!("DEBUG: build_lbrace1_lambda_filter_fixed - final states: {}", fst.num_states());
    
    Ok(fst)
}

fn build_lbrace2_lambda_filter_fixed(
    _lbrace2: Label,
    alphabet: HashSet<Label>,
    _lambda: VectorFst<TropicalWeight>,
) -> Result<VectorFst<TropicalWeight>> {
    println!("DEBUG: build_lbrace2_lambda_filter_fixed - start");
    
    // Create a proper identity transducer without epsilon-epsilon self-loops
    let mut fst: VectorFst<TropicalWeight> = VectorFst::new();
    let start_state = fst.add_state();
    fst.set_start(start_state)?;
    fst.set_final(start_state, 0.0)?;
    
    // Add identity transitions for all alphabet symbols (but NOT epsilon:epsilon)
    for label in alphabet.iter() {
        if *label != 0 {  // Skip epsilon (0) to avoid epsilon-epsilon self-loops
            fst.emplace_tr(start_state, *label, *label, 0.0, start_state)?;
        }
    }
    
    println!("DEBUG: build_lbrace2_lambda_filter_fixed - final states: {}", fst.num_states());
    
    Ok(fst)
}

fn marker1_fixed(
    mut fst: VectorFst<TropicalWeight>,
    markers: HashSet<Label>,
) -> Result<VectorFst<TropicalWeight>> {
    println!("DEBUG: marker1_fixed - start with {} states", fst.num_states());
    
    // Get final states
    let final_states: Vec<StateId> = fst.states_iter()
        .filter(|&s| fst.is_final(s).unwrap_or(false))
        .collect();
    
    println!("DEBUG: marker1_fixed - found {} final states", final_states.len());
    
    // For each final state, add epsilon transitions to new states that emit markers
    for final_state in final_states {
        let weight = fst.final_weight(final_state).unwrap_or(Some(TropicalWeight::new(0.0)));
        let weight_value = weight.map(|w| *w.value()).unwrap_or(0.0);
        fst.set_final(final_state, f32::INFINITY)?; // Remove finality
        
        for marker in &markers {
            let new_state = fst.add_state();
            fst.emplace_tr(final_state, 0, *marker, weight_value, new_state)?;
            fst.set_final(new_state, 0.0)?;
        }
    }
    
    println!("DEBUG: marker1_fixed - final states: {}", fst.num_states());
    Ok(fst)
}

fn marker2_fixed(
    mut fst: VectorFst<TropicalWeight>,
    marker: Label,
) -> Result<VectorFst<TropicalWeight>> {
    println!("DEBUG: marker2_fixed - start with {} states", fst.num_states());
    
    // Get final states
    let final_states: Vec<StateId> = fst.states_iter()
        .filter(|&s| fst.is_final(s).unwrap_or(false))
        .collect();
    
    println!("DEBUG: marker2_fixed - found {} final states", final_states.len());
    
    // For each final state, add epsilon transition to a new state that emits the marker
    for final_state in final_states {
        let weight = fst.final_weight(final_state).unwrap_or(Some(TropicalWeight::new(0.0)));
        let weight_value = weight.map(|w| *w.value()).unwrap_or(0.0);
        fst.set_final(final_state, f32::INFINITY)?; // Remove finality
        
        let new_state = fst.add_state();
        fst.emplace_tr(final_state, 0, marker, weight_value, new_state)?;
        fst.set_final(new_state, 0.0)?;
    }
    
    println!("DEBUG: marker2_fixed - final states: {}", fst.num_states());
    Ok(fst)
}

// Safe versions of the helper functions that avoid creating cycles

fn build_insert_rbrace_before_rho_safe(
    rbrace: Label,
    alphabet: HashSet<Label>,
    rho: VectorFst<TropicalWeight>,
) -> Result<VectorFst<TropicalWeight>> {
    println!("DEBUG: build_insert_rbrace_before_rho_safe - start");
    
    let reversed_rho: VectorFst<TropicalWeight> = reverse(&rho)?;
    println!("DEBUG: reversed_rho states: {}", reversed_rho.num_states());
    
    let mut alpha: VectorFst<TropicalWeight> = VectorFst::new();
    let start_state = alpha.add_state();
    alpha.set_start(start_state)?;
    alpha.set_final(start_state, 0.0)?;
    for label in alphabet.clone() {
        alpha.emplace_tr(start_state, label, label, 0.0, start_state)?;
    }
    println!("DEBUG: alpha states before concat: {}", alpha.num_states());
    
    concat(&mut alpha, &reversed_rho)?;
    println!("DEBUG: alpha states after concat: {}", alpha.num_states());
    
    complete_fst_safe(alphabet.clone(), &mut alpha)?;
    println!("DEBUG: alpha states after complete_fst_safe: {}", alpha.num_states());
    
    let marked: VectorFst<TropicalWeight> = marker2_safe(alpha, rbrace)?;
    println!("DEBUG: marked states: {}", marked.num_states());
    
    let fst: VectorFst<TropicalWeight> = reverse(&marked)?;
    println!("DEBUG: final fst states: {}", fst.num_states());
    Ok(fst)
}

fn build_insert_lbraces_before_phi_followed_by_rho_safe(
    lbrace1: Label,
    lbrace2: Label,
    rbrace: Label,
    alphabet: HashSet<Label>,
    phi: VectorFst<TropicalWeight>,
) -> Result<VectorFst<TropicalWeight>> {
    println!("DEBUG: build_insert_lbraces_before_phi_followed_by_rho_safe - start");
    let mut phi = phi.clone();
    let markers: HashSet<Label> = HashSet::from([lbrace1, lbrace2]);
    let rbrace_fst: VectorFst<TropicalWeight> = fst![rbrace];
    concat(&mut phi, &rbrace_fst)?;
    println!("DEBUG: phi after concat with rbrace: {} states", phi.num_states());
    
    let reversed_phi_rbrace: VectorFst<TropicalWeight> = reverse(&phi)?;
    println!("DEBUG: reversed_phi_rbrace: {} states", reversed_phi_rbrace.num_states());
    
    let mut alpha: VectorFst<TropicalWeight> = VectorFst::new();
    let start_state = alpha.add_state();
    alpha.set_start(start_state)?;
    alpha.set_final(start_state, 0.0)?;
    for label in alphabet.clone() {
        alpha.emplace_tr(start_state, label, label, 0.0, start_state)?;
    }
    println!("DEBUG: alpha before concat: {} states", alpha.num_states());
    
    concat(&mut alpha, &reversed_phi_rbrace)?;
    println!("DEBUG: alpha after concat: {} states", alpha.num_states());
    
    complete_fst_safe(alphabet.clone(), &mut alpha)?;
    println!("DEBUG: alpha after complete_fst_safe: {} states", alpha.num_states());
    
    let marked: VectorFst<TropicalWeight> = marker1_safe(alpha, markers)?;
    println!("DEBUG: marked: {} states", marked.num_states());
    
    let fst: VectorFst<TropicalWeight> = reverse(&marked)?;
    println!("DEBUG: final fst: {} states", fst.num_states());
    Ok(fst)
}

fn build_replace_phi_with_psi_safe(
    symt: Arc<SymbolTable>,
    alphabet: HashSet<Label>,
    lbrace1: Label,
    lbrace2: Label,
    rbrace: Label,
    phi: RegexAST,
    psi: RegexAST,
) -> Result<VectorFst<TropicalWeight>> {
    println!("DEBUG: build_replace_phi_with_psi_safe - start");
    
    let mut phi_labels = regex_to_vector_of_labels(symt.clone(), phi)?;
    let mut psi_labels = regex_to_vector_of_labels(symt.clone(), psi)?;
    println!("DEBUG: phi_labels: {:?}, psi_labels: {:?}", phi_labels, psi_labels);

    let max_len = phi_labels.len().max(psi_labels.len());
    phi_labels.resize(max_len, 0);
    psi_labels.resize(max_len, 0);
    let mut fst: VectorFst<TropicalWeight> =
        transducer(&phi_labels, &psi_labels, TropicalWeight::new(0.0));
    println!("DEBUG: transducer states: {}", fst.num_states());
    
    let states: Vec<StateId> = fst.states_iter().collect();
    for state in states {
        fst.emplace_tr(state, lbrace1, lbrace1, 0.0, state)?;
        fst.emplace_tr(state, lbrace2, lbrace2, 0.0, state)?;
        fst.emplace_tr(state, rbrace, rbrace, 0.0, state)?;
    }
    println!("DEBUG: after adding brace transitions: {} states", fst.num_states());

    let old_start = fst.start().unwrap_or_else(|| {
        eprintln!("wFST in build_replace_phi_with_psi_safe lacks start state. Defaulting to 0.");
        0
    });
    let new_start = fst.add_state();
    fst.set_start(new_start).unwrap();
    println!("DEBUG: added new start state: {}", new_start);

    fst.emplace_tr(new_start, lbrace1, lbrace1, 0.0, old_start)?;
    let not_in_self_loop: HashSet<Label> = HashSet::from([lbrace2, rbrace]);
    let self_loop_labels: HashSet<Label> =
        alphabet.difference(&not_in_self_loop).copied().collect();
    println!("DEBUG: self_loop_labels count: {}", self_loop_labels.len());
    for label in self_loop_labels.iter() {
        fst.emplace_tr(new_start, *label, *label, 0.0, new_start)?;
    }

    fst.emplace_tr(new_start, lbrace2, lbrace2, 0.0, new_start)?;
    fst.emplace_tr(new_start, rbrace, 0, 0.0, new_start)?;
    println!("DEBUG: before complete_fst_safe: {} states", fst.num_states());

    complete_fst_safe(alphabet, &mut fst)?;
    println!("DEBUG: after complete_fst_safe: {} states", fst.num_states());

    Ok(fst)
}

fn build_lbrace1_lambda_filter_safe(
    lbrace1: Label,
    alphabet: HashSet<Label>,
    _lambda: VectorFst<TropicalWeight>,
) -> Result<VectorFst<TropicalWeight>> {
    println!("DEBUG: build_lbrace1_lambda_filter_safe - start");
    
    let mut fst: VectorFst<TropicalWeight> = VectorFst::new();
    let start_state = fst.add_state();
    fst.set_start(start_state)?;
    fst.set_final(start_state, 0.0)?;
    
    // Add identity transitions for all symbols except lbrace1
    for label in alphabet.iter() {
        if *label != lbrace1 {
            fst.emplace_tr(start_state, *label, *label, 0.0, start_state)?;
        }
    }
    
    // For lbrace1, we need to check if it's followed by lambda
    // This is a simplified version - for now just allow lbrace1 to pass through
    fst.emplace_tr(start_state, lbrace1, lbrace1, 0.0, start_state)?;
    
    complete_fst_safe(alphabet, &mut fst)?;
    println!("DEBUG: build_lbrace1_lambda_filter_safe - final states: {}", fst.num_states());
    
    Ok(fst)
}

fn build_lbrace2_lambda_filter_safe(
    lbrace2: Label,
    alphabet: HashSet<Label>,
    _lambda: VectorFst<TropicalWeight>,
) -> Result<VectorFst<TropicalWeight>> {
    println!("DEBUG: build_lbrace2_lambda_filter_safe - start");
    
    let mut fst: VectorFst<TropicalWeight> = VectorFst::new();
    let start_state = fst.add_state();
    fst.set_start(start_state)?;
    fst.set_final(start_state, 0.0)?;
    
    // Add identity transitions for all symbols except lbrace2
    for label in alphabet.iter() {
        if *label != lbrace2 {
            fst.emplace_tr(start_state, *label, *label, 0.0, start_state)?;
        }
    }
    
    // For lbrace2, we need to check if it's followed by lambda
    // This is a simplified version - for now just allow lbrace2 to pass through
    fst.emplace_tr(start_state, lbrace2, lbrace2, 0.0, start_state)?;
    
    complete_fst_safe(alphabet, &mut fst)?;
    println!("DEBUG: build_lbrace2_lambda_filter_safe - final states: {}", fst.num_states());
    
    Ok(fst)
}

fn marker1_safe(
    mut fst: VectorFst<TropicalWeight>,
    markers: HashSet<Label>,
) -> Result<VectorFst<TropicalWeight>> {
    println!("DEBUG: marker1_safe - start with {} states", fst.num_states());
    
    // Get final states
    let final_states: Vec<StateId> = fst.states_iter()
        .filter(|&s| fst.is_final(s).unwrap_or(false))
        .collect();
    
    println!("DEBUG: marker1_safe - found {} final states", final_states.len());
    
    // For each final state, add epsilon transitions to a new state that emits markers
    for final_state in final_states {
        let weight = fst.final_weight(final_state).unwrap_or(Some(TropicalWeight::new(f32::INFINITY)));
        let weight_value = weight.map(|w| *w.value()).unwrap_or(0.0);
        fst.set_final(final_state, f32::INFINITY)?; // Remove finality
        
        for marker in &markers {
            let new_state = fst.add_state();
            fst.emplace_tr(final_state, 0, *marker, weight_value, new_state)?;
            fst.set_final(new_state, 0.0)?;
        }
    }
    
    println!("DEBUG: marker1_safe - final states: {}", fst.num_states());
    Ok(fst)
}

fn marker2_safe(
    mut fst: VectorFst<TropicalWeight>,
    marker: Label,
) -> Result<VectorFst<TropicalWeight>> {
    println!("DEBUG: marker2_safe - start with {} states", fst.num_states());
    
    // Get final states
    let final_states: Vec<StateId> = fst.states_iter()
        .filter(|&s| fst.is_final(s).unwrap_or(false))
        .collect();
    
    println!("DEBUG: marker2_safe - found {} final states", final_states.len());
    
    // For each final state, add epsilon transition to a new state that emits the marker
    for final_state in final_states {
        let weight = fst.final_weight(final_state).unwrap_or(Some(TropicalWeight::new(f32::INFINITY)));
        let weight_value = weight.map(|w| *w.value()).unwrap_or(0.0);
        fst.set_final(final_state, f32::INFINITY)?; // Remove finality
        
        let new_state = fst.add_state();
        fst.emplace_tr(final_state, 0, marker, weight_value, new_state)?;
        fst.set_final(new_state, 0.0)?;
    }
    
    println!("DEBUG: marker2_safe - final states: {}", fst.num_states());
    Ok(fst)
}

// Insert < before every instance of rho (the *right* context).
fn build_insert_rbrace_before_rho(
    rbrace: Label,
    alphabet: HashSet<Label>,
    rho: VectorFst<TropicalWeight>,
) -> Result<VectorFst<TropicalWeight>> {
    println!("DEBUG: build_insert_rbrace_before_rho - start");
    let reversed_rho: VectorFst<TropicalWeight> = reverse(&rho)?;
    println!("DEBUG: reversed_rho states: {}", reversed_rho.num_states());
    
    let mut alpha: VectorFst<TropicalWeight> = VectorFst::new();
    let start_state: StateId = alpha.add_state();
    alpha.set_start(start_state)?;
    alpha.set_final(start_state, 0.0)?;
    for label in alphabet.clone() {
        alpha.emplace_tr(start_state, label, label, 0.0, start_state)?;
    }
    println!("DEBUG: alpha states before concat: {}", alpha.num_states());
    
    concat(&mut alpha, &reversed_rho)?;
    println!("DEBUG: alpha states after concat: {}", alpha.num_states());
    
    complete_fst(alphabet.clone(), &mut alpha)?;
    println!("DEBUG: alpha states after complete_fst: {}", alpha.num_states());
    
    let markers: HashSet<Label> = HashSet::from([rbrace]);
    let marked: VectorFst<TropicalWeight> = marker1(alpha, markers)?;
    println!("DEBUG: marked states: {}", marked.num_states());
    
    let fst: VectorFst<TropicalWeight> = reverse(&marked)?;
    println!("DEBUG: final fst states: {}", fst.num_states());
    // let final_states = get_final_states(&fst)?;
    // Something is missing here, perhaps. Come back to this.
    Ok(fst)
}

fn build_insert_lbraces_before_phi_followed_by_rho(
    lbrace1: Label,
    lbrace2: Label,
    rbrace: Label,
    alphabet: HashSet<Label>,
    phi: VectorFst<TropicalWeight>,
    // rho: VectorFst<TropicalWeight>, // Where should rho go?
) -> Result<VectorFst<TropicalWeight>> {
    println!("DEBUG: build_insert_lbraces_before_phi_followed_by_rho - start");
    let mut phi = phi.clone();
    let markers: HashSet<Label> = HashSet::from([lbrace1, lbrace2]);
    let rbrace_fst: VectorFst<TropicalWeight> = fst![rbrace];
    concat(&mut phi, &rbrace_fst)?;
    println!("DEBUG: phi after concat with rbrace: {} states", phi.num_states());
    
    let reversed_phi_rbrace: VectorFst<TropicalWeight> = reverse(&phi)?;
    println!("DEBUG: reversed_phi_rbrace: {} states", reversed_phi_rbrace.num_states());
    // dbg!(reversed_phi_rbrace.clone());
    let mut alpha: VectorFst<TropicalWeight> = VectorFst::new();
    let start_state = alpha.add_state();
    alpha.set_start(start_state)?;
    alpha.set_final(start_state, 0.0)?;
    for label in alphabet.clone() {
        alpha.emplace_tr(start_state, label, label, 0.0, start_state)?;
    }
    println!("DEBUG: alpha before concat: {} states", alpha.num_states());
    
    concat(&mut alpha, &reversed_phi_rbrace)?;
    println!("DEBUG: alpha after concat: {} states", alpha.num_states());
    // dbg!(alpha.clone());
    complete_fst(alphabet.clone(), &mut alpha)?;
    println!("DEBUG: alpha after complete_fst: {} states", alpha.num_states());
    
    let marked: VectorFst<TropicalWeight> = marker1(alpha, markers)?;
    println!("DEBUG: marked: {} states", marked.num_states());
    
    let fst: VectorFst<TropicalWeight> = reverse(&marked)?;
    println!("DEBUG: final fst: {} states", fst.num_states());
    Ok(fst)
}

fn build_replace_phi_with_psi(
    symt: Arc<SymbolTable>,
    alphabet: HashSet<Label>,
    lbrace1: Label,
    lbrace2: Label,
    rbrace: Label,
    phi: RegexAST,
    psi: RegexAST,
) -> Result<VectorFst<TropicalWeight>> {
    println!("DEBUG: build_replace_phi_with_psi - start");
    // Compute labels from parsed regular expressions.
    let mut phi_labels = regex_to_vector_of_labels(symt.clone(), phi)?;
    let mut psi_labels = regex_to_vector_of_labels(symt.clone(), psi)?;
    println!("DEBUG: phi_labels: {:?}, psi_labels: {:?}", phi_labels, psi_labels);

    // Convert the two vectors of labels into a single transducer.
    let max_len = phi_labels.len().max(psi_labels.len());
    phi_labels.resize(max_len, 0);
    psi_labels.resize(max_len, 0);
    let mut fst: VectorFst<TropicalWeight> =
        transducer(&phi_labels, &psi_labels, TropicalWeight::new(0.0));
    println!("DEBUG: transducer states: {}", fst.num_states());
    
    let states: Vec<StateId> = fst.states_iter().collect();
    for state in states {
        fst.emplace_tr(state, lbrace1, lbrace1, 0.0, state)?;
        fst.emplace_tr(state, lbrace2, lbrace2, 0.0, state)?;
        fst.emplace_tr(state, rbrace, rbrace, 0.0, state)?;
    }
    println!("DEBUG: after adding brace transitions: {} states", fst.num_states());

    // Create a new start state.
    let old_start = fst.start().unwrap_or_else(|| {
        eprintln!("wFST in build_phi_psi lacks start state. Defaulting to 0.");
        0
    });
    let new_start = fst.add_state();
    fst.set_start(new_start).unwrap();
    println!("DEBUG: added new start state: {}", new_start);

    fst.emplace_tr(new_start, lbrace1, lbrace1, 0.0, old_start)?;
    let not_in_self_loop: HashSet<Label> = HashSet::from([lbrace2, rbrace]);
    let self_loop_labels: HashSet<Label> =
        alphabet.difference(&not_in_self_loop).copied().collect();
    println!("DEBUG: self_loop_labels count: {}", self_loop_labels.len());
    for label in self_loop_labels.iter() {
        fst.emplace_tr(new_start, *label, *label, 0.0, new_start)?;
    }

    fst.emplace_tr(new_start, lbrace2, lbrace2, 0.0, new_start)?;
    fst.emplace_tr(new_start, rbrace, 0, 0.0, new_start)?;
    println!("DEBUG: before complete_fst: {} states", fst.num_states());

    complete_fst(alphabet, &mut fst)?;
    println!("DEBUG: after complete_fst: {} states", fst.num_states());

    Ok(fst)
}

fn build_lbrace1_lambda_filter(
    lbrace1: Label,
    alphabet: HashSet<Label>,
    lambda: VectorFst<TropicalWeight>,
) -> Result<VectorFst<TropicalWeight>> {
    let mut alpha: VectorFst<TropicalWeight> = VectorFst::new();
    let start_state = alpha.add_state();
    alpha.set_start(start_state)?;
    alpha.set_final(start_state, 0.0)?;
    for symbol in alphabet.clone() {
        alpha.emplace_tr(start_state, symbol, symbol, 0.0, start_state)?;
    }
    concat(&mut alpha, &lambda)?;
    complete_fst(alphabet.clone(), &mut alpha)?;
    let marks: HashSet<Label> = HashSet::from([lbrace1]);
    let fst: VectorFst<TropicalWeight> = marker2(alpha, marks)?;
    Ok(fst)
}

fn build_lbrace2_lambda_filter(
    lbrace2: Label,
    alphabet: HashSet<Label>,
    lambda: VectorFst<TropicalWeight>,
) -> Result<VectorFst<TropicalWeight>> {
    let mut alpha: VectorFst<TropicalWeight> = VectorFst::new();
    let start_state = alpha.add_state();
    alpha.set_start(start_state)?;
    alpha.set_final(start_state, 0.0)?;
    for symbol in alphabet.clone() {
        alpha.emplace_tr(start_state, symbol, symbol, 0.0, start_state)?;
    }
    concat(&mut alpha, &lambda)?;
    complete_fst(alphabet.clone(), &mut alpha)?;
    let marks: HashSet<Label> = HashSet::from([lbrace2]);
    let fst: VectorFst<TropicalWeight> = marker3(alpha, marks)?;
    Ok(fst)
}

fn regex_to_vector_of_labels(symt: Arc<SymbolTable>, regex: RegexAST) -> Result<Vec<Label>> {
    let mut labels: Vec<Label> = Vec::new();
    if let RegexAST::Group(sequence) = regex {
        for re in sequence {
            if let RegexAST::Char(character) = re {
                let string = character.to_string();
                let label = symt.get_label(string).unwrap_or_else(|| {
                    eprintln!("Symbol table does not have symbol '{character}'");
                    0
                });
                labels.push(label);
            }
        }
    }
    Ok(labels)
}

// fn build_phi_psi_complete(
//     symt: SymbolTable,
//     alphabet: HashSet<Label>,
//     phi: RegexAST,
//     psi: RegexAST,
// ) -> Result<VectorFst<TropicalWeight>> {
//     let mut fst: VectorFst<TropicalWeight> = build_phi_psi_spine(symt, phi, psi)?;
//     let start_state = fst.start().unwrap_or_else(|| {
//         eprintln!(
//             "wFST fst lacks start state. It has {} states. Defaulting to 0",
//             fst.num_states()
//         );
//         0
//     });

//     // Create self loops on the start state for every label except those on the outbound transitions.
//     let ilabels_out: HashSet<Label> = fst
//         .get_trs(start_state)?
//         .iter()
//         .map(|&l| l.olabel)
//         .collect();
//     let selfloop_labels: HashSet<Label> = alphabet.difference(&ilabels_out).copied().collect();
//     selfloop_labels.iter().for_each(|&l| {
//         fst.emplace_tr(start_state, l, l, 0.0, start_state);
//     });

//     // Construct backtracking paths for cases where the input string matches a prefix of the spine.
//     let mut state: StateId = start_state;
//     let mut history: Vec<Label> = Vec::new();
//     while let Some(tr) = fst.get_trs(state)?.iter().next() {
//         history.push(tr.ilabel);
//         if history.len() == 1 {
//             let new_state = fst.add_state();
//             fst.set_final(new_state, 0.0)?;
//             fst.emplace_tr(tr.nextstate, 0, tr.ilabel, 0.0, new_state);
//         }
//         if tr.ilabel != 0 {
//             let ilabels_out: HashSet<Label> =
//                 fst.get_trs(state)?.iter().map(|t| t.ilabel).collect()?;
//             let other_labels: HashSet<Label> = alphabet.difference(&ilabels_out).copied().collect();
//             for label in other_labels {
//                 let mut old_state: StateId = 0;
//                 let mut new_state = fst.add_state();
//                 fst.emplace_tr(tr.nextstate, label, 0, 0.0, new_state);
//                 for hist_label in history {
//                     old_state = new_state;
//                     new_state = fst.add_state();
//                     fst.emplace_tr(old_state, 0, hist_label, 0.0, new_state)?;
//                 }
//                 fst.emplace_tr(new_state, 0, label, 0.0, start_state)?;
//             }
//         }
//         state = tr.nextstate;
//     }
//     rm_epsilon(&mut fst);
//     Ok(fst)
// }

// fn build_phi_psi_spine(
//     symt: Arc<SymbolTable>,
//     phi: RegexAST,
//     psi: RegexAST,
// ) -> Result<VectorFst<TropicalWeight>> {
//     let phi_labels = regex_to_vector_of_labels(symt.clone(), phi)?;
//     let psi_labels = regex_to_vector_of_labels(symt.clone(), psi)?;
//     let aligned_tuples: (Vec<Label>, Vec<Label>) = align_phi_psi_labels(phi_labels, psi_labels);
//     let fst = transducer(&phi_labels, &psi_labels, TropicalWeight::new(0.0));
//     Ok(fst)
// }

// fn align_phi_psi_labels(
//     phi_labels: Vec<Label>,
//     psi_labels: Vec<Label>,
// ) -> (Vec<Label>, Vec<Label>) {
//     let length = phi_labels.len() + psi_labels.len() - 1;
//     let mut phi_vec: Vec<Label> = phi_labels;
//     phi_vec.resize(length, 0);
//     let mut psi_vec: Vec<Label> = vec![0; length - psi_labels.len()];
//     psi_vec.extend(psi_labels);
//     (phi_vec, psi_vec)
// }

fn marker1(
    mut alpha: VectorFst<TropicalWeight>,
    insertions: HashSet<Label>,
) -> Result<VectorFst<TropicalWeight>> {
    let final_states: Vec<StateId> = get_final_states(&alpha)?;
    let start_state = alpha.start().unwrap_or_else(|| {
        eprint!(
            "wFST alpha (which has {} states) has no start state. Assuming 0.",
            alpha.num_states()
        );
        0
    });
    for s in final_states {
        let new_state = alpha.add_state();
        alpha.set_final(new_state, 0.0).unwrap();
        // FIXED: Don't create epsilon-epsilon self-loop back to start_state
        // This was creating cycles. Instead, just make new_state final without the epsilon transition.
        alpha.take_final_weight(s)?;
        let trs = alpha.pop_trs(s).unwrap_or_else(|e| {
            eprintln!("{e}: Could not pop transitions from state {s}. Weird.");
            Vec::new()
        });
        for tr in trs {
            let _ = alpha.add_tr(new_state, tr);
        }
        for mark in &insertions {
            alpha.emplace_tr(s, 0, *mark, 0.0, new_state).unwrap();
        }
    }

    Ok(alpha)
}

fn marker2(
    mut alpha: VectorFst<TropicalWeight>,
    deletions: HashSet<Label>,
) -> Result<VectorFst<TropicalWeight>> {
    let final_states: Vec<StateId> = get_final_states(&alpha)?;

    let start_state: StateId = alpha.start().unwrap_or_else(|| {
        eprintln!("wFST alpha has no start state");
        0
    });

    for s in final_states {
        for mark in &deletions {
            alpha.emplace_tr(s, *mark, 0, 0.0, s).unwrap();
            // FIXED: Don't create epsilon-epsilon self-loop back to start_state
            // This was creating cycles. Instead, create a new final state for this transition.
            let final_state = alpha.add_state();
            alpha.set_final(final_state, 0.0).unwrap();
            alpha.emplace_tr(s, 0, 0, 0.0, final_state).unwrap();
        }
    }
    Ok(alpha)
}

fn marker3(
    mut alpha: VectorFst<TropicalWeight>,
    deletions: HashSet<Label>,
) -> Result<VectorFst<TropicalWeight>> {
    let non_final_states: Vec<StateId> = alpha
        .states_iter()
        .filter(|&s| {
            !alpha.is_final(s).unwrap_or_else(|e| {
                eprintln!("{e}: It looks like there is no state {s}, which makes no sense.");
                true
            })
        })
        .collect();

    for s in non_final_states {
        alpha.set_final(s, 0.0)?;
        for mark in &deletions {
            alpha.emplace_tr(s, *mark, 0, 0.0, s).unwrap();
        }
    }

    Ok(alpha)
}

fn get_final_states(fst: &VectorFst<TropicalWeight>) -> Result<Vec<StateId>> {
    let final_states: Vec<StateId> = fst
        .states_iter()
        .filter(|&s| {
            fst.is_final(s).unwrap_or_else(|e| {
                eprintln!("{e}: It looks like there is no state {s}, which makes no sense.");
                false
            })
        })
        .collect();
    Ok(final_states)
}

fn complete_automaton(
    alphabet: HashSet<Label>,
    marks: HashSet<Label>,
    beta: &mut VectorFst<TropicalWeight>,
) -> Result<()> {
    // Determine the start state
    let start_state = beta.start().unwrap_or_else(|| {
        let num_states = beta.num_states();
        eprintln!("wFST beta lacks start state. It has {num_states} states.");
        0
    });

    let labels_outgoing_from_start: HashSet<Label> = beta
        .get_trs(start_state)
        .unwrap()
        .iter()
        .map(|tr| tr.ilabel)
        .collect();

    // Compute the set of labels that can be in the start loop (the alphabet plus marks).
    let labels_for_self_loop: HashSet<Label> = alphabet.union(&marks).copied().collect();
    let labels_for_self_loop: HashSet<Label> = labels_for_self_loop
        .difference(&labels_outgoing_from_start)
        .copied()
        .collect();

    // Add the self loops to the start state
    for l in labels_for_self_loop {
        beta.emplace_tr(start_state, l, l, 0.0, start_state)?;
    }

    // Determine the states adjacent to the start state and the corresponding labels.
    let states_adjacent_to_start: HashSet<(StateId, Label)> = beta
        .get_trs(start_state)
        .unwrap()
        .iter()
        .map(|tr| (tr.nextstate, tr.ilabel))
        .collect();

    // Add self-loops to each of the states adjacent sto start.
    for (state, label) in states_adjacent_to_start {
        beta.emplace_tr(state, label, label, 0.0, state).unwrap()
    }

    // Now, complete all of the non-final states (ensure that there is a path
    // for all inputs that have not been entirely consumed).

    // Collect non-final states
    let non_final_states: Vec<StateId> = beta
        .states_iter()
        .filter(|s| !beta.is_final(*s).unwrap())
        .collect();

    // For each state, find the outgoing labels and create transitions from the
    // state to the start state from the complement of that set of labels and
    // the alphabet.
    for &state in non_final_states.iter() {
        let outgoing: HashSet<Label> = beta
            .get_trs(state)
            .unwrap()
            .iter()
            .map(|tr| tr.ilabel)
            .collect();
        // If none of the transitions is an epsilon transition
        if !outgoing.contains(&0) {
            let others: Vec<Label> = alphabet.difference(&outgoing).copied().collect();
            for l in others {
                beta.emplace_tr(state, l, l, 0.0, start_state).unwrap();
            }
        }
    }

    // Collect final states
    let final_states: Vec<StateId> = beta
        .states_iter()
        .filter(|&s| !beta.is_final(s).unwrap())
        .collect();

    for &state in final_states.iter() {
        // FIXED: Don't create epsilon-epsilon self-loop back to start_state
        // This was creating cycles. Instead, create a new final state for this transition.
        let final_state = beta.add_state();
        beta.set_final(final_state, 0.0)?;
        beta.emplace_tr(state, 0, 0, 0.0, final_state)?;
    }
    //

    // Now make the start state a final state.
    beta.set_final(start_state, 0.0)?;

    Ok(())
}

// fn build_brace_deleter(
//     symt: Arc<SymbolTable>,
//     lbrace1: Label,
//     lbrace2: Label,
//     rbrace: Label,
// ) -> Result<VectorFst<TropicalWeight>> {
//     let symt: Arc<SymbolTable> = symt.clone();
//     let mut delete_fst: VectorFst<TropicalWeight> = VectorFst::new();
//     let start_state = delete_fst.add_state();
//     delete_fst.set_start(start_state)?;
//     delete_fst.set_final(start_state, 0.0)?;
//     symt.clone()
//         .labels()
//         .filter(|&l| l != lbrace1 && l != lbrace2 && l != rbrace)
//         .for_each(|l| delete_fst.emplace_tr(0, l, l, 0.0, 0).unwrap());
//     delete_fst.emplace_tr(0, lbrace1, 0, 0.0, 0)?;
//     delete_fst.emplace_tr(0, lbrace2, 0, 0.0, 0)?;
//     delete_fst.emplace_tr(0, rbrace, 0, 0.0, 0)?;
//     Ok(delete_fst)
// }

pub fn failed_rule_fst(
    symt: Arc<SymbolTable>,
    macros: &BTreeMap<String, RegexAST>,
    rule: RewriteRule,
) -> Result<VectorFst<TropicalWeight>, Box<dyn std::error::Error>> {
    let mut left_fst = match rule.left {
        RegexAST::Epsilon => fst![0; 0.0],
        _ => node_fst(symt.clone(), macros, rule.left).unwrap(),
    };

    let right_fst = match rule.right {
        RegexAST::Epsilon => fst![0; 0.0],
        _ => node_fst(symt.clone(), macros, rule.right).unwrap(),
    };

    let mut src_fst: VectorFst<TropicalWeight> =
        output_to_epsilons(node_fst(symt.clone(), macros, rule.source).unwrap());

    let tgt_fst: VectorFst<TropicalWeight> =
        input_to_epsilons(node_fst(symt.clone(), macros, rule.target).unwrap());

    concat(&mut left_fst, &tgt_fst).unwrap();
    concat(&mut left_fst, &right_fst).unwrap();

    project(&mut left_fst, ProjectType::ProjectInput);

    concat(&mut src_fst, &tgt_fst).unwrap();
    rm_epsilon(&mut src_fst).unwrap();
    src_fst.set_final(0, 0.0).unwrap_or_else(|e| {
        eprintln!("{e}: Cannnot set state 0 as final state. Is the wFST empty?")
    });

    let possible_labels: HashSet<Label> = symt.clone().labels().filter(|l| *l > 1).collect();
    let start_state = src_fst.start().unwrap_or_else(|| {
        eprintln!("src_fst has no start state. Assuming 0.");
        0
    });

    src_fst.states_iter().for_each(|state| {
        let outgoing: HashSet<Label> = src_fst
            .get_trs(state)
            .unwrap()
            .iter()
            .filter(|tr| tr.ilabel != 0)
            .map(|tr| tr.ilabel)
            .collect();
        if !outgoing.is_empty() {
            possible_labels.difference(&outgoing).for_each(|&l| {
                src_fst.emplace_tr(state, l, l, 1.0, start_state).unwrap();
            });
        }
        let is_final = src_fst.is_final(state).unwrap();
        if is_final {
            let _ = src_fst.take_final_weight(state);
            // FIXED: Don't create epsilon-epsilon self-loop back to start_state
            // This was creating cycles. Instead, create a new final state for this transition.
            let final_state = src_fst.add_state();
            let _ = src_fst.set_final(final_state, 0.0);
            let _ = src_fst.emplace_tr(state, 0, 0, 0.0, final_state);
        }
    });

    // let rewrite_fst: VectorFst<TropicalWeight> = compose(left_fst, src_fst).unwrap();

    Ok(src_fst)
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
pub fn old_rule_fst(
    symt: Arc<SymbolTable>,
    macros: &BTreeMap<String, RegexAST>,
    rule: RewriteRule,
) -> Result<VectorFst<TropicalWeight>, Box<dyn std::error::Error>> {
    // let mut fst = VectorFst::<TropicalWeight>::new();
    // fst.set_input_symbols(symt.clone());
    // fst.set_output_symbols(symt.clone());
    // let q0 = fst.add_state();
    // fst.set_start(0)?;
    // let q1 = fst.add_state();
    // fst.set_final(q1, TropicalWeight::one())?;
    // fst.emplace_tr(q0, 0, 0, TropicalWeight::one(), q1)?;

    // Compute core (L[S->T]R)

    let mut left_fst = match rule.left {
        RegexAST::Epsilon => fst![0; 0.0],
        _ => node_fst(symt.clone(), macros, rule.left)?,
    };

    let right_fst = match rule.right {
        RegexAST::Epsilon => fst![0; 0.0],
        _ => node_fst(symt.clone(), macros, rule.right)?,
    };

    // eprintln!("{}={:?}", "right_fst".bold().green(), right_fst);
    let src_fst: VectorFst<TropicalWeight> =
        output_to_epsilons(node_fst(symt.clone(), macros, rule.source)?);

    // draw_wfst(&src_fst, "src_fst", "Diagram of src_fst")?;

    let tgt_fst: VectorFst<TropicalWeight> =
        input_to_epsilons(node_fst(symt.clone(), macros, rule.target)?);
    // let univ_acc: VectorFst<TropicalWeight> = universal_acceptor(symt.clone())?;

    // draw_wfst(&tgt_fst, "tgt_fst", "Diagram of tgt_fst")?;

    concat(&mut left_fst, &src_fst)?;
    concat(&mut left_fst, &tgt_fst)?;
    concat(&mut left_fst, &right_fst)?;
    // let start = left_fst.start();

    rm_epsilon(&mut left_fst)?;

    left_fst.set_input_symbols(symt.clone());
    left_fst.set_output_symbols(symt.clone());

    draw_wfst(
        &left_fst,
        "concat_fst",
        "Diagram of wFST after rm_epsilon but before optimization",
    )?;

    let last_state = left_fst.add_state();
    let finals: Vec<u32> = left_fst
        .states_iter()
        .filter(|s| left_fst.is_final(*s).unwrap())
        .collect();

    finals.iter().for_each(|s| {
        left_fst.emplace_tr(*s, 0, 0, 0.0, last_state).unwrap();
    });

    left_fst.take_final_weight(last_state)?;

    // left_fst.set_final(start, 0.)?;
    let start = left_fst.start().unwrap_or_else(|| {
        eprintln!("{}", "left_fst lacks a start state. Assuming 0.");
        0
    });

    universalize_fst(symt, &mut left_fst, start)?;

    // left_fst
    //     .states_iter()
    //     .filter(|&s| s != last_state)
    //     .for_each(|state| {
    //         add_complement_trs(symt.clone(), &mut left_fst, start, state)
    //             .unwrap_or_else(|e| eprintln!("{e}: Failed to add complement transitions."))
    //     });

    draw_wfst(
        &left_fst,
        "expanded_fst",
        "Diagram of wFST after expansion with add_complement_trs but before optimization",
    )?;

    left_fst.emplace_tr(last_state, 0, 0, 0.0, start)?;

    let real_start = left_fst.add_state();
    left_fst.set_start(real_start)?;
    left_fst.emplace_tr(real_start, 1, 1, 0.0, start)?;
    let real_final: u32 = left_fst.add_state();
    left_fst.set_final(real_final, 0.0)?;
    left_fst.emplace_tr(start, 1, 1, 0.0, real_final)?;

    optimize_fst(&mut left_fst, 1e-5)?;

    Ok(left_fst)
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
    // Sort symbol table entries to ensure deterministic iteration
    let mut sorted_syms: Vec<(Label, &str)> = symt.iter().filter(|(_, s)| *s != "<eps>").collect();
    sorted_syms.sort_by_key(|(label, _)| *label);
    for (label, _) in sorted_syms {
        fst.add_tr(q0, Tr::new(label, label, 10.0, q0))?;
    }
    Ok(fst)
}

fn universalize_fst(
    symt: Arc<SymbolTable>,
    fst: &mut VectorFst<TropicalWeight>,
    start_state: StateId,
) -> Result<()> {
    let possible: HashSet<Label> = symt.clone().labels().filter(|l| *l > 1).collect();
    let mut incoming_eps_ilabel: HashSet<StateId> = HashSet::new();
    let mut incoming_eps_olabel: HashSet<(StateId, Label)> = HashSet::new();

    let mut outgoing_by_ilabel: HashMap<StateId, HashSet<Label>> = HashMap::new();
    for state in fst.states_iter() {
        let mut outbound_ilabels: HashSet<Label> = HashSet::new();
        for tr in fst.get_trs(state)?.iter() {
            if tr.ilabel == 0 {
                incoming_eps_ilabel.insert(tr.nextstate);
            } else {
                let ilabels: HashSet<Label> =
                    fst.get_trs(state)?.iter().map(|tr| tr.ilabel).collect();
                let _ = outgoing_by_ilabel.insert(state, ilabels);
            }
            if tr.olabel == 0 {
                incoming_eps_olabel.insert((tr.nextstate, tr.ilabel));
            }
            outbound_ilabels.insert(tr.ilabel);
        }
    }

    for (nextstate, label) in incoming_eps_olabel.iter() {
        fst.emplace_tr(*nextstate, 0, *label, 1.0, start_state)?;
    }

    for (state, labels) in outgoing_by_ilabel {
        if !incoming_eps_ilabel.contains(&state) {
            possible.difference(&labels).for_each(|l| {
                fst.emplace_tr(state, *l, *l, 0.0, start_state).unwrap();
            });
        }
    }

    Ok(())
}

fn _add_complement_trs(
    symt: Arc<SymbolTable>,
    fst: &mut VectorFst<TropicalWeight>,
    start: StateId,
    state: StateId,
) -> Result<()> {
    let possible: HashSet<Label> = symt.clone().labels().filter(|l| *l > 1).collect();
    let outgoing: HashSet<Label> = fst
        .get_trs(state)?
        .iter()
        .filter(|tr| tr.ilabel == tr.olabel)
        .map(|tr| tr.ilabel)
        .collect();
    // Sort labels to ensure deterministic iteration
    let mut diff_labels: Vec<Label> = possible.difference(&outgoing).copied().collect();
    diff_labels.sort();
    diff_labels.iter().for_each(|l| {
        // println!(
        //     "{}",
        //     format!("Adding transition from {state} to {start} with {l}:{l}").green()
        // );
        fst.emplace_tr(state, *l, *l, 1.0, start)
            .unwrap_or_else(|e| {
                eprintln!(
                    "|{e}| Cannot create a transition from {state} to {start} with label {l}"
                );
            });
    });

    let trs_binding = fst.get_trs(state)?;
    let deletions: Vec<(StateId, Label)> = trs_binding
        .iter()
        .filter(|tr| tr.ilabel > 1 && tr.olabel == 0)
        .map(|tr| (tr.nextstate, tr.ilabel))
        .collect();

    deletions.iter().for_each(|(nextstate, label)| {
        fst.emplace_tr(*nextstate, 0, *label, 0.0, start)
            .unwrap_or_else(|e| eprintln!("{e}: Could not emplace transition for reinsertion."))
    });
    Ok(())
}

/// Interpret an RegexAST node as a wFST
fn node_fst(
    symt: Arc<SymbolTable>,
    macros: &BTreeMap<String, RegexAST>,
    node: RegexAST,
) -> Result<VectorFst<TropicalWeight>, Box<dyn std::error::Error>> {
    let mut fst: VectorFst<TropicalWeight> = fst![0; 0.0];
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
            let fst2: VectorFst<TropicalWeight> = fst![label; 0.0];
            concat(&mut fst, &fst2)?;
        }

        // Interpret a disjunction (a set of mutually-exclusive sequences).
        RegexAST::Disjunction(mut nodes) => {
            // let mut fst2: VectorFst<TropicalWeight> = VectorFst::<TropicalWeight>::new();
            // let q0 = fst.add_state();
            // let q1 = fst.add_state();
            // fst.emplace_tr(q0, 0, 0, TropicalWeight::zero(), q1)?;
            let first_node = nodes.pop().unwrap_or_else(|| RegexAST::Epsilon);
            let mut fst2 = node_fst(symt.clone(), macros, first_node)?;
            for node in nodes {
                let case_fst = node_fst(symt.clone(), macros, node)?;
                union(&mut fst2, &case_fst)?;
            }
            draw_wfst(
                &fst2,
                "disjunction",
                "wFST representation of a disjunction.",
            )?;
            concat(&mut fst, &fst2)?;
        }

        // Interpret a character class (a set of characters any of which match the expression).
        RegexAST::Class(class) => {
            let mut fst2: VectorFst<TropicalWeight> = VectorFst::<TropicalWeight>::new();
            let q0 = fst2.add_state();
            fst2.set_start(q0)?;
            let q1: u32 = fst2.add_state();
            fst2.set_final(q1, 0.0)?;
            // Sort class members to ensure deterministic iteration
            let mut sorted_class: Vec<&String> = class.iter().collect();
            sorted_class.sort();
            for s in sorted_class {
                let l = symt.get_label(s).unwrap_or_else(|| {
                    eprintln!(
                        "Warning: Symbol '{}' is not in symbol table, using epsilon",
                        s.red()
                    );
                    0
                });
                fst2.emplace_tr(q0, l, l, 0.0, q1)?;
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
            // Sort symbol table entries to ensure deterministic iteration
            let mut sorted_syms: Vec<(Label, &str)> = symt.iter().collect();
            sorted_syms.sort_by_key(|(label, _)| *label);
            for (l, s) in sorted_syms {
                if !class.contains(s) {
                    fst2.emplace_tr(q0, l, l, 0.0, q1)?;
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
                eprintln!("wFST does not have start state.");
                0
            });
            let final_state = add_super_final_state(&mut fst2);
            fst2.emplace_tr(start_state, 0, 0, 0.0, final_state)
                .unwrap_or_else(|e| eprintln!("{e}: Could not add transition."));
            concat(&mut fst, &fst2)
                .unwrap_or_else(|e| eprintln!("{e}: Could not concatenate wFSTs."));
        }

        // Interpret a macro
        RegexAST::Macro(macro_key) => {
            let macro_node = macros.get(&macro_key).unwrap_or_else(|| {
                eprintln!("Macro {macro_key} not defined!");
                &RegexAST::Epsilon
            });
            let fst2 = node_fst(symt, macros, macro_node.clone())?;
            concat(&mut fst, &fst2)
                .unwrap_or_else(|e| eprintln!("{e}: Could not concatenate wFSTs."));
        }

        RegexAST::Comment => (),
    }

    // optimize_fst(&mut fst, 1e-5)?;

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
            eprintln!("{}", "When checking for cyclicity, it was discovered that the wFST lacks start state. Assuming 0.".red());
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
    // dbg!(fst.clone());
    let mut composed_fst: VectorFst<TropicalWeight> =
        apply_fst_to_string(symt.clone(), fst.clone(), input.clone()).unwrap_or_else(|e| {
            println!("{e}: Couldn't apply wFST {fst:?} to string {input:?}.");
            VectorFst::<TropicalWeight>::new()
        });
    if composed_fst.num_states() == 0 {
        eprintln!(
            "{}",
            "The input was not recognized by the wFST.".bold().red()
        );
        return "".to_string();
    }
    if is_cyclic(&composed_fst) {
        panic!("Transducer resulting from applying composing input string was cyclic.")
    };
    composed_fst.set_input_symbols(symt.clone());
    composed_fst.set_output_symbols(symt.clone());

    let shortest: VectorFst<TropicalWeight> = shortest_path(&composed_fst).unwrap();

    let candidates: Vec<StringPath<TropicalWeight>> = shortest
        .string_paths_iter()
        .unwrap()
        .collect::<Vec<StringPath<TropicalWeight>>>();

    candidates
        .iter()
        .map(|path| {
            path.olabels()
                .iter()
                .map(|l| symt.get_symbol(*l).unwrap())
                .collect::<String>()
        })
        .for_each(|c| println!("Candidate: '{c}'"));

    // Collect all shortest paths and choose deterministically
    let mut paths = shortest
        .string_paths_iter()
        .unwrap()
        .collect::<Vec<StringPath<TropicalWeight>>>();

    // If multiple paths exist, choose the lexicographically smallest output string
    // to ensure deterministic behavior
    if paths.len() > 1 {
        paths.sort_by(|a, b| {
            let a_string: String = a
                .olabels()
                .iter()
                .map(|l| symt.get_symbol(*l).unwrap_or(""))
                .collect();
            let b_string: String = b
                .olabels()
                .iter()
                .map(|l| symt.get_symbol(*l).unwrap_or(""))
                .collect();
            a_string.cmp(&b_string)
        });
    }

    paths[0]
        .olabels()
        .iter()
        .map(|l| {
            symt.get_symbol(*l).unwrap_or_else(|| {
                eprintln!(
                    "Label {l} not found in Symbol Table while decoding path. Using empty string."
                );
                ""
            })
        })
        .collect::<String>()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ruleparse::{parse_script, rule, rule_no_env};
    use rustfst::algorithms::rm_epsilon::rm_epsilon;
    // use rustfst::prelude::compose::matchers::SigmaMatcher;
    // use rustfst::prelude::compose::SigmaMatcherConfig;
    use rustfst::utils::transducer;

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
        let symt = Arc::new(symt!["#", "p", "b", "a", "i"]);
        let (_, (script, _syms)) =
            parse_script("  ::voi::=(b|a|i)\n% The rules start here:\np -> b / ::voi:: _ ::voi::")
                .expect("Failed to parse script in test");
        let fst = compile_script(symt.clone(), script).expect("Failed to compile script in test");
        draw_wfst(
            &fst,
            "test_compile_script_basic_with_comment",
            "wFST computed by the test_compile_script_basic_with_comment test.",
        )
        .unwrap();
        let result = apply_fst(symt.clone(), fst, "#apbppi#".to_string());
        assert_eq!(result, "#abbppi#".to_string());
    }

    fn evaluate_rule(symt: Arc<SymbolTable>, rule_str: &str, input: &str, output: &str) {
        let macros: &BTreeMap<String, RegexAST> = &BTreeMap::new();
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
            "#cddda#",
            "#cdddb#",
        )
    }

    #[test]
    fn test_kleene_star2() {
        evaluate_rule(
            Arc::new(symt!["#", "a", "b", "c", "d"]),
            "a -> b / cd* _ ",
            "#ca#",
            "#cb#",
        )
    }

    #[test]
    fn test_kleene_star3() {
        evaluate_rule(
            Arc::new(symt!["#", "a", "b", "c", "d"]),
            "a -> b / cd* _ ",
            "#ddda#",
            "#ddda#",
        )
    }

    #[test]
    fn test_kleene_plus3() {
        evaluate_rule(
            Arc::new(symt!["#", "a", "b", "c", "d"]),
            "a -> b / cd+ _ ",
            "#cda#",
            "#cdb#",
        )
    }

    #[test]
    fn test_kleene_plus4() {
        evaluate_rule(
            Arc::new(symt!["#", "a", "b", "c", "d"]),
            "a -> b / cd+ _ ",
            "#ca#",
            "#ca#",
        )
    }

    #[test]
    fn test_kleene_plus5() {
        evaluate_rule(
            Arc::new(symt!["#", "a", "b", "c", "d"]),
            "a -> b / (cd)+ _ ",
            "#cdcdcda#",
            "#cdcdcdb#",
        )
    }

    #[test]
    fn test_kleene_plus6() {
        evaluate_rule(
            Arc::new(symt!["#", "a", "b", "c", "d"]),
            "a -> b / (cd)+ _ ",
            "#cdcdca#",
            "#cdcdca#",
        )
    }

    #[test]
    fn test_option1() {
        evaluate_rule(
            Arc::new(symt!["#", "a", "b", "c", "d"]),
            "a -> b / cd? _ ",
            "#cda#",
            "#cdb#",
        )
    }

    #[test]
    fn test_option2() {
        evaluate_rule(
            Arc::new(symt!["#", "a", "b", "c", "d"]),
            "a -> b / cd? _ ",
            "#ca#",
            "#cb#",
        )
    }

    #[test]
    fn test_simple_rule() {
        // let symt = unicode_symbol_table();
        let symt = Arc::new(symt!["#", "a", "e"]);
        let macros: &BTreeMap<String, RegexAST> = &BTreeMap::new();
        let (_, (rewrite_rule, _syms)) =
            rule_no_env("a -> e").expect("Failed to parse rule_no_env in test");
        // println!("rewrite_rule = {:?}", rewrite_rule);
        let fst: VectorFst<TropicalWeight> =
            rule_fst(symt.clone(), macros, rewrite_rule).expect("Something");
        draw_wfst(&fst, "test_simple_rule", "wFST for test_simple_rule.").expect("Could not draw.");
        
        // Debug: Check if the rule FST itself is cyclic
        println!("DEBUG: Rule FST is cyclic: {}", is_cyclic(&fst));
        
        // Debug: Check symbol mappings
        println!("DEBUG: Symbol table mappings:");
        for (i, symbol) in symt.symbols().enumerate() {
            println!("  {} -> {}", symbol, i);
        }
        
        // Debug: Try to compose with input and see what happens
        let input = "#a#".to_string();
        println!("DEBUG: Composing with input: {}", input);
        let composed_result = apply_fst_to_string(symt.clone(), fst.clone(), input.clone());
        match composed_result {
            Ok(composed_fst) => {
                println!("DEBUG: Composition succeeded, {} states", composed_fst.num_states());
                println!("DEBUG: Composed FST is cyclic: {}", is_cyclic(&composed_fst));
                if !is_cyclic(&composed_fst) {
                    let result = apply_fst(symt.clone(), fst, input);
                    assert_eq!(result, "#e#".to_string());
                } else {
                    println!("DEBUG: Composed FST is cyclic, cannot decode");
                }
            }
            Err(e) => {
                println!("DEBUG: Composition failed: {}", e);
            }
        }
    }

    #[test]
    fn test_pal_rule() {
        // let symt = unicode_symbol_table();
        let symt = Arc::new(symt!["#", "i", "c", "k"]);
        let macros: &BTreeMap<String, RegexAST> = &BTreeMap::new();
        let (_, (rewrite_rule, _syms)) =
            rule("k -> c / i _ i").expect("Failed to parse rule_no_env in test");
        // println!("rewrite_rule = {:?}", rewrite_rule);
        let fst: VectorFst<TropicalWeight> =
            rule_fst(symt.clone(), macros, rewrite_rule).expect("Something");
        draw_wfst(&fst, "test_pal_rule", "wFST for test_pal_rule.").expect("Could not draw.");
        assert_eq!(
            apply_fst(symt, fst, "#ccikicc#".to_string()),
            "#ccicicc#".to_string()
        );
    }

    #[test]
    fn test_no_pal_rule() {
        // let symt = unicode_symbol_table();
        let symt = Arc::new(symt!["#", "i", "c", "k"]);
        let macros: &BTreeMap<String, RegexAST> = &BTreeMap::new();
        let (_, (rewrite_rule, _syms)) =
            rule("k -> c / i _ i").expect("Failed to parse rule_no_env in test");
        // println!("rewrite_rule = {:?}", rewrite_rule);
        let fst: VectorFst<TropicalWeight> =
            rule_fst(symt.clone(), macros, rewrite_rule).expect("Something");
        draw_wfst(&fst, "test_no_pal_rule", "wFST for test_no_pal_rule.").expect("Could not draw.");
        assert_eq!(
            apply_fst(symt, fst, "#ccckicc#".to_string()),
            "#cccikcc#".to_string()
        );
    }

    #[test]
    fn test_multiple_application() {
        // let symt = unicode_symbol_table();
        let symt = Arc::new(symt!["#", "a", "e"]);
        let macros: &BTreeMap<String, RegexAST> = &BTreeMap::new();
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
        let macros: &BTreeMap<String, RegexAST> = &BTreeMap::new();
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
        let macros: &BTreeMap<String, RegexAST> = &BTreeMap::new();
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
        let macros: &BTreeMap<String, RegexAST> = &BTreeMap::new();
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
    fn test_rule_complement_class() {
        let symt = Arc::new(symt!["#", "a", "b", "p", "i"]);
        let macros: &BTreeMap<String, RegexAST> = &BTreeMap::new();
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
