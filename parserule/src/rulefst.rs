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
use rustfst::prelude::determinize::{determinize_with_config, DeterminizeConfig, DeterminizeType};
use rustfst::prelude::rm_epsilon::rm_epsilon;
use rustfst::prelude::*;
use rustfst::utils::{acceptor, transducer};
// use rustfst::DrawingConfig;
use std::char;
use std::cmp::Ordering;
// Explicitly import HashMap to avoid conflicts
use std::collections::{HashMap, HashSet};
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
    let mut fst = weighted_sigma_star(symt.clone(), 1.0)?;
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

pub fn rule_fst(
    symt: Arc<SymbolTable>,
    macros: &HashMap<String, RegexAST>,
    rule: RewriteRule,
) -> Result<VectorFst<TropicalWeight>> {
    let mut symt_ext = symt.as_ref().clone();
    let rangle = symt_ext.add_symbol("$");
    let langle1 = symt_ext.add_symbol("^");
    let langle2 = symt_ext.add_symbol("%");
    let symt_ext_ref = Arc::new(symt_ext);

    let rulestr = format!("{:?}", rule.clone());

    let phi_fst: VectorFst<TropicalWeight> = node_fst(symt.clone(), macros, rule.source)?;
    let psi_fst: VectorFst<TropicalWeight> =
        input_to_epsilons(node_fst(symt.clone(), macros, rule.target)?);
    let lambda_fst = match rule.left {
        RegexAST::Epsilon => {
            let inner_fst: VectorFst<TropicalWeight> = fst![EPS_LABEL => EPS_LABEL];
            // let inner_fst = weighted_sigma_star(symt.clone(), 1.0)?;
            //closure(&mut inner_fst, ClosureType::ClosureStar);
            inner_fst
        }
        _ => node_fst(symt.clone(), macros, rule.left)?,
    };
    let rho_fst = match rule.right {
        RegexAST::Epsilon => {
            let inner_fst: VectorFst<TropicalWeight> = fst![EPS_LABEL => EPS_LABEL];
            //closure(&mut inner_fst, ClosureType::ClosureStar);
            inner_fst
        }
        _ => node_fst(symt.clone(), macros, rule.right)?,
    };
    let sigma_star: VectorFst<TropicalWeight> = weighted_sigma_star(symt.clone(), 1.0)?;
    let mut sigma_star_with_rangle: VectorFst<TropicalWeight> = sigma_star.clone();
    let q0 = sigma_star_with_rangle.start().unwrap();
    sigma_star_with_rangle.add_tr(q0, Tr::new(rangle, rangle, 1.0, q0))?;

    rho_fst.draw("partial_rho.dot", &DrawingConfig::default())?;

    let mut fst_r: VectorFst<TropicalWeight> =
        build_fst_r(sigma_star.clone(), rho_fst.clone(), rangle)?;

    let mut fst_f: VectorFst<TropicalWeight> = build_fst_f(
        sigma_star_with_rangle.clone(),
        phi_fst.clone(),
        rangle,
        langle1,
        langle2,
    )?;

    let mut fst_replacer = build_fst_replacer(
        sigma_star.clone(),
        phi_fst.clone(),
        psi_fst.clone(),
        rangle,
        langle1,
        langle2,
    )?;

    let mut fst_l1 = build_fst_l1(sigma_star.clone(), lambda_fst.clone(), langle1, langle2)?;

    let mut fst_l2 = build_fst_l2(
        symt_ext_ref.clone(),
        sigma_star.clone(),
        lambda_fst.clone(),
        langle2,
    )?;

    fst_r.set_output_symbols(symt_ext_ref.clone());
    fst_f.set_output_symbols(symt_ext_ref.clone());
    fst_replacer.set_output_symbols(symt_ext_ref.clone());
    fst_l1.set_output_symbols(symt_ext_ref.clone());
    fst_l2.set_output_symbols(symt_ext_ref.clone());

    fst_r.set_input_symbols(symt_ext_ref.clone());
    fst_f.set_input_symbols(symt_ext_ref.clone());
    fst_replacer.set_input_symbols(symt_ext_ref.clone());
    fst_l1.set_input_symbols(symt_ext_ref.clone());
    fst_l2.set_input_symbols(symt_ext_ref.clone());
    fst_r.draw("partial_r.dot", &DrawingConfig::default())?;
    fst_f.draw("partial_f.dot", &DrawingConfig::default())?;
    fst_replacer.draw("partial_repl.dot", &DrawingConfig::default())?;
    fst_l1.draw("partial_l1.dot", &DrawingConfig::default())?;
    fst_l2.draw("partial_l2.dot", &DrawingConfig::default())?;
    /*
     */

    let mut output = fst_r;
    output.set_start(0)?;
    tr_sort(&mut output, OLabelCompare {});
    tr_sort(&mut fst_f, ILabelCompare {});
    tr_sort(&mut fst_replacer, ILabelCompare {});
    tr_sort(&mut fst_l1, ILabelCompare {});
    tr_sort(&mut fst_l2, ILabelCompare {});
    output = compose::<_, VectorFst<_>, VectorFst<_>, VectorFst<_>, &_, &_>(&output, &fst_f)?;
    output =
        compose::<_, VectorFst<_>, VectorFst<_>, VectorFst<_>, &_, &_>(&output, &fst_replacer)?;
    output = compose::<_, VectorFst<_>, VectorFst<_>, VectorFst<_>, &_, &_>(&output, &fst_l1)?;
    output = compose::<_, VectorFst<_>, VectorFst<_>, VectorFst<_>, &_, &_>(&output, &fst_l2)?;

    println!("Created machine for rule: {}", rulestr);
    output.draw("rulefst.dot", &DrawingConfig::default())?;
    //println!("Optimizing...");
    // optimize_fst(&mut output, 1e-6).unwrap_or(());
    //println!("Successfully optimized");
    // minimize_with_config(
    //     &mut output,
    //     MinimizeConfig {
    //         delta: 1e-4,
    //         allow_nondet: true,
    //     },
    // )?;
    // let mut output: VectorFst<TropicalWeight> = determinize_with_config(
    //     &output,
    //     DeterminizeConfig {
    //         delta: 1.0e-4,
    //         det_type: DeterminizeType::DeterminizeNonFunctional,
    //     },
    // )?;
    //println!("Successfully minimized");
    // output.draw("rulefst_opt.dot", &DrawingConfig::default())?;
    rm_epsilon(&mut output)?;

    // println!("Successfully removed epsilon transitions");

    Ok(output)
}

fn build_fst_r(
    sigma_star: VectorFst<TropicalWeight>,
    rho_fst: VectorFst<TropicalWeight>,
    rangle: Label,
) -> Result<VectorFst<TropicalWeight>> {
    let insert_rangle: VectorFst<TropicalWeight> = fst![EPS_LABEL => rangle; 0.0];
    let mut fst_r = sigma_star.clone();
    concat(&mut fst_r, &insert_rangle)?;
    concat(&mut fst_r, &rho_fst)?;
    closure(&mut fst_r, ClosureType::ClosureStar);
    concat(&mut fst_r, &sigma_star)?;
    // optimize_fst(&mut fst_r, 1e-4).unwrap();
    Ok(fst_r)
}

fn build_fst_f(
    sigma_star: VectorFst<TropicalWeight>,
    phi_fst: VectorFst<TropicalWeight>,
    rangle: Label,
    langle1: Label,
    langle2: Label,
) -> Result<VectorFst<TropicalWeight>> {
    let mut sigma_star_with_rangle: VectorFst<TropicalWeight> = sigma_star.clone();
    let q0 = sigma_star_with_rangle.start().unwrap();
    sigma_star_with_rangle.add_tr(q0, Tr::new(rangle, rangle, 0.0, q0))?;

    let mut insert_langle: VectorFst<TropicalWeight> = fst![EPS_LABEL => langle1; 0.0];
    let insert_langle2: VectorFst<TropicalWeight> = fst![EPS_LABEL => langle2; 0.0];
    union(&mut insert_langle, &insert_langle2)?;

    let rangle_fst: VectorFst<TropicalWeight> = fst![rangle => rangle; 0.0];

    let mut fst_f = sigma_star_with_rangle.clone();
    concat(&mut fst_f, &insert_langle)?;
    concat(&mut fst_f, &phi_fst)?;
    concat(&mut fst_f, &rangle_fst)?;
    closure(&mut fst_f, ClosureType::ClosureStar);
    concat(&mut fst_f, &sigma_star_with_rangle)?;
    // optimize_fst(&mut fst_f, 1e-4).unwrap();
    Ok(fst_f)
}

fn build_fst_replacer(
    sigma_star: VectorFst<TropicalWeight>,
    phi_fst: VectorFst<TropicalWeight>,
    psi_fst: VectorFst<TropicalWeight>,
    rangle: Label,
    langle1: Label,
    langle2: Label,
) -> Result<VectorFst<TropicalWeight>> {
    let mut sigma_star: VectorFst<TropicalWeight> = sigma_star.clone();
    let mut new_sigma_star: VectorFst<TropicalWeight> = sigma_star.clone();
    let start_state: StateId = sigma_star.start().unwrap();
    let trs = sigma_star.pop_trs(start_state)?;
    trs.iter()
        .filter(|tr| tr.ilabel != rangle)
        .for_each(|tr| new_sigma_star.add_tr(start_state, tr.clone()).unwrap());
    new_sigma_star.emplace_tr(start_state, rangle, EPS_LABEL, 0.0, start_state)?;

    let mut phi_fst: VectorFst<TropicalWeight> = output_to_epsilons(phi_fst);
    let mut psi_fst: VectorFst<TropicalWeight> = input_to_epsilons(psi_fst);
    let rangle_fst: VectorFst<TropicalWeight> = fst![rangle => EPS_LABEL];
    let langle1_fst: VectorFst<TropicalWeight> = fst![langle1 => langle1];

    // let s = phi_fst.start().unwrap();
    let phi_states: Vec<StateId> = phi_fst.states_iter().collect();
    phi_states.iter().for_each(|s| {
        phi_fst.emplace_tr(*s, rangle, EPS_LABEL, 0.0, *s).unwrap();
        phi_fst.emplace_tr(*s, langle1, EPS_LABEL, 0.0, *s).unwrap();
        phi_fst.emplace_tr(*s, langle2, EPS_LABEL, 0.0, *s).unwrap();
    });
    tr_sort(&mut phi_fst, OLabelCompare {});
    tr_sort(&mut psi_fst, ILabelCompare {});
    let phi_psi_fst: VectorFst<TropicalWeight> = compose(phi_fst, psi_fst)?;

    let mut fst: VectorFst<TropicalWeight> = new_sigma_star.clone();
    concat(&mut fst, &langle1_fst)?;
    concat(&mut fst, &phi_psi_fst)?;
    concat(&mut fst, &rangle_fst)?;
    closure(&mut fst, ClosureType::ClosureStar);
    concat(&mut fst, &new_sigma_star.clone())?;

    Ok(fst)
}

// fn old_build_fst_replacer(
//     sigma_star: VectorFst<TropicalWeight>,
//     phi_fst: VectorFst<TropicalWeight>,
//     psi_fst: VectorFst<TropicalWeight>,
//     rangle: Label,
//     langle1: Label,
//     langle2: Label,
// ) -> Result<VectorFst<TropicalWeight>> {
//     let mut sigma_star_drop_angle = sigma_star.clone();
//     let q0 = sigma_star_drop_angle.start().unwrap_or_else(|| {
//         eprintln!("wFST sigma_star_drop_angle lacks a start state, which shouldn't happen.");
//         0
//     });
//     sigma_star_drop_angle.add_tr(q0, Tr::new(rangle, EPS_LABEL, 10.0, q0))?;
//     sigma_star_drop_angle.add_tr(q0, Tr::new(langle1, EPS_LABEL, 5.0, q0))?;
//     sigma_star_drop_angle.add_tr(q0, Tr::new(langle2, EPS_LABEL, 5.0, q0))?;
//     tr_sort(&mut sigma_star_drop_angle, OLabelCompare {});
//     let consume_phi: VectorFst<TropicalWeight> =
//         compose(sigma_star_drop_angle, output_to_epsilons(phi_fst))?;
//     let mut sigma_star_consume_rangle: VectorFst<TropicalWeight> = sigma_star.clone();
//     let q0 = sigma_star_consume_rangle.start().unwrap();
//     sigma_star_consume_rangle.add_tr(q0, Tr::new(rangle, EPS_LABEL, 20.0, q0))?;
//     sigma_star_consume_rangle.add_tr(q0, Tr::new(langle2, langle2, 0.0, q0))?;
//     let single_langle: VectorFst<TropicalWeight> = fst![langle1 => langle1];
//     let consume_rangle: VectorFst<TropicalWeight> = fst![rangle => EPS_LABEL; 10.0];

//     let mut fst_replacer = sigma_star_consume_rangle.clone();
//     concat(&mut fst_replacer, &single_langle)?;
//     concat(&mut fst_replacer, &consume_phi)?;
//     concat(&mut fst_replacer, &psi_fst)?;
//     concat(&mut fst_replacer, &consume_rangle)?;
//     //println!("Concatenation done");
//     closure(&mut fst_replacer, ClosureType::ClosureStar);
//     //println!("Closure done");
//     concat(&mut fst_replacer, &sigma_star_consume_rangle)?;
//     //println!("Removing epsilons...");
//     optimize_fst(&mut fst_replacer, 1e-4)
//         .unwrap_or_else(|e| eprintln!("{e}: Optimization of fst_replacer failed."));
//     Ok(fst_replacer)
// }

fn build_fst_l1(
    sigma_star: VectorFst<TropicalWeight>,
    lambda_fst: VectorFst<TropicalWeight>,
    langle1: Label,
    langle2: Label,
) -> Result<VectorFst<TropicalWeight>> {
    let mut sigma_star: VectorFst<TropicalWeight> = sigma_star.clone();
    let start_state: StateId = sigma_star.start().unwrap();
    sigma_star.emplace_tr(start_state, langle2, langle2, 0.0, start_state)?;
    let consume_langle1: VectorFst<TropicalWeight> = fst![langle1 => EPS_LABEL; 0.0];
    let mut fst_l1 = sigma_star.clone();
    concat(&mut fst_l1, &lambda_fst)?;
    concat(&mut fst_l1, &consume_langle1)?;
    closure(&mut fst_l1, ClosureType::ClosureStar);
    concat(&mut fst_l1, &sigma_star)?;
    rm_epsilon(&mut fst_l1)?;
    Ok(fst_l1)
}

fn build_fst_l2(
    symt: Arc<SymbolTable>,
    sigma_star: VectorFst<TropicalWeight>,
    lambda_fst: VectorFst<TropicalWeight>,
    langle2: Label,
) -> Result<VectorFst<TropicalWeight>> {
    // Start with a universal acceptor
    let mut fst_l2 = sigma_star.clone();

    // Also construct the complement of lambda.
    let left_complement: VectorFst<TropicalWeight> =
        fst_complement(symt.clone(), lambda_fst, langle2)?;

    // left_complement.draw(
    //     "build_fst_l2_complement.dot",
    //     &DrawingConfig {
    //         vertical: true,
    //         size: Some((6.0, 4.0)),
    //         title: "Complement".to_string(),
    //         portrait: false,
    //         ranksep: Some(2.0),
    //         nodesep: Some(2.0),
    //         fontsize: 12,
    //         acceptor: true,
    //         show_weight_one: true,
    //         print_weight: true,
    //     },
    // )?;

    // We also need to create a transducer for the langle symbol
    let consume_langle2: VectorFst<TropicalWeight> = fst![langle2 => EPS_LABEL; 0.0];
    // fst_l2.draw(
    //     "build_fst_l2.dot",
    //     &DrawingConfig {
    //         vertical: true,
    //         size: Some((6.0, 4.0)),
    //         title: "l2 FST".to_string(),
    //         portrait: false,
    //         ranksep: Some(1.0),
    //         nodesep: Some(1.0),
    //         fontsize: 12,
    //         acceptor: false,
    //         show_weight_one: true,
    //         print_weight: true,
    //     },
    // )?;

    // Add the complment of lambda to the universal acceptor.
    concat(&mut fst_l2, &left_complement)?;
    // Then add the transducer for langle2.
    concat(&mut fst_l2, &consume_langle2)?;
    // Take the closure of the resulting FST
    closure(&mut fst_l2, ClosureType::ClosureStar);
    // Then compose a unversal acceptor.
    concat(&mut fst_l2, &sigma_star)?;

    // Remove the epsilon transitions.
    rm_epsilon(&mut fst_l2)?;
    Ok(fst_l2)
}

fn fst_complement(
    symt: Arc<SymbolTable>,
    fst: VectorFst<TropicalWeight>,
    langle2: Label,
) -> Result<VectorFst<TropicalWeight>> {
    let sigma: HashSet<Label> = symt
        .labels()
        .filter(|l| *l != EPS_LABEL && *l != langle2)
        .collect();
    let mut fst: VectorFst<TropicalWeight> = fst.clone();
    rm_epsilon(&mut fst)?;
    let mut fst: VectorFst<TropicalWeight> = determinize_with_config(
        &fst,
        DeterminizeConfig {
            delta: 1.0e-4,
            det_type: DeterminizeType::DeterminizeNonFunctional,
        },
    )?;
    let states: Vec<StateId> = fst.states_iter().collect();
    let sink: StateId = fst.add_state();
    fst.set_final(sink, 0.0)?;
    states.iter().for_each(|s| {
        let leaving: HashSet<Label> = fst
            .get_trs(*s)
            .unwrap()
            .iter()
            .map(|tr| tr.ilabel)
            .collect();
        let complement: HashSet<Label> = sigma.difference(&leaving).copied().collect();
        complement
            .iter()
            .for_each(|l| fst.emplace_tr(*s, *l, *l, 0.0, sink).unwrap());
        if fst.is_final(*s).unwrap() {
            fst.delete_final_weight(*s).unwrap();
        } else {
            fst.set_final(*s, 0.0).unwrap();
        }
    });
    Ok(fst)
}

// fn fst_complement_old(
//     fst: VectorFst<TropicalWeight>,
//     symt: Arc<SymbolTable>,
// ) -> Result<VectorFst<TropicalWeight>> {
//     let mut complement = fst.clone();
//     rm_epsilon(&mut complement)?;
//     let q_sink = complement.add_state();
//     for q in complement.states_iter() {
//         if q == q_sink {
//             continue;
//         }
//         let mut outbound = HashSet::<u32>::from_iter(symt.labels());
//         outbound.remove(&EPS_LABEL);
//         for tr in complement.get_trs(q)?.iter() {
//             if tr.ilabel != tr.olabel {
//                 return Err(anyhow::anyhow!("FST must be an acceptor"));
//             }
//             outbound.remove(&tr.ilabel);
//         }
//         for label in outbound {
//             complement.add_tr(q, Tr::new(label, label, 0.0, q_sink))?;
//         }
//         if complement.is_final(q)? {
//             complement.delete_final_weight(q)?;
//         } else {
//             complement.set_final(q, 0.0)?;
//         }
//     }
//     for label in symt.labels() {
//         if label == EPS_LABEL {
//             continue;
//         }
//         complement.add_tr(q_sink, Tr::new(label, label, 0.0, q_sink))?;
//     }
//     complement.set_final(q_sink, 0.0)?;

//     Ok(complement)
// }

#[allow(dead_code)]
fn any_symbol(symt: Arc<SymbolTable>) -> Result<VectorFst<TropicalWeight>> {
    let mut fst: VectorFst<TropicalWeight> = VectorFst::new();
    let q0 = fst.add_state();
    let q1 = fst.add_state();
    fst.set_start(q0)?;
    fst.set_final(q1, 0.0)?;
    symt.labels()
        .filter(|l| *l != 0)
        .for_each(|l| fst.emplace_tr(q0, l, l, 0.0, q1).unwrap());
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
pub fn sigma_star(symt: Arc<SymbolTable>) -> Result<VectorFst<TropicalWeight>> {
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

/// Return an fst that will accept any string s ∈ Σ*, with specified weight for each transition
pub fn weighted_sigma_star(
    symt: Arc<SymbolTable>,
    weight: f32,
) -> Result<VectorFst<TropicalWeight>> {
    let mut fst = VectorFst::<TropicalWeight>::new();
    fst.set_input_symbols(symt.clone());
    fst.set_output_symbols(symt.clone());
    let q0 = fst.add_state();
    fst.set_start(q0)?;
    fst.set_final(q0, 0.0)?;
    for (label, _) in symt.iter().filter(|(_, s)| *s != "<eps>") {
        fst.add_tr(q0, Tr::new(label, label, weight, q0))?;
    }
    let sink = fst.add_state();
    fst.set_final(sink, 0.0)?;
    fst.emplace_tr(q0, EPS_LABEL, EPS_LABEL, 0.0, sink)?;
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

// pub fn sigma_star(symt: Arc<SymbolTable>) -> Result<VectorFst<TropicalWeight>> {
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
    //println!("\n*** outputs={:?}", outputs);
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
            println!("{e}: Couldn't apply wFST {:?} to string {:?}.", fst, input);
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

pub fn fst_accepts(symt: Arc<SymbolTable>, fst: VectorFst<TropicalWeight>, string: String) -> bool {
    let linear_automaton: VectorFst<TropicalWeight> = string_to_linear_automaton(symt, &string);
    let composed: VectorFst<TropicalWeight> = compose(linear_automaton, fst).unwrap();
    composed.num_states() > 0
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::ruleparse::{parse_script, rule, rule_no_env};
    use rustfst::algorithms::rm_epsilon::rm_epsilon;

    #[test]
    fn test_component_build_fst_r1_a() {
        let symt: Arc<SymbolTable> = Arc::new(symt!["a", "b", "c", "d", "#", "$", "^", "%"]);
        let rho_fst: VectorFst<TropicalWeight> = fst![1 => 1];
        let sigma_star = weighted_sigma_star(symt.clone(), 1.0).unwrap();
        let rangle: Label = 6;

        let fst_r = build_fst_r(sigma_star, rho_fst, rangle).unwrap();

        let output = apply_fst(symt.clone(), fst_r, "#bacad#".to_string());
        assert_eq!(output, "#b$ac$ad#".to_string());
    }

    #[test]
    fn test_component_build_fst_r2_eps() {
        let symt: Arc<SymbolTable> = Arc::new(symt!["a", "b", "c", "d", "#", "$", "^", "%"]);
        let rho_fst: VectorFst<TropicalWeight> = any_symbol(symt.clone()).unwrap();
        let sigma_star = weighted_sigma_star(symt.clone(), 1.0).unwrap();
        let rangle: Label = 6;

        let fst_r = build_fst_r(sigma_star, rho_fst, rangle).unwrap();

        let output = apply_fst(symt.clone(), fst_r, "#abc#".to_string());
        assert_eq!(output, "$#$a$b$c$#".to_string());
    }

    #[test]
    fn test_component_build_fst_r1_one_char1() {
        let symt: Arc<SymbolTable> = Arc::new(symt!["a", "b", "c", "d", "#", "$", "^", "%"]);
        let rho_fst: VectorFst<TropicalWeight> = fst![1 => 1];
        let sigma_star = weighted_sigma_star(symt.clone(), 1.0).unwrap();
        let rangle: Label = 6;

        let fst_r = build_fst_r(sigma_star, rho_fst, rangle).unwrap();

        let output = apply_fst(symt.clone(), fst_r, "b".to_string());
        assert_eq!(output, "b".to_string());
    }

    #[test]
    fn test_component_build_fst_r1_one_char2() {
        let symt: Arc<SymbolTable> = Arc::new(symt!["a", "b", "c", "d", "#", "$", "^", "%"]);
        let rho_fst: VectorFst<TropicalWeight> = fst![1, 2 => 1, 2];
        let sigma_star = weighted_sigma_star(symt.clone(), 1.0).unwrap();
        let rangle: Label = 6;

        let fst_r = build_fst_r(sigma_star, rho_fst, rangle).unwrap();

        let output = apply_fst(symt.clone(), fst_r, "b".to_string());
        assert_eq!(output, "b".to_string());
    }

    #[test]
    fn test_component_build_fst_f1() {
        let symt: Arc<SymbolTable> = Arc::new(symt!["a", "b", "c", "#", "$", "^", "%"]);
        let sigma_star: VectorFst<TropicalWeight> = weighted_sigma_star(symt.clone(), 1.0).unwrap();
        let phi_fst = fst![1 => 1];
        let rangle = 5;
        let langle1 = 6;
        let langle2 = 7;

        let fst_f: VectorFst<TropicalWeight> =
            build_fst_f(sigma_star, phi_fst, rangle, langle1, langle2).unwrap();
        // rm_epsilon(&mut fst_f).unwrap();

        let input = "#ba$c#".to_string();

        let output: String = apply_fst(symt.clone(), fst_f, input);
        assert_eq!(output, "#b%a$c#");
    }

    #[test]
    fn test_component_build_fst_f2() {
        let symt: Arc<SymbolTable> = Arc::new(symt!["a", "b", "c", "#", "$", "^", "%"]);
        let sigma_star: VectorFst<TropicalWeight> = weighted_sigma_star(symt.clone(), 1.0).unwrap();
        let phi_fst = fst![1 => 1];
        let rangle = 5;
        let langle1 = 6;
        let langle2 = 7;

        let fst_f: VectorFst<TropicalWeight> =
            build_fst_f(sigma_star, phi_fst, rangle, langle1, langle2).unwrap();
        // rm_epsilon(&mut fst_f).unwrap();

        let input = "#ba$ccca$b#".to_string();

        let output: String = apply_fst(symt.clone(), fst_f, input);
        assert_eq!(output, "#b%a$ccc%a$b#");
    }

    #[test]
    fn test_component_build_fst_f_one_char1() {
        let symt: Arc<SymbolTable> = Arc::new(symt!["a", "b", "c", "#", "$", "^", "%"]);
        let sigma_star: VectorFst<TropicalWeight> = weighted_sigma_star(symt.clone(), 1.0).unwrap();
        let phi_fst = fst![1 => 1];
        let rangle = 5;
        let langle1 = 6;
        let langle2 = 7;

        let fst_f: VectorFst<TropicalWeight> =
            build_fst_f(sigma_star, phi_fst, rangle, langle1, langle2).unwrap();
        // rm_epsilon(&mut fst_f).unwrap();

        let input = "a".to_string();

        let output: String = apply_fst(symt.clone(), fst_f, input);
        assert_eq!(output, "a");
    }

    #[test]
    fn test_component_build_fst_f_one_char2() {
        let symt: Arc<SymbolTable> = Arc::new(symt!["a", "b", "c", "#", "$", "^", "%"]);
        let sigma_star: VectorFst<TropicalWeight> = weighted_sigma_star(symt.clone(), 1.0).unwrap();
        let phi_fst = fst![1 => 1];
        let rangle = 5;
        let langle1 = 6;
        let langle2 = 7;

        let fst_f: VectorFst<TropicalWeight> =
            build_fst_f(sigma_star, phi_fst, rangle, langle1, langle2).unwrap();
        // rm_epsilon(&mut fst_f).unwrap();

        let input = "a$".to_string();

        let output: String = apply_fst(symt.clone(), fst_f, input);
        assert!(output == "^a$" || output == "%a$");
    }

    #[test]
    fn test_component_build_fst_replacer1() {
        let symt: Arc<SymbolTable> = Arc::new(symt!["a", "b", "c", "#", "$", "^", "%"]);
        let sigma_star: VectorFst<TropicalWeight> = weighted_sigma_star(symt.clone(), 1.0).unwrap();
        let phi_fst = fst![1 => 0; 0.0];
        let psi_fst = fst![0 => 2; 0.0];
        let rangle = 5;
        let langle1 = 6;
        let langle2 = 7;

        let fst_replacer: VectorFst<TropicalWeight> =
            build_fst_replacer(sigma_star, phi_fst, psi_fst, rangle, langle1, langle2).unwrap();

        let input: String = "aa^a$".to_string();

        let output: String = apply_fst(symt.clone(), fst_replacer, input);
        assert_eq!(output, "aa^b");
    }

    #[test]
    fn test_component_build_fst_replacer2() {
        let symt: Arc<SymbolTable> = Arc::new(symt!["a", "b", "c", "#", "$", "^", "%"]);
        let sigma_star: VectorFst<TropicalWeight> = weighted_sigma_star(symt.clone(), 1.0).unwrap();
        let phi_fst = fst![1 => 0; 0.0];
        let psi_fst = fst![0 => 2; 0.0];
        let rangle = 5;
        let langle1 = 6;
        let langle2 = 7;

        let fst_replacer: VectorFst<TropicalWeight> =
            build_fst_replacer(sigma_star, phi_fst, psi_fst, rangle, langle1, langle2).unwrap();

        let input: String = "^a$ca$ca$c".to_string();

        let output: String = apply_fst(symt.clone(), fst_replacer, input);
        assert_eq!(output, "^bcacac");
    }

    #[test]
    fn test_component_build_fst_replacer3() {
        let symt: Arc<SymbolTable> = Arc::new(symt!["a", "b", "c", "#", "$", "^", "%"]);
        let sigma_star: VectorFst<TropicalWeight> = weighted_sigma_star(symt.clone(), 1.0).unwrap();
        let phi_fst = fst![1,3 => 0; 0.0];
        let psi_fst = fst![0 => 2; 0.0];
        let rangle = 5;
        let langle1 = 6;
        let langle2 = 7;

        let fst_replacer: VectorFst<TropicalWeight> =
            build_fst_replacer(sigma_star, phi_fst, psi_fst, rangle, langle1, langle2).unwrap();

        let input: String = "^ac$^ac$ac".to_string();

        let output: String = apply_fst(symt.clone(), fst_replacer, input);
        assert_eq!(output, "^b^bac");
    }

    #[test]
    fn test_component_build_fst_replacer4() {
        let symt: Arc<SymbolTable> = Arc::new(symt!["a", "b", "c", "#", "$", "^", "%"]);
        let sigma_star: VectorFst<TropicalWeight> = weighted_sigma_star(symt.clone(), 1.0).unwrap();
        let phi_fst = fst![1,3 => 0; 0.0];
        let psi_fst = fst![0 => 2; 0.0];
        let rangle = 5;
        let langle1 = 6;
        let langle2 = 7;

        let fst_replacer: VectorFst<TropicalWeight> =
            build_fst_replacer(sigma_star, phi_fst, psi_fst, rangle, langle1, langle2).unwrap();

        let input: String = "acacac".to_string();

        let output: String = apply_fst(symt.clone(), fst_replacer, input);
        assert_eq!(output, "acacac");
    }

    #[test]
    fn test_component_build_fst_replacer_one_char1() {
        let symt: Arc<SymbolTable> = Arc::new(symt!["a", "b", "c", "#", "$", "^", "%"]);
        let sigma_star: VectorFst<TropicalWeight> = weighted_sigma_star(symt.clone(), 1.0).unwrap();
        let phi_fst = fst![2 => 0; 0.0];
        let psi_fst = fst![0 => 3; 0.0];
        let rangle = 5;
        let langle1 = 6;
        let langle2 = 7;

        let fst_replacer: VectorFst<TropicalWeight> =
            build_fst_replacer(sigma_star, phi_fst, psi_fst, rangle, langle1, langle2).unwrap();

        let input: String = "a".to_string();

        let output: String = apply_fst(symt.clone(), fst_replacer, input);
        assert_eq!(output, "a");
    }

    #[test]
    fn test_component_build_fst_replacer_one_char2() {
        let symt: Arc<SymbolTable> = Arc::new(symt!["a", "b", "c", "#", "$", "^", "%"]);
        let sigma_star: VectorFst<TropicalWeight> = weighted_sigma_star(symt.clone(), 1.0).unwrap();
        let phi_fst = fst![1 => 0; 0.0];
        let psi_fst = fst![0 => 2; 0.0];
        let rangle = 5;
        let langle1 = 6;
        let langle2 = 7;

        let fst_replacer: VectorFst<TropicalWeight> =
            build_fst_replacer(sigma_star, phi_fst, psi_fst, rangle, langle1, langle2).unwrap();

        let input: String = "a".to_string();

        let output: String = apply_fst(symt.clone(), fst_replacer, input);
        assert_eq!(output, "a");
    }

    #[test]
    fn test_component_build_fst_l1_1() {
        let symt: Arc<SymbolTable> = Arc::new(symt!["a", "b", "c", "#", "$", "^", "%"]);
        // let sigma_star: VectorFst<TropicalWeight> = weighted_sigma_star(symt.clone(), 1.0).unwrap();
        let mut sigma_star: VectorFst<TropicalWeight> = VectorFst::new();
        let start_state = sigma_star.add_state();
        sigma_star.set_start(start_state).unwrap();
        sigma_star.set_final(start_state, 0.0).unwrap();
        symt.labels().filter(|l| *l != 0 && *l != 6).for_each(|l| {
            sigma_star
                .emplace_tr(start_state, l, l, 10.0, start_state)
                .unwrap()
        });
        let lambda_fst: VectorFst<TropicalWeight> = fst![1 => 1; 0.0];
        let langle1: Label = 6;
        let langle2: Label = 7;
        let fst_l1: VectorFst<TropicalWeight> =
            build_fst_l1(sigma_star, lambda_fst, langle1, langle2).unwrap();
        assert!(fst_accepts(symt, fst_l1, "a^b".to_string()));
    }

    #[test]
    fn test_component_build_fst_l1_2() {
        let symt: Arc<SymbolTable> = Arc::new(symt!["a", "b", "c", "#", "$", "^", "%"]);
        // let sigma_star: VectorFst<TropicalWeight> = weighted_sigma_star(symt.clone(), 1.0).unwrap();
        let mut sigma_star: VectorFst<TropicalWeight> = VectorFst::new();
        let start_state = sigma_star.add_state();
        sigma_star.set_start(start_state).unwrap();
        sigma_star.set_final(start_state, 0.0).unwrap();
        symt.labels().filter(|l| *l != 0 && *l != 6).for_each(|l| {
            sigma_star
                .emplace_tr(start_state, l, l, 10.0, start_state)
                .unwrap()
        });
        let lambda_fst: VectorFst<TropicalWeight> = fst![1 => 1; 0.0];
        let langle1: Label = 6;
        let langle2: Label = 7;
        let fst_l1: VectorFst<TropicalWeight> =
            build_fst_l1(sigma_star, lambda_fst, langle1, langle2).unwrap();
        assert!(!fst_accepts(symt, fst_l1, "c^b".to_string()));
    }

    #[test]
    fn test_component_build_fst_l1_on_char1() {
        let symt: Arc<SymbolTable> = Arc::new(symt!["a", "b", "c", "#", "$", "^", "%"]);
        // let sigma_star: VectorFst<TropicalWeight> = weighted_sigma_star(symt.clone(), 1.0).unwrap();
        let mut sigma_star: VectorFst<TropicalWeight> = VectorFst::new();
        let start_state = sigma_star.add_state();
        sigma_star.set_start(start_state).unwrap();
        sigma_star.set_final(start_state, 0.0).unwrap();
        symt.labels().filter(|l| *l != 0 && *l != 6).for_each(|l| {
            sigma_star
                .emplace_tr(start_state, l, l, 10.0, start_state)
                .unwrap()
        });
        let lambda_fst: VectorFst<TropicalWeight> = fst![1 => 1; 0.0];
        let langle1: Label = 6;
        let langle2: Label = 7;
        let fst_l1: VectorFst<TropicalWeight> =
            build_fst_l1(sigma_star, lambda_fst, langle1, langle2).unwrap();
        assert!(fst_accepts(symt, fst_l1, "a".to_string()));
    }

    #[test]
    fn test_component_build_fst_l1_on_char2() {
        let symt: Arc<SymbolTable> = Arc::new(symt!["a", "b", "c", "#", "$", "^", "%"]);
        // let sigma_star: VectorFst<TropicalWeight> = weighted_sigma_star(symt.clone(), 1.0).unwrap();
        let mut sigma_star: VectorFst<TropicalWeight> = VectorFst::new();
        let start_state = sigma_star.add_state();
        sigma_star.set_start(start_state).unwrap();
        sigma_star.set_final(start_state, 0.0).unwrap();
        symt.labels().filter(|l| *l != 0 && *l != 6).for_each(|l| {
            sigma_star
                .emplace_tr(start_state, l, l, 10.0, start_state)
                .unwrap()
        });
        let lambda_fst: VectorFst<TropicalWeight> = fst![1 => 1; 0.0];
        let langle1: Label = 6;
        let langle2: Label = 7;
        let fst_l1: VectorFst<TropicalWeight> =
            build_fst_l1(sigma_star, lambda_fst, langle1, langle2).unwrap();
        assert!(!fst_accepts(symt, fst_l1, "b^".to_string()));
    }

    #[test]
    fn test_component_build_fst_l2_1() {
        let symt: Arc<SymbolTable> = Arc::new(symt!["a", "b", "c", "#", "$", "^", "%"]);
        // let sigma_star: VectorFst<TropicalWeight> = weighted_sigma_star(symt.clone(), 1.0).unwrap();
        let mut sigma_star: VectorFst<TropicalWeight> = VectorFst::new();
        let start_state = sigma_star.add_state();
        sigma_star.set_start(start_state).unwrap();
        sigma_star.set_final(start_state, 0.0).unwrap();
        symt.clone()
            .labels()
            .filter(|l| *l != 0 && *l < 4)
            .for_each(|l| {
                sigma_star
                    .emplace_tr(start_state, l, l, 10.0, start_state)
                    .unwrap()
            });
        let lambda_fst: VectorFst<TropicalWeight> = fst![1 => 1; 0.0];
        let langle2: Label = 7;
        let fst_l2: VectorFst<TropicalWeight> =
            build_fst_l2(symt.clone(), sigma_star, lambda_fst, langle2).unwrap();
        assert!(fst_accepts(symt.clone(), fst_l2, "c%b".to_string()));
    }

    #[test]
    fn test_component_build_fst_l2_2() {
        let symt: Arc<SymbolTable> = Arc::new(symt!["a", "b", "c", "#", "$", "^", "%"]);
        // let sigma_star: VectorFst<TropicalWeight> = weighted_sigma_star(symt.clone(), 1.0).unwrap();
        let mut sigma_star: VectorFst<TropicalWeight> = VectorFst::new();
        let start_state = sigma_star.add_state();
        sigma_star.set_start(start_state).unwrap();
        sigma_star.set_final(start_state, 0.0).unwrap();
        symt.clone()
            .labels()
            .filter(|l| *l != 0 && *l < 4)
            .for_each(|l| {
                dbg!(l);
                sigma_star
                    .emplace_tr(start_state, l, l, 10.0, start_state)
                    .unwrap()
            });
        let lambda_fst: VectorFst<TropicalWeight> = fst![1 => 1; 0.0];
        let langle2: Label = 7;
        let fst_l2: VectorFst<TropicalWeight> =
            build_fst_l2(symt.clone(), sigma_star, lambda_fst, langle2).unwrap();
        assert!(!fst_accepts(symt.clone(), fst_l2, "a%b".to_string()))
    }

    #[test]
    fn test_component_build_fst_l2_3() {
        let symt: Arc<SymbolTable> = Arc::new(symt!["a", "b", "c", "#", "$", "^", "%"]);
        // let sigma_star: VectorFst<TropicalWeight> = weighted_sigma_star(symt.clone(), 1.0).unwrap();
        let mut sigma_star: VectorFst<TropicalWeight> = VectorFst::new();
        let start_state = sigma_star.add_state();
        sigma_star.set_start(start_state).unwrap();
        sigma_star.set_final(start_state, 0.0).unwrap();
        symt.clone()
            .labels()
            .filter(|l| *l != 0 && *l < 4)
            .for_each(|l| {
                sigma_star
                    .emplace_tr(start_state, l, l, 10.0, start_state)
                    .unwrap()
            });
        let lambda_fst: VectorFst<TropicalWeight> = fst![1, 3 => 1, 3; 0.0];
        let langle2: Label = 7;
        let fst_l2: VectorFst<TropicalWeight> =
            build_fst_l2(symt.clone(), sigma_star, lambda_fst, langle2).unwrap();
        assert!(!fst_accepts(symt.clone(), fst_l2, "ac%b".to_string()));
    }

    #[test]
    fn test_fst_complement1() {
        let symt: Arc<SymbolTable> = Arc::new(symt!["a", "b", "c", "%"]);
        let mut fst1: VectorFst<TropicalWeight> = fst![1 => 1; 0.0];
        let fst2: VectorFst<TropicalWeight> = fst![2 => 2; 0.0];
        union(&mut fst1, &fst2).unwrap();
        let mut fst: VectorFst<TropicalWeight> = fst_complement(symt.clone(), fst1, 4).unwrap();
        fst.set_input_symbols(symt.clone());
        fst.set_output_symbols(symt.clone());
        assert!(fst_accepts(symt.clone(), fst, "c".to_string()))
    }

    #[test]
    fn test_fst_complement2() {
        let symt: Arc<SymbolTable> = Arc::new(symt!["a", "b", "c", "%"]);
        let mut fst1: VectorFst<TropicalWeight> = fst![1 => 1; 0.0];
        let fst2: VectorFst<TropicalWeight> = fst![2 => 2; 0.0];
        union(&mut fst1, &fst2).unwrap();
        let mut fst: VectorFst<TropicalWeight> = fst_complement(symt.clone(), fst1, 4).unwrap();
        fst.set_input_symbols(symt.clone());
        fst.set_output_symbols(symt.clone());
        assert!(!fst_accepts(symt.clone(), fst, "a".to_string()))
    }

    #[test]
    fn test_fst_complement3() {
        let symt: Arc<SymbolTable> = Arc::new(symt!["a", "b", "c", "%"]);
        let mut fst1: VectorFst<TropicalWeight> = fst![1,2 => 1; 0.0];
        let fst2: VectorFst<TropicalWeight> = fst![2,3 => 2; 0.0];
        union(&mut fst1, &fst2).unwrap();
        let mut fst: VectorFst<TropicalWeight> = fst_complement(symt.clone(), fst1, 4).unwrap();
        fst.set_input_symbols(symt.clone());
        fst.set_output_symbols(symt.clone());
        assert!(fst_accepts(symt.clone(), fst, "ac".to_string()))
    }

    #[test]
    fn test_fst_complement4() {
        let symt: Arc<SymbolTable> = Arc::new(symt!["a", "b", "c", "%"]);
        let mut fst1: VectorFst<TropicalWeight> = fst![1,2 => 1; 0.0];
        let fst2: VectorFst<TropicalWeight> = fst![2,3 => 2; 0.0];
        union(&mut fst1, &fst2).unwrap();
        let mut fst: VectorFst<TropicalWeight> = fst_complement(symt.clone(), fst1, 4).unwrap();
        fst.set_input_symbols(symt.clone());
        fst.set_output_symbols(symt.clone());
        assert!(!fst_accepts(symt.clone(), fst, "ab".to_string()))
    }

    #[test]
    fn test_fst_complement_accepts_one_char1() {
        let symt: Arc<SymbolTable> = Arc::new(symt!["a", "b", "c", "%"]);
        let fst1: VectorFst<TropicalWeight> = fst![2 => 2; 0.0];
        let mut fst: VectorFst<TropicalWeight> = fst_complement(symt.clone(), fst1, 4).unwrap();
        fst.set_input_symbols(symt.clone());
        fst.set_output_symbols(symt.clone());
        assert!(fst_accepts(symt.clone(), fst, "a".to_string()))
    }

    #[test]
    fn test_fst_complement_one_char1() {
        let symt: Arc<SymbolTable> = Arc::new(symt!["a", "b", "c", "%"]);
        let fst1: VectorFst<TropicalWeight> = fst![1 => 1; 0.0];
        let mut fst: VectorFst<TropicalWeight> = fst_complement(symt.clone(), fst1, 4).unwrap();
        fst.set_input_symbols(symt.clone());
        fst.set_output_symbols(symt.clone());
        assert!(!fst_accepts(symt.clone(), fst, "a".to_string()))
    }

    #[test]
    fn test_closure() {
        let symt: Arc<SymbolTable> = Arc::new(symt!["a", "b", "c", "#"]);
        let mut fst: VectorFst<TropicalWeight> = fst![1 => 2, 3; 0.0];
        closure(&mut fst, ClosureType::ClosureStar);

        let input: String = "aaa".to_string();
        let output: String = apply_fst(symt.clone(), fst, input);
        assert_eq!(output, "bcbcbc".to_string());
    }

    #[test]
    fn test_closure2() {
        let symt: Arc<SymbolTable> = Arc::new(symt!["a", "b", "c", "#"]);
        let sigma_star: VectorFst<TropicalWeight> = weighted_sigma_star(symt.clone(), 1.0).unwrap();
        let mut fst: VectorFst<TropicalWeight> = sigma_star.clone();
        let replace_fst: VectorFst<TropicalWeight> = fst![1 => 2, 3; 0.0];
        concat(&mut fst, &replace_fst).unwrap();
        closure(&mut fst, ClosureType::ClosureStar);
        concat(&mut fst, &sigma_star).unwrap();

        let input: String = "aaa".to_string();
        let output: String = apply_fst(symt.clone(), fst, input);
        assert_eq!(output, "bcbcbc".to_string());
    }

    // #[test]
    // fn test_compile_script_basic() {
    //     let (_, (script, syms)) = parse_script("::seg:: = abcdefghijklmnopqrstuvwxyzñ']\n[1234] -> {14} / #::seg::+ _ \n[23] -> {4} / _ ").expect("Failed to parse script in test");
    //     let mut inner_symt = symt!["#"];
    //     inner_symt.add_symbols(syms);
    //     let symt = Arc::new(inner_symt);
    //     println!("script={:?}", script);
    //     let fst = compile_script(symt.clone(), script).unwrap_or_else(|e| {
    //         println!("{e}: Could not compile script.");
    //         VectorFst::<TropicalWeight>::new()
    //     });
    //     fst.draw("test2.dot", &DrawingConfig::default()).unwrap();
    //     let result = apply_fst(symt.clone(), fst, "#ni1hao3#".to_string());
    //     assert_eq!(result, "#ni{14}hao{4}#".to_string());
    // }

    #[test]
    fn test_compile_script_basic2() {
        let symt = Arc::new(symt!["p", "b", "a", "i"]);
        let (_, (script, _syms)) =
            parse_script("p -> b / (a|i|b) _ (a|i|b)").expect("Failed to parse script in test");
        let mut fst =
            compile_script(symt.clone(), script).expect("Failed to compile script in test");
        rm_epsilon(&mut fst).unwrap();
        fst.draw("test.dot", &DrawingConfig::default()).unwrap();
        let result = apply_fst(symt.clone(), fst, "apbppi".to_string());
        assert_eq!(result, "abbppi".to_string());
    }

    #[test]
    fn test_compile_script_basic3() {
        let symt = Arc::new(symt!["p", "b", "a", "i"]);
        let (_, (script, _syms)) =
            parse_script("p -> b / a _ a").expect("Failed to parse script in test");
        let mut fst =
            compile_script(symt.clone(), script).expect("Failed to compile script in test");
        rm_epsilon(&mut fst).unwrap();
        fst.draw("test.dot", &DrawingConfig::default()).unwrap();
        let result = apply_fst(symt.clone(), fst, "papapbipapap".to_string());
        assert_eq!(result, "pabapbipabap".to_string());
    }

    #[test]
    fn test_compile_script_basic_with_comment() {
        let symt = Arc::new(symt!["p", "b", "a", "i"]);
        let (_, (script, _syms)) = parse_script(
            "::voi::=(b|a|i)\n% The rules start here:\np -> b / (::voi::) _ (::voi::)",
        )
        .expect("Failed to parse script in test");
        let mut fst =
            compile_script(symt.clone(), script).expect("Failed to compile script in test");
        rm_epsilon(&mut fst).unwrap();
        fst.draw("test.dot", &DrawingConfig::default()).unwrap();
        let result = apply_fst(symt.clone(), fst, "apbppi".to_string());
        assert_eq!(result, "abbppi".to_string());
    }

    fn evaluate_rule(symt: Arc<SymbolTable>, rule_str: &str, input: &str, output: &str) {
        let macros: &HashMap<String, RegexAST> = &HashMap::new();
        let (_, (rewrite_rule, _syms)) = rule(rule_str).expect("Failed to parse rule in test");
        let fst: VectorFst<TropicalWeight> = rule_fst(symt.clone(), macros, rewrite_rule)
            .unwrap_or_else(|e| {
                eprintln!("{e}: Failed to create rule FST in test.");
                VectorFst::new()
            });
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
    fn test_kleene_plus7() {
        evaluate_rule(
            Arc::new(symt!["#", "a", "b", "c", "d"]),
            "a -> b / (cd)+ _ ",
            "a",
            "a",
        )
    }

    #[test]
    fn test_kleene_plus8() {
        evaluate_rule(
            Arc::new(symt!["#", "a", "b", "c", "d"]),
            "a -> b / (cd)+ _ ",
            "ca",
            "ca",
        )
    }

    #[test]
    fn test_kleene_plus9() {
        evaluate_rule(
            Arc::new(symt!["#", "a", "b", "c", "d"]),
            "a -> b / _ (cd)+",
            "acd",
            "bcd",
        )
    }

    #[test]
    fn test_kleene_plus10() {
        evaluate_rule(
            Arc::new(symt!["#", "a", "b", "c", "d"]),
            "a -> b / _ (cd)+",
            "a",
            "a",
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

    fn evaluate_script(symt: Arc<SymbolTable>, script: &str, input: &str, output: &str) {
        let (_, (script, _syms)) = parse_script(script).expect("Failed to parse script in test");
        dbg!(script.clone());
        // panic!("Stopped here");
        let fst: VectorFst<TropicalWeight> =
            compile_script(symt.clone(), script).expect("Faiiled to compile script in test");
        let hypothesis = apply_fst(symt.clone(), fst, input.to_string());
        assert_eq!(hypothesis, output);
    }

    #[test]

    fn test_script_order_two_simple_rules() {
        let symt = Arc::new(symt!["a", "b", "c", "d", "#"]);
        let script = r#"a -> b
c -> d
"#;
        evaluate_script(symt, script, "aac", "bbd");
    }

    #[test]
    fn test_script_order_feed1() {
        let symt = Arc::new(symt!["a", "b", "c", "d", "#"]);
        let script = r#"a -> b / b _ c
    c -> d / b _
"#;
        evaluate_script(symt, script, "bac", "bbd");
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
