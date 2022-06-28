use anyhow::Result;
use rustfst::prelude::*;
use rustfst::trs::Trs;
use rustfst::utils::*;
use std::char;
use std::sync::Arc;

use crate::ruleparse::RegexAST;
// use crate::*;
// use rustfst::algorithms::determinize::{DeterminizeType, determinize};
// buse rustfst::algorithms::rm_epsilon::rm_epsilon;

fn unicode_symbol_table() -> Arc<SymbolTable> {
    let mut symt = SymbolTable::new();
    (1..0xFFFF)
        .map(|i| char::from_u32(i))
        .filter_map(|i| i)
        .for_each(|i| {
            let _ = symt.add_symbol((i));
        });
    Arc::new(symt)
}

fn context_node_fst(symt: Arc<SymbolTable>, node: RegexAST) -> Result<VectorFst<TropicalWeight>> {
    match node {
        RegexAST::Char(c) => char_fst(c),
        RegexAST::Group(v) => group_fst(v),
        RegexAST::Option(n) => option_fst(n),
        RegexAST::Star(n) => star_fst(n),
        RegexAST::Plus(n) => plus_fst(n),
        RegexAST::Disjunction(v) => disjunction_fst(v),
        RegexAST::Class(v) => class_fst(v),
        RegexAST::ClassComplement(v) => class_complement_fst(v),
        RegexAST::Epsilon => epsilon_fst(),
        RegexAST::Boundary => boundary_fst(),
        RegexAST::Comment => comment_fst(),
    }
}

fn char_fst(symt: Arc<SymbolTable>, c: char) -> Result<VectorFst<TropicalWeight>> {
    let mut fst = VectorFst::<TropicalWeight>::new();
    fst.set_input_symbols(symt.clone());
    fst.set_output_symbols(symt.clone());
    let q0 = fst.add_state();
    let q1 = fst.add_state();
    fst.set_start(q0);
    fst.set_final(q1, 0.0);
    let label = symt.get_label(c.to_string()).unwrap();
    fst.add_tr(q0, Tr::new(label, label, 0.0, q1))?;
    Ok(fst)
}

fn epsilon_fst(symt: Arc<SymbolTable>) -> Result<VectorFst<TropicalWeight>> {
    let mut fst = VectorFst::<TropicalWeight>::new();
    fst.set_input_symbols(symt.clone());
    fst.set_output_symbols(symt.clone());
    let q0 = fst.add_state();
    let q1 = fst.add_state();
    fst.set_start(q0);
    fst.set_final(q1, 0.0);
    // The label 0 indicates epsilon
    fst.add_tr(q0, Tr::new(0, 0, 0.0, q1))?;
    Ok(fst)
}

fn group_fst(symt: Arc<SymbolTable>, v: Vec<RegexAST>) -> Result<VectorFst<TropicalWeight>> {
    let mut fst = VectorFst::<TropicalWeight>::new();
    fst.set_input_symbols(symt.clone());
    fst.set_output_symbols(symt.clone());
    let q0 = fst.add_state();
    fst.set_start(q0);
    // Need to implement loop with selection
    Ok(fst)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_symt1() {
        let symt = unicode_symbol_table();
        assert_eq!(symt.get_symbol(0x0021), Some("!"));
    }

    #[test]
    fn test_char1() {
        let symt = unicode_symbol_table();
        let fst = char_fst(symt, 'a');
        let paths: Vec<_> = fst.unwrap().paths_iter().collect();
        assert_eq!(paths.len(), 1);
    }
}
