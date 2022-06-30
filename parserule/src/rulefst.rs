use anyhow::Result;
use rustfst::algorithms::compose::compose;
use rustfst::algorithms::union::union;
use rustfst::fst_impls::VectorFst;
use rustfst::fst_traits::{CoreFst, MutableFst};
use rustfst::prelude::*;
use std::char;
use std::collections::HashMap;
use std::collections::HashSet;
use std::sync::Arc;

use crate::ruleparse::{RegexAST, Statement};

fn unicode_symbol_table() -> Arc<SymbolTable> {
    let mut symt = SymbolTable::new();
    (1..0xFFFF)
        .map(|i| char::from_u32(i))
        .filter_map(|i| i)
        .for_each(|i| {
            let _ = symt.add_symbol(i);
        });
    Arc::new(symt)
}

fn universal_acceptor(symt: Arc<SymbolTable>) -> Result<VectorFst<TropicalWeight>> {
    let mut fst = VectorFst::<TropicalWeight>::new();
    fst.set_input_symbols(symt.clone());
    fst.set_output_symbols(symt.clone());
    let q0 = fst.add_state();
    fst.set_start(q0)?;
    fst.set_final(q0, 0.0)?;
    for (label, _) in symt.iter() {
        fst.add_tr(q0, Tr::new(label, label, 0.0, q0));
    }
    Ok(fst)
}

fn compile_script(statements: Vec<Statement>) -> Result<VectorFst<TropicalWeight>> {
    let symt = unicode_symbol_table();
    let fst = universal_acceptor(symt)?;
    for statement in statements {
        match statement {
            Statement::Comment => (),
            Statement::MacroDef((mac, def)) => (),
            Statement::Rule(rule) => (),
        }
    }
    Ok(fst)
}

fn context_node_fst(
    symt: Arc<SymbolTable>,
    macros: &HashMap<String, RegexAST>,
    node: RegexAST,
) -> Result<VectorFst<TropicalWeight>> {
    match node {
        RegexAST::Char(c) => char_fst(symt, macros, c),
        RegexAST::Group(v) => group_fst(symt, macros, v),
        RegexAST::Option(n) => option_fst(symt, macros, *n),
        RegexAST::Star(n) => star_fst(symt, macros, *n),
        RegexAST::Plus(n) => plus_fst(symt, macros, *n),
        RegexAST::Disjunction(v) => disjunction_fst(symt, macros, v),
        RegexAST::Class(v) => class_fst(symt, macros, v),
        RegexAST::ClassComplement(v) => class_complement_fst(symt, macros, v),
        RegexAST::Macro(m) => macro_fst(symt, macros, m),
        // RegexAST::MacroDef(mdef) => macro_def_fst(symt, macros, mdef),
        RegexAST::Epsilon => epsilon_fst(symt, macros),
        _ => epsilon_fst(symt, macros),
    }
}

fn char_fst(
    symt: Arc<SymbolTable>,
    macros: &HashMap<String, RegexAST>,
    c: char,
) -> Result<VectorFst<TropicalWeight>> {
    let mut fst = VectorFst::<TropicalWeight>::new();
    fst.set_input_symbols(symt.clone());
    fst.set_output_symbols(symt.clone());
    let q0 = fst.add_state();
    let q1 = fst.add_state();
    fst.set_start(q0)?;
    fst.set_final(q1, 0.0)?;
    let label = symt.get_label(c.to_string()).unwrap();
    fst.add_tr(q0, Tr::new(label, label, 0.0, q1))?;
    Ok(fst)
}

fn epsilon_fst(
    symt: Arc<SymbolTable>,
    macros: &HashMap<String, RegexAST>,
) -> Result<VectorFst<TropicalWeight>> {
    let mut fst = VectorFst::<TropicalWeight>::new();
    fst.set_input_symbols(symt.clone());
    fst.set_output_symbols(symt.clone());
    let q0 = fst.add_state();
    let q1 = fst.add_state();
    fst.set_start(q0)?;
    fst.set_final(q1, 0.0)?;
    // The label 0 indicates epsilon
    fst.add_tr(q0, Tr::new(0, 0, 0.0, q1))?;
    Ok(fst)
}

fn class_fst(
    symt: Arc<SymbolTable>,
    macros: &HashMap<String, RegexAST>,
    v: Vec<RegexAST>,
) -> Result<VectorFst<TropicalWeight>> {
    let mut fst = VectorFst::<TropicalWeight>::new();
    fst.set_input_symbols(symt.clone());
    fst.set_output_symbols(symt.clone());
    let q0 = fst.add_state();
    let q1 = fst.add_state();
    fst.set_start(q0)?;
    fst.set_final(q1, 0.0)?;
    for n in v {
        match n {
            RegexAST::Char(c) => {
                let label = symt.get_label(c.to_string()).unwrap();
                fst.add_tr(q0, Tr::new(label, label, 0.0, q1))?;
            }
            _ => (),
        }
    }
    Ok(fst)
}

fn class_complement_fst(
    symt: Arc<SymbolTable>,
    macros: &HashMap<String, RegexAST>,
    v: Vec<RegexAST>,
) -> Result<VectorFst<TropicalWeight>> {
    let mut fst = VectorFst::<TropicalWeight>::new();
    fst.set_input_symbols(symt.clone());
    fst.set_output_symbols(symt.clone());
    let q0 = fst.add_state();
    let q1 = fst.add_state();
    fst.set_start(q0)?;
    fst.set_final(q1, 0.0)?;
    let mut excluded: HashSet<u32> = HashSet::new();
    for n in v {
        match n {
            RegexAST::Char(c) => {
                let label = symt.get_label(c.to_string()).unwrap();
                excluded.insert(label);
            }
            _ => (),
        }
    }
    for (label, _) in symt.iter() {
        if !excluded.contains(&label) {
            fst.add_tr(q0, Tr::new(label, label, 0.0, q1))?;
        }
    }
    Ok(fst)
}

fn group_fst(
    symt: Arc<SymbolTable>,
    macros: &HashMap<String, RegexAST>,
    v: Vec<RegexAST>,
) -> Result<VectorFst<TropicalWeight>> {
    let mut fst = VectorFst::<TropicalWeight>::new();
    fst.set_input_symbols(symt.clone());
    fst.set_output_symbols(symt.clone());
    let q0 = fst.add_state();
    fst.set_start(q0)?;
    let mut last_final_state = 0;
    for n in v {
        match n {
            RegexAST::Boundary => {
                fst.set_final(last_final_state, -1.0)?;
            }
            _ => {
                let inner_fst = context_node_fst(symt.clone(), macros, n).unwrap();
                fst = compose(fst, inner_fst).unwrap();
                for s in fst.states_iter() {
                    if fst.is_final(s).unwrap() {
                        last_final_state = s;
                    }
                }
            }
        }
    }
    Ok(fst)
}

fn option_fst(
    symt: Arc<SymbolTable>,
    macros: &HashMap<String, RegexAST>,
    n: RegexAST,
) -> Result<VectorFst<TropicalWeight>> {
    let mut fst = context_node_fst(symt, macros, n).unwrap();
    let q0 = fst.start().unwrap();
    fst.set_final(q0, 0.0)?;
    Ok(fst)
}

fn star_fst(
    symt: Arc<SymbolTable>,
    macros: &HashMap<String, RegexAST>,
    n: RegexAST,
) -> Result<VectorFst<TropicalWeight>> {
    let mut fst = context_node_fst(symt, macros, n).unwrap();
    let q0 = fst.start().unwrap();
    fst.set_final(q0, 0.0)?;
    let fst2 = fst.clone();
    let final_states = fst2
        .states_iter()
        .filter(|&s| fst2.final_weight(s).unwrap().unwrap() != TropicalWeight::zero());
    for s in final_states {
        fst.add_tr(s, Tr::new(0, 0, 0.0, q0))?;
    }
    Ok(fst)
}

fn plus_fst(
    symt: Arc<SymbolTable>,
    macros: &HashMap<String, RegexAST>,
    n: RegexAST,
) -> Result<VectorFst<TropicalWeight>> {
    let mut fst = context_node_fst(symt, macros, n).unwrap();
    let q0 = fst.start().unwrap();
    let fst2 = fst.clone();
    let final_states = fst2
        .states_iter()
        .filter(|&s| fst2.final_weight(s).unwrap().unwrap() != TropicalWeight::zero());
    for s in final_states {
        fst.add_tr(s, Tr::new(0, 0, 0.0, q0))?;
    }
    Ok(fst)
}

fn macro_def_fst(
    _symt: Arc<SymbolTable>,
    macros: &HashMap<String, RegexAST>,
    mdef: (String, Box<RegexAST>),
) -> Result<VectorFst<TropicalWeight>> {
    let (mac, def) = mdef;
    let mut macros2 = macros.clone();
    macros2.insert(mac, *def);
    let fst = VectorFst::<TropicalWeight>::new();
    Ok(fst)
}

fn macro_fst(
    symt: Arc<SymbolTable>,
    macros: &HashMap<String, RegexAST>,
    mac: String,
) -> Result<VectorFst<TropicalWeight>> {
    let node = macros.get(&mac).unwrap();
    let fst = context_node_fst(symt, macros, node.clone())?;
    Ok(fst)
}

fn disjunction_fst(
    symt: Arc<SymbolTable>,
    macros: &HashMap<String, RegexAST>,
    alternates: Vec<RegexAST>,
) -> Result<VectorFst<TropicalWeight>> {
    let mut fst = VectorFst::<TropicalWeight>::new();
    fst.set_input_symbols(symt.clone());
    fst.set_output_symbols(symt.clone());
    let q0 = fst.add_state();
    let q1 = fst.add_state();
    fst.set_start(q0)?;
    fst.set_final(q1, 0.0)?;
    for alternate in alternates {
        let alt_fst = context_node_fst(symt.clone(), macros, alternate)?;
        union(&mut fst, &alt_fst)?;
    }
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
        let macros = HashMap::new();
        let fst = char_fst(symt, &macros, 'a').unwrap();
        let paths: Vec<_> = fst.paths_iter().collect();
        assert_eq!(paths.len(), 1);
    }
}
