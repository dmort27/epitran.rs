//use std::error::Error;
use std::collections::HashSet;
use std::sync::Arc;

use rustfst::fst_impls::VectorFst;
use rustfst::fst_traits::{CoreFst, ExpandedFst, MutableFst};
//use rustfst::prelude::determinize::{determinize, determinize_with_config, DeterminizeConfig};
use rustfst::algorithms::tr_sort;
use rustfst::prelude::{compose::compose, union::union};
use rustfst::prelude::*;
use rustfst::utils::{acceptor, transducer};
//use rustfst::prelude::{TropicalWeight, VectorFst};

// use anyhow::Result;

use crate::mapparse::{process_map, ParsedMapping};
use crate::rulefst::compile_script;
use crate::ruleparse::parse_script;

pub fn build_lang_fst<'a>(
    preproc: &'a str,
    postproc: &'a str,
    mapping: &'a str,
) -> Result<(Arc<SymbolTable>, VectorFst<TropicalWeight>), Box<dyn std::error::Error + 'a>> {
    let (map_syms, mapping) = process_map(mapping).unwrap_or_else(|e| {
        println!("{e}: Could not parse mapping file.");
        (HashSet::new(), Vec::new())
    });
    let (preproc_ast, preproc_syms) = parse_script(preproc)?;
    let (postproc_ast, postproc_syms) = parse_script(postproc)?;

    let mut syms = HashSet::new();
    syms.extend(&map_syms);
    syms.extend(&preproc_syms);
    syms.extend(&postproc_syms);

    let mut symt_inner = SymbolTable::new();
    symt_inner.add_symbols(syms);
    let symt = Arc::new(symt_inner);

    let mut preproc_fst = compile_script(symt.clone(), preproc_ast)?;
    let mut postproc_fst = compile_script(symt.clone(), postproc_ast)?;
    let mut mapping_fst = compile_mapping_fst(symt.clone(), mapping)?;

    tr_sort(&mut preproc_fst, OLabelCompare {});
    tr_sort(&mut mapping_fst, ILabelCompare {});
    let mut composed_fst: VectorFst<TropicalWeight> = compose(preproc_fst, mapping_fst)?;

    tr_sort(&mut composed_fst, OLabelCompare {});
    tr_sort(&mut postproc_fst, ILabelCompare {});
    let composed_fst: VectorFst<TropicalWeight> = compose(composed_fst, postproc_fst)?;

    Ok((symt, composed_fst))
}

fn compile_mapping_fst(
    symt: Arc<SymbolTable>,
    mapping: Vec<ParsedMapping>,
) -> Result<VectorFst<TropicalWeight>, Box<dyn std::error::Error>> {
    let mut fst = VectorFst::<TropicalWeight>::new();
    let mut q0 = fst.add_state();
    let _ = fst.set_start(q0);
    mapping.iter().for_each(|m| {
        let mut transducer_fst: VectorFst<TropicalWeight> = VectorFst::new();
        let mut last = transducer_fst.add_state();
        transducer_fst.set_start(last);
        m.orth.iter().zip(m.phon.iter()).for_each(|(i, o)| {
            let next = transducer_fst.add_state();
            let ilabel = symt.get_label(i).unwrap_or_else(|| {
                println!("Symbol {i} is unknown.");
                0
            });
            let olabel = symt.get_label(o).unwrap_or_else(|| {
                println!("Symbol {o} is unknown.");
                0
            });
            let _ = transducer_fst.emplace_tr(last, ilabel, olabel, 0.0, next);
            last = next;
        });
        transducer_fst.set_final(last, 0.0);
        union(&mut fst, &transducer_fst);
    });
    Ok(fst)
}
