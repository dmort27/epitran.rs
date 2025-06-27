use std::collections::HashSet;
use std::sync::Arc;

use rustfst::fst_impls::VectorFst;
use rustfst::fst_traits::MutableFst;
use rustfst::algorithms::{
    add_super_final_state,
    determinize::{determinize_with_config, DeterminizeConfig, DeterminizeType},
    minimize_with_config, MinimizeConfig, push_weights,
    rm_epsilon::rm_epsilon,
    tr_sort, ReweightType,
};
use rustfst::prelude::*;
use rustfst::prelude::{
    compose::compose,
    union::union,
};
use crate::mapparse::{process_map, ParsedMapping};
use crate::rulefst::compile_script;
use crate::ruleparse::parse_script;

/// Build a wFST for a language using the preprocessing and postprocessing
/// scripts and the mapping table.
///
/// The `preproc` and `postproc` arguments are scripts written in the format
/// specified in [`crate::ruleparse`]. `mapping` is a table represented as CSV
/// data (with the headers `orth` and `phon`). The resulting wFST is created by
/// converting each of these strings into a wFST, then composing them. A
/// `SymbolTable` `symt` is generated, based on characters and Unicode escapes
/// found in the strings. This is also returned.
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
    symt_inner.add_symbol("#");
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
    let mut composed_fst: VectorFst<TropicalWeight> = compose(composed_fst, postproc_fst)?;

    rm_epsilon(&mut composed_fst).unwrap_or_else(|e| {
        eprintln!("Warning: Could not remove epsilon transitions from composed FST: {}", e);
    });
    top_sort(&mut composed_fst)
        .unwrap_or_else(|e| println!("{e}: Could not sort topologically. There is cycle"));
    // let mut composed_fst = determinize_with_config(&composed_fst, DeterminizeConfig { delta: 1e-6, det_type: DeterminizeType::DeterminizeNonFunctional })?;

    Ok((symt, composed_fst))
}

fn compile_mapping_fst(
    symt: Arc<SymbolTable>,
    mapping: Vec<ParsedMapping>,
) -> Result<VectorFst<TropicalWeight>, Box<dyn std::error::Error>> {
    let mut fst = VectorFst::<TropicalWeight>::new();
    let q0 = fst.add_state();
    let _ = fst.set_start(q0);
    let _ = fst.set_final(q0, 1.0);
    fst.set_input_symbols(symt.clone());
    fst.set_output_symbols(symt.clone());
    mapping.iter().for_each(|m| {
        let mut transducer_fst: VectorFst<TropicalWeight> = VectorFst::new();
        let mut last = transducer_fst.add_state();
        let _ = transducer_fst.set_start(last);
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
        transducer_fst
            .set_final(last, 0.0)
            .unwrap_or_else(|e| println!("{e}: {last} is not a know state."));
        union(&mut fst, &transducer_fst).unwrap_or_else(|e| {
            println!(
                "{e}: Could not compute the union between {:?} and {:?}",
                fst, transducer_fst
            )
        });
    });
    let qn = add_super_final_state(&mut fst);
    let _ = fst.emplace_tr(qn, 0, 0, 1.0, q0);
    // symt.labels().for_each(|l| {
    //     if l > 1 {
    //         let _ = fst.emplace_tr(q0, l, l, 1.0, q0);
    //     }
    // });
    rm_epsilon(&mut fst).unwrap_or_else(|e| {
        eprintln!("Warning: Could not remove epsilon transitions from mapping FST: {}", e);
    });
    let mut fst: VectorFst<TropicalWeight> = determinize_with_config(
        &fst,
        DeterminizeConfig {
            delta: 1e-6,
            det_type: DeterminizeType::DeterminizeFunctional,
        },
    )?;
    push_weights(&mut fst, ReweightType::ReweightToInitial)?;
    minimize_with_config(&mut fst, MinimizeConfig { delta: 1e-7, allow_nondet: (true) })?;

    fst.set_input_symbols(symt.clone());
    fst.set_output_symbols(symt.clone());
    
    // Optional FST visualization - only if debug mode and external tools available
    #[cfg(debug_assertions)]
    {
        if let Ok(_) = fst.draw(
            "map_fst.dot",
            &DrawingConfig {
                vertical: false,
                size: (Some((10.0, 10.0))),
                title: ("Mapping FST".to_string()),
                portrait: (true),
                ranksep: (None),
                nodesep: (None),
                fontsize: (12),
                acceptor: (false),
                show_weight_one: (true),
                print_weight: (true),
            },
        ) {
            // Only attempt to run dot if the file was created successfully
            // This is optional and won't fail the function if dot is not available
            let _ = std::process::Command::new("dot")
                .args(["-Tpdf", "-o", "map_fst.pdf", "map_fst.dot"])
                .output(); // Use output() instead of spawn() to avoid panics
        }
    }

    Ok(fst)
}

#[cfg(test)]
mod test {
    use crate::{langfst::build_lang_fst, rulefst::apply_fst};

    #[test]
    fn test_build_lang_fst1() {
        let pre_str = "a -> b / c_d";
        let mapping_str = "orth,phon\na,a\nb,c\nc,c\nd,d";
        let post_str = "c -> d / _d";
        let (symt, fst) = build_lang_fst(pre_str, post_str, mapping_str)
            .expect("Failed to build language FST in test");
        let input = "acad";
        assert_eq!(apply_fst(symt, fst, input.to_string()), "acdd".to_string())
    }
}
