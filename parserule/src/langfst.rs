use std::collections::HashSet;
// Explicitly import Arc to avoid conflicts
use std::sync::Arc;

// Explicitly import VectorFst to avoid conflicts
use crate::mapparse::{process_map, ParsedMapping};
use crate::rulefst::compile_script;
use crate::ruleparse::parse_script;
use crate::utils::optimize_fst;
use rustfst::algorithms::{add_super_final_state, tr_sort};
use rustfst::fst_impls::VectorFst;
use rustfst::fst_traits::MutableFst;
use rustfst::prelude::*;
use rustfst::prelude::{compose::compose, union::union};

/// Build a wFST for a language using the preprocessing and postprocessing
/// scripts and the mapping table.
///
/// The `preproc` and `postproc` arguments are scripts written in the format
/// specified in [`crate::ruleparse`]. `mapping` is a table represented as CSV
/// data (with the headers `orth` and `phon`). The resulting wFST is created by
/// converting each of these strings into a wFST, then composing them. A
/// `SymbolTable` `symt` is generated, based on characters and Unicode escapes
/// found in the strings. This is also returned.
pub fn build_lang_fst(
    preproc: String,
    postproc: String,
    mapping: String,
) -> Result<(Arc<SymbolTable>, VectorFst<TropicalWeight>), Box<dyn std::error::Error>> {
    let (map_syms, mapping) = process_map(mapping).unwrap_or_else(|e| {
        println!("{e}: Could not parse mapping file.");
        (HashSet::new(), Vec::new())
    });
    let (_, (preproc_ast, preproc_syms)) = parse_script(&preproc)?;
    let (_, (postproc_ast, postproc_syms)) = parse_script(&postproc)?;

    println!("==> preproc_ast={:?}", preproc_ast);
    println!("==> postproc_ast={:?}", postproc_ast);

    let mut syms = HashSet::from(["#".to_string()]); // Add the super-final state symbol
    syms.extend(map_syms);
    syms.extend(preproc_syms);
    syms.extend(postproc_syms);

    let mut symt_inner = SymbolTable::new();
    symt_inner.add_symbol("#");
    symt_inner.add_symbols(syms);
    let symt = Arc::new(symt_inner);

    let mut preproc_fst = compile_script(symt.clone(), preproc_ast)?;
    optimize_fst(&mut preproc_fst, 1.0e-5)?;
    let mut postproc_fst = compile_script(symt.clone(), postproc_ast)?;
    optimize_fst(&mut postproc_fst, 1.0e-5)?;
    let mut mapping_fst = compile_mapping_fst(symt.clone(), mapping)?;
    optimize_fst(&mut mapping_fst, 1.0e-5)?;

    // println!("--> preproc_fst={:?}", preproc_fst);
    // println!("--> postproc_fst={:?}", postproc_fst);

    tr_sort(&mut preproc_fst, OLabelCompare {});
    tr_sort(&mut mapping_fst, ILabelCompare {});
    let mut composed_fst: VectorFst<TropicalWeight> = compose(preproc_fst, mapping_fst)?;

    tr_sort(&mut composed_fst, OLabelCompare {});
    tr_sort(&mut postproc_fst, ILabelCompare {});
    let mut composed_fst: VectorFst<TropicalWeight> = compose(composed_fst, postproc_fst)?;

    // rm_epsilon(&mut composed_fst).unwrap_or_else(|e| {
    //     eprintln!(
    //         "Warning: Could not remove epsilon transitions from composed FST: {}",
    //         e
    //     );
    // });
    // top_sort(&mut composed_fst)
    //     .unwrap_or_else(|e| println!("{e}: Could not sort topologically. There is cycle"));
    // // let mut composed_fst = determinize_with_config(&composed_fst, DeterminizeConfig { delta: 1e-6, det_type: DeterminizeType::DeterminizeNonFunctional })?;

    // Sort `composed_fst` by the input labels because an acceptor will be composed with it.
    tr_sort(&mut composed_fst, ILabelCompare {});

    Ok((symt, composed_fst))
}

fn compile_mapping_fst(
    symt: Arc<SymbolTable>,
    mapping: Vec<ParsedMapping>,
) -> Result<VectorFst<TropicalWeight>, Box<dyn std::error::Error>> {
    let mut fst = VectorFst::<TropicalWeight>::new();
    let q0 = fst.add_state();
    fst.set_start(q0)?;
    fst.set_final(q0, 1.0)?;
    fst.set_input_symbols(symt.clone());
    fst.set_output_symbols(symt.clone());
    for m in mapping.iter() {
        let mut transducer_fst: VectorFst<TropicalWeight> = VectorFst::new();
        let mut last = transducer_fst.add_state();
        transducer_fst.set_start(last)?;
        for (i, o) in m.orth.iter().zip(m.phon.iter()) {
            let next = transducer_fst.add_state();
            let ilabel = symt.get_label(i).unwrap_or_else(|| {
                println!("Warning: Symbol '{i}' is unknown, using epsilon");
                0
            });
            let olabel = symt.get_label(o).unwrap_or_else(|| {
                println!("Warning: Symbol '{o}' is unknown, using epsilon");
                0
            });
            transducer_fst.emplace_tr(last, ilabel, olabel, 0.0, next)?;
            last = next;
        }
        transducer_fst.set_final(last, 0.0)?;
        optimize_fst(&mut transducer_fst, 1e-5)?;
        union(&mut fst, &transducer_fst)?;
        optimize_fst(&mut fst, 1e-5)?;
    }
    let qn = add_super_final_state(&mut fst);
    fst.emplace_tr(qn, 0, 0, 1.0, q0)?;
    // symt.labels().for_each(|l| {
    //     if l > 1 {
    //         let _ = fst.emplace_tr(q0, l, l, 1.0, q0);
    //     }
    // });
    // rm_epsilon(&mut fst).unwrap_or_else(|e| {
    //     eprintln!(
    //         "Warning: Could not remove epsilon transitions from mapping FST: {}",
    //         e
    //     );
    // });
    // let mut fst: VectorFst<TropicalWeight> = determinize_with_config(
    //     &fst,
    //     DeterminizeConfig {
    //         delta: 1e-6,
    //         det_type: DeterminizeType::DeterminizeNonFunctional,
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
            if let Err(e) = std::process::Command::new("dot")
                .args(["-Tpdf", "-o", "map_fst.pdf", "map_fst.dot"])
                .output()
            {
                eprintln!("Warning: Could not run dot command: {}", e);
            }
        }
    }

    Ok(fst)
}

#[cfg(test)]
mod test {

    use crate::{langfst::build_lang_fst, rulefst::apply_fst};

    #[test]
    fn test_build_lang_fst1() {
        let pre_str = "a -> b / c_d".to_string();
        let mapping_str = "orth,phon\na,a\nb,c\nc,c\nd,d\n".to_string();
        let post_str = "c -> d / _d".to_string();
        let (symt, fst) = build_lang_fst(pre_str, post_str, mapping_str)
            .expect("Failed to build language FST in test");
        let input = "#acad#";
        assert_eq!(
            apply_fst(symt, fst, input.to_string()),
            "#acdd#".to_string()
        )
    }

    #[test]
    fn test_build_lang_just_mapping() {
        let pre_str = "".to_string();
        let mapping_str = "orth,phon\na,a\nl,l\nn,n\ng,g\nng,ŋ\n".to_string();
        let post_str = "".to_string();
        let (symt, fst) = build_lang_fst(pre_str, post_str, mapping_str)
            .expect("Failed to build language FST in test");
        let input = "#ngalngal#";
        assert_eq!(
            apply_fst(symt, fst, input.to_string()),
            "#ŋalŋal#".to_string()
        )
    }

    #[test]
    fn test_build_lang_pre_mapping_post() {
        let pre_str = "ng -> ŋ / _ a".to_string();
        let mapping_str = "orth,phon\nŋ,ŋ\na,a\nl,l\nn,n\ng,g\n".to_string();
        let post_str = "l -> r / _ ŋ".to_string();
        let (symt, fst) = build_lang_fst(pre_str, post_str, mapping_str)
            .expect("Failed to build language FST in test");
        let input = "#ngalngal#";
        assert_eq!(
            apply_fst(symt, fst, input.to_string()),
            "#ŋarŋal#".to_string()
        )
    }

    const MAP: &str = r#"orth,phon
i,i
e,e
u,u
o,o
a,a
̂,ʔ
-,ʔ
',ʔ
m,m
p,p
b,b
n,n
t,t
d,d
s,s
l,l
r,ɾ
c,k
ch,t͡ʃ
ty,t͡ʃ
ts,t͡ʃ
j,d͡ʒ
dy,d͡ʒ
y,j
ng,ŋ
k,k
g,ɡ
w,w
h,h
"#;

    const PRE: &str = r##"
::vowel:: = (a|e|i|o|u)

% Palatalization
di -> d͡ʒ / _ ::vowel::
ti -> t͡ʃ / _ ::vowel::
ni -> nʲ / _ ::vowel::
li -> lʲ / _ ::vowel::

% Devocalization
u -> w / _ ::vowel::
i -> j / _ ::vowel::
% u -> w / _ ::vowel::
"##;

    const POST: &str = r##"
"##;

    // #[test]
    // fn test_build_realistic_lang_fst1() {
    //     let (symt, fst) = build_lang_fst(PRE.to_string(), POST.to_string(), MAP.to_string())
    //         .expect("Failed to build language FST in test");
    //     let input = "#ngalngal#";
    //     assert_eq!(
    //         apply_fst(symt, fst, input.to_string()),
    //         "#ŋalŋal#".to_string()
    //     );
    // }
}
