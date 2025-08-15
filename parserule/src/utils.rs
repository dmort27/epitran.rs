use rustfst::algorithms::determinize::{
    determinize_with_config, DeterminizeConfig, DeterminizeType,
};

use rustfst::algorithms::{rm_epsilon::rm_epsilon, tr_sum};
use rustfst::fst_impls::VectorFst;
use rustfst::prelude::*;

pub fn optimize_fst(
    fst: &mut VectorFst<TropicalWeight>,
    _delta: f32,
) -> Result<(), Box<dyn std::error::Error>> {
    rm_epsilon(fst)?;
    tr_sum(fst);
    // let dfst: VectorFst<TropicalWeight> = determinize_with_config(
    //     fst,
    //     DeterminizeConfig {
    //         delta: 1.0e-5,
    //         det_type: DeterminizeType::DeterminizeNonFunctional,
    //     },
    // )?;
    minimize_with_config(
        fst,
        MinimizeConfig {
            delta: 1e-4,
            allow_nondet: true,
        },
    )?;
    // *fst = dfst;
    Ok(())
}

pub fn sort_and_compose(
    fst1: &VectorFst<TropicalWeight>,
    fst2: &VectorFst<TropicalWeight>,
) -> Result<VectorFst<TropicalWeight>, Box<dyn std::error::Error>> {
    let mut fst1_local = fst1.clone();
    let mut fst2_local = fst2.clone();
    tr_sort(&mut fst1_local, OLabelCompare {});
    tr_sort(&mut fst2_local, ILabelCompare {});
    Ok(compose::compose::<
        _,
        VectorFst<_>,
        VectorFst<_>,
        VectorFst<_>,
        &_,
        &_,
    >(&fst1_local, &fst2_local)?)
}
