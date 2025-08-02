use rustfst::algorithms::{
    tr_sum,
    push_weights_with_config,
    rm_epsilon::rm_epsilon,
    PushWeightsConfig,
};
use rustfst::fst_impls::VectorFst;
use rustfst::prelude::*;

pub fn optimize_fst(
    fst: &mut VectorFst<TropicalWeight>,
    _delta: f32,
) -> Result<(), Box<dyn std::error::Error>> {
    rm_epsilon(fst)?;
    tr_sum(fst);
    // minimize_with_config(fst, MinimizeConfig { delta: 1e-4, allow_nondet: true })?;
    /*
    push_weights_with_config(
        fst,
        ReweightType::ReweightToInitial,
        PushWeightsConfig::default(),
    )?;
    // */
    // *fst = det_fst;
    Ok(())
}

pub fn sort_and_compose(fst1: &VectorFst<TropicalWeight>, fst2: &VectorFst<TropicalWeight>) -> Result<VectorFst<TropicalWeight>, Box<dyn std::error::Error>> {
    let mut fst1_local = fst1.clone();
    let mut fst2_local = fst2.clone();
    tr_sort(&mut fst1_local, OLabelCompare {});
    tr_sort(&mut fst2_local, ILabelCompare {});
    Ok(compose::compose::<_, VectorFst<_>, VectorFst<_>, VectorFst<_>, &_, &_>(&fst1_local, &fst2_local)?)
}
