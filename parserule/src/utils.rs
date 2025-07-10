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
    push_weights_with_config(
        fst,
        ReweightType::ReweightToInitial,
        PushWeightsConfig::default(),
    )?;
    // *fst = det_fst;
    Ok(())
}
