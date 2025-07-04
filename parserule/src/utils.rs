use rustfst::algorithms::{
    determinize::{determinize_with_config, DeterminizeConfig, DeterminizeType},
    minimize_with_config, push_weights_with_config,
    rm_epsilon::rm_epsilon,
    MinimizeConfig, PushWeightsConfig,
};
use rustfst::fst_impls::VectorFst;
use rustfst::prelude::*;

pub fn optimize_fst(
    fst: &mut VectorFst<TropicalWeight>,
    delta: f32,
) -> Result<(), Box<dyn std::error::Error>> {
    rm_epsilon(fst)?;
    // let mut det_fst = determinize_with_config(
    //     fst,
    //     DeterminizeConfig {
    //         delta,
    //         det_type: DeterminizeType::DeterminizeNonFunctional,
    //     },
    // )?;
    // minimize_with_config(fst, MinimizeConfig { delta: delta, allow_nondet: true })?;
    push_weights_with_config(
        fst,
        ReweightType::ReweightToInitial,
        PushWeightsConfig::default(),
    )?;
    // *fst = det_fst;
    Ok(())
}
