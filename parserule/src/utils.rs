use rustfst::algorithms::{
    determinize::{determinize_with_config, DeterminizeConfig, DeterminizeType},
    minimize_with_config, MinimizeConfig,
    push_weights_with_config, PushWeightsConfig,
    rm_epsilon::rm_epsilon,
};
use rustfst::fst_impls::VectorFst;
use rustfst::prelude::*;

pub fn optimize_fst(
    fst: &mut VectorFst<TropicalWeight>,
    delta: f32,
) -> Result<(), Box<dyn std::error::Error>> {
    rm_epsilon(fst)?;
    let mut det_fst = determinize_with_config(
        fst,
        DeterminizeConfig {
            delta,
            det_type: DeterminizeType::DeterminizeNonFunctional,
        },
    )?;
    push_weights_with_config(
        &mut det_fst,
        ReweightType::ReweightToInitial,
        PushWeightsConfig::default()
    )?;
    minimize_with_config(&mut det_fst, MinimizeConfig { delta: delta, allow_nondet: true })?;
    *fst = det_fst;
    Ok(())
}