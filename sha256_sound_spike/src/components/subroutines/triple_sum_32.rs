// SOUNDNESS-CRITICAL — re-expression of the vendored fca831a subroutine
// spike/vendor/stwo-cairo/.../cairo-air/src/components/subroutines/triple_sum_32.rs
// in PR #1425's convention (unused CommonLookupElements argument dropped, matching the
// call sites in the decoded sha_256_round.rs, which pass no lookup elements).
use crate::components::prelude::*;
use crate::components::subroutines::verify_triple_sum_32::VerifyTripleSum32;

#[derive(Copy, Clone)]
pub struct TripleSum32 {}

impl TripleSum32 {
    #[allow(unused_parens)]
    #[allow(clippy::double_parens)]
    #[allow(non_snake_case)]
    #[allow(clippy::unused_unit)]
    #[allow(unused_variables)]
    #[allow(clippy::too_many_arguments)]
    pub fn evaluate<E: EvalAtRow>(
        [triple_sum_32_input_a_limb_0, triple_sum_32_input_a_limb_1, triple_sum_32_input_b_limb_0, triple_sum_32_input_b_limb_1, triple_sum_32_input_c_limb_0, triple_sum_32_input_c_limb_1]: [E::F; 6],
        triple_sum32_res_limb_0_col0: E::F,
        triple_sum32_res_limb_1_col1: E::F,
        eval: &mut E,
    ) -> [E::F; 0] {
        VerifyTripleSum32::evaluate(
            [
                triple_sum_32_input_a_limb_0.clone(),
                triple_sum_32_input_a_limb_1.clone(),
                triple_sum_32_input_b_limb_0.clone(),
                triple_sum_32_input_b_limb_1.clone(),
                triple_sum_32_input_c_limb_0.clone(),
                triple_sum_32_input_c_limb_1.clone(),
                triple_sum32_res_limb_0_col0.clone(),
                triple_sum32_res_limb_1_col1.clone(),
            ],
            eval,
        );
        []
    }
}
