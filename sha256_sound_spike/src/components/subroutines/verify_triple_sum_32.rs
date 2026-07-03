// SOUNDNESS-CRITICAL — re-expression of the vendored fca831a subroutine
// spike/vendor/stwo-cairo/.../cairo-air/src/components/subroutines/verify_triple_sum_32.rs
// in PR #1425's convention (the fca831a version threads an unused CommonLookupElements
// argument; constraint content is byte-identical).
//
// Verifies res = a + b + c (mod 2^32) over (lo16, hi16) limb pairs.
// M31_32768 = 2^15 is the inverse of 2^16 in M31 (2^16 * 2^15 = 2^31 = 1 mod (2^31 - 1)),
// so carry_low = (a0 + b0 + c0 - res0) / 2^16, constrained to {0, 1, 2} by the cubic;
// same for carry_high, whose own overflow is dropped (mod-2^32 semantics).
// The res limbs are NOT range-checked here — in the full tower they are 16-bit-pinned when
// consumed (split + 8-bit table lookups in the next round row / builtin output verification).
use crate::components::prelude::*;

#[derive(Copy, Clone)]
pub struct VerifyTripleSum32 {}

impl VerifyTripleSum32 {
    #[allow(unused_parens)]
    #[allow(clippy::double_parens)]
    #[allow(non_snake_case)]
    #[allow(clippy::unused_unit)]
    #[allow(unused_variables)]
    #[allow(clippy::too_many_arguments)]
    pub fn evaluate<E: EvalAtRow>(
        [verify_triple_sum_32_input_limb_0, verify_triple_sum_32_input_limb_1, verify_triple_sum_32_input_limb_2, verify_triple_sum_32_input_limb_3, verify_triple_sum_32_input_limb_4, verify_triple_sum_32_input_limb_5, verify_triple_sum_32_input_limb_6, verify_triple_sum_32_input_limb_7]: [E::F; 8],
        eval: &mut E,
    ) -> [E::F; 0] {
        let M31_1 = E::F::from(M31::from(1));
        let M31_2 = E::F::from(M31::from(2));
        let M31_32768 = E::F::from(M31::from(32768));

        let carry_low_tmp = eval.add_intermediate(
            ((((verify_triple_sum_32_input_limb_0.clone()
                + verify_triple_sum_32_input_limb_2.clone())
                + verify_triple_sum_32_input_limb_4.clone())
                - verify_triple_sum_32_input_limb_6.clone())
                * M31_32768.clone()),
        );
        // carry low is 0 or 1 or 2.
        eval.add_constraint(
            ((carry_low_tmp.clone() * (carry_low_tmp.clone() - M31_1.clone()))
                * (carry_low_tmp.clone() - M31_2.clone())),
        );
        let carry_high_tmp = eval.add_intermediate(
            (((((verify_triple_sum_32_input_limb_1.clone()
                + verify_triple_sum_32_input_limb_3.clone())
                + verify_triple_sum_32_input_limb_5.clone())
                + carry_low_tmp.clone())
                - verify_triple_sum_32_input_limb_7.clone())
                * M31_32768.clone()),
        );
        // carry high is 0 or 1 or 2.
        eval.add_constraint(
            ((carry_high_tmp.clone() * (carry_high_tmp.clone() - M31_1.clone()))
                * (carry_high_tmp.clone() - M31_2.clone())),
        );
        []
    }
}
