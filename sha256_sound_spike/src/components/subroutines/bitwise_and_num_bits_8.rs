// SOUNDNESS-CRITICAL — ported verbatim from the decoded upstream reference
// spike/sha256-air/pr1425-ref/subroutines/bitwise_and_num_bits_8.rs (PR #1425,
// AIR version 52ac7695-dirty). Only change: CairoSerialize derive stripped.
//
// Emits a "use" of the 8-bit AND truth table (a, b, a & b). Table membership is
// enforced globally by the (not-yet-ported) verify_bitwise_and_8 table component;
// within a single component the pull only shows up in the logup fractions.
use crate::components::prelude::*;

#[derive(Copy, Clone)]
pub struct BitwiseAndNumBits8 {}

impl BitwiseAndNumBits8 {
    #[allow(unused_parens)]
    #[allow(clippy::double_parens)]
    #[allow(non_snake_case)]
    #[allow(clippy::unused_unit)]
    #[allow(unused_variables)]
    #[allow(clippy::too_many_arguments)]
    pub fn evaluate<E: EvalAtRow>(
        [bitwise_and_num_bits_8_input_limb_0, bitwise_and_num_bits_8_input_limb_1]: [E::F; 2],
        and_col0: E::F,
        verify_bitwise_and_8_lookup_elements: &relations::VerifyBitwiseAnd_8,
        eval: &mut E,
    ) -> [E::F; 0] {
        eval.add_to_relation(RelationEntry::new(
            verify_bitwise_and_8_lookup_elements,
            E::EF::one(),
            &[
                bitwise_and_num_bits_8_input_limb_0.clone(),
                bitwise_and_num_bits_8_input_limb_1.clone(),
                and_col0.clone(),
            ],
        ));

        []
    }
}
