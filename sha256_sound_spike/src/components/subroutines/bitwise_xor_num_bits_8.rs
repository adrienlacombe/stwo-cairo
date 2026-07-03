// SOUNDNESS-CRITICAL — re-expression of the vendored fca831a subroutine
// spike/vendor/stwo-cairo/.../cairo-air/src/components/subroutines/bitwise_xor_num_bits_8.rs
// in PR #1425's per-relation convention (mirrors the decoded AND twin exactly):
// the fca831a version pushes the tuple on the single CommonLookupElements bus with an
// M31 prefix tag (112558620); here the tuple goes on the dedicated VerifyBitwiseXor_8
// relation with no tag, matching the call sites in the decoded sha_256_round.rs.
use crate::components::prelude::*;

#[derive(Copy, Clone)]
pub struct BitwiseXorNumBits8 {}

impl BitwiseXorNumBits8 {
    #[allow(unused_parens)]
    #[allow(clippy::double_parens)]
    #[allow(non_snake_case)]
    #[allow(clippy::unused_unit)]
    #[allow(unused_variables)]
    #[allow(clippy::too_many_arguments)]
    pub fn evaluate<E: EvalAtRow>(
        [bitwise_xor_num_bits_8_input_limb_0, bitwise_xor_num_bits_8_input_limb_1]: [E::F; 2],
        xor_col0: E::F,
        verify_bitwise_xor_8_lookup_elements: &relations::VerifyBitwiseXor_8,
        eval: &mut E,
    ) -> [E::F; 0] {
        eval.add_to_relation(RelationEntry::new(
            verify_bitwise_xor_8_lookup_elements,
            E::EF::one(),
            &[
                bitwise_xor_num_bits_8_input_limb_0.clone(),
                bitwise_xor_num_bits_8_input_limb_1.clone(),
                xor_col0.clone(),
            ],
        ));

        []
    }
}
