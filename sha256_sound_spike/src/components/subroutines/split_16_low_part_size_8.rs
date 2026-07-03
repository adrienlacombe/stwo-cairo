// SOUNDNESS-CRITICAL — re-expression of the vendored fca831a subroutine
// spike/vendor/stwo-cairo/.../cairo-air/src/components/subroutines/split_16_low_part_size_8.rs
// in PR #1425's convention: the fca831a version threads the (unused) CommonLookupElements
// argument; the decoded sha_256_round.rs calls this WITHOUT a lookup-elements argument.
// Constraint content is identical: returns low = input - ms8 * 256 as an in-line expression.
//
// NOTE (soundness scope): this subroutine alone does NOT range-check `ms_8_bits_col0` or the
// returned low part; both become 8-bit-constrained only when fed into an 8-bit truth-table
// lookup (AND/XOR), which is how every call site in sha_256_round.rs uses them.
use crate::components::prelude::*;

#[derive(Copy, Clone)]
pub struct Split16LowPartSize8 {}

impl Split16LowPartSize8 {
    #[allow(unused_parens)]
    #[allow(clippy::double_parens)]
    #[allow(non_snake_case)]
    #[allow(clippy::unused_unit)]
    #[allow(unused_variables)]
    #[allow(clippy::too_many_arguments)]
    pub fn evaluate<E: EvalAtRow>(
        [split_16_low_part_size_8_input]: [E::F; 1],
        ms_8_bits_col0: E::F,
        _eval: &mut E,
    ) -> [E::F; 1] {
        let M31_256 = E::F::from(M31::from(256));

        [(split_16_low_part_size_8_input.clone() - (ms_8_bits_col0.clone() * M31_256.clone()))]
    }
}
