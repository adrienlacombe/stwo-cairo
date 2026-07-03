//! Prelude for ported PR #1425 components.
//!
//! Mirrors `spike/vendor/stwo-cairo/.../cairo-air/src/components/prelude.rs`, minus the
//! stwo-cairo-serialize re-exports (CairoSerialize/CairoDeserialize derives are stripped
//! from the ported components — they only matter for proof wire serialization, which this
//! spike does not do) and plus `num_traits::One` (used by `E::EF::one()` call sites).

pub use num_traits::One;
pub use serde::{Deserialize, Serialize};
pub use stwo::core::channel::Channel;
pub use stwo::core::fields::m31::M31;
pub use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
pub use stwo::core::pcs::TreeVec;
pub use stwo_constraint_framework::{EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry};

pub use crate::relations;

/// Bookkeeping struct, copied from vendored `cairo-air/src/verifier.rs:117-120`.
#[derive(Copy, Clone, Debug)]
pub struct RelationUse {
    pub relation_id: &'static str,
    pub uses: u64,
}
