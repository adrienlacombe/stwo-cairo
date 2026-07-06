//! SHA256 AIR spike — standalone port of stwo-cairo PR #1425's `sha_256_round` component.
//!
//! SOUNDNESS-CRITICAL SPIKE. Nothing here is wired into starkbtcd or any production path.
//!
//! Provenance:
//! - `components/sha_256_round.rs` is a line-faithful port of the decoded upstream
//!   reference `spike/sha256-air/pr1425-ref/components/sha_256_round.rs`
//!   (PR https://github.com/starkware-libs/stwo-cairo/pull/1425, AIR version 52ac7695-dirty),
//!   with only mechanical changes (documented in that file's header).
//! - `components/subroutines/*` re-express the vendored fca831a subroutines
//!   (spike/vendor/stwo-cairo/.../cairo-air/src/components/subroutines/) in PR #1425's
//!   per-relation convention. The vendored files are NOT modified.
//! - `reference.rs` is an independent scalar FIPS-180-4 implementation, KAT-pinned.
//! - `witness.rs` is a spike-only scalar witness builder for the round component.
//!
//! Honest scope: only the ROUND component is ported. The schedule / builtin / sigma-table /
//! k-table / bitwise-AND-table components and the cairo-vm builtin runner are NOT ported yet;
//! see spike/results/sha256-air-status.md for the remaining plan.

pub mod check;
pub mod components;
pub mod reference;
pub mod relations;
pub mod symbolic;
pub mod witness;
