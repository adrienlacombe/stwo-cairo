//! Logup relations used by the sha256 tower, in PR #1425's per-relation convention.
//!
//! Widths copied verbatim from the decoded upstream reference
//! `spike/sha256-air/pr1425-ref/relations.rs` (AIR version 52ac7695-dirty).
//! Only the relations reachable from the round component (plus the rest of the sha256
//! family, kept for the follow-on schedule/builtin port) are declared here.

#![allow(non_camel_case_types)]
use stwo_constraint_framework::relation;

// 8-bit bitwise truth-table relations (tuple: a, b, a OP b).
relation!(VerifyBitwiseAnd_8, 3);
relation!(VerifyBitwiseXor_8, 3);

// sha256 family — widths from pr1425-ref/relations.rs.
relation!(Sha256Round, 50);
relation!(Sha256BigSigma0, 4);
relation!(Sha256BigSigma1, 4);
relation!(Sha256Schedule, 34);
relation!(Sha256SmallSigma0, 4);
relation!(Sha256SmallSigma1, 4);
relation!(Sha256BigSigma0O0, 6);
relation!(Sha256BigSigma0O1, 6);
relation!(Sha256BigSigma1O0, 6);
relation!(Sha256BigSigma1O1, 6);
relation!(Sha256SmallSigma0O0, 6);
relation!(Sha256SmallSigma0O1, 6);
relation!(Sha256SmallSigma1O0, 6);
relation!(Sha256SmallSigma1O1, 6);
relation!(Sha256KTable, 3);
