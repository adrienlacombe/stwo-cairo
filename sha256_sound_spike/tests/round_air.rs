//! Behavioural accept/reject tests for the ported `sha_256_round` AIR component.
//!
//! Bar being cleared here (task priority (b)): the constraint evaluation ACCEPTS a valid
//! FIPS-180-4 compression trace and REJECTS corrupted ones. `check_constraints_on_trace`
//! (src/check.rs — a non-panicking mirror of stwo's `assert_constraints_on_trace`)
//! evaluates every constraint, including the logup interaction-column constraints, on
//! every trace row — the same evaluation the prover must satisfy, without FRI.
//!
//! Also demonstrates the upstream soundness flag documented in the component header:
//! the decoded PR #1425 reference leaves ch_limb/maj_limb unconstrained, so a consistent
//! Ch forgery is ACCEPTED verbatim and only rejected with the spike's binding constraints.

use sha256_round_sound_spike::check::{check_constraints_on_trace, Violation};
use sha256_round_sound_spike::components::sha_256_round::{Claim, Eval};
use sha256_round_sound_spike::reference;
use sha256_round_sound_spike::witness::{
    as_tree, build_interaction_trace, build_round_trace, build_round_trace_forge, forge_ch, Forge,
    CompressionInput, RoundRelations, RoundTrace,
};
use stwo::core::fields::m31::M31;
use stwo_constraint_framework::FrameworkEval;

/// "abc" padded single block (FIPS-180-4 5.1.1): 0x61626380, 0..0, len=24 bits.
fn abc_block() -> [u32; 16] {
    let mut block = [0u32; 16];
    block[0] = 0x61626380;
    block[15] = 24;
    block
}

fn abc_trace() -> RoundTrace {
    build_round_trace(&[CompressionInput {
        h_in: reference::IV,
        block: abc_block(),
    }])
}

fn make_eval(log_size: u32, bind: bool, rels: &RoundRelations) -> Eval {
    Eval {
        claim: Claim { log_size },
        bind_ch_maj_limbs: bind,
        sha_256_big_sigma_1_lookup_elements: rels.big_sigma_1.clone(),
        sha_256_big_sigma_0_lookup_elements: rels.big_sigma_0.clone(),
        verify_bitwise_and_8_lookup_elements: rels.and_8.clone(),
        verify_bitwise_xor_8_lookup_elements: rels.xor_8.clone(),
        sha_256_k_table_lookup_elements: rels.k_table.clone(),
        sha_256_schedule_lookup_elements: rels.schedule.clone(),
        sha_256_round_lookup_elements: rels.round.clone(),
    }
}

/// Build the interaction trace from the (possibly corrupted) base trace — as a malicious
/// prover would — then run every constraint on every row.
fn check(trace: &RoundTrace, bind: bool) -> Vec<Violation> {
    let rels = RoundRelations::draw_test();
    let (interaction, claimed_sum) = build_interaction_trace(trace, &rels);
    let tree = as_tree(&trace.cols, &interaction);
    let eval = make_eval(trace.log_size, bind, &rels);
    check_constraints_on_trace(
        &tree,
        trace.log_size,
        |e| {
            eval.evaluate(e);
        },
        claimed_sum,
    )
}

/// Valid single-compression trace ("abc" block from the IV) is accepted, and the round
/// chain's final state feed-forwards to the pinned FIPS-180-4 digest.
#[test]
fn valid_single_compression_accepted() {
    let trace = abc_trace();
    assert_eq!(trace.log_size, 6);

    // KAT anchor: state-after-64-rounds + IV must equal the known SHA-256("abc") digest.
    // (reference.rs is itself KAT-pinned; this re-checks the exact chain the trace encodes.)
    let digest: Vec<u32> = trace.final_states[0]
        .iter()
        .zip(reference::IV)
        .map(|(s, iv)| s.wrapping_add(iv))
        .collect();
    assert_eq!(
        digest,
        vec![
            0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223, 0xb00361a3, 0x96177a9c, 0xb410ff61,
            0xf20015ad
        ]
    );

    let violations = check(&trace, true);
    assert!(violations.is_empty(), "valid trace rejected: {violations:?}");
}

/// Two chained compressions (the two-block NIST KAT message) are accepted; exercises
/// seq > 0 and h_in != IV.
#[test]
fn valid_two_compression_chain_accepted() {
    let msg = b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
    // Manual padding: 56 bytes + 0x80 + zeros + 64-bit length = exactly 2 blocks.
    let mut padded = msg.to_vec();
    padded.push(0x80);
    while padded.len() % 64 != 56 {
        padded.push(0);
    }
    padded.extend_from_slice(&(msg.len() as u64 * 8).to_be_bytes());
    let blocks: Vec<[u32; 16]> = padded
        .chunks_exact(64)
        .map(|chunk| {
            let mut b = [0u32; 16];
            for (i, w) in chunk.chunks_exact(4).enumerate() {
                b[i] = u32::from_be_bytes(w.try_into().unwrap());
            }
            b
        })
        .collect();
    assert_eq!(blocks.len(), 2);

    let (_, h1) = reference::compress(reference::IV, &blocks[0]);
    let trace = build_round_trace(&[
        CompressionInput {
            h_in: reference::IV,
            block: blocks[0],
        },
        CompressionInput {
            h_in: h1,
            block: blocks[1],
        },
    ]);
    assert_eq!(trace.log_size, 7);

    let digest: Vec<u32> = trace.final_states[1]
        .iter()
        .zip(h1)
        .map(|(s, h)| s.wrapping_add(h))
        .collect();
    assert_eq!(
        digest,
        vec![
            0x248d6a61, 0xd20638b8, 0xe5c02693, 0x0c3e6039, 0xa33ce459, 0x64ff2167, 0xf6ecedd4,
            0x19db06c1
        ]
    );

    let violations = check(&trace, true);
    assert!(violations.is_empty(), "valid trace rejected: {violations:?}");
}

/// Corrupting the recombined Ch column violates the chl plain constraint.
#[test]
fn corrupted_chl_rejected() {
    let mut trace = abc_trace();
    trace.cols[76][5] += M31::from(1);
    let violations = check(&trace, true);
    assert!(!violations.is_empty(), "chl_col76 += 1 at row 5 was ACCEPTED");
    assert!(violations.iter().any(|v| v.row == 5));
}

/// Corrupting new_e violates the TripleSum32 carry constraint (carry leaves {0,1,2}).
#[test]
fn corrupted_new_e_rejected() {
    let mut trace = abc_trace();
    trace.cols[120][20] += M31::from(1);
    let violations = check(&trace, true);
    assert!(
        !violations.is_empty(),
        "new_e lo limb += 1 at row 20 was ACCEPTED"
    );
    assert!(violations.iter().any(|v| v.row == 20));
}

/// A non-boolean enabler violates the enabler gate.
#[test]
fn corrupted_enabler_rejected() {
    let mut trace = abc_trace();
    trace.cols[124][7] = M31::from(2);
    let violations = check(&trace, true);
    assert!(!violations.is_empty(), "enabler = 2 at row 7 was ACCEPTED");
    assert!(violations.iter().any(|v| v.row == 7 && v.constraint_index == 0));
}

/// Corrupting a lookup-only cell (an AND byte) with a STALE interaction trace breaks the
/// logup column constraints. (With a rebuilt interaction trace this cell is only caught
/// globally, by the AND table component's multiplicity balance — not ported yet.)
#[test]
fn corrupted_and_byte_stale_interaction_rejected() {
    let trace = abc_trace();
    let rels = RoundRelations::draw_test();
    let (interaction, claimed_sum) = build_interaction_trace(&trace, &rels);

    let mut corrupted = trace;
    corrupted.cols[58][9] += M31::from(1);

    let eval = make_eval(corrupted.log_size, true, &rels);
    let tree = as_tree(&corrupted.cols, &interaction);
    let violations = check_constraints_on_trace(
        &tree,
        corrupted.log_size,
        |e| {
            eval.evaluate(e);
        },
        claimed_sum,
    );
    assert!(
        !violations.is_empty(),
        "corrupted AND byte with stale interaction trace was ACCEPTED"
    );
    assert!(violations.iter().any(|v| v.row == 9));
}

/// UPSTREAM SOUNDNESS FLAG (see component header, deviation 3) — ROW-LOCAL demonstration.
/// A consistent single-row Ch forgery (overwrite the unconstrained ch_limb columns,
/// recompute that row, rebuild the interaction trace) is ACCEPTED by the verbatim decoded
/// component and rejected only with the binding constraints.
///
/// SCOPE CAVEAT (per adversarial review): this is a per-component (`assert_constraints_on_trace`)
/// verdict, not a full-AIR verdict. Corrupting ONE row leaves the round self-relation's
/// PUSH(row+1)/PULL(row) disagreeing at that boundary; in the full multi-component AIR the
/// round relation's global multiplicity balance would itself reject this specific trace, even
/// WITHOUT the binding fix. The end-to-end exploit that the fix is genuinely required to stop
/// is the PROPAGATED forgery — see `propagated_*_forgery_*` below. (Same "only caught
/// globally" character as `corrupted_and_byte_stale_interaction_rejected`.)
#[test]
fn forged_ch_row_local_underconstraint_and_binding_fix() {
    let mut trace = abc_trace();

    // Forge Ch at row 10 to a value that changes the digest.
    let honest_ch = trace.cols[78][10].0 | (trace.cols[79][10].0 << 16);
    let forged = honest_ch ^ 0xdead_beef;
    forge_ch(&mut trace, 10, forged);

    // The forged row's new_a now differs from the true SHA-256 round output.
    let w = reference::message_schedule_80(&abc_block());
    let mut state = reference::IV;
    for (wt, kt) in w.iter().zip(reference::K).take(10) {
        state = reference::round(state, *wt, kt);
    }
    let true_next = reference::round(state, w[10], reference::K[10]);
    let forged_new_a = trace.cols[122][10].0 | (trace.cols[123][10].0 << 16);
    assert_ne!(
        forged_new_a, true_next[0],
        "forgery should change the round output"
    );

    // Verbatim decoded component (bind = false): ACCEPTED. This is the demonstrated hole.
    let verbatim_violations = check(&trace, false);
    assert!(
        verbatim_violations.is_empty(),
        "expected the verbatim decoded component to ACCEPT the consistent Ch forgery \
         (if this now fails, the underconstraint got fixed — update the component header \
         and the status doc): {verbatim_violations:?}"
    );

    // With the spike's binding constraints (bind = true): REJECTED.
    let bound_violations = check(&trace, true);
    assert!(
        !bound_violations.is_empty(),
        "consistent Ch forgery with binding constraints on was ACCEPTED"
    );
    assert!(bound_violations.iter().any(|v| v.row == 10));
}

/// END-TO-END exploit: a PROPAGATED Ch forgery. Forge Ch at round 10, then carry the
/// corrupted state honestly through rounds 11..63 so the round self-relation chains
/// consistently across every row. Now BOTH the row-local constraints AND the round chain
/// hold, so the verbatim decoded component accepts a trace whose final digest is not
/// SHA-256 — the full-AIR-relevant attack the binding fix is genuinely required to stop
/// (the global round-relation balance does NOT catch it; the chain is consistent). The
/// binding constraints reject it at the forged row.
#[test]
fn propagated_ch_forgery_accepted_without_binding_rejected_with() {
    let input = CompressionInput {
        h_in: reference::IV,
        block: abc_block(),
    };
    let forge_t = 10;

    let honest = build_round_trace(&[input]);
    let honest_ch = honest.cols[78][forge_t].0 | (honest.cols[79][forge_t].0 << 16);
    let forged_ch = honest_ch ^ 0xdead_beef;

    let trace = build_round_trace_forge(&[input], 0, forge_t, Forge::Ch(forged_ch));

    // The propagated chain yields a genuinely wrong post-64-round state (digest forgery),
    // not just a single corrupted row.
    assert_ne!(
        trace.final_states[0], honest.final_states[0],
        "propagated forgery should change the final state"
    );

    // Verbatim decoded component (bind = false): ACCEPTS the wrong-digest trace. This is the
    // end-to-end soundness hole.
    let verbatim = check(&trace, false);
    assert!(
        verbatim.is_empty(),
        "verbatim component must ACCEPT the propagated forgery (row-local constraints and \
         the round chain all hold): {verbatim:?}"
    );

    // Binding fix (bind = true): REJECTS, at the forged row (ch_limb != chl there; every
    // other row is an honest computation on the forged state, so ch_limb == chl).
    let bound = check(&trace, true);
    assert!(!bound.is_empty(), "propagated Ch forgery was ACCEPTED with binding on");
    assert!(bound.iter().any(|v| v.row == forge_t));
    assert!(
        bound.iter().all(|v| v.row == forge_t),
        "only the forged row should violate the binding constraints: {bound:?}"
    );
}

/// Maj counterpart of the propagated Ch exploit: proves the two `maj_limb` binding
/// constraints are independently necessary (the Ch tests never exercise cols 114/115).
#[test]
fn propagated_maj_forgery_accepted_without_binding_rejected_with() {
    let input = CompressionInput {
        h_in: reference::IV,
        block: abc_block(),
    };
    let forge_t = 10;

    let honest = build_round_trace(&[input]);
    let honest_maj = honest.cols[114][forge_t].0 | (honest.cols[115][forge_t].0 << 16);
    let forged_maj = honest_maj ^ 0xdead_beef;

    let trace = build_round_trace_forge(&[input], 0, forge_t, Forge::Maj(forged_maj));

    assert_ne!(
        trace.final_states[0], honest.final_states[0],
        "propagated forgery should change the final state"
    );

    let verbatim = check(&trace, false);
    assert!(
        verbatim.is_empty(),
        "verbatim component must ACCEPT the propagated Maj forgery: {verbatim:?}"
    );

    let bound = check(&trace, true);
    assert!(!bound.is_empty(), "propagated Maj forgery was ACCEPTED with binding on");
    assert!(bound.iter().any(|v| v.row == forge_t));
    assert!(
        bound.iter().all(|v| v.row == forge_t),
        "only the forged row should violate the binding constraints: {bound:?}"
    );
}
