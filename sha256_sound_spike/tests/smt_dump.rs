//! Internal-consistency tests for the SMT extraction layer (src/symbolic.rs) — NEW test
//! file; tests/round_air.rs is untouched per the spike's hard boundaries.
//!
//! Asserts the dump the `dump_smt` binary produces is internally consistent
//! (smt/DESIGN.md §1.2-§1.3): constraint counts 21 bind-on / 17 bind-off, the 4-constraint
//! structural set-diff with its index/pair tripwires, relation-use counts
//! {Σ1:1, Σ0:1, KTable:1, Schedule:1, Round:2(±enabler), And8:20, Xor8:12} = 38,
//! enabler derivation, JSON node grammar, and the two independent numeric gates (raw-tree
//! `assign` and converted-tree `Node` interpreter) on honest + forged witness rows
//! exercising TripleSum32 carries {0,1,2}.

use std::collections::{BTreeMap, BTreeSet};

use sha256_round_sound_spike::components::sha_256_round::N_TRACE_COLUMNS;
use sha256_round_sound_spike::reference;
use sha256_round_sound_spike::symbolic::{
    carry_values, check_row, eval_node, extract, node_violations, relation_name_counts,
    structural_checks, Node, P,
};
use sha256_round_sound_spike::witness::{
    build_round_trace, build_round_trace_forge, forge_ch, CompressionInput, Forge, RoundTrace,
};

/// "abc" padded single block (FIPS-180-4 5.1.1) — same constant as tests/round_air.rs.
fn abc_block() -> [u32; 16] {
    let mut block = [0u32; 16];
    block[0] = 0x61626380;
    block[15] = 24;
    block
}

fn abc_input() -> CompressionInput {
    CompressionInput {
        h_in: reference::IV,
        block: abc_block(),
    }
}

fn row_cols(trace: &RoundTrace, row: usize) -> Vec<u32> {
    (0..N_TRACE_COLUMNS).map(|c| trace.cols[c][row].0).collect()
}

/// Structural gates: counts, set-diff, tripwires, relation uses, enabler, coverage.
#[test]
fn extraction_structure_matches_design() {
    let bind_on = extract(true);
    let bind_off = extract(false);

    // structural_checks itself asserts: 21/17 constraints, bind_off ⊂ bind_on in order,
    // diff = exactly 4 Sub(Col,Col) at indices {5,6,13,14} with pairs
    // (78,76),(79,77),(114,112),(115,113), 38 variant-identical relation uses, Round
    // ±enabler shape, table mults (+1, Const 1), column coverage == 0..125.
    let info = structural_checks(&bind_on.dump, &bind_off.dump);
    assert_eq!(info.enabler_col, 124);
    assert_eq!(info.binding_indices, vec![5, 6, 13, 14]);
    assert_eq!(
        info.binding_pairs,
        vec![(78, 76), (79, 77), (114, 112), (115, 113)]
    );

    // Re-assert the headline numbers here so this test names them explicitly.
    assert_eq!(bind_on.dump.constraints.len(), 21);
    assert_eq!(bind_off.dump.constraints.len(), 17);
    assert_eq!(bind_on.dump.relation_uses.len(), 38);
    let expected: BTreeMap<String, usize> = [
        ("Sha256BigSigma0", 1),
        ("Sha256BigSigma1", 1),
        ("Sha256KTable", 1),
        ("Sha256Schedule", 1),
        ("Sha256Round", 2),
        ("VerifyBitwiseAnd_8", 20),
        ("VerifyBitwiseXor_8", 12),
    ]
    .into_iter()
    .map(|(k, v)| (k.to_string(), v))
    .collect();
    assert_eq!(relation_name_counts(&bind_on.dump), expected);
    assert_eq!(relation_name_counts(&bind_off.dump), expected);
}

/// The exact JSON grammar of smt/DESIGN.md §2, spot-checked on a binding constraint
/// (index 5 must be exactly `ch_limb_0_col78 - chl_col76`).
#[test]
fn json_grammar_spot_check() {
    let bind_on = extract(true);
    let binding = &bind_on.dump.constraints[5];
    assert_eq!(
        serde_json::to_string(&binding.expr).unwrap(),
        r#"{"op":"sub","lhs":{"op":"col","interaction":1,"idx":78,"offset":0},"rhs":{"op":"col","interaction":1,"idx":76,"offset":0}}"#
    );

    // The enabler booleanity constraint (index 0): enabler*enabler - enabler.
    let enabler = Node::Col {
        interaction: 1,
        idx: 124,
        offset: 0,
    };
    assert_eq!(
        bind_on.dump.constraints[0].expr,
        Node::Sub {
            lhs: Box::new(Node::Mul {
                lhs: Box::new(enabler.clone()),
                rhs: Box::new(enabler.clone()),
            }),
            rhs: Box::new(enabler),
        }
    );

    // Carry cubics carry the 2^15 (= 2^-16 mod p) inlined-intermediate factor.
    let json = serde_json::to_string(&bind_on.dump.constraints[7].expr).unwrap();
    assert!(
        json.contains(r#"{"op":"const","val":32768}"#),
        "first TripleSum32 carry cubic must contain the 2^15 constant: {json}"
    );
}

/// Numeric gates A (raw `assign`) + B (Node interpreter) on all 64 honest rows of the
/// "abc" trace, plus the carry-class coverage {0,1,2} the brief requires.
#[test]
fn honest_rows_satisfy_both_variants_and_exercise_all_carries() {
    let bind_on = extract(true);
    let bind_off = extract(false);
    let trace = build_round_trace(&[abc_input()]);
    assert_eq!(trace.log_size, 6);

    let mut carries_seen: BTreeSet<u32> = BTreeSet::new();
    for row in 0..64usize {
        let cols = row_cols(&trace, row);
        check_row(&bind_on, &bind_off, &cols, &[], &[], &format!("honest row {row}"));
        carries_seen.extend(carry_values(&bind_on.evaluator, &cols));
    }
    assert_eq!(
        carries_seen,
        [0u32, 1, 2].into_iter().collect::<BTreeSet<u32>>(),
        "honest trace must exercise TripleSum32 carries 0, 1 AND 2"
    );
}

/// Forged rows: bind_off (decoded PR #1425) fully satisfied; bind_on violated at exactly
/// the binding-constraint indices — the same verdicts as tests/round_air.rs, reproduced on
/// the EXTRACTED trees (fidelity corroboration for the M.bind_off z3 mutation).
#[test]
fn forged_rows_violate_exactly_the_binding_constraints() {
    let bind_on = extract(true);
    let bind_off = extract(false);
    let forge_row = 10usize;

    let mut ch_trace = build_round_trace(&[abc_input()]);
    let honest_ch = ch_trace.cols[78][forge_row].0 | (ch_trace.cols[79][forge_row].0 << 16);
    forge_ch(&mut ch_trace, forge_row, honest_ch ^ 0xdead_beef);
    check_row(
        &bind_on,
        &bind_off,
        &row_cols(&ch_trace, forge_row),
        &[5, 6],
        &[],
        "forged ch row",
    );

    let honest = build_round_trace(&[abc_input()]);
    let honest_maj = honest.cols[114][forge_row].0 | (honest.cols[115][forge_row].0 << 16);
    let maj_trace = build_round_trace_forge(
        &[abc_input()],
        0,
        forge_row,
        Forge::Maj(honest_maj ^ 0xdead_beef),
    );
    check_row(
        &bind_on,
        &bind_off,
        &row_cols(&maj_trace, forge_row),
        &[13, 14],
        &[],
        "forged maj row",
    );
}

/// The Node interpreter is exact M31 arithmetic: spot-check the M31 wraparound identity
/// 2^16 * 2^15 = 2^31 ≡ 1 (mod p) that the carry constraints rely on, and eager mod-p
/// subtraction/negation.
#[test]
fn node_interpreter_is_exact_m31() {
    let c = |val: u32| Node::Const { val };
    let mul = Node::Mul {
        lhs: Box::new(c(1 << 16)),
        rhs: Box::new(c(1 << 15)),
    };
    assert_eq!(eval_node(&mul, &[]), 1);
    let sub = Node::Sub {
        lhs: Box::new(c(0)),
        rhs: Box::new(c(1)),
    };
    assert_eq!(eval_node(&sub, &[]) as u64, P - 1);
    let neg = Node::Neg {
        arg: Box::new(c(0)),
    };
    assert_eq!(eval_node(&neg, &[]), 0);
}

/// Gate independence sanity: a corrupted honest row is flagged by BOTH evaluators (a
/// converter bug cannot hide behind gate A alone).
#[test]
fn corrupted_row_is_flagged_by_the_node_interpreter() {
    let bind_on = extract(true);
    let trace = build_round_trace(&[abc_input()]);
    let mut cols = row_cols(&trace, 20);
    cols[120] = (cols[120] + 1) % P as u32; // new_e lo limb — breaks a carry cubic.
    assert!(
        !node_violations(&bind_on.dump, &cols).is_empty(),
        "corrupted new_e must violate at least one converted constraint"
    );
}
