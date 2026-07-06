//! dump_smt — writes the SMT extraction artifact `smt/out/air.json` (path from argv).
//!
//! SPIKE TEST INFRASTRUCTURE (smt/DESIGN.md §1.3). Provenance: stwo rev 5ea05973 +
//! stwo-cairo PR #1425 (open/undisclosed — never push this branch to a public remote).
//!
//! Deterministic: `dummy()` relations, fixed padded-"abc" `CompressionInput`, stable JSON
//! key order (serde struct-field order). Every fidelity gate failure is a panic = nonzero
//! exit, so `smt/run.sh` can trust a zero exit:
//!   - structural gates (counts, in-order subset, 4x Sub(Col,Col) diff, index/pair/enabler
//!     tripwires, per-relation use counts, Round entry shape, column coverage 0..125);
//!   - numeric gate A: `assign()` on the RAW trees, both variants, all 64 honest rows == 0;
//!   - numeric gate B: `Node` interpreter on the CONVERTED trees, same coverage;
//!   - carry-class coverage: the honest trace exercises carries {0,1,2};
//!   - forged rows: bind_off fully satisfied, bind_on violated at EXACTLY [5,6] / [13,14].

use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

use serde::Serialize;
use sha256_round_sound_spike::components::sha_256_round::N_TRACE_COLUMNS;
use sha256_round_sound_spike::reference;
use sha256_round_sound_spike::symbolic::{
    carry_values, check_row, extract, structural_checks, Extraction, VariantDump, P, STWO_REV,
};
use sha256_round_sound_spike::witness::{
    build_round_trace, build_round_trace_forge, forge_ch, CompressionInput, Forge, RoundTrace,
};

/// "abc" padded single block (FIPS-180-4 5.1.1): 0x61626380, 0..0, len=24 bits — the same
/// constant as `tests/round_air.rs::abc_block` (copied; the tests file stays untouched).
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

#[derive(Serialize)]
struct Variants {
    bind_on: VariantDump,
    bind_off: VariantDump,
}

#[derive(Serialize)]
struct HonestRow {
    row: usize,
    cols: Vec<u32>,
}

#[derive(Serialize)]
struct ForgedRow {
    label: String,
    row: usize,
    forge: &'static str,
    forge_xor_mask: u32,
    cols: Vec<u32>,
    expected_bind_off_violations: Vec<usize>,
    expected_bind_on_violations: Vec<usize>,
}

#[derive(Serialize)]
struct AirJson {
    schema_version: u32,
    stwo_rev: &'static str,
    p: u64,
    n_columns: usize,
    enabler_col: usize,
    k_table: Vec<u32>,
    trace_block: &'static str,
    variants: Variants,
    honest_rows: Vec<HonestRow>,
    forged_rows: Vec<ForgedRow>,
}

const FORGE_ROW: usize = 10;
const FORGE_XOR_MASK: u32 = 0xdead_beef;
const CH_BINDINGS: [usize; 2] = [5, 6];
const MAJ_BINDINGS: [usize; 2] = [13, 14];

fn main() {
    let out_path = std::env::args()
        .nth(1)
        .expect("usage: dump_smt <output-path.json> (e.g. smt/out/air.json)");

    // 1. Extract both variants and run the structural gates.
    let bind_on: Extraction = extract(true);
    let bind_off: Extraction = extract(false);
    let info = structural_checks(&bind_on.dump, &bind_off.dump);
    eprintln!(
        "structural gates OK: 21/17 constraints, 38 relation uses, enabler_col={}, \
         binding indices {:?}, pairs {:?}",
        info.enabler_col, info.binding_indices, info.binding_pairs
    );

    // 2. Honest trace: all 64 rows of the "abc" compression. Honest columns are
    //    variant-independent (bind is an Eval field, not a witness difference; the honest
    //    witness already writes col78=col76 etc.).
    let honest = build_round_trace(&[abc_input()]);
    assert_eq!(honest.log_size, 6, "expected exactly 64 honest rows");
    let mut carries_seen: BTreeSet<u32> = BTreeSet::new();
    let mut honest_rows = Vec::with_capacity(64);
    for row in 0..64usize {
        let cols = row_cols(&honest, row);
        assert_eq!(cols[info.enabler_col], 1, "honest row {row}: enabler");
        assert_eq!(cols[1] as usize, row, "honest row {row}: t counter");
        check_row(&bind_on, &bind_off, &cols, &[], &[], &format!("honest row {row}"));
        carries_seen.extend(carry_values(&bind_on.evaluator, &cols));
        honest_rows.push(HonestRow { row, cols });
    }
    let expected_carries: BTreeSet<u32> = [0, 1, 2].into_iter().collect();
    assert_eq!(
        carries_seen, expected_carries,
        "honest trace must exercise TripleSum32 carries exactly {{0,1,2}}"
    );
    eprintln!("numeric gates A+B OK on 64 honest rows; carry classes seen: {carries_seen:?}");

    // 3. Forged rows (Rust-constructed SAT witnesses corroborating M.bind_off).
    //    0xdeadbeef flips both 16-bit halves, so both bindings of each pair fire.
    // (a) ch-forged: single-row forge_ch on an honest trace, dump row 10.
    let mut ch_trace = build_round_trace(&[abc_input()]);
    let honest_ch = ch_trace.cols[78][FORGE_ROW].0 | (ch_trace.cols[79][FORGE_ROW].0 << 16);
    forge_ch(&mut ch_trace, FORGE_ROW, honest_ch ^ FORGE_XOR_MASK);
    let ch_cols = row_cols(&ch_trace, FORGE_ROW);
    check_row(&bind_on, &bind_off, &ch_cols, &CH_BINDINGS, &[], "forged ch row");
    // (b) maj-forged: propagated forgery builder, dump row 10.
    let honest_maj = honest.cols[114][FORGE_ROW].0 | (honest.cols[115][FORGE_ROW].0 << 16);
    let maj_trace = build_round_trace_forge(
        &[abc_input()],
        0,
        FORGE_ROW,
        Forge::Maj(honest_maj ^ FORGE_XOR_MASK),
    );
    let maj_cols = row_cols(&maj_trace, FORGE_ROW);
    check_row(&bind_on, &bind_off, &maj_cols, &MAJ_BINDINGS, &[], "forged maj row");
    eprintln!(
        "forged rows OK: bind_off satisfied, bind_on violated at exactly {CH_BINDINGS:?} (ch) \
         and {MAJ_BINDINGS:?} (maj)"
    );

    let forged_rows = vec![
        ForgedRow {
            label: "row10_forged_ch".to_string(),
            row: FORGE_ROW,
            forge: "ch",
            forge_xor_mask: FORGE_XOR_MASK,
            cols: ch_cols,
            expected_bind_off_violations: vec![],
            expected_bind_on_violations: CH_BINDINGS.to_vec(),
        },
        ForgedRow {
            label: "row10_forged_maj".to_string(),
            row: FORGE_ROW,
            forge: "maj",
            forge_xor_mask: FORGE_XOR_MASK,
            cols: maj_cols,
            expected_bind_off_violations: vec![],
            expected_bind_on_violations: MAJ_BINDINGS.to_vec(),
        },
    ];

    // 4. Assemble and write (K dumped from reference.rs — the Rust source of the two-source
    //    K check; fips.py carries the independent FIPS 180-4 §4.2.2 list).
    let air = AirJson {
        schema_version: 1,
        stwo_rev: STWO_REV,
        p: P,
        n_columns: N_TRACE_COLUMNS,
        enabler_col: info.enabler_col,
        k_table: reference::K.to_vec(),
        trace_block: "abc",
        variants: Variants {
            bind_on: bind_on.dump,
            bind_off: bind_off.dump,
        },
        honest_rows,
        forged_rows,
    };

    if let Some(parent) = Path::new(&out_path).parent() {
        fs::create_dir_all(parent).expect("failed to create output directory");
    }
    let json = serde_json::to_string_pretty(&air).expect("JSON serialization failed");
    fs::write(&out_path, &json).expect("failed to write output file");
    eprintln!("wrote {} ({} bytes)", out_path, json.len());
}
