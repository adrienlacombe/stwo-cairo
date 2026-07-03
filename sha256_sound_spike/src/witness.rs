//! Spike-only scalar witness builder for the ported `sha_256_round` component.
//!
//! HAND-AUTHORED (not a port): the upstream SIMD witness generator
//! (pr1425-ref/witness/sha_256_round.rs) needs the whole sub-component ClaimGenerator
//! network, which is not ported yet. This scalar builder fills the same 125 columns with
//! the same values (cross-checked cell-by-cell against the column semantics in the
//! component's `evaluate` and against pr1425-ref/witness/sha_256_round.rs), computing
//! everything from the independent FIPS-180-4 reference in `reference.rs`.
//!
//! Column map (from the decoded component; limbs are (lo16, hi16) of each u32):
//!   0: seq (compression index)      1: t (round counter 0..63)
//!   2..=17:  state a,b,c,d,e,f,g,h  18..=49: schedule window W[t..t+15]
//!   50/51: BigSigma1(e)             52/53: BigSigma0(a)
//!   54..=57: ms8 of e_lo,e_hi,f_lo,f_hi      58..=61: AND bytes of e&f
//!   62/63: not_e limbs              64..=67: ms8 of not_e_lo,not_e_hi,g_lo,g_hi
//!   68..=71: AND bytes of ~e&g      72..=75: XOR bytes -> Ch
//!   76/77: chl/chh                  78/79: ch_limb (duplicates; see component header)
//!   80/81: K[t]                     82/83: h+Sigma1+Ch     84/85: T1 (=82/83+K+W[t])
//!   86..=91: ms8 of a_lo,a_hi,b_lo,b_hi,c_lo,c_hi
//!   92..=103: AND bytes of a&b,a&c,b&c        104..=111: XOR bytes -> Maj
//!   112/113: majl/majh              114/115: maj_limb (duplicates)
//!   116/117: T2 (=Sigma0+Maj)       118/119: schedule output W[t+16]
//!   120/121: new_e (=d+T1)          122/123: new_a (=T1+T2)     124: enabler

use itertools::Itertools;
use num_traits::One;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::m31::{BaseField, M31};
use stwo::core::fields::qm31::SecureField;
use stwo::core::pcs::TreeVec;
use stwo::core::poly::circle::CanonicCoset;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::m31::N_LANES;
use stwo::prover::backend::simd::qm31::PackedSecureField;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::Column;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo_constraint_framework::{LogupTraceGenerator, Relation};

use crate::components::sha_256_round::N_TRACE_COLUMNS;
use crate::reference;
use crate::relations;

/// Number of logup fractions per row emitted by the round component's `evaluate`,
/// in exact eval order (see `row_fractions`).
pub const N_FRACTIONS: usize = 38;
/// `finalize_logup_in_pairs` batches them 2-per-column.
pub const N_LOGUP_COLS: usize = N_FRACTIONS / 2;

/// The seven lookup-element sets the round component takes, drawn from one channel.
pub struct RoundRelations {
    pub big_sigma_1: relations::Sha256BigSigma1,
    pub big_sigma_0: relations::Sha256BigSigma0,
    pub and_8: relations::VerifyBitwiseAnd_8,
    pub xor_8: relations::VerifyBitwiseXor_8,
    pub k_table: relations::Sha256KTable,
    pub schedule: relations::Sha256Schedule,
    pub round: relations::Sha256Round,
}

impl RoundRelations {
    /// Draw order is arbitrary for a single-component spike (in the full AIR the draw order
    /// is fixed by CairoInteractionElements); it only has to match between prover and
    /// constraint check, which it does because both use this struct.
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            big_sigma_1: relations::Sha256BigSigma1::draw(channel),
            big_sigma_0: relations::Sha256BigSigma0::draw(channel),
            and_8: relations::VerifyBitwiseAnd_8::draw(channel),
            xor_8: relations::VerifyBitwiseXor_8::draw(channel),
            k_table: relations::Sha256KTable::draw(channel),
            schedule: relations::Sha256Schedule::draw(channel),
            round: relations::Sha256Round::draw(channel),
        }
    }

    pub fn draw_test() -> Self {
        let mut channel = Blake2sChannel::default();
        channel.mix_u64(0x5ea_256);
        Self::draw(&mut channel)
    }
}

#[inline]
fn lo16(x: u32) -> u32 {
    x & 0xffff
}
#[inline]
fn hi16(x: u32) -> u32 {
    x >> 16
}
#[inline]
fn m(x: u32) -> M31 {
    M31::from(x)
}

/// One compression's worth of round-component inputs.
#[derive(Clone, Copy)]
pub struct CompressionInput {
    pub h_in: [u32; 8],
    pub block: [u32; 16],
}

/// The base trace (125 columns) plus per-compression reference outputs for KAT checks.
pub struct RoundTrace {
    pub log_size: u32,
    /// `N_TRACE_COLUMNS` columns of `1 << log_size` rows. Row index = storage index
    /// (bit-reversed circle-domain order), same convention as the SIMD ComponentTrace:
    /// the component has no non-zero mask offsets on base columns, so filling rows
    /// sequentially is equivalent.
    pub cols: Vec<Vec<M31>>,
    /// Reference state after 64 rounds (pre-feed-forward), one per compression.
    pub final_states: Vec<[u32; 8]>,
}

/// Fill the 125-column base trace for `inputs.len()` compressions (must be a power of two,
/// so rows = 64 * n fills the domain exactly and every row is enabled).
pub fn build_round_trace(inputs: &[CompressionInput]) -> RoundTrace {
    assert!(inputs.len().is_power_of_two(), "spike keeps every row enabled");
    let n_rows = inputs.len() * 64;
    let log_size = n_rows.ilog2();
    let mut cols = vec![vec![M31::from(0); n_rows]; N_TRACE_COLUMNS];
    let mut final_states = Vec::with_capacity(inputs.len());

    for (seq, input) in inputs.iter().enumerate() {
        let w = reference::message_schedule_80(&input.block);
        let mut state = input.h_in;
        for t in 0..64usize {
            let row = seq * 64 + t;
            fill_row(&mut cols, row, seq as u32, t as u32, state, &w);
            state = reference::round(state, w[t], reference::K[t]);
        }
        final_states.push(state);
    }
    RoundTrace {
        log_size,
        cols,
        final_states,
    }
}

/// Fill one row. `state` = (a..h) entering round `t`; `w` = 80-word extended schedule.
#[allow(clippy::needless_range_loop)]
fn fill_row(cols: &mut [Vec<M31>], row: usize, seq: u32, t: u32, state: [u32; 8], w: &[u32; 80]) {
    let ti = t as usize;
    let [a, b, c, d, e, f, g, h] = state;

    cols[0][row] = m(seq);
    cols[1][row] = m(t);
    for i in 0..8 {
        cols[2 + 2 * i][row] = m(lo16(state[i]));
        cols[3 + 2 * i][row] = m(hi16(state[i]));
    }
    for i in 0..16 {
        cols[18 + 2 * i][row] = m(lo16(w[ti + i]));
        cols[19 + 2 * i][row] = m(hi16(w[ti + i]));
    }

    let bs1 = reference::big_sigma_1(e);
    cols[50][row] = m(lo16(bs1));
    cols[51][row] = m(hi16(bs1));
    let bs0 = reference::big_sigma_0(a);
    cols[52][row] = m(lo16(bs0));
    cols[53][row] = m(hi16(bs0));

    // Ch = (e & f) ^ (~e & g), byte-decomposed.
    cols[54][row] = m(lo16(e) >> 8);
    cols[55][row] = m(hi16(e) >> 8);
    cols[56][row] = m(lo16(f) >> 8);
    cols[57][row] = m(hi16(f) >> 8);
    let ef = e & f;
    cols[58][row] = m(lo16(ef) & 0xff);
    cols[59][row] = m(lo16(ef) >> 8);
    cols[60][row] = m(hi16(ef) & 0xff);
    cols[61][row] = m(hi16(ef) >> 8);
    let ne = !e;
    cols[62][row] = m(lo16(ne));
    cols[63][row] = m(hi16(ne));
    cols[64][row] = m(lo16(ne) >> 8);
    cols[65][row] = m(hi16(ne) >> 8);
    cols[66][row] = m(lo16(g) >> 8);
    cols[67][row] = m(hi16(g) >> 8);
    let neg = ne & g;
    cols[68][row] = m(lo16(neg) & 0xff);
    cols[69][row] = m(lo16(neg) >> 8);
    cols[70][row] = m(hi16(neg) & 0xff);
    cols[71][row] = m(hi16(neg) >> 8);
    let ch = reference::ch(e, f, g);
    cols[72][row] = m(lo16(ch) & 0xff);
    cols[73][row] = m(lo16(ch) >> 8);
    cols[74][row] = m(hi16(ch) & 0xff);
    cols[75][row] = m(hi16(ch) >> 8);
    cols[76][row] = m(lo16(ch));
    cols[77][row] = m(hi16(ch));
    // ch_limb duplicates (see component header, deviation 3).
    cols[78][row] = cols[76][row];
    cols[79][row] = cols[77][row];

    let k = reference::K[ti];
    cols[80][row] = m(lo16(k));
    cols[81][row] = m(hi16(k));

    // T1 chain.
    let s1 = h.wrapping_add(bs1).wrapping_add(ch);
    cols[82][row] = m(lo16(s1));
    cols[83][row] = m(hi16(s1));
    let t1 = s1.wrapping_add(k).wrapping_add(w[ti]);
    cols[84][row] = m(lo16(t1));
    cols[85][row] = m(hi16(t1));

    // Maj = (a & b) ^ (a & c) ^ (b & c), byte-decomposed.
    cols[86][row] = m(lo16(a) >> 8);
    cols[87][row] = m(hi16(a) >> 8);
    cols[88][row] = m(lo16(b) >> 8);
    cols[89][row] = m(hi16(b) >> 8);
    cols[90][row] = m(lo16(c) >> 8);
    cols[91][row] = m(hi16(c) >> 8);
    let ab = a & b;
    let ac = a & c;
    let bc = b & c;
    cols[92][row] = m(lo16(ab) & 0xff);
    cols[93][row] = m(lo16(ab) >> 8);
    cols[94][row] = m(hi16(ab) & 0xff);
    cols[95][row] = m(hi16(ab) >> 8);
    cols[96][row] = m(lo16(ac) & 0xff);
    cols[97][row] = m(lo16(ac) >> 8);
    cols[98][row] = m(hi16(ac) & 0xff);
    cols[99][row] = m(hi16(ac) >> 8);
    cols[100][row] = m(lo16(bc) & 0xff);
    cols[101][row] = m(lo16(bc) >> 8);
    cols[102][row] = m(hi16(bc) & 0xff);
    cols[103][row] = m(hi16(bc) >> 8);
    let abac = ab ^ ac;
    cols[104][row] = m(lo16(abac) & 0xff);
    cols[105][row] = m(lo16(abac) >> 8);
    cols[106][row] = m(hi16(abac) & 0xff);
    cols[107][row] = m(hi16(abac) >> 8);
    let maj = reference::maj(a, b, c);
    cols[108][row] = m(lo16(maj) & 0xff);
    cols[109][row] = m(lo16(maj) >> 8);
    cols[110][row] = m(hi16(maj) & 0xff);
    cols[111][row] = m(hi16(maj) >> 8);
    cols[112][row] = m(lo16(maj));
    cols[113][row] = m(hi16(maj));
    // maj_limb duplicates (see component header, deviation 3).
    cols[114][row] = cols[112][row];
    cols[115][row] = cols[113][row];

    // T2 = Sigma0 + Maj.
    let t2 = bs0.wrapping_add(maj);
    cols[116][row] = m(lo16(t2));
    cols[117][row] = m(hi16(t2));

    // Schedule output: W[t+16] (extended schedule; see reference::message_schedule_80).
    cols[118][row] = m(lo16(w[ti + 16]));
    cols[119][row] = m(hi16(w[ti + 16]));

    // new_e = d + T1, new_a = T1 + T2.
    let new_e = d.wrapping_add(t1);
    cols[120][row] = m(lo16(new_e));
    cols[121][row] = m(hi16(new_e));
    let new_a = t1.wrapping_add(t2);
    cols[122][row] = m(lo16(new_a));
    cols[123][row] = m(hi16(new_a));

    // Enabler (all rows enabled in this spike; padding-free power-of-two fit).
    cols[124][row] = m(1);
}

/// The 38 (numerator, denominator) logup fractions of one row, in the EXACT order the
/// component's `evaluate` emits them. Any divergence from that order breaks the
/// interaction-trace/constraint correspondence — cross-check against sha_256_round.rs
/// when either side changes.
fn row_fractions(
    cols: &[Vec<M31>],
    row: usize,
    rels: &RoundRelations,
) -> Vec<(SecureField, SecureField)> {
    let c = |i: usize| cols[i][row];
    let one = SecureField::one();
    let enabler: SecureField = c(124).into();
    let m256 = M31::from(256);

    let mut fracs: Vec<(SecureField, SecureField)> = Vec::with_capacity(N_FRACTIONS);

    // 1-2: BigSigma1(e), BigSigma0(a).
    fracs.push((one, rels.big_sigma_1.combine(&[c(10), c(11), c(50), c(51)])));
    fracs.push((one, rels.big_sigma_0.combine(&[c(2), c(3), c(52), c(53)])));

    // Low-byte helper: lo8(x16) = x16 - ms8 * 256 (mirrors Split16LowPartSize8).
    let lo8 = |x: M31, ms8: M31| x - ms8 * m256;

    // 3-6: AND bytes of e & f.
    fracs.push((one, rels.and_8.combine(&[lo8(c(10), c(54)), lo8(c(12), c(56)), c(58)])));
    fracs.push((one, rels.and_8.combine(&[c(54), c(56), c(59)])));
    fracs.push((one, rels.and_8.combine(&[lo8(c(11), c(55)), lo8(c(13), c(57)), c(60)])));
    fracs.push((one, rels.and_8.combine(&[c(55), c(57), c(61)])));
    // 7-10: AND bytes of ~e & g.
    fracs.push((one, rels.and_8.combine(&[lo8(c(62), c(64)), lo8(c(14), c(66)), c(68)])));
    fracs.push((one, rels.and_8.combine(&[c(64), c(66), c(69)])));
    fracs.push((one, rels.and_8.combine(&[lo8(c(63), c(65)), lo8(c(15), c(67)), c(70)])));
    fracs.push((one, rels.and_8.combine(&[c(65), c(67), c(71)])));
    // 11-14: XOR bytes -> Ch.
    fracs.push((one, rels.xor_8.combine(&[c(58), c(68), c(72)])));
    fracs.push((one, rels.xor_8.combine(&[c(59), c(69), c(73)])));
    fracs.push((one, rels.xor_8.combine(&[c(60), c(70), c(74)])));
    fracs.push((one, rels.xor_8.combine(&[c(61), c(71), c(75)])));

    // 15: K table.
    fracs.push((one, rels.k_table.combine(&[c(1), c(80), c(81)])));

    // 16-27: AND bytes of a&b, a&c, b&c.
    fracs.push((one, rels.and_8.combine(&[lo8(c(2), c(86)), lo8(c(4), c(88)), c(92)])));
    fracs.push((one, rels.and_8.combine(&[c(86), c(88), c(93)])));
    fracs.push((one, rels.and_8.combine(&[lo8(c(3), c(87)), lo8(c(5), c(89)), c(94)])));
    fracs.push((one, rels.and_8.combine(&[c(87), c(89), c(95)])));
    fracs.push((one, rels.and_8.combine(&[lo8(c(2), c(86)), lo8(c(6), c(90)), c(96)])));
    fracs.push((one, rels.and_8.combine(&[c(86), c(90), c(97)])));
    fracs.push((one, rels.and_8.combine(&[lo8(c(3), c(87)), lo8(c(7), c(91)), c(98)])));
    fracs.push((one, rels.and_8.combine(&[c(87), c(91), c(99)])));
    fracs.push((one, rels.and_8.combine(&[lo8(c(4), c(88)), lo8(c(6), c(90)), c(100)])));
    fracs.push((one, rels.and_8.combine(&[c(88), c(90), c(101)])));
    fracs.push((one, rels.and_8.combine(&[lo8(c(5), c(89)), lo8(c(7), c(91)), c(102)])));
    fracs.push((one, rels.and_8.combine(&[c(89), c(91), c(103)])));
    // 28-35: XOR bytes -> Maj.
    fracs.push((one, rels.xor_8.combine(&[c(92), c(96), c(104)])));
    fracs.push((one, rels.xor_8.combine(&[c(93), c(97), c(105)])));
    fracs.push((one, rels.xor_8.combine(&[c(94), c(98), c(106)])));
    fracs.push((one, rels.xor_8.combine(&[c(95), c(99), c(107)])));
    fracs.push((one, rels.xor_8.combine(&[c(104), c(100), c(108)])));
    fracs.push((one, rels.xor_8.combine(&[c(105), c(101), c(109)])));
    fracs.push((one, rels.xor_8.combine(&[c(106), c(102), c(110)])));
    fracs.push((one, rels.xor_8.combine(&[c(107), c(103), c(111)])));

    // 36: schedule pull (window + next word).
    let mut sched: Vec<M31> = (18..=49).map(c).collect();
    sched.push(c(118));
    sched.push(c(119));
    fracs.push((one, rels.schedule.combine(&sched)));

    // 37: round self-chain push (seq, t, full state+window), +enabler.
    let mut push: Vec<M31> = Vec::with_capacity(50);
    push.push(c(0));
    push.push(c(1));
    push.extend((2..=49).map(c));
    fracs.push((enabler, rels.round.combine(&push)));

    // 38: round self-chain pull (seq, t+1, rotated state + advanced window), -enabler.
    let mut pull: Vec<M31> = Vec::with_capacity(50);
    pull.push(c(0));
    pull.push(c(1) + M31::from(1));
    pull.extend([c(122), c(123), c(2), c(3), c(4), c(5), c(6), c(7)]);
    pull.extend([c(120), c(121), c(10), c(11), c(12), c(13), c(14), c(15)]);
    pull.extend((20..=49).map(c));
    pull.extend([c(118), c(119)]);
    fracs.push((-enabler, rels.round.combine(&pull)));

    assert_eq!(fracs.len(), N_FRACTIONS);
    fracs
}

/// The base trace as committed SIMD circle evaluations (for the real prover pipeline).
pub fn base_trace_evals(
    trace: &RoundTrace,
) -> Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    let domain = CanonicCoset::new(trace.log_size).circle_domain();
    trace
        .cols
        .iter()
        .map(|col| CircleEvaluation::new(domain, BaseColumn::from_iter(col.iter().copied())))
        .collect()
}

/// Build the interaction trace (19 secure columns = 76 base columns) exactly as
/// `finalize_logup_in_pairs` expects, plus the claimed sum, as committed SIMD circle
/// evaluations (for the real prover pipeline).
#[allow(clippy::needless_range_loop)] // `j` indexes the per-row batched-fraction vectors.
pub fn build_interaction_evals(
    trace: &RoundTrace,
    rels: &RoundRelations,
) -> (
    Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    SecureField,
) {
    let n_rows = 1usize << trace.log_size;
    assert!(n_rows >= N_LANES, "log_size must be >= LOG_N_LANES");

    // Per-row fractions, then batch pairs (2j, 2j+1): num = n0*d1 + n1*d0, den = d0*d1.
    let batched: Vec<Vec<(SecureField, SecureField)>> = (0..n_rows)
        .map(|row| {
            row_fractions(&trace.cols, row, rels)
                .chunks(2)
                .map(|pair| {
                    let (n0, d0) = pair[0];
                    let (n1, d1) = pair[1];
                    (n0 * d1 + n1 * d0, d0 * d1)
                })
                .collect()
        })
        .collect();

    let mut logup_gen = LogupTraceGenerator::new(trace.log_size);
    for j in 0..N_LOGUP_COLS {
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..(n_rows / N_LANES) {
            let num = PackedSecureField::from_array(std::array::from_fn(|lane| {
                batched[vec_row * N_LANES + lane][j].0
            }));
            let den = PackedSecureField::from_array(std::array::from_fn(|lane| {
                batched[vec_row * N_LANES + lane][j].1
            }));
            col_gen.write_frac(vec_row, num, den);
        }
        col_gen.finalize_col();
    }
    logup_gen.finalize_last()
}

/// CPU-column form of the interaction trace, for the row-by-row constraint checker.
pub fn build_interaction_trace(
    trace: &RoundTrace,
    rels: &RoundRelations,
) -> (Vec<Vec<M31>>, SecureField) {
    let (evals, claimed_sum) = build_interaction_evals(trace, rels);
    let interaction_cols = evals
        .into_iter()
        .map(|eval| eval.values.to_cpu())
        .collect_vec();
    (interaction_cols, claimed_sum)
}

/// Assemble the TreeVec layout `assert_constraints_on_trace` expects:
/// [preprocessed (none for this component), base (125), interaction (76)].
pub fn as_tree<'a>(
    base: &'a [Vec<M31>],
    interaction: &'a [Vec<M31>],
) -> TreeVec<Vec<&'a Vec<M31>>> {
    TreeVec::new(vec![
        vec![],
        base.iter().collect(),
        interaction.iter().collect(),
    ])
}

#[inline]
fn u32_at(cols: &[Vec<M31>], row: usize, lo: usize, hi: usize) -> u32 {
    cols[lo][row].0 | (cols[hi][row].0 << 16)
}

/// Overwrite one row's Ch to `forged_ch`: set the unconstrained `ch_limb` columns (78/79)
/// and recompute the row's downstream T1 chain / new_e / new_a. `chl`/`chh` (76/77) stay
/// honest — the AND/XOR lookups pin them, so a real prover cannot touch them. Returns the
/// forged post-round state `[a..h]` entering the NEXT round (ordering matches
/// [`reference::round`]), for callers that propagate the corruption forward.
fn overwrite_row_forged_ch(cols: &mut [Vec<M31>], row: usize, forged_ch: u32) -> [u32; 8] {
    let a = u32_at(cols, row, 2, 3);
    let b = u32_at(cols, row, 4, 5);
    let c = u32_at(cols, row, 6, 7);
    let d = u32_at(cols, row, 8, 9);
    let e = u32_at(cols, row, 10, 11);
    let f = u32_at(cols, row, 12, 13);
    let g = u32_at(cols, row, 14, 15);
    let h = u32_at(cols, row, 16, 17);
    let bs1 = u32_at(cols, row, 50, 51);
    let k = u32_at(cols, row, 80, 81);
    let wt = u32_at(cols, row, 18, 19);
    let t2 = u32_at(cols, row, 116, 117);

    cols[78][row] = m(lo16(forged_ch));
    cols[79][row] = m(hi16(forged_ch));
    let s1 = h.wrapping_add(bs1).wrapping_add(forged_ch);
    cols[82][row] = m(lo16(s1));
    cols[83][row] = m(hi16(s1));
    let t1 = s1.wrapping_add(k).wrapping_add(wt);
    cols[84][row] = m(lo16(t1));
    cols[85][row] = m(hi16(t1));
    let new_e = d.wrapping_add(t1);
    cols[120][row] = m(lo16(new_e));
    cols[121][row] = m(hi16(new_e));
    let new_a = t1.wrapping_add(t2);
    cols[122][row] = m(lo16(new_a));
    cols[123][row] = m(hi16(new_a));

    [new_a, a, b, c, new_e, e, f, g]
}

/// Overwrite one row's Maj to `forged_maj`: set the unconstrained `maj_limb` columns
/// (114/115) and recompute T2 (116/117) and new_a (122/123). `majl`/`majh` (112/113) stay
/// honest (pinned by the AND/XOR lookups); `new_e`/T1 are unaffected (they depend only on
/// Ch). Returns the forged post-round state `[a..h]`.
fn overwrite_row_forged_maj(cols: &mut [Vec<M31>], row: usize, forged_maj: u32) -> [u32; 8] {
    let a = u32_at(cols, row, 2, 3);
    let b = u32_at(cols, row, 4, 5);
    let c = u32_at(cols, row, 6, 7);
    let e = u32_at(cols, row, 10, 11);
    let f = u32_at(cols, row, 12, 13);
    let g = u32_at(cols, row, 14, 15);
    let bs0 = u32_at(cols, row, 52, 53);
    let t1 = u32_at(cols, row, 84, 85);
    let new_e = u32_at(cols, row, 120, 121);

    cols[114][row] = m(lo16(forged_maj));
    cols[115][row] = m(hi16(forged_maj));
    let t2 = bs0.wrapping_add(forged_maj);
    cols[116][row] = m(lo16(t2));
    cols[117][row] = m(hi16(t2));
    let new_a = t1.wrapping_add(t2);
    cols[122][row] = m(lo16(new_a));
    cols[123][row] = m(hi16(new_a));

    [new_a, a, b, c, new_e, e, f, g]
}

/// TEST HELPER — forge the Ch value of a SINGLE row the way a malicious prover would against
/// the verbatim decoded component: overwrite the unconstrained ch_limb columns (78/79) and
/// recompute that row's downstream columns (T1 chain, new_e, new_a). All row-local
/// constraints of the VERBATIM component remain satisfied; only the added
/// `bind_ch_maj_limbs` constraints catch it AT THIS ROW.
///
/// NOTE: this corrupts one row WITHOUT updating the next row's input state, so it leaves the
/// round self-relation's PUSH (row+1) / PULL (this row) disagreeing at the boundary — a
/// residual the full multi-component AIR would itself reject via the round relation's global
/// balance. For the end-to-end exploit that the binding fix is genuinely needed to stop, see
/// [`build_round_trace_forge`] (a PROPAGATED forgery that keeps the round chain consistent).
pub fn forge_ch(trace: &mut RoundTrace, row: usize, forged_ch: u32) {
    let _ = overwrite_row_forged_ch(&mut trace.cols, row, forged_ch);
}

/// Which round-choice function to forge, and to what value, in [`build_round_trace_forge`].
#[derive(Clone, Copy)]
pub enum Forge {
    Ch(u32),
    Maj(u32),
}

/// TEST HELPER — build a trace with a PROPAGATED forgery: forge the Ch (or Maj) of round
/// `forge_t` in compression `forge_seq`, then carry the corrupted state honestly through
/// every remaining round so the round self-relation chains consistently across all rows.
///
/// This models the actual end-to-end exploit of the ch_limb/maj_limb under-constraint. Unlike
/// [`forge_ch`] (single row → round-chain boundary residual the full AIR catches on its own),
/// here EVERY row-local constraint AND the round self-chain hold, so the verbatim decoded
/// component accepts a trace whose final digest is NOT SHA-256. Only the binding constraints
/// reject it, at exactly the forged row. `final_states[forge_seq]` is the forged (wrong)
/// post-64-round state.
pub fn build_round_trace_forge(
    inputs: &[CompressionInput],
    forge_seq: usize,
    forge_t: usize,
    forge: Forge,
) -> RoundTrace {
    assert!(inputs.len().is_power_of_two(), "spike keeps every row enabled");
    let n_rows = inputs.len() * 64;
    let log_size = n_rows.ilog2();
    let mut cols = vec![vec![M31::from(0); n_rows]; N_TRACE_COLUMNS];
    let mut final_states = Vec::with_capacity(inputs.len());

    for (seq, input) in inputs.iter().enumerate() {
        let w = reference::message_schedule_80(&input.block);
        let mut state = input.h_in;
        for t in 0..64usize {
            let row = seq * 64 + t;
            fill_row(&mut cols, row, seq as u32, t as u32, state, &w);
            state = if seq == forge_seq && t == forge_t {
                match forge {
                    Forge::Ch(v) => overwrite_row_forged_ch(&mut cols, row, v),
                    Forge::Maj(v) => overwrite_row_forged_maj(&mut cols, row, v),
                }
            } else {
                reference::round(state, w[t], reference::K[t])
            };
        }
        final_states.push(state);
    }
    RoundTrace {
        log_size,
        cols,
        final_states,
    }
}
