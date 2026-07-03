//! Non-panicking constraint checker (spike-only test infrastructure).
//!
//! Mirror of stwo-constraint-framework's `AssertEvaluator`
//! (crates/constraint-framework/src/prover/assert.rs @ 93dd93e0) that RECORDS violations
//! instead of `assert!`-ing. Needed because `AssertEvaluator` panics inside `evaluate`,
//! which unwinds through `LogupAtRow`'s finalization-asserting `Drop` and turns every
//! rejected trace into a process abort (panic-in-drop) — unusable for reject-path tests.
//!
//! The mask-offset indexing and the logup batching/finalization logic are copied
//! line-faithfully from assert.rs and the `logup_proxy!` macro (lib.rs:181-261) at the
//! same pin, so accepting/rejecting here is equivalent to `assert_constraints_on_trace`.

use std::cell::RefCell;
use std::rc::Rc;

use num_traits::Zero;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo::core::pcs::TreeVec;
use stwo::core::utils::{
    bit_reverse_index, circle_domain_index_to_coset_index, coset_index_to_circle_domain_index,
};
use stwo::core::Fraction;
use stwo_constraint_framework::{EvalAtRow, INTERACTION_TRACE_IDX};

/// One recorded constraint violation.
#[derive(Debug, Clone)]
pub struct Violation {
    pub row: usize,
    pub constraint_index: usize,
}

pub struct CheckEvaluator<'a> {
    trace: &'a TreeVec<Vec<&'a Vec<BaseField>>>,
    col_index: TreeVec<usize>,
    row: usize,
    constraint_counter: usize,
    violations: Rc<RefCell<Vec<Violation>>>,
    // Logup state — mirrors LogupAtRow's fields, without its panicking Drop.
    log_size: u32,
    cumsum_shift: SecureField,
    fracs: Vec<Fraction<SecureField, SecureField>>,
}

impl<'a> CheckEvaluator<'a> {
    pub fn new(
        trace: &'a TreeVec<Vec<&'a Vec<BaseField>>>,
        row: usize,
        log_size: u32,
        claimed_sum: SecureField,
        violations: Rc<RefCell<Vec<Violation>>>,
    ) -> Self {
        Self {
            trace,
            col_index: TreeVec::new(vec![0; trace.len()]),
            row,
            constraint_counter: 0,
            violations,
            log_size,
            cumsum_shift: claimed_sum / BaseField::from_u32_unchecked(1 << log_size),
            fracs: vec![],
        }
    }
}

impl EvalAtRow for CheckEvaluator<'_> {
    type F = BaseField;
    type EF = SecureField;

    // Copied from AssertEvaluator::next_interaction_mask (assert.rs:48-77): offsets are
    // interpreted in coset order while columns are stored in bit-reversed circle-domain
    // order.
    fn next_interaction_mask<const N: usize>(
        &mut self,
        interaction: usize,
        offsets: [isize; N],
    ) -> [Self::F; N] {
        let col_index = self.col_index[interaction];
        self.col_index[interaction] += 1;
        offsets.map(|off| {
            if off == 0 {
                return self.trace[interaction][col_index][self.row];
            }
            let log_size = self.log_size;
            let domain_size = 1 << log_size;
            let coset_index =
                circle_domain_index_to_coset_index(bit_reverse_index(self.row, log_size), log_size);
            let next_coset_index = (coset_index as isize + off).rem_euclid(domain_size);
            let next_index = bit_reverse_index(
                coset_index_to_circle_domain_index(next_coset_index as usize, log_size),
                log_size,
            );
            self.trace[interaction][col_index][next_index]
        })
    }

    fn add_constraint<G>(&mut self, constraint: G)
    where
        Self::EF: std::ops::Mul<G, Output = Self::EF> + From<G>,
    {
        if Self::EF::from(constraint) != SecureField::zero() {
            self.violations.borrow_mut().push(Violation {
                row: self.row,
                constraint_index: self.constraint_counter,
            });
        }
        self.constraint_counter += 1;
    }

    fn combine_ef(values: [Self::F; SECURE_EXTENSION_DEGREE]) -> Self::EF {
        SecureField::from_m31_array(values)
    }

    fn write_logup_frac(&mut self, fraction: Fraction<Self::EF, Self::EF>) {
        self.fracs.push(fraction);
    }

    // Mirrors stwo-constraint-framework rev 5ea05973: batches consecutive fractions into
    // groups of `batch_size` (chunking), rather than the older explicit per-fraction batch
    // vector. `finalize_logup_in_pairs` (batch_size 2) is behaviourally identical to the
    // previous `n / 2` grouping. The prover-side `is_finalized` bookkeeping is intentionally
    // omitted here (no Drop guard in this checker mirror).
    fn finalize_logup_batched(&mut self, batch_size: usize) {
        assert!(batch_size > 0, "Batch size must be positive");

        let mut batched: Vec<Fraction<SecureField, SecureField>> = self
            .fracs
            .chunks(batch_size)
            .map(|chunk| chunk.iter().cloned().sum())
            .collect();

        let last_frac = batched.pop().expect("No fractions to finalize");

        let mut prev_col_cumsum = SecureField::zero();
        for cur_frac in batched {
            let [cur_cumsum] = self.next_extension_interaction_mask(INTERACTION_TRACE_IDX, [0]);
            let diff = cur_cumsum - prev_col_cumsum;
            prev_col_cumsum = cur_cumsum;
            self.add_constraint(diff * cur_frac.denominator - cur_frac.numerator);
        }

        let [prev_row_cumsum, cur_cumsum] =
            self.next_extension_interaction_mask(INTERACTION_TRACE_IDX, [-1, 0]);
        let diff = cur_cumsum - prev_row_cumsum - prev_col_cumsum;
        let shifted_diff = diff + self.cumsum_shift;
        self.add_constraint(shifted_diff * last_frac.denominator - last_frac.numerator);
    }

    fn finalize_logup(&mut self) {
        self.finalize_logup_batched(1)
    }

    fn finalize_logup_in_pairs(&mut self) {
        self.finalize_logup_batched(2)
    }
}

/// Evaluate every constraint on every row; return all violations (empty = accepted).
/// Non-panicking analogue of `assert_constraints_on_trace`.
///
/// Scope: unlike real stwo, this mirror does not enforce stwo's finalize-logup-exactly-once
/// invariant (the `is_finalized` assert + `Drop` guard). An `evaluate` that forgot to
/// finalize, or finalized twice, would be silently accepted here but panics under the real
/// `AssertEvaluator`. The ported component finalizes exactly once (`finalize_logup_in_pairs`
/// at the end of `evaluate`), so this does not affect any verdict; a future component reusing
/// this checker must preserve that invariant itself.
pub fn check_constraints_on_trace(
    evals: &TreeVec<Vec<&Vec<BaseField>>>,
    log_size: u32,
    eval_fn: impl Fn(CheckEvaluator<'_>),
    claimed_sum: SecureField,
) -> Vec<Violation> {
    let violations = Rc::new(RefCell::new(Vec::new()));
    let n_rows: usize = 1 << log_size;
    for row in 0..n_rows {
        let evaluator =
            CheckEvaluator::new(evals, row, log_size, claimed_sum, Rc::clone(&violations));
        eval_fn(evaluator);
    }
    Rc::try_unwrap(violations).unwrap().into_inner()
}
