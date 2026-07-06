//! Symbolic constraint extraction for the SMT soundness layer — SPIKE TEST INFRASTRUCTURE.
//!
//! Role: mechanically extract the sha_256_round component's base constraints and logup
//! relation uses as expression trees, with NO hand transcription, for consumption by the
//! z3 checker under `smt/` (see smt/DESIGN.md §1). Provenance: stwo rev 5ea05973
//! `constraint-framework/src/expr/` + stwo-cairo PR #1425 (open/undisclosed — see the
//! disclosure guardrail in smt/DESIGN.md; never push this branch to a public remote).
//!
//! Honest scope: `SymbolicEval` no-ops all three `finalize_logup*` methods DELIBERATELY —
//! the logup cumsum argument's soundness is an assumed stwo-core property (smt/README.md
//! §Not-covered); relation entries are modeled by their table semantics instead. Only the
//! single-row base-constraint system (125 columns, all mask offsets 0) is extracted; any
//! read outside interaction 1 / offset 0 / idx < 125 is a hard panic, never a fallback.
//!
//! Fidelity gates (smt/DESIGN.md §1.3): every conversion violation panics with the
//! offending subtree; structural counts/diff/Round-shape asserts plus two independent
//! numeric evaluators (raw-tree `assign`, converted-tree `Node` interpreter) are exposed
//! here and run by both `src/bin/dump_smt.rs` and `tests/smt_dump.rs`.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::ops::Mul;

use num_traits::Zero;
use serde::Serialize;
use stwo::core::fields::m31::{BaseField, M31};
use stwo::core::fields::qm31::SecureField;
use stwo_constraint_framework::expr::{BaseExpr, ColumnExpr, ExprEvaluator, ExtExpr};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{EvalAtRow, FrameworkEval, Relation, RelationEntry};

use crate::components::sha_256_round::{Claim, Eval, N_TRACE_COLUMNS};
use crate::relations;

/// M31 modulus, p = 2^31 - 1.
pub const P: u64 = (1 << 31) - 1;

/// Pinned stwo revision this extraction was written against (echoed into the JSON).
pub const STWO_REV: &str = "5ea05973";

// ---------------------------------------------------------------------------
// SymbolicEval: pass-through newtype over stwo's ExprEvaluator.
// ---------------------------------------------------------------------------

/// Pass-through wrapper over [`ExprEvaluator`]; its ONLY job is to no-op the three
/// `finalize_logup*` methods so the (excluded) cumsum constraints are never emitted and
/// `cur_var_index` never bleeds past the 125 base columns.
pub struct SymbolicEval(pub ExprEvaluator);

impl EvalAtRow for SymbolicEval {
    type F = BaseExpr;
    type EF = ExtExpr;

    fn next_interaction_mask<const N: usize>(
        &mut self,
        interaction: usize,
        offsets: [isize; N],
    ) -> [BaseExpr; N] {
        self.0.next_interaction_mask(interaction, offsets)
    }

    fn add_constraint<G>(&mut self, constraint: G)
    where
        Self::EF: Mul<G, Output = Self::EF> + From<G>,
    {
        self.0.add_constraint(constraint)
    }

    fn combine_ef(values: [BaseExpr; 4]) -> ExtExpr {
        <ExprEvaluator as EvalAtRow>::combine_ef(values)
    }

    fn add_intermediate(&mut self, val: BaseExpr) -> BaseExpr {
        self.0.add_intermediate(val)
    }

    fn add_extension_intermediate(&mut self, val: ExtExpr) -> ExtExpr {
        self.0.add_extension_intermediate(val)
    }

    /// Moves the entry unread (fields are private at rev 5ea05973) into ExprEvaluator's
    /// override, which records (relation name, multiplicity, pre-combination values) via
    /// `combine_formal` as an ext intermediate + a formal logup fraction.
    fn add_to_relation<R: Relation<BaseExpr, ExtExpr>>(
        &mut self,
        entry: RelationEntry<'_, BaseExpr, ExtExpr, R>,
    ) {
        self.0.add_to_relation(entry)
    }

    /// The round component reads no preprocessed columns; a preprocessed read would
    /// invalidate the single-row model, so fail loudly instead of delegating.
    fn get_preprocessed_column(&mut self, column: PreProcessedColumnId) -> BaseExpr {
        panic!(
            "preprocessed column read is outside the single-row SMT model: {:?}",
            column.id
        )
    }

    // Cumsum EXCLUDED from the model (smt/DESIGN.md §1.1): logup-argument soundness is an
    // assumed stwo-core property. Overriding all three prevents the trait defaults'
    // `unimplemented!()` from firing on `finalize_logup_in_pairs` (sha_256_round.rs:859)
    // and prevents the 4 trailing cumsum constraints / cur_var_index bleed.
    fn finalize_logup_batched(&mut self, _batch_size: usize) {}
    fn finalize_logup(&mut self) {}
    fn finalize_logup_in_pairs(&mut self) {}
    // `write_logup_frac` keeps its default (`unimplemented!()`): the inner ExprEvaluator's
    // own `add_to_relation` routes through the INNER `write_logup_frac`, never the wrapper.
}

// ---------------------------------------------------------------------------
// Node IR (the JSON grammar) + serializable dump structures.
// ---------------------------------------------------------------------------

/// 6-op expression IR over a single row of 125 M31 base columns. Exactly the JSON node
/// grammar of smt/DESIGN.md §2; the Python loader rejects anything else.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize)]
#[serde(tag = "op", rename_all = "snake_case")]
pub enum Node {
    Col {
        interaction: usize,
        idx: usize,
        offset: isize,
    },
    Const {
        val: u32,
    },
    Add {
        lhs: Box<Node>,
        rhs: Box<Node>,
    },
    Sub {
        lhs: Box<Node>,
        rhs: Box<Node>,
    },
    Mul {
        lhs: Box<Node>,
        rhs: Box<Node>,
    },
    Neg {
        arg: Box<Node>,
    },
}

/// One base constraint (index = emission order within its variant).
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ConstraintDump {
    pub index: usize,
    pub expr: Node,
}

/// One `add_to_relation` use, decoded BEFORE randomness combination.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RelationUseDump {
    pub order: usize,
    pub relation: String,
    pub declared_size: usize,
    pub mult_sign: i8,
    pub mult: Node,
    pub values: Vec<Node>,
}

/// One extracted variant (bind_ch_maj_limbs true/false) of the component.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct VariantDump {
    pub bind_ch_maj_limbs: bool,
    pub constraints: Vec<ConstraintDump>,
    pub relation_uses: Vec<RelationUseDump>,
}

/// Extraction result: the converted dump plus the raw evaluator (kept for numeric gate A —
/// `assign()` on the RAW pre-conversion trees, independent of the converter).
pub struct Extraction {
    pub evaluator: ExprEvaluator,
    pub dump: VariantDump,
}

// ---------------------------------------------------------------------------
// Converter: BaseExpr/ExtExpr -> Node. Every violation panics; no permissive fallback.
// ---------------------------------------------------------------------------

/// Reverse lookup for `ColumnExpr` (fields private at rev 5ea05973): equality-search the
/// space (0..=2) x (0..512) x (-2..=2) via the public `From<(usize, usize, isize)>` + `Eq`.
fn col_table() -> HashMap<ColumnExpr, (usize, usize, isize)> {
    let mut map = HashMap::new();
    for interaction in 0..=2usize {
        for idx in 0..512usize {
            for offset in -2..=2isize {
                map.insert(
                    ColumnExpr::from((interaction, idx, offset)),
                    (interaction, idx, offset),
                );
            }
        }
    }
    map
}

struct Converter<'a> {
    col_table: HashMap<ColumnExpr, (usize, usize, isize)>,
    /// Base intermediates by NAME (base carries and relation denominators share the
    /// `intermediateN` counter — resolve by name only, never by order).
    intermediates: &'a HashMap<String, BaseExpr>,
    memo: HashMap<String, Node>,
}

impl<'a> Converter<'a> {
    fn new(intermediates: &'a HashMap<String, BaseExpr>) -> Self {
        Self {
            col_table: col_table(),
            intermediates,
            memo: HashMap::new(),
        }
    }

    fn convert(&mut self, expr: &BaseExpr, depth: usize) -> Node {
        assert!(
            depth < 64,
            "intermediate inlining depth guard exceeded at {expr:?}"
        );
        match expr {
            BaseExpr::Col(col) => {
                let &(interaction, idx, offset) = self.col_table.get(col).unwrap_or_else(|| {
                    panic!("Col outside the (0..=2)x(0..512)x(-2..=2) search space: {col:?}")
                });
                assert!(
                    interaction == 1 && offset == 0 && idx < N_TRACE_COLUMNS,
                    "column read outside the single-row model: \
                     (interaction={interaction}, idx={idx}, offset={offset})"
                );
                Node::Col {
                    interaction,
                    idx,
                    offset,
                }
            }
            BaseExpr::Const(c) => {
                let val = c.0;
                assert!((val as u64) < P, "non-canonical M31 constant: {val}");
                Node::Const { val }
            }
            BaseExpr::Param(name) => {
                if let Some(node) = self.memo.get(name) {
                    return node.clone();
                }
                let def = self.intermediates.get(name).unwrap_or_else(|| {
                    panic!("unresolved Param {name:?} (not a base intermediate)")
                });
                let node = self.convert(def, depth + 1);
                self.memo.insert(name.clone(), node.clone());
                node
            }
            BaseExpr::Add(a, b) => Node::Add {
                lhs: Box::new(self.convert(a, depth)),
                rhs: Box::new(self.convert(b, depth)),
            },
            BaseExpr::Sub(a, b) => Node::Sub {
                lhs: Box::new(self.convert(a, depth)),
                rhs: Box::new(self.convert(b, depth)),
            },
            BaseExpr::Mul(a, b) => Node::Mul {
                lhs: Box::new(self.convert(a, depth)),
                rhs: Box::new(self.convert(b, depth)),
            },
            BaseExpr::Neg(a) => Node::Neg {
                arg: Box::new(self.convert(a, depth)),
            },
            BaseExpr::Inv(a) => panic!("Inv is unsupported in the SMT model: {a:?}"),
        }
    }
}

fn is_zero_const(expr: &BaseExpr) -> bool {
    matches!(expr, BaseExpr::Const(c) if c.0 == 0)
}

/// Collapse `SecureCol([b, 0, 0, 0])` to `b`; any non-zero residue panics.
fn collapse_secure_col(expr: &ExtExpr) -> &BaseExpr {
    match expr {
        ExtExpr::SecureCol([b, x, y, z]) => {
            for residue in [x, y, z] {
                assert!(
                    is_zero_const(residue),
                    "non-zero residue in SecureCol collapse: {residue:?}"
                );
            }
            b
        }
        other => panic!("expected a collapsed SecureCol([b,0,0,0]), got: {other:?}"),
    }
}

/// Decode a formal logup multiplicity numerator. Exactly three accepted shapes
/// (smt/DESIGN.md §1.2); anything else panics.
fn decode_multiplicity(conv: &mut Converter<'_>, numerator: &ExtExpr) -> (i8, Node) {
    match numerator {
        ExtExpr::SecureCol(_) => (1, conv.convert(collapse_secure_col(numerator), 0)),
        ExtExpr::Neg(inner) => (-1, conv.convert(collapse_secure_col(inner), 0)),
        other => panic!("unexpected multiplicity shape: {other:?}"),
    }
}

/// Strict-match `combine_formal`'s shape:
/// `Sub(fold Add(Mul(Param("{name}_alpha{i}"), SecureCol([v_i,0,0,0]))), Param("{name}_z"))`
/// with the `ExtExpr::zero()` fold seed dropped. Returns `(name, [v_0..v_{n-1}])`.
fn decode_combine_formal(conv: &mut Converter<'_>, def: &ExtExpr) -> (String, Vec<Node>) {
    let ExtExpr::Sub(fold, z) = def else {
        panic!("relation denominator is not Sub(fold, z): {def:?}");
    };
    let ExtExpr::Param(z_name) = &**z else {
        panic!("relation z-term is not a Param: {z:?}");
    };
    let prefix = z_name
        .strip_suffix("_z")
        .unwrap_or_else(|| panic!("z param {z_name:?} lacks the _z suffix"));

    // Peel the left-leaning Add chain down to the zero fold seed.
    let mut terms: Vec<&ExtExpr> = Vec::new();
    let mut cursor: &ExtExpr = fold;
    loop {
        match cursor {
            ExtExpr::Add(acc, term) => {
                terms.push(term);
                cursor = acc;
            }
            ExtExpr::SecureCol(parts) => {
                assert!(
                    parts.iter().all(|p| is_zero_const(p)),
                    "fold seed is not ExtExpr::zero(): {cursor:?}"
                );
                break;
            }
            other => panic!("unexpected node in combine_formal fold chain: {other:?}"),
        }
    }
    terms.reverse();

    let values: Vec<Node> = terms
        .iter()
        .enumerate()
        .map(|(i, term)| {
            let ExtExpr::Mul(alpha, value) = term else {
                panic!("combine_formal term {i} is not Mul(alpha, value): {term:?}");
            };
            let ExtExpr::Param(alpha_name) = &**alpha else {
                panic!("combine_formal term {i} alpha is not a Param: {alpha:?}");
            };
            // Contiguous alpha indices 0..n with an identical name prefix, by construction
            // of the expected name; a mismatch (gap, reorder, foreign prefix) panics here.
            let expected = format!("{prefix}_alpha{i}");
            assert_eq!(
                alpha_name, &expected,
                "alpha param mismatch (expected {expected:?})"
            );
            conv.convert(collapse_secure_col(value), 0)
        })
        .collect();

    (prefix.to_string(), values)
}

/// Declared sizes straight from the relation TYPES via `Relation::get_name/get_size`
/// (never hand-transcribed).
fn relation_sizes() -> HashMap<String, usize> {
    fn entry<R: Relation<BaseExpr, ExtExpr>>(relation: &R) -> (String, usize) {
        (relation.get_name().to_string(), relation.get_size())
    }
    [
        entry(&relations::Sha256BigSigma1::dummy()),
        entry(&relations::Sha256BigSigma0::dummy()),
        entry(&relations::VerifyBitwiseAnd_8::dummy()),
        entry(&relations::VerifyBitwiseXor_8::dummy()),
        entry(&relations::Sha256KTable::dummy()),
        entry(&relations::Sha256Schedule::dummy()),
        entry(&relations::Sha256Round::dummy()),
    ]
    .into_iter()
    .collect()
}

/// The component `Eval` with `dummy()` relations (names come from the TYPE via `get_name`)
/// — mirrors `tests/round_air.rs::make_eval`, copied here so the tests file stays untouched.
fn dummy_eval(bind_ch_maj_limbs: bool) -> Eval {
    Eval {
        claim: Claim { log_size: 6 },
        bind_ch_maj_limbs,
        sha_256_big_sigma_1_lookup_elements: relations::Sha256BigSigma1::dummy(),
        sha_256_big_sigma_0_lookup_elements: relations::Sha256BigSigma0::dummy(),
        verify_bitwise_and_8_lookup_elements: relations::VerifyBitwiseAnd_8::dummy(),
        verify_bitwise_xor_8_lookup_elements: relations::VerifyBitwiseXor_8::dummy(),
        sha_256_k_table_lookup_elements: relations::Sha256KTable::dummy(),
        sha_256_schedule_lookup_elements: relations::Sha256Schedule::dummy(),
        sha_256_round_lookup_elements: relations::Sha256Round::dummy(),
    }
}

/// Run the ACTUAL `Eval::evaluate` under [`SymbolicEval`] and convert everything to the
/// [`Node`] IR. Never call `simplify()` (raw trees only) and never `Zero::is_zero` on expr
/// types (panics at rev 5ea05973).
pub fn extract(bind_ch_maj_limbs: bool) -> Extraction {
    let eval = dummy_eval(bind_ch_maj_limbs);
    let symbolic = eval.evaluate(SymbolicEval(ExprEvaluator::new()));
    let evaluator = symbolic.0;

    let sizes = relation_sizes();
    let mut conv = Converter::new(&evaluator.intermediates);

    let constraints: Vec<ConstraintDump> = evaluator
        .constraints
        .iter()
        .enumerate()
        .map(|(index, c)| ConstraintDump {
            index,
            expr: conv.convert(collapse_secure_col(c), 0),
        })
        .collect();

    let relation_uses: Vec<RelationUseDump> = evaluator
        .logup
        .fracs
        .iter()
        .enumerate()
        .map(|(order, frac)| {
            let (mult_sign, mult) = decode_multiplicity(&mut conv, &frac.numerator);
            let ExtExpr::Param(den_name) = &frac.denominator else {
                panic!(
                    "relation use {order}: denominator is not an intermediate Param: {:?}",
                    frac.denominator
                );
            };
            let def = evaluator.ext_intermediates.get(den_name).unwrap_or_else(|| {
                panic!("relation use {order}: ext intermediate {den_name:?} not found")
            });
            let (relation, values) = decode_combine_formal(&mut conv, def);
            let declared_size = *sizes
                .get(&relation)
                .unwrap_or_else(|| panic!("relation use {order}: unknown relation {relation:?}"));
            assert_eq!(
                values.len(),
                declared_size,
                "relation use {order} ({relation}): decoded {} values, declared size {declared_size}",
                values.len()
            );
            RelationUseDump {
                order,
                relation,
                declared_size,
                mult_sign,
                mult,
                values,
            }
        })
        .collect();

    let dump = VariantDump {
        bind_ch_maj_limbs,
        constraints,
        relation_uses,
    };
    Extraction { evaluator, dump }
}

// ---------------------------------------------------------------------------
// Structural checks (fidelity gate #1; duplicated by the Python loader).
// ---------------------------------------------------------------------------

/// Mechanically derived structure: enabler column (from the two Round entries' shared
/// multiplicity Col) and the binding constraints (set-diff bind_on \ bind_off).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructuralInfo {
    pub enabler_col: usize,
    /// bind_on indices of the four binding constraints.
    pub binding_indices: Vec<usize>,
    /// (limb_col, recombined_col) pairs, i.e. each binding is Sub(Col(limb), Col(recomb)).
    pub binding_pairs: Vec<(usize, usize)>,
}

fn collect_cols(node: &Node, out: &mut BTreeSet<usize>) {
    match node {
        Node::Col { idx, .. } => {
            out.insert(*idx);
        }
        Node::Const { .. } => {}
        Node::Add { lhs, rhs } | Node::Sub { lhs, rhs } | Node::Mul { lhs, rhs } => {
            collect_cols(lhs, out);
            collect_cols(rhs, out);
        }
        Node::Neg { arg } => collect_cols(arg, out),
    }
}

/// Per-relation use counts, sorted by name.
pub fn relation_name_counts(dump: &VariantDump) -> BTreeMap<String, usize> {
    let mut counts = BTreeMap::new();
    for use_ in &dump.relation_uses {
        *counts.entry(use_.relation.clone()).or_insert(0) += 1;
    }
    counts
}

/// All dump-time hard asserts of smt/DESIGN.md §1.3 item 4 (minus the numeric gates, which
/// need the witness — see [`assign_violations`] / [`node_violations`]). Panics on any
/// violation; returns the mechanically derived [`StructuralInfo`].
pub fn structural_checks(bind_on: &VariantDump, bind_off: &VariantDump) -> StructuralInfo {
    assert!(bind_on.bind_ch_maj_limbs && !bind_off.bind_ch_maj_limbs);

    // Constraint counts + in-order subset + structural set-diff.
    assert_eq!(bind_on.constraints.len(), 21, "bind_on constraint count");
    assert_eq!(bind_off.constraints.len(), 17, "bind_off constraint count");
    let mut off_cursor = 0usize;
    let mut binding_indices: Vec<usize> = Vec::new();
    for (i, c) in bind_on.constraints.iter().enumerate() {
        if off_cursor < bind_off.constraints.len()
            && bind_off.constraints[off_cursor].expr == c.expr
        {
            off_cursor += 1;
        } else {
            binding_indices.push(i);
        }
    }
    assert_eq!(
        off_cursor,
        bind_off.constraints.len(),
        "bind_off is not an in-order subsequence of bind_on"
    );
    assert_eq!(binding_indices.len(), 4, "set-diff must be exactly 4 trees");
    // Tripwires (values from R2/tests; the derivation above is authoritative).
    assert_eq!(
        binding_indices,
        vec![5, 6, 13, 14],
        "binding-constraint index tripwire"
    );
    let binding_pairs: Vec<(usize, usize)> = binding_indices
        .iter()
        .map(|&i| match &bind_on.constraints[i].expr {
            Node::Sub { lhs, rhs } => match (lhs.as_ref(), rhs.as_ref()) {
                (Node::Col { idx: limb, .. }, Node::Col { idx: recomb, .. }) => (*limb, *recomb),
                other => panic!("binding constraint {i} is not Sub(Col, Col): {other:?}"),
            },
            other => panic!("binding constraint {i} is not a Sub: {other:?}"),
        })
        .collect();
    assert_eq!(
        binding_pairs,
        vec![(78, 76), (79, 77), (114, 112), (115, 113)],
        "binding-pair tripwire"
    );

    // Relation uses: 38 per variant, node-for-node identical across variants.
    assert_eq!(bind_on.relation_uses.len(), 38, "relation-use count");
    assert_eq!(
        bind_on.relation_uses, bind_off.relation_uses,
        "relation uses must be variant-identical"
    );
    let expected_counts: BTreeMap<String, usize> = [
        ("Sha256Round", 2),
        ("Sha256BigSigma0", 1),
        ("Sha256BigSigma1", 1),
        ("Sha256KTable", 1),
        ("Sha256Schedule", 1),
        ("VerifyBitwiseAnd_8", 20),
        ("VerifyBitwiseXor_8", 12),
    ]
    .into_iter()
    .map(|(k, v)| (k.to_string(), v))
    .collect();
    assert_eq!(
        relation_name_counts(bind_on),
        expected_counts,
        "per-relation use counts"
    );

    // Round entries: exactly one +1 and one -1, both size 50, multiplicities the same bare
    // Col — that col IS the enabler (derivation authoritative; ==124 is a tripwire).
    let round_uses: Vec<&RelationUseDump> = bind_on
        .relation_uses
        .iter()
        .filter(|u| u.relation == "Sha256Round")
        .collect();
    assert_eq!(round_uses.len(), 2);
    let plus: Vec<&&RelationUseDump> = round_uses.iter().filter(|u| u.mult_sign == 1).collect();
    let minus: Vec<&&RelationUseDump> = round_uses.iter().filter(|u| u.mult_sign == -1).collect();
    assert_eq!((plus.len(), minus.len()), (1, 1), "Round entry signs");
    for u in &round_uses {
        assert_eq!(u.values.len(), 50, "Round entry size");
    }
    let enabler_col = match (&plus[0].mult, &minus[0].mult) {
        (
            Node::Col { idx: a, .. },
            Node::Col { idx: b, .. },
        ) if a == b => *a,
        other => panic!("Round multiplicities are not the same bare Col: {other:?}"),
    };
    assert_eq!(enabler_col, 124, "enabler column tripwire");

    // All table-use multiplicities are (+1, Const 1).
    for u in bind_on
        .relation_uses
        .iter()
        .filter(|u| u.relation != "Sha256Round")
    {
        assert_eq!(u.mult_sign, 1, "table use {} sign", u.order);
        assert_eq!(
            u.mult,
            Node::Const { val: 1 },
            "table use {} multiplicity",
            u.order
        );
    }

    // Column coverage: exactly 0..125 across constraints + uses (both variants).
    for variant in [bind_on, bind_off] {
        let mut seen = BTreeSet::new();
        for c in &variant.constraints {
            collect_cols(&c.expr, &mut seen);
        }
        for u in &variant.relation_uses {
            collect_cols(&u.mult, &mut seen);
            for v in &u.values {
                collect_cols(v, &mut seen);
            }
        }
        let expected: BTreeSet<usize> = (0..N_TRACE_COLUMNS).collect();
        assert_eq!(
            seen, expected,
            "column coverage (bind={})",
            variant.bind_ch_maj_limbs
        );
    }

    StructuralInfo {
        enabler_col,
        binding_indices,
        binding_pairs,
    }
}

// ---------------------------------------------------------------------------
// Numeric gates.
// Gate A: `assign()` on the RAW pre-conversion trees (validates inlining fidelity).
// Gate B: a small `Node` interpreter on the CONVERTED trees (validates the converter).
// ---------------------------------------------------------------------------

/// Exact M31 arithmetic over the converted tree: eager mod-p at every node, mirroring the
/// Python `ev()` encoding (operands < 2^31 so u64 products < 2^62 — no overflow).
pub fn eval_node(node: &Node, cols: &[u32]) -> u32 {
    fn go(node: &Node, cols: &[u32]) -> u64 {
        match node {
            Node::Col { idx, .. } => {
                let v = cols[*idx] as u64;
                assert!(v < P, "column {idx} value {v} is not a canonical M31");
                v
            }
            Node::Const { val } => *val as u64,
            Node::Add { lhs, rhs } => (go(lhs, cols) + go(rhs, cols)) % P,
            Node::Sub { lhs, rhs } => (go(lhs, cols) + P - go(rhs, cols)) % P,
            Node::Mul { lhs, rhs } => (go(lhs, cols) * go(rhs, cols)) % P,
            Node::Neg { arg } => (P - go(arg, cols)) % P,
        }
    }
    go(node, cols) as u32
}

/// Gate B: indices of converted constraint trees that do NOT evaluate to 0 at this row.
pub fn node_violations(dump: &VariantDump, cols: &[u32]) -> Vec<usize> {
    dump.constraints
        .iter()
        .filter(|c| eval_node(&c.expr, cols) != 0)
        .map(|c| c.index)
        .collect()
}

/// Build an `ExprVarAssignment` for one row: the 125 columns plus every BASE intermediate
/// resolved numerically by name in `intermediateN` order (carry_high references carry_low).
/// Ext intermediates (the formal relation denominators) are intentionally left unassigned —
/// no base constraint references them.
pub fn resolve_assignment(
    evaluator: &ExprEvaluator,
    cols: &[u32],
) -> (
    HashMap<(usize, usize, isize), BaseField>,
    HashMap<String, BaseField>,
    HashMap<String, SecureField>,
) {
    let columns: HashMap<(usize, usize, isize), BaseField> = cols
        .iter()
        .enumerate()
        .map(|(idx, &v)| ((1usize, idx, 0isize), M31::from(v)))
        .collect();
    let mut assignment = (columns, HashMap::new(), HashMap::new());
    let total = evaluator.intermediates.len() + evaluator.ext_intermediates.len();
    for k in 0..total {
        let name = format!("intermediate{k}");
        if let Some(expr) = evaluator.intermediates.get(&name) {
            let value = expr.assign(&assignment);
            assignment.1.insert(name, value);
        } else if evaluator.ext_intermediates.contains_key(&name) {
            // Formal relation denominator — carries alpha/z params, unused by constraints.
        } else {
            panic!("intermediate {name} found in neither intermediates map");
        }
    }
    assignment
}

/// Gate A: indices of RAW constraint trees whose `assign()` is non-zero at this row.
pub fn assign_violations(evaluator: &ExprEvaluator, cols: &[u32]) -> Vec<usize> {
    let assignment = resolve_assignment(evaluator, cols);
    evaluator
        .constraints
        .iter()
        .enumerate()
        .filter(|(_, c)| c.assign(&assignment) != SecureField::zero())
        .map(|(i, _)| i)
        .collect()
}

/// The base-intermediate (TripleSum32 carry) values at one row, for the carry-class
/// coverage check ({0,1,2} must all be exercised by the honest trace).
pub fn carry_values(evaluator: &ExprEvaluator, cols: &[u32]) -> Vec<u32> {
    let assignment = resolve_assignment(evaluator, cols);
    let mut values: Vec<u32> = assignment.1.values().map(|v| v.0).collect();
    values.sort_unstable();
    values
}

/// Both numeric gates on one row of BOTH variants; panics unless the violated-index sets
/// (gate A on raw trees, gate B on converted trees) equal `expected_bind_on` /
/// `expected_bind_off` exactly.
pub fn check_row(
    bind_on: &Extraction,
    bind_off: &Extraction,
    cols: &[u32],
    expected_bind_on: &[usize],
    expected_bind_off: &[usize],
    label: &str,
) {
    assert_eq!(cols.len(), N_TRACE_COLUMNS, "{label}: row width");
    assert_eq!(
        assign_violations(&bind_on.evaluator, cols),
        expected_bind_on,
        "{label}: gate A (raw assign), bind_on"
    );
    assert_eq!(
        assign_violations(&bind_off.evaluator, cols),
        expected_bind_off,
        "{label}: gate A (raw assign), bind_off"
    );
    assert_eq!(
        node_violations(&bind_on.dump, cols),
        expected_bind_on,
        "{label}: gate B (Node interpreter), bind_on"
    );
    assert_eq!(
        node_violations(&bind_off.dump, cols),
        expected_bind_off,
        "{label}: gate B (Node interpreter), bind_off"
    );
}
