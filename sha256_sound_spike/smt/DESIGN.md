# SMT Soundness Layer — Final Design (judged synthesis)

**Role**: authoritative implementation spec for the SMT layer of `sha256_sound_spike`
(spike-only test infrastructure — NOT wired into any production path).
**Provenance**: synthesized 2026-07-03 from three independent designs (A: minimal-trusted-base,
B: theorem-strength, C: maintainability) plus recon reports R1 (stwo constraint-framework API
at pinned rev `5ea05973`), R2 (component semantic map, read-only), R3 (environment/conventions).
Governing brief: orchestrator BRIEF (per-row functional-soundness theorem, mandated architecture).
Master doc: `../SHA256-SOUNDNESS-FIX.md` (PR #1425 context).
**Honest scope**: this layer proves ONE per-row theorem about the base constraints + table
semantics of `src/components/sha_256_round.rs`. It deliberately does NOT model logup cumsum,
FRI, Fiat-Shamir, bus multiset counting, padding rows, builtin injection/extraction, or the
table components' own AIRs — see §8. Every deviation of this spec from a source design is an
explicit resolved conflict, recorded in §0.
**Disclosure guardrail (verbatim intent, do not soften)**: PR #1425 is open, unmerged, and
undisclosed. Nothing on this branch — including everything under `smt/` — may be pushed to a
public remote until the fix is disclosed through the process in `SHA256-SOUNDNESS-FIX.md`.

---

## 0. Conflict resolutions (which design won, and why)

| # | Question | Decision | Sided with | Why |
|---|---|---|---|---|
| 1 | Extraction mechanism | Pass-through newtype over stwo `ExprEvaluator` | A=B=C (unanimous) | R1 decisive: `RelationEntry` fields private, `ExprEvaluator` records names + pre-randomness values as formal Params; a custom evaluator loses names irrecoverably (`dummy()` z-collision) |
| 2 | Honest rows dumped | **All 64 rows** (t=0..63) of the "abc" trace | A | Costs nothing (64×125 u32s); exercises every K[t], all carry classes {0,1,2} (R2: carry 2 at rows 1,21,23,25,26,28), forge locus row 10, and full-trace bus chaining. B/C's 4-row set kept only as labels for the z3-pinned subset |
| 3 | Forged rows in JSON | **Yes** — ch-forged and maj-forged row 10 | B (extended to maj) | A Rust-constructed SAT witness corroborates M.bind_off independently of z3's model search; strongest surviving anti-vacuity mitigation |
| 4 | DF lemmas assumed in the main FS query | **No** — FS asserts constraints+tables and lets z3 re-derive ranges; DF queries are standalone discharge documentation | C (and B) over A | Fewer assumptions in the main proof; no taint path from a mis-stated lemma; A's "goal well-definedness" worry doesn't apply because tables (which carry the ranges) are asserted in every model FS considers. A's "tables-only DF" claim is recorded as a note, not relied on (brief group (a) says "constraints + table semantics") |
| 5 | Positional checks vs zero-column-coupling | **Tuple-position syntactic ledger**: OUT[k] ≡ IN[j] node identities where FIPS says pass-through; bare-Col requirements for I_out/DF targets | Synthesis of B+C | B's machine-checked composition ledger is load-bearing (the induction discharge IS a positional claim); expressing it as OUT-vs-IN node equality (not raw column numbers) gives C's regeneration robustness. Raw column indices (120..123, enabler=124) appear only as dump-time tripwire asserts |
| 6 | Binding-constraint identification | Mechanical set-diff bind_on∖bind_off; assert count=4, shape `Sub(Col,Col)`; current indices {5,6,13,14} asserted as dump-time tripwire | C (mechanism) + B (tripwire) | Survives regeneration (diff re-derives), fails loudly on drift; forgery-model printing uses the derived pairs, never hard-coded (78,76)/(79,77)/(114,112)/(115,113) |
| 7 | Expected-verdict storage | `expectations.json` keyed by query id with justification strings; drop-sweep entries generated from a blanket rule; reclassification only via constraint **fingerprint** (SHA-256 of canonical JSON) allowlist entry with written justification | B (explicit file) + C (blanket rule + fingerprint, fail-safe on drift) | Per-index tables rot on regeneration; a stale fingerprint stops matching and re-fails — the safe direction |
| 8 | Spec/table sensitivity canaries | **B's full set** (6 spec + 3 table mutations), superset of A's 3 | B | All survive scrutiny; endian-swap canary kills the universal-fatal lo/hi bug class (R2); `and_norange` proves DF genuinely rests on table ranges (brief's Split16 fact) |
| 9 | FIPS spec: single-source vs duplicated | **Single-source `fips.py`** generic over int/z3-BV32; NO second hand-written Python spec | B/C over A | The independent oracle A wanted already exists: honest rows are produced by the Rust reference implementation (`reference.rs`, KAT-tested). A fips.py transcription bug fails the honest-row goal check against Rust-produced data. A duplicate Python spec adds trusted lines without adding an independent ground truth |
| 10 | SAT-model replay | **Gating**: every SAT model replayed through the pure-int evaluator against that query's exact (mutated) system | A+B | Kills "SAT because the encoding is slop"; C lacked it |
| 11 | Assumption-necessity sweep | **Keep** — drop each of the 8 FS assumptions individually, expect SAT | B | Proves the assumed set minimal and observed; surprise UNSAT = trusted-base-shrinking finding, reported via the §6 policy |
| 12 | Rust-side dump validation | **Both** `assign()` on raw `ExtExpr`s AND a ~15-line `Node` interpreter on converted trees, all 64 rows ≡ 0 | B+C | The Node interpreter validates the converter itself (the audit-critical code); `assign()` validates that intermediate inlining preserved semantics. Four independent evaluators total (Rust raw, Rust converted, Python int, z3) |
| 13 | Bin name / file split | `src/bin/dump_smt.rs`; Python split `check.py`/`encoding.py`/`fips.py`/`mutations.py` | A+B naming, B layout | Single-file check.py (C) mixes trusted axioms with orchestration; the split keeps the ~150 trusted lines auditable in one sitting |
| 14 | Enabler column | Derived from the two Round entries' shared multiplicity Col; dump-time assert it equals 124 (B verified: all masks read up-front, sha_256_round.rs:117-246) | A/C mechanism + B fact | Derivation is authoritative; the assert is a regeneration tripwire |

Everything below is the merged, binding spec.

---

## 1. Extraction (Rust)

### 1.1 `src/symbolic.rs` (NEW; `pub mod symbolic;` added to `src/lib.rs` — the only lib.rs edit)

File header per R3 conventions (role + scope tag, provenance = stwo rev `5ea05973` `expr`
module + PR #1425, honest-scope paragraph: finalize_* are deliberate no-ops because logup
cumsum soundness is an assumed stwo-core property, see README §Not-covered).

```rust
pub struct SymbolicEval(pub ExprEvaluator);   // ExprEvaluator::new() — zero-arg (evaluator.rs:80; re-verify at impl)

impl EvalAtRow for SymbolicEval {
    type F = BaseExpr;
    type EF = ExtExpr;
    fn next_interaction_mask<const N: usize>(&mut self, i: usize, o: [isize; N]) -> [BaseExpr; N]
        { self.0.next_interaction_mask(i, o) }
    fn add_constraint<G>(&mut self, c: G) where ExtExpr: Mul<G, Output = ExtExpr> + From<G>
        { self.0.add_constraint(c) }
    fn combine_ef(v: [BaseExpr; 4]) -> ExtExpr { ExprEvaluator::combine_ef(v) }
    fn add_intermediate(&mut self, v: BaseExpr) -> BaseExpr { self.0.add_intermediate(v) }
    fn add_extension_intermediate(&mut self, v: ExtExpr) -> ExtExpr { self.0.add_extension_intermediate(v) }
    // Moves the entry unread (fields private, R1 §2) into ExprEvaluator's override, which
    // records (relation name, multiplicity, pre-combination values) via combine_formal.
    fn add_to_relation<R: Relation<BaseExpr, ExtExpr>>(&mut self, e: RelationEntry<'_, BaseExpr, ExtExpr, R>)
        { self.0.add_to_relation(e) }
    // Cumsum EXCLUDED from the model (brief). Overriding all three prevents the
    // unimplemented!() defaults firing on finalize_logup_in_pairs (sha_256_round.rs:859)
    // and prevents the 4 trailing cumsum constraints / cur_var_index bleed (R1 trap #2).
    fn finalize_logup_batched(&mut self, _b: /* exact type from lib.rs:154-167 at impl time */) {}
    fn finalize_logup(&mut self) {}
    fn finalize_logup_in_pairs(&mut self) {}
}
```

`write_logup_frac` keeps its default: unreachable (the inner override never routes through the
wrapper). Never call `Zero::is_zero` on expr types (panics, R1 trap); never `simplify()` — dump
raw trees.

### 1.2 IR + converter (same file)

```rust
#[derive(Serialize, PartialEq, Eq, Clone)]
#[serde(tag = "op", rename_all = "snake_case")]
pub enum Node {
    Col { interaction: usize, idx: usize, offset: isize },
    Const { val: u32 },                              // canonical M31 in [0, p)
    Add { lhs: Box<Node>, rhs: Box<Node> },
    Sub { lhs: Box<Node>, rhs: Box<Node> },
    Mul { lhs: Box<Node>, rhs: Box<Node> },
    Neg { arg: Box<Node> },
}
pub struct RelationUse { pub order: usize, pub relation: String, pub declared_size: usize,
                         pub mult_sign: i8, pub mult: Node, pub values: Vec<Node> }
pub fn extract(bind_ch_maj_limbs: bool) -> VariantDump  // runs evaluate, converts, self-checks
```

Conversion rules — **every violation panics with `{:?}` of the offending subtree; no
permissive fallback exists to audit**:
- `BaseExpr::Col(c)`: equality-search `(0..=2)×(0..512)×(-2..=2)` via public
  `ColumnExpr::from((i, idx, off))` + `Eq` (fields private, R1 §5). Then **assert**
  interaction==1, offset==0, idx<125 — a preprocessed/shifted read invalidates the
  single-row model; hard-error with the found coordinates.
- `Param("intermediateN")` in a base tree → recursively inline its definition from
  `intermediates` (memoized, depth-guarded — carry_high references carry_low). Base carries
  and relation denominators SHARE the N-counter: resolve by name only, never by order (R1).
- `Inv`, unresolved `Param`, non-zero residue in a `SecureCol([b, x, y, z])` collapse → panic.
- Constraints: collapse each stored `ExtExpr` to its base component (`SecureCol([b,0,0,0]) → b`).
- Relation decode, per `logup.fracs[k]` in order: denominator `Param` → `ext_intermediates`
  → strict-match `combine_formal` shape
  `Sub(fold Add(Mul(Param("{name}_alpha{i}"), SecureCol([v_i,0,0,0]))), Param("{name}_z"))`
  (drop the `ExtExpr::zero()` fold seed); assert alpha indices contiguous `0..n`, all name
  prefixes identical → `(name, [v_0..v_{n-1}])`. Multiplicity numerator:
  `SecureCol([Const(1),0,0,0])` → `(+1, Const 1)`; `SecureCol([b,0,0,0])` → `(+1, b)`;
  `Neg(SecureCol([b,0,0,0]))` → `(−1, b)`; anything else panics.

Relations constructed via each type's `dummy()` (names come from the TYPE via `get_name`,
R1 §3). `Eval` built mirroring `tests/round_air.rs::make_eval` (l.38-50) — copied into the
bin, tests file untouched.

### 1.3 `src/bin/dump_smt.rs` (NEW)

Deterministic: `dummy()` relations; fixed `CompressionInput { h_in: reference::IV, block }`
with the padded-"abc" block constant copied from the test; stable JSON key order.

1. `extract(true)`, `extract(false)`.
2. `build_round_trace(&[input])` → dump **all 64 rows**: `cols[c][row].0` for c in 0..125.
   Honest columns are variant-independent (bind is an `Eval` field, not a witness difference;
   the honest witness already writes col78=col76 etc., witness.rs l.197-198, 247-248).
3. Forged rows: (a) `witness::forge_ch(trace, 10, honest_ch ^ 0xdeadbeef)` → dump row 10,
   `expected_bind_on_violations: [5,6]`, `expected_bind_off_violations: []`;
   (b) `build_round_trace_forge(&[input], 0, 10, Forge::Maj(honest_maj ^ 0xdeadbeef))` →
   dump row 10, expected bind_on violations `[13,14]`. (0xdeadbeef flips both 16-bit halves,
   so both bindings of the pair fire — matches the tests' exact-index assertions.)
4. **Dump-time hard asserts (fidelity gate #1; duplicated by the Python loader)**:
   - constraint counts: bind_on == 21, bind_off == 17; bind_off ⊂ bind_on in order; the
     structural set-diff is exactly 4 trees, each `Sub(Col{x}, Col{y})`; assert the diff's
     bind_on indices are `{5,6,13,14}` and pairs are (78,76),(79,77),(114,112),(115,113)
     (tripwire: values from R2/tests, derivation is authoritative);
   - relation uses: 38 per variant, node-for-node identical across variants; per-name counts
     exactly `{Sha256Round:2, Sha256BigSigma0:1, Sha256BigSigma1:1, Sha256KTable:1,
     Sha256Schedule:1, VerifyBitwiseAnd_8:20, VerifyBitwiseXor_8:12}`;
   - Round entries: exactly one sign +1 and one sign −1, both size 50, multiplicities the
     same bare `Col` → that col is **enabler**; assert it == 124 (tripwire); all table-use
     multiplicities are `(+1, Const 1)`;
   - column coverage: the set of Col idx seen across constraints+uses == exactly `0..125`;
   - **numeric gate A** — `BaseExpr/ExtExpr::assign` (via `ExprVarAssignment`) evaluates every
     RAW pre-conversion constraint of both variants at all 64 honest rows ≡ 0 mod p
     (intermediates resolved numerically by name in N-order first);
   - **numeric gate B** — a ~15-line `Node` interpreter evaluates every CONVERTED constraint
     tree at all 64 honest rows ≡ 0 mod p (validates the converter itself);
   - forged rows: bind_off trees all ≡ 0; bind_on violated at exactly the expected index sets.
5. Write `smt/out/air.json` (path from argv). Any assert failure = panic = nonzero exit.

### 1.4 Allowed existing-file edits

`src/lib.rs`: `pub mod symbolic;` only. `Cargo.toml`: add `serde_json = "1.0"`. Nothing else.

---

## 2. JSON schema — `smt/out/air.json` (single artifact)

Node grammar (exact; loader rejects unknown `op` values or unknown keys):
```
{"op":"col","interaction":1,"idx":<0..124>,"offset":0}
{"op":"const","val":<0..p-1>}
{"op":"add"|"sub"|"mul","lhs":<NODE>,"rhs":<NODE>}
{"op":"neg","arg":<NODE>}
```

Top level:
```json
{
  "schema_version": 1,
  "stwo_rev": "5ea05973",
  "p": 2147483647,
  "n_columns": 125,
  "enabler_col": 124,
  "k_table": [1116352408, "... 64 u32s dumped from reference::K ..."],
  "trace_block": "abc",
  "variants": {
    "bind_on": {
      "bind_ch_maj_limbs": true,
      "constraints": [ {"index": 0, "expr": NODE}, "... 21 ..." ],
      "relation_uses": [
        {"order": 0, "relation": "Sha256BigSigma1", "declared_size": 4,
         "mult_sign": 1, "mult": NODE, "values": [NODE, "..."]},
        "... 38, in add_to_relation order ..."
      ]
    },
    "bind_off": { "bind_ch_maj_limbs": false, "constraints": ["... 17 ..."], "relation_uses": ["... 38 ..."] }
  },
  "honest_rows":  [ {"row": 0, "cols": ["... 125 u32s ..."]}, "... 64 entries, t = row ..." ],
  "forged_rows": [
    {"label": "row10_forged_ch",  "row": 10, "forge": "ch",  "forge_xor_mask": 3735928559,
     "cols": ["...125..."], "expected_bind_off_violations": [], "expected_bind_on_violations": [5, 6]},
    {"label": "row10_forged_maj", "row": 10, "forge": "maj", "forge_xor_mask": 3735928559,
     "cols": ["...125..."], "expected_bind_off_violations": [], "expected_bind_on_violations": [13, 14]}
  ]
}
```

Column semantic labels are deliberately NOT in the JSON: `witness.rs`'s header is the
authoritative 125-entry map (cited by README); duplicating it invites drift. The theorem's
I/O tuples come from the decoded Round entries, never a hand-written column map.
`enabler_col` is derived (Round multiplicities), echoed for the loader's cross-assert.

---

## 3. SMT encoding (`smt/encoding.py`, `smt/fips.py`)

### 3.1 Variables and field layer

- One `BitVec(f"c{i}", 64)` per column; loader hard-errors on any Col triple ≠ `(1, i<125, 0)`.
- `RANGE = And(*(ULT(c[i], p) for i in range(125)))` — asserted in every query (assumption A4).
- `ENABLER = (c[enabler_col] == 1)` — asserted in every query (assumption A1).
- `ev(node)` — memoized recursive compiler, **eager mod-p at every node** (invariant: every
  compiled term < p by construction; NO small-range shortcut anywhere in this layer):
  `add → URem(a+b, P)` (operands < 2^31 ⇒ sum < 2^32, no BV64 wrap);
  `sub → URem(a + P − b, P)`; `mul → URem(a*b, P)` (product < 2^62); `neg → URem(P − a, P)`;
  `const → BitVecVal(v, 64)` with loader assert `v < p`. Constraint predicate: `ev(expr) == 0`.
- Pure-int twin: the same tree walk over Python ints mod p (used for honest/forged numeric
  checks and SAT-model replay). Same module, different leaf/op bindings — the operations
  differ (int vs BV) so a compiler bug does not automatically mirror.

### 3.2 Single-source FIPS spec (`fips.py` — trusted, ~100 lines, audited in one sitting)

One implementation of rotr/shr/Σ0/Σ1/σ0/σ1/Ch/Maj/K/round-step against a small `BV32` wrapper
(mod-2^32 `+ & | ^`, logical shift via `LShR` for z3 terms, plain ops for ints). Instantiated
over ints = the numeric reference (KAT-validated at startup: rotation vectors, K[0]=0x428a2f98,
K[63]=0xc67178f2, full-message "abc" digest via the round loop); instantiated over z3 BV32
terms = the goal builder. The KATs therefore validate the very functions inside the solver
goal. Loader asserts `k_table` (from reference.rs) == fips.py's own hard-coded FIPS 180-4
§4.2.2 list — two independent sources or the run dies.

### 3.3 Table-semantics axioms (trusted base T1–T6; dispatch on relation name against a frozen
allowlist of exactly 7; unknown name = hard error)

Applied to `ev()` of the **value expressions** (some operands are inline exprs like
`limb − 256·ms8`, not bare columns — essential for the split-based forcings).
`word32(lo, hi) = Extract(31, 0, lo + hi*65536)` — legal only where the same predicate asserts
both limbs < 2^16 (sum < 2^32 in BV64, extract exact).

- **T1** `VerifyBitwiseAnd_8(a,b,c)`: `ULT(a,256) ∧ ULT(b,256) ∧ c == a & b` (forces c < 256).
- **T2** `VerifyBitwiseXor_8(a,b,c)`: same with `^`.
- **T3** `Sha256BigSigma0(il,ih,ol,oh)`: all four `< 2^16` ∧ `word32(ol,oh) == Σ0(word32(il,ih))`,
  Σ0 = rotr2^rotr13^rotr22 (BV32 `RotateRight`; reference.rs:30-32, FIPS §4.1.2).
- **T4** `Sha256BigSigma1`: rotations 6/11/25 (reference.rs:34-36).
- **T5** `Sha256KTable(t,kl,kh)`: `ULT(t,64) ∧ kl,kh < 2^16 ∧ Or_{i<64}(t==i ∧ word32(kl,kh)==K[i])`.
- **T6** `Sha256Schedule(l_0..l_31, ol, oh)`: all 34 limbs `< 2^16`; `w_j = word32(l_{2j}, l_{2j+1})`
  (lo at even tuple index — R2-verified); `word32(ol,oh) == σ1(w14) + w9 + σ0(w1) + w0` in BV32;
  σ0 = rotr7^rotr18^lshr3, σ1 = rotr17^rotr19^lshr10 (reference.rs:38-44, FIPS §6.2.2).
- **T7** `Sha256Round`: NOT a predicate. Structural only: the +1-sign entry's 50 values = `IN`,
  the −1 entry's = `OUT` (hard error unless exactly one of each sign, both size 50, sharing the
  enabler multiplicity col). Bus equality/counting = trusted stwo-core (README §Not-covered).

Axiom instances enter solvers via `assert_and_track(pred, f"T{k}.use{order}")`; UNSAT verdicts
log `unsat_core()` into `smt/out/verdicts.json` (audit output, non-gating).

### 3.4 Goal `G` (built by fips.py over the tuple exprs; references only IN/OUT tuple values,
never non-tuple witness columns — K comes from the If-chain over fips.py constants, fully
independent of witness cols 80/81)

Words: `A..H = word32(IN[2],IN[3]) .. word32(IN[16],IN[17])`, `W_j = word32(IN[18+2j], IN[19+2j])`,
`t = ev(IN[1])`, `K_spec = 64-way If over t`. `T1 = H + Σ1(E) + Ch(E,F,G) + K_spec + W_0`,
`T2 = Σ0(A) + Maj(A,B,C)` (BV32, native wrap). Conjuncts (R2-verified tuple map):

```
ev(OUT[0]) == ev(IN[0])
ev(OUT[1]) == URem(ev(IN[1]) + 1, P)
word32(OUT[2],OUT[3])   == T1 + T2                    (new_a)
ev(OUT[k]) == ev(IN[k-2])   for k in 4..=9            (b,c,d shift)
word32(OUT[10],OUT[11]) == D + T1                     (new_e)
ev(OUT[k]) == ev(IN[k-2])   for k in 12..=17          (f,g,h shift)
ev(OUT[k]) == ev(IN[k+2])   for k in 18..=47          (window advance)
word32(OUT[48],OUT[49]) == σ1(W_14) + W_9 + σ0(W_1) + W_0
```

`word32` on OUT[2,3]/OUT[10,11] is legal because I_out (A3) is asserted in the same query;
on OUT[48,49] because T6 asserts their ranges; on IN limbs because tables assert theirs.
Word-level equality + 16-bit ranges ⇒ limb-level (unique decomposition) — stated once in README.
Conjuncts that are construction-trivial (OUT[1] is syntactically IN[1]+1) are kept: the theorem
is about what the component claims on the bus; the ledger (§3.6) notes the triviality.

### 3.5 Assumption register (code IDs == README IDs; the numbered trusted-assumption list)

| ID | Statement | Status / discharge story |
|---|---|---|
| A1 | `enabler == 1` | Theorem hypothesis. Enabler=0 rows push/pull nothing (multiplicity 0) — out of scope; the booleanity constraint (identified structurally, §5) makes {0,1} exhaustive |
| A2 | I_res: `IN[8],IN[9],IN[16],IN[17] < 2^16` (d, h limbs) | ASSUMED, discharged by induction: prior row's OUT[8,9] ≡ IN[6,7] (old c) and OUT[16,17] ≡ IN[14,15] (old g) — node identities machine-checked (§3.6) — and those positions are DF-forced in-row; equated across rows by the Round bus (T7, trusted). Base case = builtin injection, EXTERNAL |
| A3 | I_out: `OUT[2],OUT[3],OUT[10],OUT[11] < 2^16` (new_a, new_e limbs; bare Cols, asserted) | ASSUMED, discharged by the NEXT consumer: they become its IN[2,3]/IN[10,11], forced by its own Σ0/Σ1 membership (DF), equated by the bus. **Final row: NOT discharged by this component — the final read must range-check. EXTERNAL, force-printed in every report** |
| A4 | all 125 cols < p | Trace is typed M31 — encoding-domain condition |
| A5 | stwo-core: logup soundness, bus multiset counting, FRI, Fiat-Shamir | EXTERNAL, force-printed |
| A6 | Table axioms T1–T6 match the real table/schedule components | Trusted base (~150 lines). Validated: numerically against all 38 uses × 64 honest rows (a too-strong or wrong axiom the real witness violates fails immediately); K two-source check; V.table/V.spec sensitivity canaries prove the proof depends on the exact semantics. The table components' OWN AIR correctness stays EXTERNAL |
| A7 | Extraction fidelity (JSON == real AIR) | Discharged by four-evaluator agreement (Rust assign on raw trees, Rust Node interpreter on converted trees, Python int re-eval, z3 pinned-row SAT) + count/diff/structural asserts run twice (dump + load) + forged-row exact-violation-index checks |
| A8 | fips.py transcription correctness | Discharged by startup KATs + agreement with Rust-generated honest rows (independent implementation, reference.rs) on all 64 rows |

### 3.6 Machine-checked composition ledger (structural, no z3; runs every time, both variants)

Node-identity checks on the decoded tuples — tuple-position form, column-number-free, so AIR
regeneration cannot silently move a wire (mismatch = hard failure):
`OUT[0] ≡ IN[0]`; `OUT[1] ≡ Add(IN[1], Const 1)`; `OUT[4..9] ≡ IN[2..7]`;
`OUT[12..17] ≡ IN[10..15]`; `OUT[18..47] ≡ IN[20..49]`; `OUT[2],OUT[3],OUT[10],OUT[11],
OUT[48],OUT[49]` are bare, pairwise-distinct Cols not occurring in IN; every DF-target
position (§4a) is a bare Col. Each A2/A3 ledger row names its syntactic identity AND its
DF query id — both re-verified from the fresh JSON each run.

---

## 4. Solver obligations

Mechanics for every query: fresh `Solver()`, `set(timeout=60000, random_seed=0)`;
verdict ∈ {sat, unsat} only — `unknown`/timeout is a hard failure ("investigate the encoding,
never raise the limit"). Assumptions/axioms via `assert_and_track`; verdicts + cores + ms →
`smt/out/verdicts.json`. Every SAT model is replayed through the pure-int evaluator against
that query's exact (possibly mutated) constraint/table/goal set — replay failure = hard error.

**(a) Derived forcing — 47 queries.** Assert `RANGE ∧ ENABLER ∧ constraints(bind_on) ∧ all
table axioms ∧ Not(bound)` → expect UNSAT.
Targets: `DF.in1` (< 64); `DF.in{k}` (< 2^16) for k ∈ {2..7, 10..15, 18..49} (44 queries);
`DF.out48`, `DF.out49` (< 2^16, schedule outputs). No induction assumptions in group (a).
(Note from design A, non-binding: these likely hold from table axioms alone — b,c,f,g via
`ms8 < 256 ∧ (limb − 256·ms8 mod p) < 256 ⇒ limb < 2^16` on the operand exprs; implementers
MAY additionally log a tables-only variant as documentation, but the gated form is the above.)

**(b) Functional soundness — `FS.main`, a lemma chain (NOT one monolithic query).** The
monolithic query `RANGE ∧ ENABLER ∧ constraints(bind_on) ∧ tables ∧ I_res ∧ I_out ∧ Not(G)`
→ UNSAT is **intractable for z3 in every faithful encoding** (BV cannot root-find the carry
cubics mod p; NIA cannot combine `mod p` with the bitwise AND/XOR/rotate — see §5). It is
therefore discharged by a chain of small lemmas, and **`FS.main` is a synthetic aggregate:
PASS iff every `FS.L_*` is UNSAT**. The chain + the structural ledger cover **all 47
word-conjuncts** of `G` (50 tuple positions; the three paired-limb words collapse 6 positions):

| lemma | theory | establishes |
|---|---|---|
| `FS.L_ch` | pure BV | `word(ch_out) = Ch(E,F,G)` |
| `FS.L_maj` | pure BV | `word(maj_out) = Maj(A,B,C)` |
| `FS.L_new_e` | **pure QF_LIA** | yielded `word(OUT[10,11]) = m32(D + m32(H+Σ1+Ch+K+W0))` via the new_e-path TripleSum carry relations |
| `FS.L_new_a` | **pure QF_LIA** | yielded `word(OUT[2,3]) = m32(T1 + m32(Σ0+Maj))` via the new_a-path carry relations |
| `FS.L_sched` | pure BV | `word(OUT[48,49]) = σ1(W14)+W9+σ0(W1)+W0` (schedule output) |

The copy/increment tuple (`OUT[0]≡IN[0]`, `OUT[1]≡Add(IN[1],1)`, the shifts) is discharged by
the §3.6 ledger **node identity** (same column ⇒ `ev` equal for every assignment; increment via
A9). `SAN.goal_coverage` asserts no `G` conjunct is left unclassified — a regenerated AIR that
adds a conjunct fails loudly.

*Faithful arith lemmas (no intermediate-range crutch).* `FS.L_new_e`/`FS.L_new_a` reason at the
**limb level with the intra-row TripleSum result limbs FREE in [0,p)**. VerifyTripleSum32 does
not range-check its result limbs, and `RANGE ∧ constraints ∧ tables ∧ A2 ∧ A3` provably does
NOT force them < 2^16; assuming it (an earlier design) proved a strictly-weaker statement. Each
TripleSum's two carry cubics are lifted **mechanically** from the extracted trees (`exact_int_ev`
of the affine `inner` polynomials; the high limb's `carry_low_tmp` is replaced by the explicit
low-carry var) into `SL − rl − cl·2^16 == ql·p` / `SH + cl − rh − ch·2^16 == qh·p` with
`cl,ch ∈ {0,1,2}` and bounded wrap quotients `ql,qh ∈ [−QMAX,QMAX]` — pure linear integer
arithmetic (no `mod p` operator ⇒ tractable). QMAX=8 ⊃ the provable `{−1,0,1,2}` range; a wider
QMAX only ever *weakens* the antecedent (a loud SAT), never silently strengthens it.

**(b0) Lemma-chain non-vacuity — 4 queries.** `SAN.fs_vacuity.{bitwise,new_e,new_a,sched}`:
each `FS.L_*` antecedent must be SAT **on its own** → so a contradictory hypothesis cannot make
a lemma *vacuously* UNSAT and pass silently. (The `SAN.assume_sat/goal_sat/no_constraints`
checks cover only the monolithic `build_fs_named` antecedent, which is disjoint from these.)

**(b2) Assumption necessity — 8 queries (on the MONOLITHIC harness).** `N.res.{8,9,16,17}`,
`N.out.{2,3,10,11}`: rerun the monolithic `build_fs_named` query with one assumption dropped →
expect SAT. NOTE (finding, documented not hidden): the drop-sweep / necessity / canary matrix
below perturbs the **monolithic** `build_fs_named` query (a necessity & spec-sensitivity
harness), NOT the lemma-chain `FS.main` that produces the soundness verdict. It shows each
constraint/assumption/spec-conjunct is load-bearing for the monolithic Not(G); the lemma
chain's own safety net is `SAN.fs_vacuity.*` plus each lemma's self-validating UNSAT (a
mislabeled column/cubic yields SAT). A surprise UNSAT in the drop sweep is a
trusted-base-shrinking finding: reported, fails the run until reclassified (§6 policy).

**(c) Sanity / non-vacuity — runs FIRST; no UNSAT is trusted before this whole group passes.**
- `SAN.load`: loader re-asserts every §1.3 structural gate + schema strictness + ledger (§3.6)
  + K two-source + enabler cross-assert.
- `SAN.fips_kat`: pure-int KATs (§3.2).
- `SAN.honest_numeric`: all 64 rows, pure ints: every bind_on constraint tree ≡ 0 (bind_off as
  the asserted subset); every relation use's table axiom holds; enabler col == 1; FIPS
  next-state of the row's IN tuple == its OUT tuple; consecutive rows chain (row r's OUT tuple
  values == row r+1's IN tuple values, r = 0..62).
- `SAN.forged_numeric` ×2: forged rows satisfy bind_off + tables, violate bind_on at exactly
  the expected index sets, violate `G`.
- `SAN.honest_z3.{0,1,10,25}`: all 125 vars pinned to the row's values ∧ constraints ∧ tables
  ∧ I_res ∧ I_out ∧ `G` → SAT (validates the z3 encoding, not just the int twin; rows chosen
  per R2 to cover carries {0,1,2} + forge locus).
- `SAN.forged_z3.{ch,maj}`: vars pinned to the forged row ∧ bind_off ∧ tables ∧ `Not(G)` → SAT
  (Rust-constructed corroboration of M.bind_off, independent of z3's model search).
- `SAN.assume_sat`: `RANGE ∧ ENABLER ∧ tables ∧ I_res ∧ I_out` (no constraints, no goal) → SAT.
- `SAN.goal_sat`: FS.main's antecedent ∧ `G` (un-negated) → SAT.
- `SAN.no_constraints`: `RANGE ∧ ENABLER ∧ tables ∧ I_res ∧ I_out ∧ Not(G)` (base constraints
  REMOVED) → SAT — proves the constraints are load-bearing and `G` is not a tautology of the
  trusted base.

---

## 5. Mutation matrix (each row = one fresh solver run; SAT models always replayed + decoded)

Binding constraints and their column pairs are derived mechanically (set-diff, §0#6).
Enabler booleanity is identified structurally — the unique constraint whose free-column set is
`{enabler_col}`, numerically 0 at enabler ∈ {0,1} and ≠ 0 at 2 — and is EXEMPT from the drop
sweep (theorem conditions on enabler == 1). Indices below are current bind_on numbering (R2),
for the report only; expectations key on the blanket rule + fingerprints, not indices.

| id | mutation (applied to the MONOLITHIC `build_fs_named` harness, not the lemma-chain `FS.main`) | expect | why |
|---|---|---|---|
| `M.bind_off` | constraints = bind_off (17) | **SAT** | PR #1425 under-constraint: ch_limb/maj_limb cols unpinned. **Gate**: replayed model must exhibit `word(limb_pair) ≠ word(recombine_pair)` for at least one derived binding pair; report prints forged vs honest Ch/Maj words + failing goal conjuncts — the exact forgery class of `tests/round_air.rs`, corroborated by `SAN.forged_z3` |
| `M.drop.1/.2` | drop not_e_l / not_e_h (idx 1,2) | SAT | ¬e limb freed (still 16-bit via AND-operand ranges) → Ch wrong → T1 → new_e/new_a mismatch |
| `M.drop.3/.4` | drop chl / chh recombine (idx 3,4) | SAT | col76/77 decouple from XOR bytes; binding transports the free value into ch_limb |
| `M.drop.5/.6` | drop ch binding lo / hi (idx 5,6) | SAT | frees exactly one Ch limb — single-limb restriction of M.bind_off; proves each binding individually necessary |
| `M.drop.7/.8` | drop s1 TripleSum carry lo / hi cubic (idx 7,8) | SAT | freed carry ⇒ res limb shiftable by k·2^16 mod p; 2^31 ≡ 1 (mod p) M31-wraparound forgery; dropped-high ⇒ res-hi fully free |
| `M.drop.9/.10` | drop T1 TripleSum cubics (idx 9,10) | SAT | same; T1 feeds new_e and new_a |
| `M.drop.11/.12` | drop majl / majh recombine (idx 11,12) | SAT | Maj analogue of 3/4 |
| `M.drop.13/.14` | drop maj binding lo / hi (idx 13,14) | SAT | Maj analogue of 5/6 |
| `M.drop.15/.16` | drop T2 TripleSum cubics (idx 15,16) | SAT | T2 freed ⇒ new_a forged |
| `M.drop.17/.18` | drop new_e TripleSum cubics (idx 17,18) | SAT | OUT[10,11] only range-assumed (I_out), never value-forced elsewhere (2^16 in-range choices vs 1 correct) |
| `M.drop.19/.20` | drop new_a TripleSum cubics (idx 19,20) | SAT | identical for OUT[2,3] |
| `V.table.and_free` | T1 keeps ranges, drops `c == a & b` | SAT | Ch/Maj bytes float — FS genuinely uses AND semantics |
| `V.table.xor_free` | T2 keeps ranges, drops `c == a ^ b` | SAT | same for XOR recombination |
| `V.table.and_norange` | T1 keeps `c == a & b`, drops operand ranges; rerun **DF.in4** | SAT | derived forcing genuinely rests on table ranges (Split16 adds no constraint — brief fact) |
| `V.spec.sigma1_rot` | goal-side Σ1 rotr6 → rotr7 | SAT | AIR computes true FIPS; tampered goal demands a different function — ¬G is not vacuously unreachable |
| `V.spec.sigma0_rot` | goal-side Σ0 rotr2 → rotr3 | SAT | Σ0 path sensitivity |
| `V.spec.sched_sigma` | goal-side W16's σ1 shift 10 → 9 | SAT | schedule conjunct sensitivity (table axiom left intact) |
| `V.spec.k_perturb` | goal-side K[20] ^= 1 | SAT | solver picks t = 20; t is symbolic per-row |
| `V.spec.endian_swap` | goal lo16/hi16 swapped in the new_a conjunct | SAT | kills the universal-fatal lo/hi-swap encoding-bug class (R2 §endianness) |
| `V.spec.no_increment` | goal `OUT[1] == IN[1]` | SAT | wiring emits t+1; off-by-one sensitivity |

Drop sweep covers **all 20 non-enabler bind_on constraints** (the 4 bindings both individually
and jointly via M.bind_off). Query budget: 47 DF + 5 FS lemmas (+ synthetic FS.main) +
4 lemma-chain vacuity + 8 necessity + ~13 sanity + 21 drops/bind_off + 9 canaries =
**110 queries**, each linear/cubic mod-p over BV64, pure QF_LIA (arith lemmas), or 8-bit
bitwise + 32-bit rotates — seconds each (slowest ≈ a few s), well under 1 min total.

---

## 6. Expected-verdict policy (`smt/expectations.json`)

- One entry per query id: `{"expect": "sat"|"unsat", "justification": "<one line>"}`.
  Drop-sweep entries are GENERATED at runtime from the blanket rule "every individually
  dropped non-enabler bind_on constraint → SAT" so indices never rot.
- The runner asserts the executed-query id set == the expectation key set ∪ generated set —
  no mutation is ever silently skipped.
- Any verdict ≠ expectation → nonzero exit. An UNSAT where SAT was expected prints
  `REDUNDANT-FOR-GOAL: <query> <infix rendering>` and still fails until a human adds a
  reclassification entry keyed by the **SHA-256 fingerprint of the constraint's canonical
  JSON** (never an index) with a written justification — a stale fingerprint stops matching
  and re-fails, the safe direction. Findings are reported, never hidden (acceptance #4).

---

## 7. File layout, runner

```
sha256_sound_spike/
  Cargo.toml               EDIT — add serde_json = "1.0"
  src/lib.rs               EDIT — add `pub mod symbolic;`
  src/symbolic.rs          NEW  — SymbolicEval + Node IR + converter + extract() self-checks (§1)
  src/bin/dump_smt.rs      NEW  — traces, forged rows, both variants, gates, writes JSON (§1.3)
  smt/
    run.sh                 NEW  — end-to-end entry point (below)
    check.py               NEW  — orchestrator: load → SAN → ledger → DF → FS → necessity →
                                  mutations → report; exit code
    encoding.py            NEW  — loader (strict schema), ev() BV + int twin, table axioms T1-T6,
                                  Round decode, replay
    fips.py                NEW  — single-source FIPS-180-4 spec (int + z3 BV32) + KATs
    mutations.py           NEW  — mutation matrix as data, not code paths
    expectations.json      NEW  — §6
    README.md              NEW  — §8
    DESIGN.md              NEW  — this document
    .gitignore             NEW  — out/
    out/                   generated: air.json, verdicts.json, report.txt
```

Boundary compliance: zero edits to `src/components/**`, `src/relations.rs`, `src/witness.rs`,
`src/reference.rs`, `src/check.rs`, `tests/round_air.rs`; no test or gate weakened; standalone
workspace (all cargo from `sha256_sound_spike/`). All new files carry R3 header conventions
(role + scope tag, provenance incl. stwo rev 5ea05973 + PR #1425, honest-scope, fidelity notes).

`smt/run.sh` (R3-verified: uv 0.9.22 present, `uv run --with z3-solver` → z3 4.16.0):
```bash
#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."                                   # sha256_sound_spike/
cargo test                                                # existing gate stays green (acceptance #6)
mkdir -p smt/out
cargo run --bin dump_smt -- smt/out/air.json              # panics (nonzero) on any extraction gate
if command -v uv >/dev/null 2>&1; then
  uv run --with z3-solver python smt/check.py smt/out/air.json | tee smt/out/report.txt
else
  [ -d smt/.venv ] || { python3 -m venv smt/.venv && smt/.venv/bin/pip -q install z3-solver; }
  smt/.venv/bin/python smt/check.py smt/out/air.json | tee smt/out/report.txt
fi
```
(`tee` note: check.py's exit code must propagate — either `set -o pipefail` suffices, as here,
or write report.txt from inside check.py.) Exit nonzero on: any Rust gate, any structural/
ledger/sanity failure, any verdict ≠ expectation, any unknown/timeout, any replay failure.
Report format, CI-parseable: `PASS|FAIL <query_id> expected=<SAT|UNSAT> got=<verdict> <ms>ms`;
FAIL lines followed by the infix constraint/target and decoded model; footer = the
force-printed EXTERNAL list (A5, A3-last-row, base-case injection) + `SUMMARY: n pass, n fail`.

---

## 8. `smt/README.md` outline

1. Theorem statement (brief's per-row statement verbatim; explicit quantifiers) + query →
   obligation map.
2. Trusted base inventory: T1–T6 formulae with FIPS §§ + reference.rs line anchors; K
   two-source rule; trusted code inventory (converter ~150 lines, ev() ~40, axioms+spec ~150).
3. Assumption register (§3.5 table, verbatim) + discharge ledger (each ASSUMED fact → its
   syntactic identity + DF query id, machine-enforced every run).
4. Composition/induction argument: base case (builtin injection, EXTERNAL); step (A2 via bus +
   ledger + DF); **last-row hole** (final read must range-check new_a/new_e — EXTERNAL,
   force-printed); exactly which stwo-core properties are leaned on.
5. NOT covered: table/schedule components' own AIR correctness; logup/FRI/Fiat-Shamir; bus
   multiset counting/multiplicities; padding-row completeness; builtin injection/extraction;
   multi-block `seq` semantics; anything cross-row beyond A2/A3.
6. How to run; expected runtime (< 1 min); 60s/query policy ("investigate, don't raise").
7. Verdict catalog + expectations format + REDUNDANT-FOR-GOAL reclassification procedure
   (fingerprint allowlist, written justification).
8. Regeneration workflow: what fails loudly (counts, decode panics, ledger, tripwire asserts
   on enabler/binding indices) vs what re-proves automatically (everything keyed off the
   Round-entry interface and blanket mutation rule).
9. Disclosure guardrail — echo `SHA256-SOUNDNESS-FIX.md` verbatim; PR #1425 open/undisclosed;
   never push this branch to a public remote. Not softened.

---

## 9. Top silent-wrong-verdict risks and their (gating) mitigations

1. **Vacuous UNSAT** (contradictory antecedent / miswired goal): `SAN.assume_sat`,
   `SAN.goal_sat`, `SAN.no_constraints`, and `SAN.honest_z3` must be SAT before any UNSAT is
   reported; the 6 V.spec + 3 V.table canaries must flip to SAT — an encoding that cannot
   distinguish the true spec from a 1-bit-tampered one cannot pass; `M.bind_off`'s model must
   replay AND exhibit the concrete binding-pair inequality, tying the SMT result to the known
   forgery; `SAN.forged_z3` corroborates with a Rust-constructed witness.
2. **Extraction/conversion infidelity**: every decode path panics (no permissive branch to
   audit); counts/diff/Round-shape asserts run twice (Rust + Python); four independent
   evaluators must agree on 64 honest rows + 2 forged rows including exact violation indices.
3. **Wrong table axioms / spec transcription**: axioms validated against all 38 uses × 64
   honest rows (every K[t] exercised, all carry classes); KATs validate the exact functions in
   the goal (single-sourcing); K two-source; independence anchored by Rust-generated witness
   data, not a second hand-written Python spec.

Residual (documented, not hidden): mitigations 2/3 share the honest witness as ground truth; a
bug that preserves honest-row satisfaction and survives every count/diff/canary/replay gate
would have to be semantics-preserving on the entire reachable set — the 21-drop + 9-canary
matrix with replayed models is the backstop that the encoding still separates sound from
unsound systems.
