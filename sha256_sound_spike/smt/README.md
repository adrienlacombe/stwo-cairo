# SMT soundness layer for `sha256_sound_spike`

**Spike-only test infrastructure — NOT wired into any production path.**
Provenance: stwo rev `5ea05973`, PR #1425 (see `../SHA256-SOUNDNESS-FIX.md`). Governing spec:
`DESIGN.md` (design panel) and the orchestrator brief.

This layer machine-checks a **per-row functional-soundness** theorem about the sha256 round AIR
in `src/components/sha_256_round.rs`, and mechanically re-derives the PR #1425 Ch/Maj forgery.
It consumes exactly one artifact — `out/air.json`, dumped by `src/bin/dump_smt.rs` from the
**actual** `Eval::evaluate` of the component (no constraint is ever hand-transcribed).

> ### DISCLOSURE GUARDRAIL (verbatim intent, do not soften)
> PR #1425 is open, unmerged, and undisclosed. Nothing on this branch — including everything
> under `smt/` — may be pushed to a public remote until the fix is disclosed through the process
> in `../SHA256-SOUNDNESS-FIX.md`.

---

## 1. Theorem

> Any assignment of the 125 trace columns that satisfies all base constraints (over M31,
> p = 2³¹ − 1), whose logup relation entries satisfy their table semantics, with `enabler = 1`,
> and under a minimal explicitly-stated induction hypothesis, has its yielded next-state tuple
> equal to the FIPS-180-4 round function of its input tuple.

Formally, with the decoded Round bus tuples `IN = c0..c49` and `OUT` (§3.6 ledger):

```
RANGE ∧ ENABLER ∧ constraints(bind_on) ∧ table_semantics ∧ I_res ∧ I_out  ⟹  OUT = round_FIPS(IN)
```

checked by z3 as UNSAT of the negation. `round_FIPS` is the single-source spec in `fips.py`
(FIPS 180-4 §6.2.2), KAT-validated at startup against the "abc" digest.

### Query → obligation map

| obligation | queries | verdict |
|---|---|---|
| Sanity / non-vacuity (run FIRST) | `SAN.*` incl. `SAN.fs_vacuity.*` (4) | pass / SAT |
| Derived forcing of input ranges | `DF.in{1..49}`, `DF.out{48,49}` (47) | UNSAT |
| **Functional soundness** | `FS.main` = `FS.L_ch ∧ FS.L_maj ∧ FS.L_new_e ∧ FS.L_new_a ∧ FS.L_sched` (6) | UNSAT |
| Assumption necessity (monolithic harness) | `N.res.{8,9,16,17}`, `N.out.{2,3,10,11}` (8) | SAT |
| Under-constraint forgery (PR #1425) | `M.bind_off` | SAT + decoded model |
| Drop-sweep necessity (monolithic harness) | `M.drop.{1..20}` | SAT |
| Table / spec sensitivity canaries | `V.table.*` (3), `V.spec.*` (6) | SAT |

`run.sh` executes all 110 queries; each is well under the 60 s/query budget (slowest ≈ a few s),
≈ 80 s wall total after the cargo build.

---

## 2. Trusted base

### 2.1 Table-semantics axioms (`encoding.py`, dispatched on relation name against a frozen
allowlist of exactly 7; unknown name = hard error). Applied to `ev()` of each use's value
**expressions** (some are inline `limb − 256·ms8`, essential for the split-based forcings).

| id | relation | axiom | FIPS / reference.rs |
|---|---|---|---|
| T1 | `VerifyBitwiseAnd_8(a,b,c)` | `a,b<256 ∧ c = a & b` | forces 8-bitness of a,b |
| T2 | `VerifyBitwiseXor_8(a,b,c)` | `a,b<256 ∧ c = a ^ b` | — |
| T3 | `Sha256BigSigma0(il,ih,ol,oh)` | all `<2¹⁶` ∧ `word(ol,oh)=Σ0(word(il,ih))`, Σ0=rotr2^rotr13^rotr22 | reference.rs:30-32, §4.1.2 |
| T4 | `Sha256BigSigma1` | rotations 6/11/25 | reference.rs:34-36 |
| T5 | `Sha256KTable(t,kl,kh)` | `t<64 ∧ kl,kh<2¹⁶ ∧ word(kl,kh)=K[t]` | §4.2.2 |
| T6 | `Sha256Schedule(l₀..l₃₁,ol,oh)` | all 34 `<2¹⁶`; `word(ol,oh)=σ1(w14)+w9+σ0(w1)+w0`, wⱼ=word(l₂ⱼ,l₂ⱼ₊₁) | reference.rs:38-44, §6.2.2 |
| T7 | `Sha256Round` | **structural only**: the +1-sign entry's 50 values = IN, the −1 entry's = OUT (bus equality/counting is trusted stwo-core) | — |

**K two-source rule**: the dump's `k_table` (from `reference.rs`) must equal `fips.py`'s own
independent FIPS §4.2.2 list, or the run dies (`SAN.load` gate `k_two_source`).

### 2.2 Trusted code inventory (auditable in one sitting)
`fips.py` single-source spec (~100 lines) · table axioms T1–T6 + Round decode (~120 lines) ·
`ev()` field layer BV + Int (~60 lines). Everything else is orchestration or is cross-checked by
four independent evaluators (Rust `assign` on raw trees, Rust `Node` interpreter on converted
trees, Python int twin, z3).

---

## 3. Assumption register + discharge ledger

`ev` is exact M31: every node is eagerly reduced mod p (see A9). Column IDs are resolved from the
decoded Round tuples, never a hand-written column map.

| id | statement | discharge |
|---|---|---|
| A1 | `enabler == 1` | theorem hypothesis; enabler=0 rows push/pull nothing; booleanity constraint (structurally identified) makes {0,1} exhaustive |
| A2 | I_res: `IN[8,9,16,17] < 2¹⁶` (d,h limbs) | **ASSUMED**, discharged by induction: prior row's `OUT[8,9]≡IN[6,7]` (old c) and `OUT[16,17]≡IN[14,15]` (old g) — node identities machine-checked (§3.6 ledger) — and those positions are DF-forced in-row; equated across rows by the Round bus (T7). Base case = builtin injection, EXTERNAL |
| A3 | I_out: `OUT[2,3,10,11] < 2¹⁶` (new_a,new_e limbs) | **ASSUMED**, discharged by the NEXT consumer: they become its `IN[2,3]/IN[10,11]`, forced by its own Σ0/Σ1 membership (DF), equated by the bus. **Final row: NOT discharged here — the final read MUST range-check. EXTERNAL, force-printed** |
| A4 | all 125 cols `< p` | encoding-domain condition (typed M31 trace) |
| A5 | stwo-core: logup soundness, bus multiset counting, FRI, Fiat-Shamir | EXTERNAL, force-printed |
| A6 | axioms T1–T6 match the real table/schedule components | trusted (~150 lines); validated numerically against all 38 uses × 64 honest rows; K two-source; V.table/V.spec canaries prove the proof depends on the exact semantics. The table components' OWN AIR correctness stays EXTERNAL |
| A7 | extraction fidelity (JSON == real AIR) | four-evaluator agreement + count/diff/structural asserts run twice (Rust dump + Python `SAN.load`) + forged-row exact-violation-index checks |
| A8 | `fips.py` transcription correctness | startup KATs + agreement with Rust-generated honest rows (independent `reference.rs`) on all 64 rows |
| **A9** | fast field reductions == the brief's `urem p` semantics | **z3-proven** (`SAN.field_equiv`): add/sub/neg vs `urem` directly; mul via two decoupled obligations (Mersenne fold identity for x<2⁶² + `_red2` reducer for s<2³²) that never run `urem` on the 62-bit product. See §5 |
| **A10** | cubic `A·(A−1)·(A−2)=0` ⟺ `A ∈ {0,1,2}` (used as `inner ∈ {0,2¹⁶,2·2¹⁶}` since `A = inner·2⁻¹⁶`) | **trusted math**: M31 is a field (p = 2³¹−1 is a Mersenne prime — already foundational to the whole STARK), so it is an integral domain and a degree-3 poly has exactly its 3 distinct roots. z3 cannot itself do modular polynomial root-counting over a 31-bit prime (a documented finding, §5), but the fact is elementary. Corroborated numerically on all 64 honest rows (`SAN.honest_numeric` checks the raw cubic ≡ 0 **and** the carry ∈ {0,1,2}); every SAT model is additionally replayed against the **raw** cubic tree. Direction used for UNSAT (cubic ⟹ disjunction) needs only "p prime"; the reverse is trivial arithmetic |

### 3.6 Machine-checked composition ledger (structural, no z3, every run, both variants)
Node-identity checks on the decoded tuples (column-number-free, so AIR regeneration cannot
silently move a wire): `OUT[0]≡IN[0]`; `OUT[1]≡Add(IN[1],1)`; `OUT[4..9]≡IN[2..7]`;
`OUT[12..17]≡IN[10..15]`; `OUT[18..47]≡IN[20..49]`; `OUT[{2,3,10,11,48,49}]` bare, pairwise-distinct
cols not occurring in IN. **Sub-function column-identity** (ties the trusted table sub-functions
to the exact FIPS arguments the goal consumes, so the §4.1 substitution cannot drift on an
unchecked coincidence): `Σ1_in≡IN[10,11]` (E), `Σ0_in≡IN[2,3]` (A), `K_t≡IN[1]`,
`sched_window≡IN[18..49]`, `sched_out≡OUT[48,49]` — all derived from the relation uses.
**Goal coverage**: every `G` conjunct maps to a discharging obligation (§4.1). Mismatch = hard
failure.

**Intermediate limbs are NOT assumed canonical.** There is deliberately *no* assumption that the
TripleSum result limbs `c82,83 / c84,85 / c116,117` are `< 2¹⁶` — the AIR does not force it and
the register never asserts it; the faithful arith lemmas (§4.1) leave them free in `[0,p)`.

---

## 4. Composition / induction argument

- **Step (A2):** the bus (T7) equates a row's `OUT` prefix to the next row's `IN`; the ledger
  fixes which positions; DF forces those positions' ranges in-row. So d,h being 16-bit is
  inherited from the previous row's in-row-forced c,g.
- **Base case:** the very first row's input state is injected by the builtin — **EXTERNAL**.
- **Last-row hole (A3):** the final row's `new_a/new_e` 16-bitness is discharged by the *next*
  consumer; the final round has no next consumer in this component, so the final read must
  range-check — **EXTERNAL, force-printed in every report footer.**

### 4.1 FS decomposition (why `FS.main` is a lemma chain — read this)
The monolithic functional-soundness query is **intractable for z3 in every faithful encoding**
(exhaustively probed — see §5). It is therefore discharged by a chain of small lemmas, each
tractable in its native theory. `FS.main` is a **synthetic aggregate: PASS iff every `FS.L_*`
is UNSAT.** The chain plus the §3.6 structural ledger cover **all 47 word-conjuncts of `G`**
(50 yielded-output tuple positions; the three paired-limb words — new_a, new_e, schedule out —
collapse 6 positions into 3 word-equalities). `SAN.goal_coverage` (a `SAN.load` gate) asserts
**every** `build_goal_conjuncts` label maps to a discharging obligation, so a regenerated AIR
that introduces a new conjunct fails loudly instead of leaving it silently unproven.

| `G` conjunct(s) | discharged by | how |
|---|---|---|
| `OUT[0]≡IN[0]`, `OUT[1]=IN[1]+1`, the copy shifts (`OUT[4..9]`,`OUT[12..17]`,`OUT[18..47]`) | **§3.6 ledger** | node identity ⇒ `ev` equal for every assignment (increment via A9); no z3 needed |
| `word(OUT[10,11]) = new_e` | `FS.L_new_e` (pure QF_LIA) | `= m32(D + m32(H+Σ1+Ch+K+W0))` |
| `word(OUT[2,3]) = new_a` | `FS.L_new_a` (pure QF_LIA) | `= m32(T1 + m32(Σ0+Maj))` |
| `word(OUT[48,49]) = schedule out` | `FS.L_sched` (pure BV) | `constraints + Schedule axiom ⊢ = σ1(W14)+W9+σ0(W1)+W0` |
| (sub-function bindings, below) | `FS.L_ch`,`FS.L_maj` + tables T3–T6 | see composition |

**Faithful arith lemmas — no intermediate-range crutch.** `FS.L_new_e`/`FS.L_new_a` reason at
the **limb level with the intra-row TripleSum result limbs (`c82,83 / c84,85 / c116,117`) FREE
in `[0,p)`.** VerifyTripleSum32 does not range-check its result limbs (`verify_triple_sum_32.rs`
header), those columns are neither `I_res`/`I_out` nor DF targets, and `RANGE ∧ constraints ∧
tables ∧ A2 ∧ A3` provably does **not** force them `< 2¹⁶` (a non-canonical model exists). An
earlier design *assumed* it — that made `FS.main` prove a strictly-weaker statement than the
theorem and would let a future regeneration whose under-constraint surfaced through a non-16-bit
intermediate pass silently. Each TripleSum's two carry cubics are lifted **mechanically** from
the extracted cubic trees (`exact_int_ev` of the affine `inner`; the high limb's
`carry_low_tmp` is replaced by the explicit low-carry variable) into pure linear integer
equations `SL − rl − cl·2¹⁶ = ql·p`, `SH + cl − rh − ch·2¹⁶ = qh·p` with `cl,ch ∈ {0,1,2}` and
bounded wrap quotients `ql,qh ∈ [−QMAX,QMAX]`. No `mod p` operator (that was the perf cliff,
§5) and nothing hand-transcribed — a moved wire changes the equations and flips the lemma.
`QMAX = 8` is a comfortable superset of the provable `q ∈ {−1,0,1,2}` (every column `< p` ⇒
each side lies in `(−2p, 3p)`); widening QMAX only ever *weakens* the antecedent (a loud SAT),
never silently strengthens it into a vacuous UNSAT.

**Sub-function composition (machine-checked column identity).** The facts `word(Σ1_out)=Σ1(E)`,
`word(Σ0_out)=Σ0(A)`, `word(K_out)=K[t]`, `word(sched_out)=schedule(…)` are the **table axioms
T3–T6 (trusted)**, and `word(ch_out)=Ch`, `word(maj_out)=Maj` are `FS.L_ch`/`FS.L_maj`. The
arith lemmas consume these at columns **derived from the relation uses** (`subfn_cols`), and
`SAN.load` now asserts (§3.6) that those use-I/O columns equal the exact FIPS arguments —
`Σ1_in≡E=IN[10,11]`, `Σ0_in≡A=IN[2,3]`, `K_t≡IN[1]`, `sched_window≡IN[18..49]`,
`sched_out≡OUT[48,49]`. So the substitution that yields `OUT = round_FIPS(IN)` can no longer
drift on an unchecked column coincidence (previously the schedule output rested on exactly such
a coincidence). Each lemma's own z3 verdict remains self-validating: a mislabeled column/cubic
yields SAT and fails the run — the safe direction, never silent unsoundness. Every antecedent is
additionally proven satisfiable on its own (`SAN.fs_vacuity.*`) so no lemma is vacuously UNSAT.

---

## 5. Encoding findings (the 60 s/query policy: "investigate, don't raise the limit")
Documented because they drove the architecture and are reproducible:

1. **Naïve `urem p` (BV)** bit-blasts a 64-bit division per node → FS/mutation queries exceed
   60 s. Replaced by an exact Mersenne fold + conditional subtraction, **proven bit-equal to
   `urem p`** (`SAN.field_equiv`, A9).
2. **BV cannot root-find a cubic mod p**: even a lone `A·(A−1)·(A−2)=0` is `unknown`. The carry
   cubics are therefore rewritten (A10). For the arith lemmas they are lifted to **explicit
   bounded carries** `cl,ch ∈ {0,1,2}` with integer wrap quotients (`SL−rl−cl·2¹⁶ = ql·p`) —
   pure linear arithmetic, no `mod p` operator.
3. **`mod p` + bitwise/deep-chain don't mix**: any `%P` operator over the chained carries is
   the perf cliff (the NIA form of `FS.L_new_a` took ~15–50 s and flirted with the 60 s budget);
   the `%P`-free **pure QF_LIA** form is ~2 s. Hence bitwise facts are **pure BV** (`FS.L_ch`,
   `FS.L_maj`, `FS.L_sched`) and the carry arithmetic is **pure QF_LIA** (`FS.L_new_e`,
   `FS.L_new_a`), kept in separate queries and composed algebraically (§4.1). This is why a
   monolithic query is infeasible.
4. **`QF_BV`** solver is ~6× the portfolio `Solver` on the pure-BV queries; used for all BV
   queries. The spec canaries pin the honest row that violates the perturbed goal (instant, and
   a stronger demonstration than an unpinned SAT search).

---

## 6. NOT covered (out of scope for this layer)
Table/schedule components' **own** AIR correctness (And/Xor/Sigma/KTable/Schedule); logup cumsum
soundness / bus multiset counting / multiplicities; FRI; Fiat-Shamir; padding-row completeness;
builtin injection/extraction; multi-block `seq` semantics; anything cross-row beyond A2/A3; the
**last-row range hole** (A3). These are the force-printed EXTERNAL items in the report footer.

---

## 7. How to run
```bash
cd sha256_sound_spike && bash smt/run.sh      # cargo test -> dump air.json -> z3 matrix
```
Requires `uv` (uses `uv run --with z3-solver`; z3 4.16.0) or falls back to a local venv.
Report → `smt/out/report.txt`; machine-readable verdicts → `smt/out/verdicts.json`
(both gitignored). Runtime ≈ 80 s after the cargo build; every query < 60 s.
Report lines: `PASS|FAIL <id> expected=<V> got=<V> <ms>ms  :: <detail>`. Nonzero exit on any
Rust gate, structural/ledger/sanity failure, verdict ≠ expectation, unknown/timeout, or replay
failure.

**60 s policy:** if any query exceeds ~60 s, the encoding is wrong — investigate (see §5), never
raise the timeout.

---

## 8. Verdict catalog & `expectations.json`
Each query id has `{expect, justification}` in `expectations.json`. `DF.*` (→UNSAT) and
`M.drop.*` (→SAT) are **generated at runtime** from blanket rules so indices never rot. The
runner asserts *executed id set == expected id set* (explicit ∪ generated) — no mutation is ever
silently skipped. Any verdict ≠ expectation → nonzero exit.

**REDUNDANT-FOR-GOAL:** a drop-sweep constraint that comes back UNSAT (unexpectedly redundant
for this goal) is reported and **fails** the run until a human adds a reclassification entry keyed
by the **SHA-256 fingerprint of the dropped constraint's canonical JSON** (never an index) in
`expectations.json.reclassifications`, with a written justification. A stale fingerprint stops
matching and re-fails — the safe direction. (Currently empty: all 20 drops are SAT.)

---

## 9. Regeneration workflow
When the AIR regenerates, re-run `run.sh`. **Fails loudly** on drift: constraint counts,
set-diff `{5,6,13,14}` / binding pairs `(78,76),(79,77),(114,112),(115,113)`, enabler==124,
Round decode, `TS_CUBICS` cubic tripwires (`cubic_arg`/`_carry_inner` must match each cited
index), per-name relation counts, column coverage, K two-source, the composition ledger
(now incl. the sub-function column-identity checks and goal coverage), and the four-evaluator
numeric gates. **Re-proves automatically** everything keyed off the Round-entry interface, the
sub-function relation uses, and the blanket mutation rule. Column indices in
`TS_CUBICS`/binding pairs are tripwire data cross-checked by z3 UNSAT verdicts (a wrong cubic
index or moved wire flips the affected lemma to SAT), never trusted silently. The faithful arith
lemmas derive their carry arithmetic *mechanically* from the extracted cubic trees, so a moved
wire changes the equations rather than being silently ignored.
