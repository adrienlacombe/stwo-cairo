# SHA-256 round AIR — Ch/Maj under-constraint: finding, fix, and proof

**Status:** soundness-critical. Confirmed against `starkware-libs/stwo-cairo` PR #1425
(branch `sha256-builtin`, HEAD `fc7d3ff7`) on both the prover Rust AIR and the Cairo
verifier mirror. The fix here is **proven correct and sufficient** against this repo's
current stwo pin (`5ea05973`).

**Disclosure guardrail:** PR #1425 is an *open, unmerged* upstream PR and this finding has
**not** been disclosed to StarkWare. Nothing on this branch should be pushed to any public
remote, and no public PR/branch/issue should be opened, until a coordinated-disclosure
decision is made by a human. The commit messages and this document describe the
vulnerability, so publishing them *is* disclosure.

---

## 1. The bug

The SHA-256 round component computes the two round choice functions Ch and Maj, XOR-checks
them into recombined half-word columns, and then **adds the wrong columns** into the round's
T1/T2 modular sums.

In `stwo_cairo_prover/crates/cairo-air/src/components/sha_256_round.rs` at PR HEAD:

- `chl_col76` / `chh_col77` (and `majl_col112` / `majh_col113`) are the **correctly
  computed** Ch/Maj halves: each is constrained to equal its XOR-lookup recombination
  (round.rs lines 394–401 for Ch, 618–625 for Maj). They are then **never used again** —
  each appears exactly twice in the file: its declaration and its own constraint.
- `ch_limb_0_col78` / `ch_limb_1_col79` (and `maj_limb_0_col114` / `maj_limb_1_col115`) are
  the columns **actually fed** into `TripleSum32` for the T1 add (lines 418–419) and T2 add
  (lines 630–631). They are bare `eval.next_trace_mask()` cells with **no constraint** tying
  them to `chl/chh/majl/majh` or to anything else.

So the intended invariant `ch_limb == chl/chh` (and the Maj analogue) is simply absent.
`TripleSum32` treats its addends as given. The honest witness generator happens to fill
`ch_limb_0 = chl` etc. as a plain Rust assignment, which masks the gap for an honest prover —
but a **malicious prover can place arbitrary values** in those trace cells, satisfy every
present constraint, and produce a verifying proof whose round output is **not** SHA-256
(i.e. forge any digest).

**No transitive rescue.** A whole-tree grep for `ch_limb|maj_limb` shows these columns are
referenced only inside the round component (AIR + witness) and are never pushed across a
lookup boundary (`add_to_relation`/`RelationEntry`) to any other component. The schedule,
k-table, builtin, sigma, and AND-8 components do not reference them, so nothing downstream
pins them.

**Both sides inherit it.** The prover Rust AIR and the Cairo verifier mirror
(`stwo_cairo_verifier/crates/cairo_air/src/components/sha_256_round.cairo`) are emitted from
one AIR definition (identical `N_TRACE_COLUMNS = 125`, identical column layout and constraint
ordering). The Cairo mirror has the identical gap: `chl`/`majl` recombination quotients near
lines 862 / 1128, `ch_limb`/`maj_limb` fed to `triple_sum_32_evaluate` with no binding.

## 2. The fix

Four linear binding constraints — bind the consumed limbs to the checked halves:

```rust
eval.add_constraint(ch_limb_0_col78.clone()  - chl_col76.clone());
eval.add_constraint(ch_limb_1_col79.clone()  - chh_col77.clone());
eval.add_constraint(maj_limb_0_col114.clone() - majl_col112.clone());
eval.add_constraint(maj_limb_1_col115.clone() - majh_col113.clone());
```

Placed immediately after the Ch/Maj recombination constraints and before the respective
`TripleSum32` calls. No new columns (`N_TRACE_COLUMNS` stays 125), no witness change (the
honest witness already writes the duplicates). `add_constraint` count in the round component
goes 7 → 11.

`pr1425-round-soundness-fix.patch` in this directory applies exactly this to the PR's prover
round component (`git apply` onto `fc7d3ff7`). The **equivalent constraints must also be
added to the Cairo verifier mirror**, and — because these components are code-generated
(`// AIR version …`) — the durable upstream fix belongs in the **AIR generator source** so
both generated files regenerate with the binding. That generator is not in scope here.

Cleaner alternative (higher blast radius, not done here): delete `ch_limb_*/maj_limb_*` and
feed `chl/chh/majl/majh` directly into `TripleSum32` (125 → 121 columns; reshuffles indices
across component + witness generator).

## 3. How the fix is proven — `sha256_sound_spike/`

This directory is a **standalone, VM-free crate** that re-ports the round component and drives
it through a non-panicking constraint checker (`src/check.rs`, a mirror of stwo's
`assert_constraints_on_trace`). It is pinned to **this repo's stwo rev `5ea05973`** (see
`Cargo.toml`), so the result reflects the current constraint framework, not an old one.

Run:

```
cd sha256_sound_spike && cargo test
```

Acceptance gate (all green):

- `valid_single_compression_accepted` — FIPS-180-4 "abc", digest
  `ba7816bf 8f01cfea 414140de 5dae2223 b00361a3 96177a9c b410ff61 f20015ad`.
- `valid_two_compression_chain_accepted` — NIST 2-block message, digest
  `248d6a61 d20638b8 e5c02693 0c3e6039 a33ce459 64ff2167 f6ecedd4 19db06c1`.
- `forged_ch_demonstrates_underconstraint_and_binding_fix` — builds a *consistent* Ch forgery
  (arbitrary `ch_limb`, downstream row + interaction trace recomputed so all other constraints
  still hold). With binding **off** (verbatim PR) the forgery is **ACCEPTED** — the hole.
  With binding **on** (the fix) it is **REJECTED**, and the forged output differs from the
  reference round output.
- `corrupted_chl_rejected`, `corrupted_new_e_rejected`, `corrupted_enabler_rejected`,
  `corrupted_and_byte_stale_interaction_rejected` — reject-path siblings.

The `bind_ch_maj_limbs` flag on `Eval` exists only so the forgery test can instantiate the
pre-fix variant; production construction sets it `true`.

## 4. Scope — what this branch is and is not

**Is:** a proof that the four constraints are necessary and sufficient, against current stwo,
plus the ready-to-apply prover-side patch and the exact verifier-mirror constraints.

**Is not** a full sha256-builtin PR against current `main`. That is a separate, multi-week
effort and is deliberately deferred:

- **Convention re-shape.** `main` moved ~273 commits past the PR's base and now uses a single
  `CommonLookupElements` bus (relation selected by a hashed-name M31 constant as `tuple[0]`),
  removed `mix_into`, and uses a 2-tree `log_sizes`. The PR's per-relation-struct components
  must be re-shaped, not copied. (This spike keeps the PR convention so the eval stays
  line-comparable with upstream.)
- **Full component tower.** 16 sha256 components + `verify_bitwise_and_8` + sha256-specific
  rotation/shift subroutines + K-table/sigma/AND preprocessed columns registered into
  `PreProcessedTrace::canonical_*` (with the hardcoded variant counts bumped).
- **End-to-end builtin.** Requires the `m-kus/cairo-vm` sha256-builtin fork (rev `c50e0daa`)
  + matching `m-kus/cairo` compiler, rebased onto `main`'s crates.io `cairo-vm 3.2.0` (which
  has no sha256 builtin). `cairo-air` itself has zero cairo-vm dependency, which is why the
  AIR-only proof above needs no VM.
- **Cairo verifier mirror + generator-source fix.** The four constraints must also land in the
  `.cairo` mirror and, durably, in the AIR generator.

## 5. Provenance

Independently confirmed for bitcoin-stark; full write-ups:
`bitcoin-stark/spike/results/sha256-air-pr1425-underconstraint.md` (the finding),
`.../sha256-air-pr1425-disclosure-DRAFT.md` (a DRAFT disclosure note — not sent),
`.../sha256-air-status.md`. The original PoC crate lives at
`bitcoin-stark/spike/sha256-air/crate/`; this is that crate re-pinned to `5ea05973` and
placed here.
