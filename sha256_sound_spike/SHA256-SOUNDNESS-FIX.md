# SHA-256 round AIR — Ch/Maj under-constraint: finding, fix, and proof

**Status:** soundness-critical. The bug and fix loci are confirmed **directly against**
`starkware-libs/stwo-cairo` PR #1425 (branch `sha256-builtin`, HEAD `fc7d3ff7`): the missing
binding constraints are absent from both the prover Rust round component
(`.../components/sha_256_round.rs`) and the Cairo verifier mirror
(`.../sha_256_round.cairo`), verified by reading those exact upstream files, and
`pr1425-round-soundness-fix.patch` applies cleanly onto `fc7d3ff7` (`git apply --check`
passes). The fix is **proven necessary and sufficient** — including an end-to-end digest
forgery — against this repo's current stwo pin (`5ea05973`).

Fidelity note: within `sha256_sound_spike/`, the round component's `evaluate` body and the
bitwise-AND subroutine are decoded from PR #1425; the four supporting arithmetic subroutines
(`triple_sum_32`, `verify_triple_sum_32`, `split_16_low_part_size_8`, `bitwise_xor_num_bits_8`)
are re-expressed from vendored stwo-cairo (`fca831a`) and validated by the FIPS-180-4 KATs,
not byte-diffed against PR #1425. The *bug and fix* do not depend on those subroutines — they
are purely the four missing binding constraints in the round `evaluate`, which are confirmed
absent upstream.

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

Acceptance gate (all green, 12 tests):

- `valid_single_compression_accepted` — FIPS-180-4 "abc", digest
  `ba7816bf 8f01cfea 414140de 5dae2223 b00361a3 96177a9c b410ff61 f20015ad`.
- `valid_two_compression_chain_accepted` — NIST 2-block message, digest
  `248d6a61 d20638b8 e5c02693 0c3e6039 a33ce459 64ff2167 f6ecedd4 19db06c1`.
- **`propagated_ch_forgery_accepted_without_binding_rejected_with`** — the **end-to-end
  exploit**. Forge Ch at round 10, then carry the corrupted state honestly through rounds
  11..63 so the round self-relation chains consistently across every row. Every row-local
  constraint AND the round chain hold, so with binding **off** (verbatim PR) the component
  **ACCEPTS** a trace whose final post-64-round state is not SHA-256 (a real digest forgery).
  With binding **on** it is **REJECTED**, and the only violation is at the forged row.
- `propagated_maj_forgery_accepted_without_binding_rejected_with` — the Maj counterpart,
  proving the two `maj_limb` binding constraints are independently necessary.
- `forged_ch_row_local_underconstraint_and_binding_fix` — the single-row demonstration.
  **Scope caveat:** a single-row forgery leaves the round relation's push(row+1)/pull(row)
  disagreeing at that boundary, so in the full multi-component AIR the round relation's global
  balance would reject *this specific trace* even without the fix. It is the *propagated*
  forgery above that the binding fix is genuinely required to stop. This is why the
  end-to-end tests exist and why this one is labeled row-local.
- `corrupted_chl_rejected`, `corrupted_new_e_rejected`, `corrupted_enabler_rejected`,
  `corrupted_and_byte_stale_interaction_rejected` — reject-path siblings.

Why the propagated forgery survives the round relation (and needs the binding fix): the
AND/XOR lookups pin `chl/chh` (resp. `majl/majh`) to the *correct* Ch/Maj of each row's
inputs, but nothing ties the *consumed* `ch_limb/maj_limb` to them; a prover sets `ch_limb`
to any value, recomputes that round's output from it, and carries the (wrong) state forward
consistently. The round self-relation only checks that adjacent rounds chain — which they do —
so it never fires. Only the binding constraint `ch_limb == chl` catches the substitution.

Oracle scope: `check.rs` faithfully mirrors `assert_constraints_on_trace` at `5ea05973`
(single-component), which verifies each row's algebraic constraints and that the logup
telescopes to a `claimed_sum` recomputed from the trace. It does **not** model the global
cross-component multiplicity balance of the full AIR — which is exactly why the propagated
(chain-consistent) forgery is the faithful end-to-end model here, and the row-local one is
flagged as caught-globally.

The `bind_ch_maj_limbs` flag on `Eval` exists only so the forgery tests can instantiate the
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
