"""Mutation matrix (§5) as DATA, not code paths.

[SPIKE-ONLY TEST INFRASTRUCTURE — smt soundness layer]

Each mutation is a perturbation of the FS.main query (or, for and_norange, of a DF query).
check.py interprets these descriptors uniformly. All expect SAT: a mutation that flips the
result to SAT proves the mutated constraint/axiom/spec-conjunct was load-bearing for the UNSAT
soundness proof. Binding-constraint drops and the drop-sweep indices are DERIVED mechanically
(never hard-coded); the drop sweep is generated at runtime from the bind_on constraint list
minus the structurally-identified enabler-booleanity constraint (§6 blanket rule).
"""

import fips

# The 6 spec canaries + 3 table canaries. `fs_opts` are keyword overrides passed to
# check.build_fs_solver(). All expect SAT.


def spec_canaries():
    return [
        (
            "V.spec.sigma1_rot",
            {"goal_spec": fips.replace(fips.DEFAULT_SPEC, bs1=(7, 11, 25))},
            "goal-side Sigma1 rotr6->rotr7; AIR computes true FIPS so ~G is reachable",
        ),
        (
            "V.spec.sigma0_rot",
            {"goal_spec": fips.replace(fips.DEFAULT_SPEC, bs0=(3, 13, 22))},
            "goal-side Sigma0 rotr2->rotr3; T2 path sensitivity",
        ),
        (
            "V.spec.sched_sigma",
            {"goal_spec": fips.replace(fips.DEFAULT_SPEC, ss1=(17, 19, 9))},
            "goal-side schedule sigma1 shift 10->9; schedule conjunct sensitivity",
        ),
        (
            "V.spec.k_perturb",
            {"goal_spec": fips.replace(fips.DEFAULT_SPEC, k=tuple(k ^ 1 if i == 20 else k for i, k in enumerate(fips.K)))},
            "goal-side K[20]^=1; solver picks t=20 (t symbolic per row)",
        ),
        (
            "V.spec.endian_swap",
            {"goal_endian_swap": True},
            "goal new_a lo/hi swapped; kills the universal-fatal lo/hi-swap encoding-bug class",
        ),
        (
            "V.spec.no_increment",
            {"goal_no_increment": True},
            "goal OUT[1]==IN[1]; wiring emits t+1, off-by-one sensitivity",
        ),
    ]


def table_canaries():
    # and_free / xor_free perturb FS.main (drop the semantic equality, keep ranges).
    # and_norange is a DF-style query (rerun DF.in4 with AND operand ranges dropped).
    return [
        (
            "V.table.and_free",
            {"table_opt_kwargs": {"drop_and_eq": True}},
            "AND keeps ranges, drops c==a&b; Ch/Maj bytes float -> FS uses AND semantics",
        ),
        (
            "V.table.xor_free",
            {"table_opt_kwargs": {"drop_xor_eq": True}},
            "XOR keeps ranges, drops c==a^b; FS uses XOR recombination",
        ),
    ]


AND_NORANGE = (
    "V.table.and_norange",
    {"table_opt_kwargs": {"drop_ranges_and": True}, "df_target": ("in", 4)},
    "T1 keeps c==a&b, drops AND operand ranges; rerun DF.in4 -> SAT (Split16 adds no constraint)",
)
