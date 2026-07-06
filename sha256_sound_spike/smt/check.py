"""SMT soundness checker — orchestrator (§4, §5, §6).

[SPIKE-ONLY TEST INFRASTRUCTURE — smt soundness layer]
Provenance: stwo rev 5ea05973, PR #1425 (see ../SHA256-SOUNDNESS-FIX.md). Consumes air.json
(from src/bin/dump_smt.rs) + fips.py (single-source FIPS spec) + encoding.py (field layer +
trusted table axioms). Proves the per-row functional-soundness theorem (README §1) by z3.

Order: SAN (sanity/non-vacuity — no UNSAT is trusted until this whole group passes) -> ledger
-> DF (derived forcing) -> FS.main (functional soundness) -> necessity -> mutations.
Every SAT model is replayed through the pure-int evaluator against the query's exact system;
replay failure is a hard error. Any verdict != expectation, any unknown/timeout, any structural
or replay failure -> nonzero exit.
"""

import hashlib
import json
import sys
import time

import z3

import encoding as enc
import fips
import mutations as mut

TWO16 = 1 << 16

# DF targets (§4a): in1<64; in{2..7,10..15,18..49}<2^16; out48,out49<2^16.
DF_TARGETS = (
    [("in", 1)]
    + [("in", k) for k in (2, 3, 4, 5, 6, 7, 10, 11, 12, 13, 14, 15)]
    + [("in", k) for k in range(18, 50)]
    + [("out", 48), ("out", 49)]
)


def df_id(target):
    return f"DF.{target[0]}{target[1]}"


# ---------------------------------------------------------------------------
# Solver plumbing.
# ---------------------------------------------------------------------------


def new_solver(logic=None):
    # QF_BV for the bit-vector queries (~6x faster than the portfolio Solver on pure BV);
    # the arithmetic FS lemmas (Int) use the general Solver.
    s = z3.SolverFor(logic) if logic else z3.Solver()
    s.set(timeout=60000, random_seed=0)
    return s


def solve(named, logic="QF_BV"):
    s = new_solver(logic)
    for name, term in named.items():
        s.assert_and_track(term, name)
    t0 = time.perf_counter()
    r = s.check()
    ms = (time.perf_counter() - t0) * 1000.0
    if r == z3.sat:
        return "sat", ms, [], s.model(), s
    if r == z3.unsat:
        return "unsat", ms, [str(c) for c in s.unsat_core()], None, s
    return "unknown", ms, [], None, s


def model_cvals(model, cvars):
    return [model.eval(cvars[i], model_completion=True).as_long() for i in range(125)]


# ---------------------------------------------------------------------------
# FS-family query builder + int replay (shared by FS.main, necessity, mutations,
# sanity assume/goal/no_constraints/honest_z3/forged_z3).
# ---------------------------------------------------------------------------

DEFAULTS = dict(
    variant="bind_on",
    drop_constraint_idx=None,
    table_opt=enc.DEFAULT_TOPT,
    goal_spec=fips.DEFAULT_SPEC,
    goal_endian_swap=False,
    goal_no_increment=False,
    include_constraints=True,
    include_i_res=True,
    include_i_out=True,
    drop_assumption=None,  # ('res',k) or ('out',k)
    negate_goal=True,
    include_goal=True,
    pin=None,  # None or list[125] of ints
)


def _opts(**over):
    o = dict(DEFAULTS)
    o.update(over)
    return o


def _cons_bv_terms(air, variant, ev, drop_idx=None):
    """BV constraint predicates; cubic-shaped trees -> carry disjunction (A10, equivalent over
    the prime field, and it removes the only var*var multiplies so z3 stays tractable)."""
    out = []
    for i, e in enumerate(air.constraints[variant]):
        if i == drop_idx:
            continue
        pred = enc.cubic_pred_bv(e, ev)
        out.append(pred if pred is not None else (ev(e) == 0))
    return out


def build_fs_named(air, cvars, o):
    ev = enc.make_ev_bv(cvars)
    named = {}
    named["RANGE"] = enc.range_term(cvars)
    named["ENABLER"] = enc.enabler_term(air, cvars)
    if o["include_constraints"]:
        named["CONSTRAINTS"] = z3.And(*_cons_bv_terms(air, o["variant"], ev, o["drop_constraint_idx"]))
    tterms = [
        enc.table_pred_bv(u, ev, spec=fips.DEFAULT_SPEC, opt=o["table_opt"])
        for u in air.relation_uses[o["variant"]]
        if u["relation"] != "Sha256Round"
    ]
    named["TABLES"] = z3.And(*tterms)
    if o["include_i_res"]:
        for k, term in enc.i_res_terms(air, cvars).items():
            if o["drop_assumption"] == ("res", k):
                continue
            named[f"A2.in{k}"] = term
    if o["include_i_out"]:
        for k, term in enc.i_out_terms(air, cvars).items():
            if o["drop_assumption"] == ("out", k):
                continue
            named[f"A3.out{k}"] = term
    if o["include_goal"]:
        conj = enc.build_goal_conjuncts(
            air, ev, spec=o["goal_spec"], endian_swap=o["goal_endian_swap"], no_increment=o["goal_no_increment"]
        )
        G = z3.And(*[t for _, t in conj])
        named["GOAL"] = z3.Not(G) if o["negate_goal"] else G
    if o["pin"] is not None:
        named["PIN"] = z3.And(*[cvars[i] == z3.BitVecVal(o["pin"][i], 64) for i in range(125)])
    return named, ev


def replay_fs(air, cvals, o):
    """Re-evaluate the asserted FS-family system over pure ints. Returns (ok, failing_goal)."""
    if not all(0 <= cvals[i] < enc.P for i in range(125)):
        return False, "RANGE violated"
    if cvals[air.enabler_col] != 1:
        return False, "ENABLER violated"
    if o["include_constraints"]:
        cons = air.constraints[o["variant"]]
        for i, e in enumerate(cons):
            if i == o["drop_constraint_idx"]:
                continue
            if enc.ev_int(e, cvals) != 0:
                return False, f"constraint[{i}] != 0"
    for u in air.relation_uses[o["variant"]]:
        if u["relation"] == "Sha256Round":
            continue
        if not enc.table_check_int(u, cvals, opt=o["table_opt"]):
            return False, f"table {u['relation']} use {u['order']} violated"
    if o["include_i_res"]:
        for k in (8, 9, 16, 17):
            if o["drop_assumption"] == ("res", k):
                continue
            if not cvals[enc._in_col(air, k)] < TWO16:
                return False, f"A2.in{k} violated"
    if o["include_i_out"]:
        for k in (2, 3, 10, 11):
            if o["drop_assumption"] == ("out", k):
                continue
            if not cvals[enc._out_col(air, k)] < TWO16:
                return False, f"A3.out{k} violated"
    failing = []
    if o["include_goal"]:
        conj = enc.goal_conjuncts_int(
            air, cvals, spec=o["goal_spec"], endian_swap=o["goal_endian_swap"], no_increment=o["goal_no_increment"]
        )
        failing = [lbl for lbl, ok in conj if not ok]
        g_holds = len(failing) == 0
        if o["negate_goal"] and g_holds:
            return False, "GOAL: Not(G) asserted but G holds"
        if (not o["negate_goal"]) and not g_holds:
            return False, f"GOAL: G asserted but fails at {failing}"
    return True, failing


def build_df_named(air, cvars, target, table_opt=enc.DEFAULT_TOPT):
    ev = enc.make_ev_bv(cvars)
    named = {"RANGE": enc.range_term(cvars), "ENABLER": enc.enabler_term(air, cvars)}
    named["CONSTRAINTS"] = z3.And(*_cons_bv_terms(air, "bind_on", ev))
    tterms = [
        enc.table_pred_bv(u, ev, spec=fips.DEFAULT_SPEC, opt=table_opt)
        for u in air.relation_uses["bind_on"]
        if u["relation"] != "Sha256Round"
    ]
    named["TABLES"] = z3.And(*tterms)
    kind, idx = target
    col = enc._in_col(air, idx) if kind == "in" else enc._out_col(air, idx)
    limit = 64 if (kind == "in" and idx == 1) else TWO16
    named["NOT_BOUND"] = z3.Not(z3.ULT(cvars[col], z3.BitVecVal(limit, 64)))
    return named, col, limit


def replay_df(air, cvals, target, table_opt=enc.DEFAULT_TOPT):
    if not all(0 <= cvals[i] < enc.P for i in range(125)):
        return False
    if cvals[air.enabler_col] != 1:
        return False
    for e in air.constraints["bind_on"]:
        if enc.ev_int(e, cvals) != 0:
            return False
    for u in air.relation_uses["bind_on"]:
        if u["relation"] == "Sha256Round":
            continue
        if not enc.table_check_int(u, cvals, opt=table_opt):
            return False
    kind, idx = target
    col = enc._in_col(air, idx) if kind == "in" else enc._out_col(air, idx)
    limit = 64 if (kind == "in" and idx == 1) else TWO16
    return cvals[col] >= limit


# ---------------------------------------------------------------------------
# Report accumulator.
# ---------------------------------------------------------------------------


class Report:
    def __init__(self):
        self.rows = []  # (query_id, expect, got, ms, detail)
        self.notes = []

    def add(self, qid, expect, got, ms=0.0, detail=""):
        self.rows.append((qid, expect.upper(), got.upper(), ms, detail))

    def note(self, s):
        self.notes.append(s)

    def n_fail(self):
        return sum(1 for _, e, g, _, _ in self.rows if e != g)


def fingerprint(node):
    return hashlib.sha256(json.dumps(node, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


# ---------------------------------------------------------------------------
# Main.
# ---------------------------------------------------------------------------


def main():
    here = __import__("os").path.dirname(__import__("os").path.abspath(__file__))
    air_path = sys.argv[1] if len(sys.argv) > 1 else here + "/out/air.json"
    exp_path = here + "/expectations.json"
    doc = json.load(open(air_path))
    expectations = json.load(open(exp_path))
    exp_queries = expectations["queries"]
    reclass = expectations.get("reclassifications", {})

    rep = Report()
    cvars = [z3.BitVec(f"c{i}", 64) for i in range(125)]
    civars = [z3.Int(f"i{i}") for i in range(125)]  # for the arithmetic FS lemmas (L_ts*, L_final)

    # ---- SAN.load: strict schema (Air ctor) + structural/ledger gates ----------
    try:
        air = enc.Air(doc)
        gates = enc.structural_gates(air)
        bad = [(n, d) for n, ok, d in gates if not ok]
        if bad:
            rep.add("SAN.load", "pass", "fail", detail=f"{bad}")
        else:
            rep.add("SAN.load", "pass", "pass", detail=f"{len(gates)} gates ok")
    except Exception as e:  # noqa: BLE001
        rep.add("SAN.load", "pass", "fail", detail=repr(e))
        _finish(rep, exp_queries, reclass, air=None)
        return

    # ---- SAN.field_equiv: prove fast reductions == brief's `urem p` for all operands<p ----
    fe_fail = []
    for guard, nm, neg in enc.field_equiv_obligations():
        s = new_solver()
        s.add(guard)
        s.add(neg)
        if s.check() != z3.unsat:
            fe_fail.append(nm)
    rep.add("SAN.field_equiv", "pass", "pass" if not fe_fail else "fail",
            detail="fast mod-p reductions proven == urem p over [0,p)" if not fe_fail else f"MISMATCH {fe_fail}")

    # ---- SAN.fips_kat -----------------------------------------------------------
    try:
        fips.run_kats()
        rep.add("SAN.fips_kat", "pass", "pass")
    except Exception as e:  # noqa: BLE001
        rep.add("SAN.fips_kat", "pass", "fail", detail=repr(e))

    # ---- SAN.honest_numeric: all 64 rows, pure ints -----------------------------
    honest = {r["row"]: [int(x) for x in r["cols"]] for r in air.honest_rows}
    hn_ok, hn_detail = _honest_numeric(air, honest)
    rep.add("SAN.honest_numeric", "pass", "pass" if hn_ok else "fail", detail=hn_detail)

    # ---- SAN.forged_numeric.{ch,maj} -------------------------------------------
    for f in air.forged_rows:
        cvals = [int(x) for x in f["cols"]]
        ok, detail = _forged_numeric(air, f, cvals)
        rep.add(f"SAN.forged_numeric.{f['forge']}", "pass", "pass" if ok else "fail", detail=detail)

    # ---- SAN.assume_sat / goal_sat / no_constraints -----------------------------
    _run_expect(rep, "SAN.assume_sat", air, cvars,
                _opts(include_constraints=False, include_goal=False), "sat")
    _run_expect(rep, "SAN.goal_sat", air, cvars,
                _opts(negate_goal=False), "sat")
    _run_expect(rep, "SAN.no_constraints", air, cvars,
                _opts(include_constraints=False), "sat")

    # ---- SAN.honest_z3.{0,1,10,25}: pinned honest rows, un-negated goal -> SAT --
    for r in (0, 1, 10, 25):
        o = _opts(negate_goal=False, pin=honest[r])
        _run_expect(rep, f"SAN.honest_z3.{r}", air, cvars, o, "sat")

    # ---- SAN.forged_z3.{ch,maj}: pinned forged rows, bind_off, Not(G) -> SAT ----
    for f in air.forged_rows:
        cvals = [int(x) for x in f["cols"]]
        o = _opts(variant="bind_off", include_i_res=False, include_i_out=False, pin=cvals)
        _run_expect(rep, f"SAN.forged_z3.{f['forge']}", air, cvars, o, "sat")

    # ---- (a) Derived forcing: 47 queries, expect UNSAT --------------------------
    for target in DF_TARGETS:
        qid = df_id(target)
        named, col, limit = build_df_named(air, cvars, target)
        verdict, ms, core, model, _ = solve(named)
        detail = ""
        if verdict == "sat":
            cvals = model_cvals(model, cvars)
            if not replay_df(air, cvals, target):
                verdict = "replayfail"
                detail = "SAT model failed int replay"
            else:
                detail = f"col c{col} >= {limit} unexpectedly"
        rep.add(qid, "unsat", verdict, ms, detail)

    # ---- (b) FS.main: functional soundness via the lemma chain (see README §Decomposition).
    # The monolithic query is intractable for z3 (documented finding); the theorem is
    # discharged by a chain of small lemmas, each expected UNSAT, composed by the tables +
    # L_ch/L_maj establishing "intermediate column == FIPS sub-function".
    fs_ids = _run_fs_lemmas(rep, air, cvars, civars)
    # Synthetic aggregate: FS.main PASSES iff every lemma is UNSAT.
    fs_ok = all(r[2] == "UNSAT" for r in rep.rows if r[0] in fs_ids)
    rep.add("FS.main", "unsat", "unsat" if fs_ok else "sat",
            detail=("discharged by " + ",".join(fs_ids)) if fs_ok else "a lemma did not hold")

    # ---- (b2) necessity: drop each of the 8 assumptions -> expect SAT -----------
    for k in (8, 9, 16, 17):
        _run_expect(rep, f"N.res.{k}", air, cvars, _opts(drop_assumption=("res", k)), "sat")
    for k in (2, 3, 10, 11):
        _run_expect(rep, f"N.out.{k}", air, cvars, _opts(drop_assumption=("out", k)), "sat")

    # ---- (5) mutations ----------------------------------------------------------
    # M.bind_off: full decoded variant. SAT + printed forgery model.
    o = _opts(variant="bind_off")
    named, _ = build_fs_named(air, cvars, o)
    verdict, ms, core, model, _ = solve(named)
    detail = ""
    if verdict == "sat":
        cvals = model_cvals(model, cvars)
        ok, failing = replay_fs(air, cvals, o)
        if not ok:
            verdict = "replayfail"
            detail = str(failing)
        else:
            detail, gate_ok = _decode_bindoff(air, cvals, failing)
            if not gate_ok:
                verdict = "gatefail"
    rep.add("M.bind_off", "sat", verdict, ms, detail)

    # drop sweep: every non-enabler bind_on constraint, generated (blanket rule -> SAT).
    drop_ids = []
    for idx in range(len(air.constraints["bind_on"])):
        if idx == air.enabler_constraint_idx:
            continue
        qid = f"M.drop.{idx}"
        drop_ids.append(qid)
        o = _opts(drop_constraint_idx=idx)
        named, _ = build_fs_named(air, cvars, o)
        verdict, ms, core, model, _ = solve(named)
        detail = ""
        if verdict == "sat":
            cvals = model_cvals(model, cvars)
            ok, failing = replay_fs(air, cvals, o)
            verdict = "sat" if ok else "replayfail"
            detail = f"free={idx}; failing={failing}"
        elif verdict == "unsat":
            # REDUNDANT-FOR-GOAL: fingerprint allowlist decides pass/fail (§6).
            fp = fingerprint(air.constraints["bind_on"][idx])
            if fp in reclass:
                rep.note(f"REDUNDANT-FOR-GOAL reclassified {qid} fp={fp[:16]}: {reclass[fp]}")
                verdict = "sat"  # accepted per allowlist; report as expected
                detail = f"REDUNDANT-FOR-GOAL (allowlisted): {reclass[fp]}"
            else:
                detail = f"REDUNDANT-FOR-GOAL {qid} fp={fp} (not allowlisted)"
        rep.add(qid, "sat", verdict, ms, detail)

    # table canaries + and_norange
    for qid, over, why in mut.table_canaries():
        topt = enc.TableOpt(**over["table_opt_kwargs"])
        _run_expect(rep, qid, air, cvars, _opts(table_opt=topt), "sat")
    qid, over, why = mut.AND_NORANGE
    topt = enc.TableOpt(**over["table_opt_kwargs"])
    named, col, limit = build_df_named(air, cvars, over["df_target"], table_opt=topt)
    verdict, ms, core, model, _ = solve(named)
    detail = ""
    if verdict == "sat":
        cvals = model_cvals(model, cvars)
        verdict = "sat" if replay_df(air, cvals, over["df_target"], table_opt=topt) else "replayfail"
    rep.add(qid, "sat", verdict, ms, detail)

    # spec canaries: pin the honest row that violates the perturbed goal (instant + a concrete
    # witness proving the z3 goal is sensitive to that spec parameter; unpinned SAT search over
    # the perturbed goal is unnecessarily hard, e.g. k_perturb must guess t=20 among 64 branches).
    for qid, over, why in mut.spec_canaries():
        _run_spec_canary(rep, qid, air, cvars, honest, over)

    _finish(rep, exp_queries, reclass, air, generated_unsat=[df_id(t) for t in DF_TARGETS], generated_sat=drop_ids)


# ---------------------------------------------------------------------------
# Helpers.
# ---------------------------------------------------------------------------


def _run_fs_lemmas(rep, air, cvars, civars):
    """Discharge FS.main as a lemma chain (README §Decomposition). Returns the list of lemma
    query ids (all expected UNSAT). Each is small and tractable in its native theory.

    The chain covers all 50 yielded-output goal conjuncts: the copy/increment tuple by the
    structural ledger (node identity, SAN.load); the two recomputed state words new_a/new_e by
    the faithful pure-LIA arith lemmas (intermediates FREE — no range crutch); and the schedule
    output by FS.L_sched. Every antecedent is first checked satisfiable (SAN.fs_vacuity.*) so a
    contradictory hypothesis cannot make a lemma vacuously UNSAT and pass silently."""
    fs_ids = []
    ev = enc.make_ev_bv(cvars)
    bit_ante = enc.lemma_bitwise_antecedent(air, cvars, ev)

    # --- non-vacuity guard: each FS lemma antecedent must be SAT on its own -------------
    # (The SAN.assume_sat/goal_sat/no_constraints checks cover the MONOLITHIC build_fs_named
    # antecedent, which is disjoint from these lemma-chain antecedents.)
    def vacuity(qid, terms, logic):
        named = {f"H{i}": t for i, t in enumerate(terms)}
        verdict, ms, _core, _model, _ = solve(named, logic=logic)
        detail = "antecedent satisfiable" if verdict == "sat" else "VACUOUS antecedent (contradictory) -> lemma proves nothing"
        rep.add(qid, "sat", verdict, ms, detail)

    vacuity("SAN.fs_vacuity.bitwise", bit_ante, "QF_BV")
    vacuity("SAN.fs_vacuity.new_e", enc.lemma_arith_antecedent(air, civars, "new_e"), "QF_LIA")
    vacuity("SAN.fs_vacuity.new_a", enc.lemma_arith_antecedent(air, civars, "new_a"), "QF_LIA")
    vacuity("SAN.fs_vacuity.sched", enc.lemma_sched_antecedent(air, cvars, ev), "QF_BV")

    # --- L_ch, L_maj: pure BV bitwise lemmas -------------------------------------------
    def bv_lemma(qid, goal_neg):
        named = {f"H{i}": t for i, t in enumerate(bit_ante)}
        named["GOAL_NEG"] = goal_neg
        verdict, ms, _core, _model, _ = solve(named)
        detail = "" if verdict == "unsat" else "lemma does NOT hold (byte computation != bitwise spec)"
        rep.add(qid, "unsat", verdict, ms, detail)
        fs_ids.append(qid)

    bv_lemma("FS.L_ch", enc.lemma_ch_goal_neg(cvars))
    bv_lemma("FS.L_maj", enc.lemma_maj_goal_neg(cvars))

    # --- L_new_e, L_new_a: faithful pure-LIA arith lemmas (intermediates FREE) ----------
    for which in ("new_e", "new_a"):
        qid = f"FS.L_{which}"
        terms = enc.lemma_arith_terms(air, civars, which)
        named = {f"H{j}": t for j, t in enumerate(terms)}
        verdict, ms, _core, _model, _ = solve(named, logic="QF_LIA")
        detail = "" if verdict == "unsat" else "arith lemma did not hold (yielded word != FIPS round value)"
        rep.add(qid, "unsat", verdict, ms, detail)
        fs_ids.append(qid)

    # --- L_sched: the schedule-output conjunct, machine-forced (was prose-only) ----------
    named = {f"H{i}": t for i, t in enumerate(enc.lemma_sched_antecedent(air, cvars, ev))}
    named["GOAL_NEG"] = enc.lemma_sched_goal_neg(air, cvars, ev)
    verdict, ms, _core, _model, _ = solve(named)
    detail = "" if verdict == "unsat" else "schedule output not forced by constraints + Schedule axiom"
    rep.add("FS.L_sched", "unsat", verdict, ms, detail)
    fs_ids.append("FS.L_sched")
    return fs_ids


def _goal_int_opts(over):
    return dict(
        spec=over.get("goal_spec", fips.DEFAULT_SPEC),
        endian_swap=over.get("goal_endian_swap", False),
        no_increment=over.get("goal_no_increment", False),
    )


def _run_spec_canary(rep, qid, air, cvars, honest, over):
    """Find an honest row that violates the PERTURBED goal, pin it, and z3-check SAT of
    Not(perturbed goal). SAT proves the z3 goal is genuinely sensitive to the perturbed spec
    parameter (a concrete honest witness distinguishes true spec from the 1-bit-tampered one)."""
    gopt = _goal_int_opts(over)
    row = None
    for r in range(64):
        conj = enc.goal_conjuncts_int(air, honest[r], **gopt)
        if any(not ok for _, ok in conj):
            row = r
            break
    if row is None:
        rep.add(qid, "sat", "nowitness", detail="no honest row violates the perturbed goal (canary vacuous)")
        return
    o = _opts(negate_goal=True, pin=honest[row], **over)
    named, _ = build_fs_named(air, cvars, o)
    verdict, ms, core, model, _ = solve(named)
    detail = f"pinned honest row {row} violates perturbed goal"
    if verdict == "sat":
        cvals = model_cvals(model, cvars)
        ok, failing = replay_fs(air, cvals, o)
        if not ok:
            verdict = "replayfail"
            detail = str(failing)
        else:
            detail += f"; failing conjuncts={failing}"
    rep.add(qid, "sat", verdict, ms, detail)


def _run_expect(rep, qid, air, cvars, o, expect):
    named, _ = build_fs_named(air, cvars, o)
    verdict, ms, core, model, _ = solve(named)
    detail = ""
    if verdict == "sat":
        cvals = model_cvals(model, cvars)
        ok, failing = replay_fs(air, cvals, o)
        if not ok:
            verdict = "replayfail"
            detail = str(failing)
    elif verdict == "unsat":
        detail = "core=" + ",".join(core)
    rep.add(qid, expect, verdict, ms, detail)


def _honest_numeric(air, honest):
    for row in range(64):
        cvals = honest[row]
        if cvals[air.enabler_col] != 1:
            return False, f"row {row}: enabler != 1"
        for i, e in enumerate(air.constraints["bind_on"]):
            if enc.ev_int(e, cvals) != 0:
                return False, f"row {row}: bind_on constraint[{i}] != 0"
            # A10 corroboration: on honest data the cubic's arg is in {0,1,2}, matching the
            # disjunction the solver uses (equivalence of raw cubic and disjunction on real rows).
            A = enc.cubic_arg(e)
            if A is not None and enc.ev_int(A, cvals) not in (0, 1, 2):
                return False, f"row {row}: cubic[{i}] arg={enc.ev_int(A, cvals)} not in {{0,1,2}}"
        for i, e in enumerate(air.constraints["bind_off"]):
            if enc.ev_int(e, cvals) != 0:
                return False, f"row {row}: bind_off constraint[{i}] != 0"
        for u in air.relation_uses["bind_on"]:
            if not enc.table_check_int(u, cvals):
                return False, f"row {row}: table {u['relation']} use {u['order']} fails"
        conj = enc.goal_conjuncts_int(air, cvals)
        bad = [lbl for lbl, ok in conj if not ok]
        if bad:
            return False, f"row {row}: FIPS next-state mismatch at {bad}"
    # consecutive-row chaining: row r OUT tuple values == row r+1 IN tuple values.
    for r in range(63):
        cur, nxt = honest[r], honest[r + 1]
        for k in range(50):
            ov = enc.ev_int(air.round_out[k], cur)
            iv = enc.ev_int(air.round_in[k], nxt)
            if ov != iv:
                return False, f"chain break row {r}->{r+1} at tuple {k}: {ov} != {iv}"
    return True, "64 rows: constraints=0, tables ok, FIPS ok, chained"


def _forged_numeric(air, f, cvals):
    # bind_off satisfied; bind_on violated at exactly the expected index set.
    for i, e in enumerate(air.constraints["bind_off"]):
        if enc.ev_int(e, cvals) != 0:
            return False, f"bind_off constraint[{i}] != 0 (should hold)"
    viol = [i for i, e in enumerate(air.constraints["bind_on"]) if enc.ev_int(e, cvals) != 0]
    if viol != f["expected_bind_on_violations"]:
        return False, f"bind_on violations {viol} != expected {f['expected_bind_on_violations']}"
    for u in air.relation_uses["bind_off"]:
        if not enc.table_check_int(u, cvals):
            return False, f"table {u['relation']} use {u['order']} fails"
    conj = enc.goal_conjuncts_int(air, cvals)
    bad = [lbl for lbl, ok in conj if not ok]
    if not bad:
        return False, "G holds on forged row (should be violated)"
    return True, f"bind_on violated at {viol}; G fails at {bad}"


def _decode_bindoff(air, cvals, failing):
    lines = []
    # binding pairs derived at load (§0#6): (78,76),(79,77) -> ch lo/hi ; (114,112),(115,113) -> maj lo/hi
    def word(lo, hi):
        # 32-bit word; ch_limb/maj_limb cols are unbound in bind_off so mask to 32 bits for display
        return ((cvals[lo] % enc.P) + (cvals[hi] % enc.P) * TWO16) & 0xFFFFFFFF
    ch_forged = word(78, 79)
    ch_true = word(76, 77)
    maj_forged = word(114, 115)
    maj_true = word(112, 113)
    lines.append(f"ch_limb(word c78,c79)=0x{ch_forged:08x} vs recombine(word c76,c77)=0x{ch_true:08x} "
                 f"{'DIFFER' if ch_forged != ch_true else 'equal'}")
    lines.append(f"maj_limb(word c114,c115)=0x{maj_forged:08x} vs recombine(word c112,c113)=0x{maj_true:08x} "
                 f"{'DIFFER' if maj_forged != maj_true else 'equal'}")
    lines.append(f"failing goal conjuncts={failing}")
    gate_ok = (ch_forged != ch_true) or (maj_forged != maj_true)
    if not gate_ok:
        lines.append("!! model does NOT exhibit a binding-pair inequality (gate violation)")
    return " | ".join(lines), gate_ok


def _finish(rep, exp_queries, reclass, air, generated_unsat=None, generated_sat=None):
    generated_unsat = generated_unsat or []
    generated_sat = generated_sat or []
    # Reconcile executed set vs expectation set (no silent skip).
    executed = {r[0] for r in rep.rows}
    expected_ids = set(exp_queries) | set(generated_unsat) | set(generated_sat)
    missing = expected_ids - executed
    extra = executed - expected_ids
    # Determine per-query expectation.
    def expected_of(qid):
        if qid in exp_queries:
            return exp_queries[qid]["expect"].upper()
        if qid in generated_unsat:
            return "UNSAT"
        if qid in generated_sat:
            return "SAT"
        return "?"

    lines = []
    n_fail = 0
    for qid, exp, got, ms, detail in rep.rows:
        canonical = expected_of(qid)
        # exp is what the call site expected; canonical is what expectations.json/generated say.
        # Both must agree with the actual verdict.
        ok = (got == exp) and (canonical == "?" or exp == canonical)
        status = "PASS" if ok else "FAIL"
        if not ok:
            n_fail += 1
        line = f"{status} {qid} expected={exp} got={got} {ms:.0f}ms"
        if detail:
            line += f"  :: {detail}"
        lines.append(line)

    if missing:
        lines.append(f"FAIL <reconcile> missing executed queries: {sorted(missing)}")
        n_fail += 1
    if extra:
        lines.append(f"FAIL <reconcile> unexpected executed queries (no expectation): {sorted(extra)}")
        n_fail += 1

    for nt in rep.notes:
        lines.append(f"NOTE {nt}")

    lines.append("")
    lines.append("EXTERNAL (not discharged by this layer; force-printed):")
    lines.append("  A5  logup cumsum soundness / bus multiset counting / FRI / Fiat-Shamir (stwo-core)")
    lines.append("  A3-last-row  final row's new_a/new_e range: the final read MUST range-check (external)")
    lines.append("  base-case  builtin injection of the initial state tuple (external)")
    lines.append("  table components' OWN AIR correctness (And/Xor/Sigma/KTable/Schedule) stays external")
    lines.append("")
    n_pass = len(rep.rows) - sum(1 for qid, exp, got, ms, detail in rep.rows
                                 if not ((got == exp) and (expected_of(qid) == "?" or exp == expected_of(qid))))
    lines.append(f"SUMMARY: {n_pass} pass, {n_fail} fail  ({len(rep.rows)} queries)")

    out = "\n".join(lines)
    print(out)
    # verdicts.json (audit output, non-gating).
    try:
        vj = [{"id": r[0], "expected": r[1], "got": r[2], "ms": round(r[3], 1), "detail": r[4]} for r in rep.rows]
        json.dump(vj, open(__import__("os").path.join(__import__("os").path.dirname(__import__("os").path.abspath(__file__)), "out", "verdicts.json"), "w"), indent=1)
    except Exception:  # noqa: BLE001
        pass
    sys.exit(1 if n_fail else 0)


if __name__ == "__main__":
    main()
