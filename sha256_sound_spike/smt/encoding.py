"""SMT encoding of the sha256 round AIR — loader, field layer, table axioms, goal.

[SPIKE-ONLY TEST INFRASTRUCTURE — smt soundness layer]
Provenance: consumes smt/out/air.json (dumped by src/bin/dump_smt.rs from the ACTUAL
Eval::evaluate of src/components/sha_256_round.rs), stwo rev 5ea05973, PR #1425 context
(see ../SHA256-SOUNDNESS-FIX.md). This file NEVER hand-transcribes a constraint: every
polynomial and relation entry comes from the JSON. The only hand-written mathematics here is
the trusted base — table-semantics axioms T1..T7 (§3.3 of DESIGN.md) — and the field layer.

Honest scope (see README §Not-covered): logup cumsum / bus multiset counting / FRI /
Fiat-Shamir are NOT modelled; relation entries are modelled by their table semantics only.

Field layer invariant: every column is a BV(64) constrained < p; every Node is evaluated with
EAGER mod-p reduction at every node (add/sub/mul/neg), so every compiled term is < p by
construction. No small-range shortcut anywhere in the field layer — this is exact M31.
"""

import z3

import fips

P = 2147483647  # 2^31 - 1, the M31 prime
PB = z3.BitVecVal(P, 64)
TWO16 = 1 << 16
TWO16B = z3.BitVecVal(TWO16, 64)

_VALID_OPS = {"col", "const", "add", "sub", "mul", "neg"}


# ---------------------------------------------------------------------------
# Strict schema loader (§2) — rejects unknown ops/keys, non-single-row columns.
# ---------------------------------------------------------------------------


def _check_node(n, path):
    if not isinstance(n, dict):
        raise ValueError(f"{path}: node is not an object: {n!r}")
    op = n.get("op")
    if op not in _VALID_OPS:
        raise ValueError(f"{path}: unknown op {op!r}")
    keys = set(n.keys())
    if op == "col":
        if keys != {"op", "interaction", "idx", "offset"}:
            raise ValueError(f"{path}: bad col keys {keys}")
        if n["interaction"] != 1:
            raise ValueError(f"{path}: col interaction {n['interaction']} != 1 (not base trace)")
        if n["offset"] != 0:
            raise ValueError(f"{path}: col offset {n['offset']} != 0 (shifted read)")
        if not (0 <= n["idx"] < 125):
            raise ValueError(f"{path}: col idx {n['idx']} out of 0..124")
    elif op == "const":
        if keys != {"op", "val"}:
            raise ValueError(f"{path}: bad const keys {keys}")
        if not (0 <= n["val"] < P):
            raise ValueError(f"{path}: const {n['val']} not in [0,p)")
    elif op == "neg":
        if keys != {"op", "arg"}:
            raise ValueError(f"{path}: bad neg keys {keys}")
        _check_node(n["arg"], path + ".arg")
    else:  # add/sub/mul
        if keys != {"op", "lhs", "rhs"}:
            raise ValueError(f"{path}: bad {op} keys {keys}")
        _check_node(n["lhs"], path + ".lhs")
        _check_node(n["rhs"], path + ".rhs")


# Frozen allowlist of relation names (§3.3). Unknown name = hard error.
_KNOWN_RELATIONS = {
    "Sha256Round",
    "Sha256BigSigma0",
    "Sha256BigSigma1",
    "Sha256KTable",
    "Sha256Schedule",
    "VerifyBitwiseAnd_8",
    "VerifyBitwiseXor_8",
}


class Air:
    """Parsed, schema-validated air.json. Exposes constraints and decoded tuples."""

    def __init__(self, doc):
        self.doc = doc
        for k, expect in [
            ("schema_version", 1),
            ("p", P),
            ("n_columns", 125),
            ("enabler_col", 124),
        ]:
            if doc.get(k) != expect:
                raise ValueError(f"top-level {k}={doc.get(k)!r} != {expect!r}")
        self.enabler_col = doc["enabler_col"]
        self.k_table = list(doc["k_table"])
        if len(self.k_table) != 64:
            raise ValueError(f"k_table length {len(self.k_table)} != 64")
        self.variants = {}
        for vn in ("bind_on", "bind_off"):
            if vn not in doc["variants"]:
                raise ValueError(f"missing variant {vn}")
            self.variants[vn] = doc["variants"][vn]
        # Validate every node grammatically.
        for vn, v in self.variants.items():
            for c in v["constraints"]:
                _check_node(c["expr"], f"{vn}.constraint[{c['index']}]")
            for u in v["relation_uses"]:
                if u["relation"] not in _KNOWN_RELATIONS:
                    raise ValueError(f"{vn}: unknown relation {u['relation']!r}")
                _check_node(u["mult"], f"{vn}.use[{u['order']}].mult")
                for j, x in enumerate(u["values"]):
                    _check_node(x, f"{vn}.use[{u['order']}].values[{j}]")
        self.constraints = {vn: [c["expr"] for c in v["constraints"]] for vn, v in self.variants.items()}
        self.relation_uses = {vn: v["relation_uses"] for vn, v in self.variants.items()}
        self.honest_rows = doc["honest_rows"]
        self.forged_rows = doc["forged_rows"]
        # Decode Round tuples from bind_on (identical across variants; asserted in gates).
        self.round_in, self.round_out = _decode_round(self.relation_uses["bind_on"], self.enabler_col)


def _decode_round(uses, enabler_col):
    rounds = [u for u in uses if u["relation"] == "Sha256Round"]
    if len(rounds) != 2:
        raise ValueError(f"expected exactly 2 Sha256Round uses, got {len(rounds)}")
    plus = [u for u in rounds if u["mult_sign"] == 1]
    minus = [u for u in rounds if u["mult_sign"] == -1]
    if len(plus) != 1 or len(minus) != 1:
        raise ValueError("Sha256Round entries must be exactly one +1 and one -1 sign")
    for u in rounds:
        if u["declared_size"] != 50 or len(u["values"]) != 50:
            raise ValueError("Sha256Round entries must both be size 50")
        m = u["mult"]
        if not (m["op"] == "col" and m["idx"] == enabler_col and m["interaction"] == 1 and m["offset"] == 0):
            raise ValueError(f"Round multiplicity must be bare enabler col {enabler_col}, got {m}")
    return plus[0]["values"], minus[0]["values"]


# ---------------------------------------------------------------------------
# Structural / ledger gates (§1.3, §3.6) — duplicated Python side of the Rust dump asserts.
# Returns a list of (name, ok, detail); caller (SAN.load) fails on any not-ok.
# ---------------------------------------------------------------------------

# Node equality on the loaded dicts.

def _node_eq(a, b):
    return a == b


def _is_col(n, idx=None):
    return n["op"] == "col" and (idx is None or n["idx"] == idx) and n["interaction"] == 1 and n["offset"] == 0


def structural_gates(air):
    out = []

    def add(name, ok, detail=""):
        out.append((name, bool(ok), detail))

    con_on = air.constraints["bind_on"]
    con_off = air.constraints["bind_off"]
    add("count.bind_on==21", len(con_on) == 21, f"{len(con_on)}")
    add("count.bind_off==17", len(con_off) == 17, f"{len(con_off)}")

    # bind_off is an in-order subsequence of bind_on; the set-diff is exactly 4 trees.
    i = 0
    diff_idx = []
    for j, e in enumerate(con_on):
        if i < len(con_off) and _node_eq(con_off[i], e):
            i += 1
        else:
            diff_idx.append(j)
    add("bind_off_subsequence", i == len(con_off), f"consumed {i}/{len(con_off)}")
    add("diff_count==4", len(diff_idx) == 4, f"{diff_idx}")
    add("diff_indices=={5,6,13,14}", diff_idx == [5, 6, 13, 14], f"{diff_idx}")

    # Each diff tree is Sub(Col, Col); record the pairs (derived, not hard-coded).
    pairs = []
    diff_shape_ok = True
    for j in diff_idx:
        e = con_on[j]
        if e["op"] == "sub" and _is_col(e["lhs"]) and _is_col(e["rhs"]):
            pairs.append((e["lhs"]["idx"], e["rhs"]["idx"]))
        else:
            diff_shape_ok = False
    add("diff_shape_Sub(Col,Col)", diff_shape_ok, f"{pairs}")
    add(
        "binding_pairs==(78,76),(79,77),(114,112),(115,113)",
        pairs == [(78, 76), (79, 77), (114, 112), (115, 113)],
        f"{pairs}",
    )
    air.binding_pairs = pairs  # (limb_col, recombine_col) — used by M.bind_off decode.

    # Enabler booleanity: the unique constraint whose free-col set is exactly {enabler_col}.
    def free_cols(n, acc):
        if n["op"] == "col":
            acc.add(n["idx"])
        for k in ("lhs", "rhs", "arg"):
            if k in n:
                free_cols(n[k], acc)
        return acc

    enab_idx = [j for j, e in enumerate(con_on) if free_cols(e, set()) == {air.enabler_col}]
    add("unique_enabler_booleanity", len(enab_idx) == 1, f"idx {enab_idx}")
    air.enabler_constraint_idx = enab_idx[0] if enab_idx else None

    # Relation uses: 38 per variant, node-for-node identical across variants; per-name counts.
    ru_on = air.relation_uses["bind_on"]
    ru_off = air.relation_uses["bind_off"]
    add("relation_uses==38", len(ru_on) == 38 and len(ru_off) == 38, f"{len(ru_on)}/{len(ru_off)}")
    add("relation_uses_identical_across_variants", ru_on == ru_off, "")
    from collections import Counter

    cnt = Counter(u["relation"] for u in ru_on)
    expect_cnt = {
        "Sha256Round": 2,
        "Sha256BigSigma0": 1,
        "Sha256BigSigma1": 1,
        "Sha256KTable": 1,
        "Sha256Schedule": 1,
        "VerifyBitwiseAnd_8": 20,
        "VerifyBitwiseXor_8": 12,
    }
    add("per_name_relation_counts", dict(cnt) == expect_cnt, f"{dict(cnt)}")

    # All table-use multiplicities are (+1, Const 1).
    tbl_mult_ok = all(
        u["mult"] == {"op": "const", "val": 1} and u["mult_sign"] == 1
        for u in ru_on
        if u["relation"] != "Sha256Round"
    )
    add("table_mult==(+1,Const1)", tbl_mult_ok, "")

    # Round: enabler derivation cross-assert.
    add("enabler_col==124", air.enabler_col == 124, f"{air.enabler_col}")

    # Column coverage across constraints + uses == exactly 0..124.
    seen = set()
    for e in con_on:
        free_cols(e, seen)
    for u in ru_on:
        free_cols(u["mult"], seen)
        for x in u["values"]:
            free_cols(x, seen)
    add("column_coverage==0..124", seen == set(range(125)), f"n={len(seen)}")

    # K two-source: dump k_table (from reference.rs) == fips.py's independent FIPS constants.
    add("k_two_source", air.k_table == list(fips.K), "")

    # Composition ledger (§3.6): node-identity on decoded tuples, column-number-free form.
    IN, OUT = air.round_in, air.round_out
    led = []
    led.append(("OUT[0]==IN[0]", _node_eq(OUT[0], IN[0])))
    led.append(("OUT[1]==Add(IN[1],1)", OUT[1] == {"op": "add", "lhs": IN[1], "rhs": {"op": "const", "val": 1}}))
    led.append(("OUT[4..9]==IN[2..7]", all(_node_eq(OUT[k], IN[k - 2]) for k in range(4, 10))))
    led.append(("OUT[12..17]==IN[10..15]", all(_node_eq(OUT[k], IN[k - 2]) for k in range(12, 18))))
    led.append(("OUT[18..47]==IN[20..49]", all(_node_eq(OUT[k], IN[k + 2]) for k in range(18, 48))))
    bare_targets = [2, 3, 10, 11, 48, 49]
    in_cols = {n["idx"] for n in IN if _is_col(n)}
    bare_ok = True
    bare_cols = []
    for k in bare_targets:
        n = OUT[k]
        if not _is_col(n) or n["idx"] in in_cols:
            bare_ok = False
        else:
            bare_cols.append(n["idx"])
    led.append(("OUT[{2,3,10,11,48,49}] bare distinct cols not in IN", bare_ok and len(set(bare_cols)) == 6))
    for nm, ok in led:
        add("ledger." + nm, ok, "")

    # Sub-function composition ledger (§3.6): tie each SHA sub-function's table I/O columns to
    # the exact FIPS-argument / yielded-output columns the goal consumes. Without these the
    # schedule/Sigma/K value facts would rest on an UNCHECKED column coincidence (a regeneration
    # could rewire OUT[48,49] or a Sigma input off its FIPS argument and still pass). Node-free
    # column identities, so a moved wire fails loudly.
    def in_col(k):
        n = IN[k]
        return n["idx"] if _is_col(n) else None

    def out_col(k):
        n = OUT[k]
        return n["idx"] if _is_col(n) else None

    try:
        sc = subfn_cols(air)
        add("subfn.sigma1_in==E(IN[10,11])", sc["sigma1_in"] == (in_col(10), in_col(11)), f"{sc['sigma1_in']}")
        add("subfn.sigma0_in==A(IN[2,3])", sc["sigma0_in"] == (in_col(2), in_col(3)), f"{sc['sigma0_in']}")
        add("subfn.k_t==IN[1]", sc["k_t"] == in_col(1), f"{sc['k_t']}")
        add("subfn.sched_window==IN[18..49]", sc["sched_window"] == tuple(in_col(k) for k in range(18, 50)),
            f"{sc['sched_window']}")
        add("subfn.sched_out==OUT[48,49]", sc["sched_out"] == (out_col(48), out_col(49)), f"{sc['sched_out']}")
    except Exception as e:  # noqa: BLE001
        add("subfn.derivable", False, repr(e))

    # Goal coverage: EVERY yielded-output goal conjunct must map to a discharging obligation, so
    # FS.main provably covers the whole negated goal (not a subset). Copy/increment tuple ->
    # structural ledger (node identity => the conjunct holds for all assignments); the two
    # recomputed words -> FS.L_new_e / FS.L_new_a; the schedule output -> FS.L_sched. A
    # regenerated AIR that introduces an unclassified conjunct fails HERE, never silently.
    import re as _re

    dummy = [z3.BitVec(f"g{i}", 64) for i in range(125)]
    labels = [lbl for lbl, _ in build_goal_conjuncts(air, make_ev_bv(dummy))]

    def _classify(lbl):
        if lbl == "new_a==T1+T2":
            return "FS.L_new_a"
        if lbl == "new_e==D+T1":
            return "FS.L_new_e"
        if lbl.startswith("sched_out"):
            return "FS.L_sched"
        if lbl == "out1==in1+1":
            return "ledger(increment)"
        if _re.fullmatch(r"out\d+==in\d+", lbl):
            return "ledger(copy)"
        return None

    # 50 yielded-output tuple positions, but the three paired-limb words (new_a, new_e, sched
    # out) collapse 6 positions into 3 word-equalities -> 47 distinct conjuncts.
    unclassified = [l for l in labels if _classify(l) is None]
    add("goal_coverage(all conjuncts discharged)", not unclassified and len(labels) == 47,
        f"n={len(labels)} (=50 tuple positions, paired limbs collapsed) unclassified={unclassified}")
    return out


# ---------------------------------------------------------------------------
# Field layer — BV64 eager mod-p, and the pure-int twin (different leaf/op bindings).
# ---------------------------------------------------------------------------


# Field reduction primitives. Eager mod-p at every node, EXACT (no small-range shortcut).
#
# The brief's reference semantics are `urem p` per op. Naive URem-by-a-prime bit-blasts to a
# full 64-bit division network per node, which makes the unpinned FS/mutation queries exceed
# the 60s budget. We instead use the standard Mersenne reduction (p = 2^31-1, so 2^31 == 1
# mod p) plus conditional subtraction. This is the SAME function as `urem p` on the operand
# ranges we ever produce (every subterm is < p by construction) — PROVEN equivalent for all
# operands < p by SAN.field_equiv (field_equiv_obligations below), which checks that the fast
# circuit == urem for symbolic inputs. No range shortcut: the reduction is exact for the full
# [0,p) domain. See README assumption A9.
_MASK31 = z3.BitVecVal((1 << 31) - 1, 64)


def _red1(s):
    """s in [0, 2p) -> s mod p, one conditional subtraction."""
    return z3.If(z3.ULT(s, PB), s, s - PB)


def _red2(s):
    """s in [0, 3p) -> s mod p."""
    return _red1(_red1(s))


def red_add(a, b):
    return _red1(a + b)  # a,b < p => a+b < 2p


def red_sub(a, b):
    return _red1(a + PB - b)  # a<p, b>=0 => a+p-b in (0, 2p)


def red_neg(a):
    return _red1(PB - a)  # a in [0,p) => p-a in (0,p]; a==0 => p -> 0


def red_mul(a, b):
    x = a * b  # < p^2 < 2^62, fits BV64
    lo = x & _MASK31
    hi = z3.LShR(x, 31)  # < 2^31
    return _red2(lo + hi)  # lo+hi < 2^32 < 3p ; x == hi*2^31+lo == hi+lo (mod p)


def make_ev_bv(cvars):
    """Return ev(node)->BV64 with eager exact mod-p at every node. cvars: list of 125 BV64."""
    memo = {}

    def ev(n):
        key = id(n)
        r = memo.get(key)
        if r is not None:
            return r
        op = n["op"]
        if op == "col":
            r = cvars[n["idx"]]
        elif op == "const":
            r = z3.BitVecVal(n["val"], 64)
        elif op == "add":
            r = red_add(ev(n["lhs"]), ev(n["rhs"]))
        elif op == "sub":
            r = red_sub(ev(n["lhs"]), ev(n["rhs"]))
        elif op == "mul":
            r = red_mul(ev(n["lhs"]), ev(n["rhs"]))
        elif op == "neg":
            r = red_neg(ev(n["arg"]))
        else:
            raise ValueError(op)
        memo[key] = r
        return r

    return ev


def field_equiv_obligations():
    """SAN.field_equiv: prove the fast reductions == the brief's `urem p` reference, for all
    operands in [0,p). Returns list of (guard, negated_claim) whose UNSAT discharges each.

    add/sub/neg are compared to `urem` directly (their pre-reduction sum is < 2p, so urem is a
    cheap ~32-bit division). mul is discharged in TWO decoupled obligations that never run urem
    on the 62-bit nonlinear product:
      mul_fold : for x < 2^62,  x - ((x&mask31)+(x>>31)) == (x>>31)*p   (Mersenne identity:
                 2^31 == p+1 so x == hi*(p+1)+lo == hi*p + (hi+lo); the a*b nonlinearity is
                 irrelevant — proven for ALL x, hence for x=a*b with a,b<p);
      mul_red  : for s < 2^32,  _red2(s) == urem(s, p)  (cheap; validates the 2-step reducer).
    red_mul(a,b) = _red2((a*b & mask31)+(a*b>>31)); the fold arg is < 2^32 and == a*b (mod p),
    so red_mul == urem(a*b,p). (This composition is the only hand-math in the equivalence; both
    mechanical halves plus mul_range are z3-checked.)"""
    a = z3.BitVec("fa", 64)
    b = z3.BitVec("fb", 64)
    x = z3.BitVec("fx", 64)
    s = z3.BitVec("fs", 64)
    ab = z3.And(z3.ULT(a, PB), z3.ULT(b, PB))
    x62 = z3.ULT(x, z3.BitVecVal(1 << 62, 64))
    s32 = z3.ULT(s, z3.BitVecVal(1 << 32, 64))
    return [
        (ab, "add", red_add(a, b) != z3.URem(a + b, PB)),
        (ab, "sub", red_sub(a, b) != z3.URem(a + PB - b, PB)),
        (ab, "neg", red_neg(a) != z3.URem(PB - a, PB)),
        (x62, "mul_fold", (x - ((x & _MASK31) + z3.LShR(x, 31))) != (z3.LShR(x, 31) * PB)),
        (s32, "mul_red", _red2(s) != z3.URem(s, PB)),
        (ab, "add_range", z3.UGE(red_add(a, b), PB)),
        (ab, "sub_range", z3.UGE(red_sub(a, b), PB)),
        (ab, "mul_range", z3.UGE(red_mul(a, b), PB)),
        (ab, "neg_range", z3.UGE(red_neg(a), PB)),
    ]


def ev_int(n, cvals):
    """Pure-int mod-p twin. cvals: list of 125 ints in [0,p)."""
    op = n["op"]
    if op == "col":
        return cvals[n["idx"]] % P
    if op == "const":
        return n["val"] % P
    if op == "add":
        return (ev_int(n["lhs"], cvals) + ev_int(n["rhs"], cvals)) % P
    if op == "sub":
        return (ev_int(n["lhs"], cvals) - ev_int(n["rhs"], cvals)) % P
    if op == "mul":
        return (ev_int(n["lhs"], cvals) * ev_int(n["rhs"], cvals)) % P
    if op == "neg":
        return (-ev_int(n["arg"], cvals)) % P
    raise ValueError(op)


# ---------------------------------------------------------------------------
# word32 bridge: legal only where the same query asserts both limbs < 2^16.
# ---------------------------------------------------------------------------


def word32_bv(lo_node, hi_node, ev):
    val = ev(lo_node) + ev(hi_node) * TWO16B  # < 2^32 given both limbs < 2^16
    return z3.Extract(31, 0, val)


def word32_int(lo, hi):
    return ((lo + hi * TWO16) & fips.MASK32)


def _bv32(v):
    return z3.BitVecVal(v, 32)


def k_if_bv(t, spec):
    """K[t] as a BV32 If-chain over t (BV64), independent of witness cols 80/81."""
    res = _bv32(spec.k[63])
    for i in range(62, -1, -1):
        res = z3.If(t == z3.BitVecVal(i, 64), _bv32(spec.k[i]), res)
    return res


# ---------------------------------------------------------------------------
# Table-semantics axioms T1..T7 (§3.3). BV form (predicate) and int form (bool).
# `opt` toggles the V.table.* mutations: drop_and_eq, drop_xor_eq, drop_ranges.
# ---------------------------------------------------------------------------


class TableOpt:
    def __init__(self, drop_and_eq=False, drop_xor_eq=False, drop_ranges_and=False):
        self.drop_and_eq = drop_and_eq
        self.drop_xor_eq = drop_xor_eq
        self.drop_ranges_and = drop_ranges_and


DEFAULT_TOPT = TableOpt()


def _ult(x, n):
    return z3.ULT(x, z3.BitVecVal(n, 64))


def table_pred_bv(use, ev, spec=fips.DEFAULT_SPEC, opt=DEFAULT_TOPT):
    """Return a z3 Bool predicate for a relation use, or None for Sha256Round."""
    rel = use["relation"]
    vals = use["values"]
    if rel == "Sha256Round":
        return None
    if rel == "VerifyBitwiseAnd_8":
        a, b, c = ev(vals[0]), ev(vals[1]), ev(vals[2])
        conj = []
        if not opt.drop_ranges_and:
            conj += [_ult(a, 256), _ult(b, 256)]
        if not opt.drop_and_eq:
            conj.append(c == (a & b))
        return z3.And(*conj) if conj else z3.BoolVal(True)
    if rel == "VerifyBitwiseXor_8":
        a, b, c = ev(vals[0]), ev(vals[1]), ev(vals[2])
        conj = [_ult(a, 256), _ult(b, 256)]
        if not opt.drop_xor_eq:
            conj.append(c == (a ^ b))
        return z3.And(*conj)
    if rel in ("Sha256BigSigma0", "Sha256BigSigma1"):
        il, ih, ol, oh = (ev(vals[i]) for i in range(4))
        rng = [_ult(il, TWO16), _ult(ih, TWO16), _ult(ol, TWO16), _ult(oh, TWO16)]
        xin = word32_bv(vals[0], vals[1], ev)
        xout = word32_bv(vals[2], vals[3], ev)
        f = fips.big_sigma0 if rel == "Sha256BigSigma0" else fips.big_sigma1
        return z3.And(*rng, xout == f(xin, fips.Z3Ops, spec))
    if rel == "Sha256KTable":
        t, kl, kh = ev(vals[0]), ev(vals[1]), ev(vals[2])
        w = word32_bv(vals[1], vals[2], ev)
        return z3.And(_ult(t, 64), _ult(kl, TWO16), _ult(kh, TWO16), w == k_if_bv(t, spec))
    if rel == "Sha256Schedule":
        limbs = vals[:32]
        ol, oh = vals[32], vals[33]
        rng = [_ult(ev(x), TWO16) for x in vals]  # all 34 limbs < 2^16
        wj = [word32_bv(limbs[2 * j], limbs[2 * j + 1], ev) for j in range(16)]
        out = word32_bv(ol, oh, ev)
        rhs = fips.schedule_next(wj[0], wj[1], wj[9], wj[14], fips.Z3Ops, spec)
        return z3.And(*rng, out == rhs)
    raise ValueError(f"unknown relation {rel}")


def table_check_int(use, cvals, opt=DEFAULT_TOPT):
    """Int-twin check of a relation use's table semantics (honest/forged numeric). -> bool."""
    rel = use["relation"]
    vals = use["values"]
    E = lambda n: ev_int(n, cvals)
    if rel == "Sha256Round":
        return True
    if rel == "VerifyBitwiseAnd_8":
        a, b, c = E(vals[0]), E(vals[1]), E(vals[2])
        ok = True
        if not opt.drop_ranges_and:
            ok = ok and a < 256 and b < 256
        if not opt.drop_and_eq:
            ok = ok and c == (a & b)
        return ok
    if rel == "VerifyBitwiseXor_8":
        a, b, c = E(vals[0]), E(vals[1]), E(vals[2])
        ok = a < 256 and b < 256
        if not opt.drop_xor_eq:
            ok = ok and c == (a ^ b)
        return ok
    if rel in ("Sha256BigSigma0", "Sha256BigSigma1"):
        il, ih, ol, oh = (E(vals[i]) for i in range(4))
        if not all(x < TWO16 for x in (il, ih, ol, oh)):
            return False
        f = fips.big_sigma0 if rel == "Sha256BigSigma0" else fips.big_sigma1
        return word32_int(ol, oh) == f(word32_int(il, ih), fips.IntOps)
    if rel == "Sha256KTable":
        t, kl, kh = E(vals[0]), E(vals[1]), E(vals[2])
        return t < 64 and kl < TWO16 and kh < TWO16 and word32_int(kl, kh) == fips.K[t]
    if rel == "Sha256Schedule":
        vv = [E(x) for x in vals]
        if not all(x < TWO16 for x in vv):
            return False
        limbs, ol, oh = vv[:32], vv[32], vv[33]
        wj = [word32_int(limbs[2 * j], limbs[2 * j + 1]) for j in range(16)]
        rhs = fips.schedule_next(wj[0], wj[1], wj[9], wj[14], fips.IntOps)
        return word32_int(ol, oh) == rhs
    raise ValueError(rel)


# ---------------------------------------------------------------------------
# Goal G (§3.4) — built over the decoded IN/OUT tuple exprs via fips.py.
# ---------------------------------------------------------------------------


def build_goal_conjuncts(air, ev, spec=fips.DEFAULT_SPEC, endian_swap=False, no_increment=False):
    """Return the list of (label, z3.Bool) goal conjuncts. G = And(all)."""
    IN, OUT = air.round_in, air.round_out
    W = lambda lo: word32_bv(IN[lo], IN[lo + 1], ev)
    A, B, C, D = W(2), W(4), W(6), W(8)
    E, F, G, H = W(10), W(12), W(14), W(16)
    W0, W1, W9, W14 = W(18), W(20), W(36), W(46)
    t = ev(IN[1])
    Ksp = k_if_bv(t, spec)
    T1 = fips.t1(H, E, F, G, Ksp, W0, fips.Z3Ops, spec)
    T2 = fips.t2(A, B, C, fips.Z3Ops, spec)
    conj = []
    conj.append(("out0==in0", ev(OUT[0]) == ev(IN[0])))
    if no_increment:
        conj.append(("out1==in1", ev(OUT[1]) == ev(IN[1])))
    else:
        conj.append(("out1==in1+1", ev(OUT[1]) == z3.URem(ev(IN[1]) + 1, PB)))
    if endian_swap:
        conj.append(("new_a==T1+T2", word32_bv(OUT[3], OUT[2], ev) == T1 + T2))
    else:
        conj.append(("new_a==T1+T2", word32_bv(OUT[2], OUT[3], ev) == T1 + T2))
    for k in range(4, 10):
        conj.append((f"out{k}==in{k-2}", ev(OUT[k]) == ev(IN[k - 2])))
    conj.append(("new_e==D+T1", word32_bv(OUT[10], OUT[11], ev) == D + T1))
    for k in range(12, 18):
        conj.append((f"out{k}==in{k-2}", ev(OUT[k]) == ev(IN[k - 2])))
    for k in range(18, 48):
        conj.append((f"out{k}==in{k+2}", ev(OUT[k]) == ev(IN[k + 2])))
    sched = fips.schedule_next(W0, W1, W9, W14, fips.Z3Ops, spec)
    conj.append(("sched_out==sigma1(W14)+W9+sigma0(W1)+W0", word32_bv(OUT[48], OUT[49], ev) == sched))
    return conj


# ---------------------------------------------------------------------------
# Assumption builders. Column indices resolved from the decoded tuples (§3.5).
# ---------------------------------------------------------------------------


def _out_col(air, k):
    n = air.round_out[k]
    assert _is_col(n), f"OUT[{k}] is not a bare col: {n}"
    return n["idx"]


def _in_col(air, k):
    n = air.round_in[k]
    assert _is_col(n), f"IN[{k}] is not a bare col: {n}"
    return n["idx"]


def i_res_terms(air, cvars):
    """A2: IN[8],IN[9],IN[16],IN[17] < 2^16 (d,h limbs). Returns dict tuple_idx -> term."""
    return {k: _ult(cvars[_in_col(air, k)], TWO16) for k in (8, 9, 16, 17)}


def i_out_terms(air, cvars):
    """A3: OUT[2],OUT[3],OUT[10],OUT[11] < 2^16 (new_a,new_e limbs)."""
    return {k: _ult(cvars[_out_col(air, k)], TWO16) for k in (2, 3, 10, 11)}


def range_term(cvars):
    return z3.And(*[_ult(cvars[i], P) for i in range(125)])


def enabler_term(air, cvars):
    return cvars[air.enabler_col] == 1


# ---------------------------------------------------------------------------
# Int-twin goal (for SAT-model replay + honest/forged numeric sanity).
# Returns list of (label, bool). G holds iff all are True.
# ---------------------------------------------------------------------------


def goal_conjuncts_int(air, cvals, spec=fips.DEFAULT_SPEC, endian_swap=False, no_increment=False):
    IN, OUT = air.round_in, air.round_out
    E = lambda n: ev_int(n, cvals)
    Wi = lambda lo: word32_int(E(IN[lo]), E(IN[lo + 1]))
    A, B, C, D = Wi(2), Wi(4), Wi(6), Wi(8)
    Ee, F, G, H = Wi(10), Wi(12), Wi(14), Wi(16)
    W0, W1, W9, W14 = Wi(18), Wi(20), Wi(36), Wi(46)
    t = E(IN[1])
    if not (0 <= t < 64):
        raise ValueError(f"int-goal replay: t={t} out of [0,64)")
    Ksp = spec.k[t]
    ops = fips.IntOps
    T1 = fips.t1(H, Ee, F, G, Ksp, W0, ops, spec)
    T2 = fips.t2(A, B, C, ops, spec)
    conj = []
    conj.append(("out0==in0", E(OUT[0]) == E(IN[0])))
    if no_increment:
        conj.append(("out1==in1", E(OUT[1]) == t))
    else:
        conj.append(("out1==in1+1", E(OUT[1]) == (t + 1) % P))
    if endian_swap:
        conj.append(("new_a==T1+T2", word32_int(E(OUT[3]), E(OUT[2])) == ((T1 + T2) & fips.MASK32)))
    else:
        conj.append(("new_a==T1+T2", word32_int(E(OUT[2]), E(OUT[3])) == ((T1 + T2) & fips.MASK32)))
    for k in range(4, 10):
        conj.append((f"out{k}==in{k-2}", E(OUT[k]) == E(IN[k - 2])))
    conj.append(("new_e==D+T1", word32_int(E(OUT[10]), E(OUT[11])) == ((D + T1) & fips.MASK32)))
    for k in range(12, 18):
        conj.append((f"out{k}==in{k-2}", E(OUT[k]) == E(IN[k - 2])))
    for k in range(18, 48):
        conj.append((f"out{k}==in{k+2}", E(OUT[k]) == E(IN[k + 2])))
    sched = fips.schedule_next(W0, W1, W9, W14, ops, spec)
    conj.append(("sched_out", word32_int(E(OUT[48]), E(OUT[49])) == (sched & fips.MASK32)))
    return conj


# ===========================================================================
# CUBIC DISJUNCTION + FS DECOMPOSITION (added after the monolithic FS query was
# found intractable for z3 — see README "Encoding findings" / assumption A10).
#
# Finding (empirical, exhaustively probed): a monolithic z3 query over the full
# round is intractable in EVERY faithful encoding (BV cannot root-find the carry
# cubics mod p; Int NIA cannot combine `mod p` with the bitwise AND/XOR/rotate).
# The soundness theorem is therefore discharged by a LAYERED lemma chain, each
# lemma tractable in its native theory:
#   * bitwise lemmas (Ch, Maj)         -> pure BV (no field wrap; values < 2^16)
#   * TripleSum carry lemmas (L_ts*)   -> Int, cubic replaced by A in {0,1,2}
#   * composition (L_final)            -> Int LIA, chains the L_ts word-equalities
# and the trusted table axioms supply "intermediate column == FIPS sub-function".
#
# Cubic rewrite soundness (assumption A10): X*(X-1)*(X-2)==0  ==>  X in {0,1,2}
# holds in any integral domain; M31 is a field because p = 2^31-1 is prime (a
# foundational fact of the whole STARK, already trusted). So `A in {0,1,2}` is a
# WEAKENING of the cubic (cubic-models subset of disjunction-models); asserting it
# gives a superset of models, so every UNSAT verdict is preserved a fortiori. For
# SAT queries the disjunction could in principle admit a spurious model, so every
# SAT model is replayed against the RAW cubic tree (ev_int) — a spurious model
# fails replay and is a hard error. Honest/forged numeric checks also use the raw
# cubic. z3 cannot itself prove the rewrite (it cannot do modular polynomial
# root-counting over a 31-bit prime — a documented finding, not a gap in rigor).
# ===========================================================================


def cubic_arg(n):
    """If n is exactly Mul(Mul(A, Sub(A, Const 1)), Sub(A, Const 2)) return A, else None.
    Structural match on the mechanically-extracted tree; A must be identical in all 3 slots."""
    if n["op"] != "mul":
        return None
    L, R = n["lhs"], n["rhs"]
    if R.get("op") != "sub" or R["rhs"] != {"op": "const", "val": 2}:
        return None
    A = R["lhs"]
    if L.get("op") != "mul" or L["lhs"] != A:
        return None
    if L["rhs"] != {"op": "sub", "lhs": A, "rhs": {"op": "const", "val": 1}}:
        return None
    return A


def is_cubic(n):
    return cubic_arg(n) is not None


def _carry_inner(A):
    """If cubic-arg A == Mul(inner, Const 32768) return inner, else None. Lets us assert the
    carry disjunction on `inner` directly (inner in {0, 2^16, 2*2^16}) instead of on
    inner*2^-16 in {0,1,2} — EXACTLY equivalent (32768 is a field unit: 32768*65536 == 2^31 == 1
    mod p) but with no modular-inverse multiply, which is far cheaper for z3."""
    if A is not None and A.get("op") == "mul":
        if A["rhs"] == {"op": "const", "val": 32768}:
            return A["lhs"]
        if A["lhs"] == {"op": "const", "val": 32768}:
            return A["rhs"]
    return None


def cubic_pred_bv(e, ev):
    """BV predicate equivalent to (cubic tree == 0), or None if e is not a cubic (A10)."""
    A = cubic_arg(e)
    if A is None:
        return None
    inner = _carry_inner(A)
    if inner is not None:
        x = ev(inner)
        return z3.Or(x == z3.BitVecVal(0, 64), x == z3.BitVecVal(TWO16, 64), x == z3.BitVecVal(2 * TWO16, 64))
    a = ev(A)
    return z3.Or(a == z3.BitVecVal(0, 64), a == z3.BitVecVal(1, 64), a == z3.BitVecVal(2, 64))


def cubic_pred_int(e, evi):
    """Int predicate equivalent to (cubic tree == 0), or None if e is not a cubic (A10)."""
    A = cubic_arg(e)
    if A is None:
        return None
    inner = _carry_inner(A)
    if inner is not None:
        x = evi(inner)
        return z3.Or(x == 0, x == TWO16, x == 2 * TWO16)
    a = evi(A)
    return z3.Or(a == 0, a == 1, a == 2)


def constraint_terms_bv(air, variant, ev, use_disjunction=True):
    """BV constraint predicates for a variant; cubic-shaped trees -> A in {0,1,2} (A10)."""
    terms = []
    for e in air.constraints[variant]:
        pred = cubic_pred_bv(e, ev) if use_disjunction else None
        terms.append(pred if pred is not None else (ev(e) == 0))
    return terms


def wcol_bv(cvars, lo, hi):
    """32-bit word from two limb columns (caller must have asserted both < 2^16)."""
    return z3.Extract(31, 0, cvars[lo] + cvars[hi] * TWO16B)


def ch_bv(e, f, g):
    return (e & f) ^ (~e & g)


def maj_bv(a, b, c):
    return (a & b) ^ (a & c) ^ (b & c)


# --- Int (LIA/NIA) layer for the arithmetic lemmas L_ts* and L_final ---------
M32 = 1 << 32


def make_ev_int_z3(civars):
    """ev(node)->z3 Int with eager `% P` (NIA). Only used inside the small L_ts lemmas."""
    memo = {}

    def ev(n):
        key = id(n)
        r = memo.get(key)
        if r is not None:
            return r
        op = n["op"]
        if op == "col":
            r = civars[n["idx"]]
        elif op == "const":
            r = z3.IntVal(n["val"])
        elif op == "add":
            r = (ev(n["lhs"]) + ev(n["rhs"])) % P
        elif op == "sub":
            r = (ev(n["lhs"]) - ev(n["rhs"])) % P
        elif op == "mul":
            r = (ev(n["lhs"]) * ev(n["rhs"])) % P
        elif op == "neg":
            r = (-ev(n["arg"])) % P
        else:
            raise ValueError(op)
        memo[key] = r
        return r

    return ev


def wint(civars, lo, hi):
    return civars[lo] + civars[hi] * TWO16


def m32_int(x):
    """Reduce a z3 Int x in [0, 5*2^32) mod 2^32: exactly one interval branch subtracts k*2^32
    (x is a sum of at most five reduced 32-bit words: T1 = H+Sigma1+Ch+K+W has 5 addends)."""
    return z3.If(x >= 4 * M32, x - 4 * M32,
           z3.If(x >= 3 * M32, x - 3 * M32,
           z3.If(x >= 2 * M32, x - 2 * M32,
           z3.If(x >= M32, x - M32, x))))


def exact_int_ev(n, civars, subnode=None, subval=None):
    """Evaluate a constraint node as an EXACT z3 Int (NO mod-p reduction), optionally
    substituting z3 term `subval` wherever a subtree structurally equal to `subnode` occurs.

    Used ONLY to lift the mechanically-extracted TripleSum carry cubics into pure LIA: the
    carry `inner` polynomials (see cubic_arg/_carry_inner) are affine in the trace columns
    (add/sub/const/col only), so their exact-integer value is a linear form and the field
    relation `inner == carry*2^16 (mod p)` becomes a linear equation with an explicit bounded
    wrap quotient (lemma_arith_terms). The one exception is the high-limb inner, which embeds
    the low carry `carry_low_tmp = (sum_lo - res_lo)*32768`; that subtree is field-only
    (32768 == 2^-16 mod p, NOT a small integer), so it is substituted by the explicit low-carry
    variable before exact evaluation (subnode = the carry_low_tmp node, subval = the cl var)."""
    if subnode is not None and n == subnode:
        return subval
    op = n["op"]
    if op == "col":
        return civars[n["idx"]]
    if op == "const":
        return z3.IntVal(n["val"])
    if op == "add":
        return exact_int_ev(n["lhs"], civars, subnode, subval) + exact_int_ev(n["rhs"], civars, subnode, subval)
    if op == "sub":
        return exact_int_ev(n["lhs"], civars, subnode, subval) - exact_int_ev(n["rhs"], civars, subnode, subval)
    if op == "mul":
        return exact_int_ev(n["lhs"], civars, subnode, subval) * exact_int_ev(n["rhs"], civars, subnode, subval)
    if op == "neg":
        return -exact_int_ev(n["arg"], civars, subnode, subval)
    raise ValueError(op)


# --- FS decomposition: bitwise lemmas (BV) ---------------------------------

def _noncubic_constraint_terms_bv(air, variant, ev):
    """BV `==0` predicates for the non-cubic constraints only (recombine/binding/not_e/enabler)."""
    return [ev(e) == 0 for e in air.constraints[variant] if not is_cubic(e)]


def lemma_bitwise_antecedent(air, cvars, ev):
    """Shared antecedent for L_ch / L_maj: RANGE, ENABLER, all non-cubic constraints, all
    AND/XOR table axioms, and the E,F,G,A,B,C input-limb ranges (< 2^16; discharged by DF)."""
    terms = [range_term(cvars), enabler_term(air, cvars)]
    terms += _noncubic_constraint_terms_bv(air, "bind_on", ev)
    for u in air.relation_uses["bind_on"]:
        if u["relation"] in ("VerifyBitwiseAnd_8", "VerifyBitwiseXor_8"):
            terms.append(table_pred_bv(u, ev))
    for c in range(2, 16):  # A,B,C,D?,E,F,G limbs c2..c15 (D handled by A2 but harmless here)
        terms.append(_ult(cvars[c], TWO16))
    return terms


def lemma_ch_goal_neg(cvars):
    E = wcol_bv(cvars, 10, 11); F = wcol_bv(cvars, 12, 13); G = wcol_bv(cvars, 14, 15)
    return z3.Not(wcol_bv(cvars, 78, 79) == ch_bv(E, F, G))


def lemma_maj_goal_neg(cvars):
    A = wcol_bv(cvars, 2, 3); B = wcol_bv(cvars, 4, 5); C = wcol_bv(cvars, 6, 7)
    return z3.Not(wcol_bv(cvars, 114, 115) == maj_bv(A, B, C))


# --- FS decomposition: faithful TripleSum carry lemmas (pure LIA) -----------
#
# THE INTERMEDIATE-RANGE CRUTCH IS GONE. The earlier decomposition assumed the six intra-row
# TripleSum result limbs (c82,83 / c84,85 / c116,117) were < 2^16. VerifyTripleSum32 does NOT
# range-check its result limbs (verify_triple_sum_32.rs header), and those columns are neither
# I_res/I_out nor DF targets, so RANGE ∧ constraints ∧ tables ∧ A2 ∧ A3 provably does NOT force
# them < 2^16 (a non-canonical model exists). Assuming it made FS.main prove a strictly-weaker
# statement than the theorem: a future regeneration whose under-constraint surfaced through a
# non-16-bit intermediate would leave the old chain UNSAT and pass silently. The lemmas below
# reason at the LIMB level with the intermediates FREE in [0,p), so no such assumption is made.
#
# Faithful encoding of one VerifyTripleSum32 (result limbs rl,rh; per-limb input sums SL,SH):
#   the two cubics are `carry_lo = (SL - rl)*2^-16 in {0,1,2}` and
#   `carry_hi = (SH + carry_lo - rh)*2^-16 in {0,1,2}` over M31. Introducing explicit carries
#   cl,ch in {0,1,2} and integer wrap quotients ql,qh this is EXACTLY (over the field):
#       SL - rl - cl*2^16 == ql*p   and   SH + cl - rh - ch*2^16 == qh*p
#   which is pure linear integer arithmetic (no `mod p` operator -> tractable; the `mod p` NIA
#   form was the perf cliff, see README §5). SL, SH and the affine `inner` polynomials are
#   read MECHANICALLY from the extracted cubic trees via exact_int_ev (SL-rl = inner_lo;
#   SH+cl-rh = inner_hi with carry_low_tmp substituted by cl), so nothing about the carry
#   arithmetic is hand-transcribed — a moved wire changes the equations and flips the lemma.
#
# Wrap-quotient bound (QMAX): every trace column is < p (RANGE), so SL,SH are sums of <=3
# values each < p, giving SL-rl-cl*2^16 in (-2p, 3p) and SH+cl-rh-ch*2^16 in (-2p, 3p); the
# UNIQUE integer quotient therefore lies in {-1,0,1,2}. QMAX=8 is a comfortable superset.
# Making QMAX WIDER only ever WEAKENS the antecedent (admits more models), so a too-wide bound
# can only flip a lemma to SAT (a loud failure) — never silently strengthen it into a vacuous
# UNSAT. A too-NARROW bound is the unsound direction and is excluded by the {-1,0,1,2} proof.
QMAX = 8

# TripleSum cubic-index pairs (lo,hi) and a label, in Eval emission order. These indices are
# tripwire DATA: lemma_arith_terms asserts each is a genuine cubic (cubic_arg != None) and every
# arith lemma z3-proves UNSAT, so a wrong pair yields SAT or trips the assert — the safe
# direction (README §9). `res` is documented for humans; it is re-derived from the cubic tree.
TS_CUBICS = {
    "h_s1_ch": (7, 8, (82, 83)),    # H + Sigma1(E) + Ch
    "t1_k_w":  (9, 10, (84, 85)),   # (..) + K + W0  = T1
    "s0_maj":  (15, 16, (116, 117)),  # Sigma0(A) + Maj = T2
    "new_e":   (17, 18, (120, 121)),  # T1 + D          = new_e
    "new_a":   (19, 20, (122, 123)),  # T1 + T2         = new_a
}
# TripleSum chain feeding each yielded output word (the FIPS 6.2.2 round structure).
ARITH_PATHS = {
    "new_e": ["h_s1_ch", "t1_k_w", "new_e"],
    "new_a": ["h_s1_ch", "t1_k_w", "s0_maj", "new_a"],
}


def subfn_cols(air):
    """Sub-function I/O columns, derived from the relation uses (never hand-written). Ties the
    Sigma0/Sigma1/K/Schedule table axioms to the exact columns the goal consumes; the FIPS-side
    identity (Sigma1 input == E, schedule window == IN[18..49], schedule out == OUT[48,49], ...)
    is asserted structurally in structural_gates so the composition cannot silently drift."""
    uses = air.relation_uses["bind_on"]

    def one(rel):
        us = [u for u in uses if u["relation"] == rel]
        if len(us) != 1:
            raise ValueError(f"expected exactly one {rel} use, got {len(us)}")
        return us[0]

    def col(n):
        if not _is_col(n):
            raise ValueError(f"sub-function value is not a bare col: {n}")
        return n["idx"]

    s1, s0, kt, sc = (one("Sha256BigSigma1"), one("Sha256BigSigma0"),
                      one("Sha256KTable"), one("Sha256Schedule"))
    pairs = air.binding_pairs  # [(78,76),(79,77),(114,112),(115,113)] — limb side = [0]
    return {
        "sigma1_in": (col(s1["values"][0]), col(s1["values"][1])),
        "sigma1_out": (col(s1["values"][2]), col(s1["values"][3])),
        "sigma0_in": (col(s0["values"][0]), col(s0["values"][1])),
        "sigma0_out": (col(s0["values"][2]), col(s0["values"][3])),
        "k_t": col(kt["values"][0]),
        "k_out": (col(kt["values"][1]), col(kt["values"][2])),
        "sched_window": tuple(col(x) for x in sc["values"][:32]),
        "sched_out": (col(sc["values"][32]), col(sc["values"][33])),
        "ch_out": (pairs[0][0], pairs[1][0]),
        "maj_out": (pairs[2][0], pairs[3][0]),
    }


def _ts_carry_terms(air, civars, tag):
    """Pure-LIA terms for one VerifyTripleSum32, mechanically from its two cubic trees.
    Returns (terms, cl) where cl is the low-carry var (fed to the high limb, already used)."""
    ci_lo, ci_hi, _res = TS_CUBICS[tag]
    e_lo = air.constraints["bind_on"][ci_lo]
    e_hi = air.constraints["bind_on"][ci_hi]
    A_lo = cubic_arg(e_lo)
    A_hi = cubic_arg(e_hi)
    assert A_lo is not None, f"TS_CUBICS[{tag}] lo constraint {ci_lo} is not a cubic (tripwire)"
    assert A_hi is not None, f"TS_CUBICS[{tag}] hi constraint {ci_hi} is not a cubic (tripwire)"
    inner_lo = _carry_inner(A_lo)  # affine: SL - res_lo
    inner_hi = _carry_inner(A_hi)  # affine once carry_low_tmp (= A_lo node) is replaced by cl
    assert inner_lo is not None and inner_hi is not None, f"TS_CUBICS[{tag}]: not a carry cubic"
    cl = z3.Int(f"cl_{tag}")
    ch = z3.Int(f"ch_{tag}")
    ql = z3.Int(f"ql_{tag}")
    qh = z3.Int(f"qh_{tag}")
    EL = exact_int_ev(inner_lo, civars)                       # SL - res_lo
    EH = exact_int_ev(inner_hi, civars, subnode=A_lo, subval=cl)  # SH + cl - res_hi
    terms = [
        z3.Or(cl == 0, cl == 1, cl == 2),
        z3.Or(ch == 0, ch == 1, ch == 2),
        ql >= -QMAX, ql <= QMAX, qh >= -QMAX, qh <= QMAX,
        EL - cl * TWO16 == ql * P,   # (SL - res_lo) == cl*2^16 (mod p)
        EH - ch * TWO16 == qh * P,   # (SH + cl - res_hi) == ch*2^16 (mod p)
    ]
    return terms, cl


def _arith_words(air, civars):
    """The 32-bit word expressions consumed by the arith goal, over air-derived columns."""
    sc = subfn_cols(air)
    W = lambda pair: wint(civars, pair[0], pair[1])
    ri = lambda k: air.round_in[k]["idx"]
    ro = lambda k: air.round_out[k]["idx"]
    return dict(
        H=W((ri(16), ri(17))), D=W((ri(8), ri(9))), W0=W((ri(18), ri(19))),
        Sig1=W(sc["sigma1_out"]), Sig0=W(sc["sigma0_out"]), K=W(sc["k_out"]),
        Ch=W(sc["ch_out"]), Maj=W(sc["maj_out"]),
        new_e=W((ro(10), ro(11))), new_a=W((ro(2), ro(3))),
    )


def lemma_arith_antecedent(air, civars, which):
    """Antecedent (no negated goal) of the faithful arith lemma for `which` in {new_e,new_a}.
    Domain RANGE + the path's TripleSum carry relations + boundary 16-bitness (inputs via
    DF/A2, yielded output via A3/next-consumer). Intermediates are deliberately UNranged."""
    terms = [z3.And(civars[i] >= 0, civars[i] < P) for i in range(125)]
    for tag in ARITH_PATHS[which]:
        tterms, _cl = _ts_carry_terms(air, civars, tag)
        terms += tterms
    sc = subfn_cols(air)
    ri = lambda k: air.round_in[k]["idx"]
    ro = lambda k: air.round_out[k]["idx"]
    # boundary words that must be canonical 32-bit (both limbs < 2^16):
    bnd = [(ri(16), ri(17)), (ri(8), ri(9)), (ri(18), ri(19)),
           sc["sigma1_out"], sc["k_out"], sc["ch_out"]]
    if which == "new_e":
        bnd.append((ro(10), ro(11)))
    else:
        bnd += [sc["sigma0_out"], sc["maj_out"], (ro(2), ro(3))]
    for lo, hi in bnd:
        terms.append(z3.And(civars[lo] >= 0, civars[lo] < TWO16))
        terms.append(z3.And(civars[hi] >= 0, civars[hi] < TWO16))
    return terms


def lemma_arith_terms(air, civars, which):
    """Faithful arith lemma: yielded new_e/new_a word == FIPS round value, with the SHA
    sub-functions supplied by their columns (word(sigma1_out)=Sigma1(E) etc. via tables/L_ch/
    L_maj, tied to the exact columns by structural_gates). Pure LIA; intermediates FREE."""
    terms = list(lemma_arith_antecedent(air, civars, which))
    w = _arith_words(air, civars)
    T1 = m32_int(w["H"] + w["Sig1"] + w["Ch"] + w["K"] + w["W0"])  # == fips.t1
    if which == "new_e":
        goal = w["new_e"] == m32_int(w["D"] + T1)
    else:
        T2 = m32_int(w["Sig0"] + w["Maj"])                        # == fips.t2
        goal = w["new_a"] == m32_int(T1 + T2)
    terms.append(z3.Not(goal))
    return terms


def lemma_sched_antecedent(air, cvars, ev, spec=fips.DEFAULT_SPEC):
    """Antecedent of L_sched: RANGE + all base constraints + table axioms + A2 + A3 (BV)."""
    terms = [range_term(cvars), enabler_term(air, cvars)]
    terms += constraint_terms_bv(air, "bind_on", ev)
    for u in air.relation_uses["bind_on"]:
        if u["relation"] != "Sha256Round":
            terms.append(table_pred_bv(u, ev, spec=spec))
    for term in i_res_terms(air, cvars).values():
        terms.append(term)
    for term in i_out_terms(air, cvars).values():
        terms.append(term)
    return terms


def lemma_sched_goal_neg(air, cvars, ev, spec=fips.DEFAULT_SPEC):
    """Negated schedule conjunct of the goal (the one yielded output the arith lemmas do NOT
    cover): word(OUT[48,49]) == sigma1(W14)+W9+sigma0(W1)+W0. This closes the gap where the
    schedule output previously rested on an unchecked column coincidence — here it is a
    machine-checked UNSAT obligation against the real constraints + Schedule table axiom."""
    IN, OUT = air.round_in, air.round_out
    Wd = lambda lo: word32_bv(IN[lo], IN[lo + 1], ev)
    sched = fips.schedule_next(Wd(18), Wd(20), Wd(36), Wd(46), fips.Z3Ops, spec)
    return z3.Not(word32_bv(OUT[48], OUT[49], ev) == sched)
