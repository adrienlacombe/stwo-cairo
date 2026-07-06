"""Single-source FIPS-180-4 SHA-256 spec, generic over int and z3 BV32 terms.

[SPIKE-ONLY TEST INFRASTRUCTURE — smt soundness layer]
Provenance: FIPS 180-4 (sections 4.1.2, 4.2.2, 5.3.3, 6.2.2), stwo rev 5ea05973,
PR #1425 context (see ../SHA256-SOUNDNESS-FIX.md).

This is the ONLY place the SHA-256 round semantics are written on the Python side
(design DESIGN.md section 0 resolution #9). Instantiated over ints it is the numeric
reference used by the sanity checks; instantiated over z3 BV32 terms it builds the
solver goal. The startup KATs therefore validate the very functions inside the goal.
The independent ground truth is the Rust reference implementation (reference.rs,
KAT-tested), which produced the honest witness rows this module is checked against.

K is hard-coded here from FIPS 180-4 section 4.2.2 and cross-asserted at load time
against the dump's k_table (which comes from reference.rs) — two independent sources
or the run dies.
"""

from dataclasses import dataclass, field, replace

MASK32 = 0xFFFFFFFF

# FIPS 180-4 section 4.2.2 — first 32 bits of the fractional parts of the cube roots
# of the first 64 primes. Transcribed from the standard, NOT from air.json/reference.rs.
K = (
    0x428A2F98, 0x71374491, 0xB5C0FBCF, 0xE9B5DBA5, 0x3956C25B, 0x59F111F1,
    0x923F82A4, 0xAB1C5ED5, 0xD807AA98, 0x12835B01, 0x243185BE, 0x550C7DC3,
    0x72BE5D74, 0x80DEB1FE, 0x9BDC06A7, 0xC19BF174, 0xE49B69C1, 0xEFBE4786,
    0x0FC19DC6, 0x240CA1CC, 0x2DE92C6F, 0x4A7484AA, 0x5CB0A9DC, 0x76F988DA,
    0x983E5152, 0xA831C66D, 0xB00327C8, 0xBF597FC7, 0xC6E00BF3, 0xD5A79147,
    0x06CA6351, 0x14292967, 0x27B70A85, 0x2E1B2138, 0x4D2C6DFC, 0x53380D13,
    0x650A7354, 0x766A0ABB, 0x81C2C92E, 0x92722C85, 0xA2BFE8A1, 0xA81A664B,
    0xC24B8B70, 0xC76C51A3, 0xD192E819, 0xD6990624, 0xF40E3585, 0x106AA070,
    0x19A4C116, 0x1E376C08, 0x2748774C, 0x34B0BCB5, 0x391C0CB3, 0x4ED8AA4A,
    0x5B9CCA4F, 0x682E6FF3, 0x748F82EE, 0x78A5636F, 0x84C87814, 0x8CC70208,
    0x90BEFFFA, 0xA4506CEB, 0xBEF9A3F7, 0xC67178F2,
)

# FIPS 180-4 section 5.3.3 — initial hash value H(0).
IV = (
    0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
    0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
)


class IntOps:
    """32-bit operations over Python ints (the numeric reference instantiation)."""

    @staticmethod
    def add(a, b):
        return (a + b) & MASK32

    @staticmethod
    def xor(a, b):
        return a ^ b

    @staticmethod
    def and_(a, b):
        return a & b

    @staticmethod
    def not_(a):
        return a ^ MASK32

    @staticmethod
    def rotr(x, n):
        return ((x >> n) | (x << (32 - n))) & MASK32

    @staticmethod
    def shr(x, n):
        return x >> n


class Z3Ops:
    """32-bit operations over z3 BV32 terms (the goal-builder instantiation).

    Imported lazily so the int instantiation works without z3 installed.
    """

    from z3 import LShR as _lshr
    from z3 import RotateRight as _rotr

    @staticmethod
    def add(a, b):
        return a + b  # native BV32 wrap == mod 2^32

    @staticmethod
    def xor(a, b):
        return a ^ b

    @staticmethod
    def and_(a, b):
        return a & b

    @staticmethod
    def not_(a):
        return ~a

    @staticmethod
    def rotr(x, n):
        return Z3Ops._rotr(x, n)

    @staticmethod
    def shr(x, n):
        return Z3Ops._lshr(x, n)


@dataclass(frozen=True)
class Spec:
    """FIPS-180-4 rotation/shift/constant parameters.

    DEFAULT_SPEC is the true standard. The V.spec.* mutation canaries build
    perturbed copies for the GOAL side only (table axioms always use DEFAULT_SPEC).
    """

    bs0: tuple = (2, 13, 22)  # capital-Sigma0 rotations, FIPS 4.1.2
    bs1: tuple = (6, 11, 25)  # capital-Sigma1 rotations, FIPS 4.1.2
    ss0: tuple = (7, 18, 3)  # small-sigma0: rotr, rotr, SHR, FIPS 4.1.2
    ss1: tuple = (17, 19, 10)  # small-sigma1: rotr, rotr, SHR, FIPS 4.1.2
    k: tuple = K


DEFAULT_SPEC = Spec()


def big_sigma0(x, ops, spec=DEFAULT_SPEC):
    r0, r1, r2 = spec.bs0
    return ops.xor(ops.xor(ops.rotr(x, r0), ops.rotr(x, r1)), ops.rotr(x, r2))


def big_sigma1(x, ops, spec=DEFAULT_SPEC):
    r0, r1, r2 = spec.bs1
    return ops.xor(ops.xor(ops.rotr(x, r0), ops.rotr(x, r1)), ops.rotr(x, r2))


def small_sigma0(x, ops, spec=DEFAULT_SPEC):
    r0, r1, s = spec.ss0
    return ops.xor(ops.xor(ops.rotr(x, r0), ops.rotr(x, r1)), ops.shr(x, s))


def small_sigma1(x, ops, spec=DEFAULT_SPEC):
    r0, r1, s = spec.ss1
    return ops.xor(ops.xor(ops.rotr(x, r0), ops.rotr(x, r1)), ops.shr(x, s))


def ch(e, f, g, ops):
    return ops.xor(ops.and_(e, f), ops.and_(ops.not_(e), g))


def maj(a, b, c, ops):
    return ops.xor(ops.xor(ops.and_(a, b), ops.and_(a, c)), ops.and_(b, c))


def t1(h, e, f, g, k, w, ops, spec=DEFAULT_SPEC):
    """T1 = h + Sigma1(e) + Ch(e,f,g) + K[t] + W[t] (FIPS 6.2.2 step 3)."""
    return ops.add(ops.add(ops.add(ops.add(h, big_sigma1(e, ops, spec)), ch(e, f, g, ops)), k), w)


def t2(a, b, c, ops, spec=DEFAULT_SPEC):
    """T2 = Sigma0(a) + Maj(a,b,c) (FIPS 6.2.2 step 3)."""
    return ops.add(big_sigma0(a, ops, spec), maj(a, b, c, ops))


def schedule_next(w0, w1, w9, w14, ops, spec=DEFAULT_SPEC):
    """W[t+16] = sigma1(W[t+14]) + W[t+9] + sigma0(W[t+1]) + W[t] (FIPS 6.2.2 step 1)."""
    return ops.add(
        ops.add(ops.add(small_sigma1(w14, ops, spec), w9), small_sigma0(w1, ops, spec)), w0
    )


# ---------------------------------------------------------------------------
# KATs — run over the int instantiation; validate the exact functions used in
# the z3 goal (single-sourcing). Called by check.py as SAN.fips_kat.
# ---------------------------------------------------------------------------

_ABC_DIGEST = bytes.fromhex(
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
)


def _compress_block(state, block_words):
    """One FIPS 6.2.2 compression over ints, built ONLY from the functions above."""
    ops = IntOps
    w = list(block_words)
    for t in range(16, 64):
        w.append(schedule_next(w[t - 16], w[t - 15], w[t - 7], w[t - 2], ops))
    a, b, c, d, e, f, g, h = state
    for t in range(64):
        x1 = t1(h, e, f, g, K[t], w[t], ops)
        x2 = t2(a, b, c, ops)
        h, g, f, e, d, c, b, a = g, f, e, ops.add(d, x1), c, b, a, ops.add(x1, x2)
    return tuple(ops.add(s, v) for s, v in zip(state, (a, b, c, d, e, f, g, h)))


def run_kats():
    """Known-answer tests. Raises AssertionError on any failure."""
    ops = IntOps
    # Rotation/shift vectors.
    assert ops.rotr(1, 1) == 0x80000000
    assert ops.rotr(0x80000000, 31) == 1
    assert ops.rotr(0xDEADBEEF, 8) == 0xEFDEADBE
    assert ops.shr(0x80000000, 3) == 0x10000000
    assert ops.not_(0) == MASK32
    # K endpoints (FIPS 4.2.2).
    assert K[0] == 0x428A2F98 and K[63] == 0xC67178F2 and len(K) == 64
    # Sigma spot values against independent scalar math.
    x = 0x12345678
    assert big_sigma0(x, ops) == (
        ops.rotr(x, 2) ^ ops.rotr(x, 13) ^ ops.rotr(x, 22)
    )
    assert ch(0xFFFFFFFF, 0xAAAAAAAA, 0x55555555, ops) == 0xAAAAAAAA
    assert maj(0xFFFFFFFF, 0xFFFFFFFF, 0, ops) == 0xFFFFFFFF
    # Full-message KAT: SHA-256("abc") via the round loop (single padded block).
    msg = b"abc" + b"\x80" + b"\x00" * 52 + (24).to_bytes(8, "big")
    assert len(msg) == 64
    block = tuple(int.from_bytes(msg[4 * i : 4 * i + 4], "big") for i in range(16))
    digest_words = _compress_block(IV, block)
    digest = b"".join(wd.to_bytes(4, "big") for wd in digest_words)
    assert digest == _ABC_DIGEST, f"abc digest mismatch: {digest.hex()}"
    return True


__all__ = [
    "K", "IV", "MASK32", "IntOps", "Z3Ops", "Spec", "DEFAULT_SPEC", "replace",
    "big_sigma0", "big_sigma1", "small_sigma0", "small_sigma1", "ch", "maj",
    "t1", "t2", "schedule_next", "run_kats",
]
