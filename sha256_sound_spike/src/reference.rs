//! Independent scalar FIPS-180-4 SHA-256 reference implementation.
//!
//! This is the ground truth the AIR witness is generated from and KAT-checked against.
//! Written directly from FIPS-180-4 (sections 4.1.2, 4.2.2, 5.3.3, 6.2.2) — deliberately
//! NOT derived from the AIR or the decoded PR #1425 witness code, so that a bug in either
//! shows up as a KAT/constraint mismatch instead of being replicated on both sides.

/// FIPS-180-4 section 4.2.2: the 64 round constants (first 32 bits of the fractional parts
/// of the cube roots of the first 64 primes).
pub const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
    0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
    0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
    0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
    0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
    0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
    0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
    0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
    0xc67178f2,
];

/// FIPS-180-4 section 5.3.3: initial hash value H(0).
pub const IV: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
    0x5be0cd19,
];

#[inline]
pub fn big_sigma_0(x: u32) -> u32 {
    x.rotate_right(2) ^ x.rotate_right(13) ^ x.rotate_right(22)
}
#[inline]
pub fn big_sigma_1(x: u32) -> u32 {
    x.rotate_right(6) ^ x.rotate_right(11) ^ x.rotate_right(25)
}
#[inline]
pub fn small_sigma_0(x: u32) -> u32 {
    x.rotate_right(7) ^ x.rotate_right(18) ^ (x >> 3)
}
#[inline]
pub fn small_sigma_1(x: u32) -> u32 {
    x.rotate_right(17) ^ x.rotate_right(19) ^ (x >> 10)
}
#[inline]
pub fn ch(e: u32, f: u32, g: u32) -> u32 {
    (e & f) ^ (!e & g)
}
#[inline]
pub fn maj(a: u32, b: u32, c: u32) -> u32 {
    (a & b) ^ (a & c) ^ (b & c)
}

/// Message schedule, EXTENDED to 80 words (not the FIPS 64): the PR #1425 round AIR keeps a
/// full 16-word look-ahead window on every row, so the round at t needs W[t..t+16] and the
/// final row (t=63) references W[64..79]. Words 64..79 are produced by simply continuing the
/// FIPS 6.2.2 recurrence; they never influence the digest.
pub fn message_schedule_80(block: &[u32; 16]) -> [u32; 80] {
    let mut w = [0u32; 80];
    w[..16].copy_from_slice(block);
    for t in 16..80 {
        w[t] = small_sigma_1(w[t - 2])
            .wrapping_add(w[t - 7])
            .wrapping_add(small_sigma_0(w[t - 15]))
            .wrapping_add(w[t - 16]);
    }
    w
}

/// One FIPS-180-4 6.2.2 round: state (a..h) x W[t] x K[t] -> next state.
pub fn round(state: [u32; 8], wt: u32, kt: u32) -> [u32; 8] {
    let [a, b, c, d, e, f, g, h] = state;
    let t1 = h
        .wrapping_add(big_sigma_1(e))
        .wrapping_add(ch(e, f, g))
        .wrapping_add(kt)
        .wrapping_add(wt);
    let t2 = big_sigma_0(a).wrapping_add(maj(a, b, c));
    [t1.wrapping_add(t2), a, b, c, d.wrapping_add(t1), e, f, g]
}

/// Full compression: returns (state_after_64_rounds, digest_state_after_feedforward).
pub fn compress(h_in: [u32; 8], block: &[u32; 16]) -> ([u32; 8], [u32; 8]) {
    let w = message_schedule_80(block);
    let mut state = h_in;
    for t in 0..64 {
        state = round(state, w[t], K[t]);
    }
    let mut digest = [0u32; 8];
    for i in 0..8 {
        digest[i] = h_in[i].wrapping_add(state[i]);
    }
    (state, digest)
}

/// SHA-256 of a byte message (single-purpose padding per FIPS-180-4 5.1.1; enough for KATs).
pub fn sha256(msg: &[u8]) -> [u32; 8] {
    let bit_len = (msg.len() as u64) * 8;
    let mut padded = msg.to_vec();
    padded.push(0x80);
    while padded.len() % 64 != 56 {
        padded.push(0);
    }
    padded.extend_from_slice(&bit_len.to_be_bytes());

    let mut h = IV;
    for chunk in padded.chunks_exact(64) {
        let mut block = [0u32; 16];
        for (i, word) in chunk.chunks_exact(4).enumerate() {
            block[i] = u32::from_be_bytes(word.try_into().unwrap());
        }
        (_, h) = compress(h, &block);
    }
    h
}

#[cfg(test)]
mod tests {
    use super::*;

    /// FIPS-180-4 / NIST CAVP KAT: SHA-256("abc")
    /// = ba7816bf 8f01cfea 414140de 5dae2223 b00361a3 96177a9c b410ff61 f20015ad
    /// (independently re-verified against python3 hashlib).
    #[test]
    fn kat_abc() {
        assert_eq!(
            sha256(b"abc"),
            [
                0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223, 0xb00361a3, 0x96177a9c,
                0xb410ff61, 0xf20015ad
            ]
        );
    }

    /// NIST KAT: SHA-256("") — empty message.
    #[test]
    fn kat_empty() {
        assert_eq!(
            sha256(b""),
            [
                0xe3b0c442, 0x98fc1c14, 0x9afbf4c8, 0x996fb924, 0x27ae41e4, 0x649b934c,
                0xa495991b, 0x7852b855
            ]
        );
    }

    /// NIST KAT: SHA-256("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")
    /// — two-block message, exercises chaining.
    #[test]
    fn kat_two_block() {
        assert_eq!(
            sha256(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"),
            [
                0x248d6a61, 0xd20638b8, 0xe5c02693, 0x0c3e6039, 0xa33ce459, 0x64ff2167,
                0xf6ecedd4, 0x19db06c1
            ]
        );
    }
}
