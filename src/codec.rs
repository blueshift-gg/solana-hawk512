//! HAWK-512 wire decoding: Golomb–Rice decompression (spec Alg 7),
//! `DecodePublic` (Alg 9), `DecodeSignature` (Alg 11), and the SHAKE256
//! hashing helpers used by `HawkVerify` (Alg 20, lines 9–11).
//!
//! Bit ordering follows FIPS 202 / the HAWK spec: a byte `b` maps to the
//! 8-bit sequence `b0 b1 … b7` with `b = Σ bᵢ·2ⁱ` (LSB-first), and
//! `DecodeInt(x₀…x_{k−1}) = Σ xᵢ·2ⁱ`. All sub-sequence boundaries used by
//! HAWK-512 are byte-aligned (salt = 192 bits, the q00/q01 split is padded
//! to a byte boundary), so the decoders operate on byte slices with an
//! implicit LSB-first bit index.

use crate::{
    HIGH_00, HIGH_01, HIGH_S1, HPUB_LEN, LOW_00, LOW_01, LOW_S1, N, PUBKEY_LEN, SALT_LEN,
    SIGNATURE_LEN,
};
use solana_shake256::Shake256;

/// LSB-first bit `idx` of a byte slice (bit sequence per FIPS 202).
///
/// Every caller (`decompress_gr`, `decode_int`, the byte-boundary scan in
/// `decode_public`) only invokes this after an up-front length check that
/// guarantees `idx < buf.len()*8`, i.e. `idx >> 3 < buf.len()`. Asserting
/// that lets the SBF codegen drop the per-bit bounds check — `bit()` is
/// called ~15k times decoding one HAWK-512 (pubkey + signature).
#[inline(always)]
pub(crate) fn bit(buf: &[u8], idx: usize) -> u32 {
    // SAFETY: callers guarantee `idx >> 3 < buf.len()` (see above).
    unsafe { core::hint::assert_unchecked((idx >> 3) < buf.len()) };
    ((buf[idx >> 3] >> (idx & 7)) & 1) as u32
}

/// `DecompressGR` (spec Algorithm 7). `y` is the bit sequence (LSB-first
/// over the byte slice), `k` the number of integers to decode, `low`/`high`
/// the Golomb–Rice sizes. Writes `k` signed integers into `out[..k]` and
/// returns `Some(j)` where `j` is the number of bits consumed, or `None`
/// (⊥) on any malformed input. In all HAWK uses `high ≤ low + 4`, so the
/// variable (unary) part of any coefficient is at most 16 bits.
pub(crate) fn decompress_gr<const K: usize, const LOW: usize, const HIGH: usize>(
    y: &[u8],
    out: &mut [i32; N],
) -> Option<usize> {
    // `K`/`LOW`/`HIGH` are const-generic: they are fixed per call site
    // (q00: 256/5/9, q01 & s1: 512/9/12 or 512/5/9), so the loop bounds,
    // `mask`, `z_max` and the length check all const-fold.
    const { assert!(K <= N) };
    let k = K;
    let low = LOW;
    let high = HIGH;
    let len_bits = y.len() * 8;
    // Alg 7 line 1: need at least the sign bits, the low parts, and one
    // terminating '1' bit per integer.
    if len_bits < k * (low + 2) {
        return None;
    }

    // Lines 3–4: the `low` fixed bits of each integer (after the k sign
    // bits). `low ≤ 9` and the LSB-first window starts at bit `base`, so it
    // spans at most two bytes — extract it with a single 2-byte word read
    // and a shift+mask instead of `low` per-bit reads (the same bits, far
    // fewer SBF ops). The initial length check guarantees bit `base` is
    // in range; the high byte is only consulted when the window actually
    // crosses into it (then it is in range too), else it reads as 0.
    let mask = (1u32 << low) - 1;
    // `needless_range_loop`: the `.iter_mut().take(k).enumerate()` form is
    // **measured +1.5k CU on the raw path** (3× `decompress_gr` for
    // q00/q01/s1) — the index loop is the tighter SBF lowering here. Kept
    // deliberately; not an oversight.
    #[allow(clippy::needless_range_loop)]
    for i in 0..k {
        let base = i * low + k;
        let bi = base >> 3;
        // SAFETY: `base < len_bits` ⇒ `bi < y.len()` (length check above).
        unsafe { core::hint::assert_unchecked(bi < y.len()) };
        let b0 = y[bi] as u32;
        let b1 = if bi + 1 < y.len() {
            y[bi + 1] as u32
        } else {
            0
        };
        out[i] = (((b0 | (b1 << 8)) >> (base & 7)) & mask) as i32;
    }

    // Lines 5–15: the unary (Golomb) high parts. Kept bit-serial: a
    // word-read + `trailing_zeros` form was re-measured (after profiling
    // the unary at ~23.5k CU on the prepared s1 decode) and is a net loss
    // — SBPF has no hardware count-trailing-zeros, so `trailing_zeros`
    // lowers to a costly software routine that beats the per-bit loop only
    // for s1's longer runs (prepared −0.9k) while losing on the raw path's
    // shorter q00/q01 runs (raw +4.4k). The per-bit scan is the SBF floor
    // here.
    let mut j = k * (low + 1);
    let z_max = 1usize << (high - low);
    for slot in out.iter_mut().take(k) {
        let mut z: usize = 0;
        loop {
            if j >= len_bits || z >= z_max {
                return None;
            }
            let t = bit(y, j);
            j += 1;
            if t == 1 {
                break;
            }
            z += 1;
        }
        *slot += (z as i32) << low;
    }

    // Lines 16–17: apply the sign bit. y[i] = 1 ⇒ x ← −x − 1 (ones'
    // complement), y[i] = 0 ⇒ unchanged. The k sign bits are the first k
    // bits of `y` (LSB-first, byte-packed), so load each sign byte once and
    // apply its 8 bits, rather than one `bit()` call per coefficient.
    let mut i = 0;
    while i < k {
        // SAFETY: i < k ⇒ i>>3 < ⌈k/8⌉ ≤ ⌈N/8⌉ ≤ y.len() (length check).
        unsafe { core::hint::assert_unchecked((i >> 3) < y.len()) };
        let sbyte = y[i >> 3];
        let n = if k - i < 8 { k - i } else { 8 };
        for b in 0..n {
            // SAFETY: i + b < k ≤ N.
            unsafe { core::hint::assert_unchecked(i + b < N) };
            let slot = &mut out[i + b];
            // y[i]=1 ⇒ x ← −x−1 (ones' complement) = bitwise !x in two's
            // complement; y[i]=0 ⇒ unchanged. `x ^ -s` is exactly that
            // (s=1: x^(-1)=!x; s=0: x^0=x) — bit-identical, no multiply.
            let s = ((sbyte >> b) & 1) as i32;
            *slot ^= -s;
        }
        i += 8;
    }

    Some(j)
}

/// `true` iff every bit of `buf` from `start_bit` to the end is zero.
/// HAWK signatures/keys are zero-padded to a fixed size, so this scans
/// hundreds–thousands of bits; do the byte-aligned tail 8 bytes at a time
/// (one unaligned u64 load + compare) instead of bit-by-bit.
#[inline]
pub(crate) fn padding_all_zero(buf: &[u8], start_bit: usize) -> bool {
    let len_bits = buf.len() * 8;
    let mut j = start_bit;
    // Finish the partial leading byte bit-by-bit.
    while j < len_bits && !j.is_multiple_of(8) {
        if (buf[j >> 3] >> (j & 7)) & 1 != 0 {
            return false;
        }
        j += 1;
    }
    let mut i = j / 8;
    while i + 8 <= buf.len() {
        // SAFETY: `i + 8 <= buf.len()`; SBF supports unaligned loads.
        let chunk = unsafe { (buf.as_ptr().add(i) as *const u64).read_unaligned() };
        if chunk != 0 {
            return false;
        }
        i += 8;
    }
    while i < buf.len() {
        if buf[i] != 0 {
            return false;
        }
        i += 1;
    }
    true
}

/// `DecodeInt(y[off : off+v])` — the LSB-first integer in a `v`-bit window.
#[inline]
fn decode_int(y: &[u8], off: usize, v: usize) -> i32 {
    let mut x: i32 = 0;
    for t in 0..v {
        x |= (bit(y, off + t) as i32) << t;
    }
    x
}

/// `DecodePublic` (spec Algorithm 9). Decodes the 1024-byte HAWK-512 public
/// key into the polynomials `q00` (n coefficients, self-adjoint) and `q01`
/// (n coefficients). Enforces the canonical encoding: exact length, the
/// special extra-precision `q00[0]`, and **all** padding bits zero (between
/// q00/q01 and after q01) — a public key has a single valid encoding.
pub fn decode_public(pub_: &[u8], q00: &mut [i32; N], q01: &mut [i32; N]) -> bool {
    if pub_.len() != PUBKEY_LEN {
        return false;
    }
    let len_bits = pub_.len() * 8;
    let v = 16 - HIGH_00;

    // q00: first n/2 coefficients via Golomb–Rice.
    let Some(mut j) = decompress_gr::<{ N / 2 }, LOW_00, HIGH_00>(pub_, q00) else {
        return false;
    };

    // q00[0] carries `v` extra low-order bits of precision.
    if len_bits < j + v {
        return false;
    }
    q00[0] = (q00[0] << v) + decode_int(pub_, j, v);
    j += v;

    // Pad to the next byte boundary; the padding bits must be zero.
    while j % 8 != 0 {
        if j >= len_bits || bit(pub_, j) != 0 {
            return false;
        }
        j += 1;
    }

    // q00 is self-adjoint: q00[n/2] = 0 and q00[i] = −q00[n−i].
    q00[N / 2] = 0;
    for i in (N / 2 + 1)..N {
        q00[i] = -q00[N - i];
    }

    // q01: all n coefficients, from the (byte-aligned) remainder. Decoded
    // straight into the caller's buffer — no extra 2 KiB stack temporary.
    let Some(jp) = decompress_gr::<N, LOW_01, HIGH_01>(&pub_[j / 8..], q01) else {
        return false;
    };
    j += jp;

    // All remaining bits (trailing padding) must be zero.
    padding_all_zero(pub_, j)
}

/// `DecodeSignature` (spec Algorithm 11). Splits the 555-byte HAWK-512
/// signature into the 24-byte `salt` and the polynomial `s1` (n
/// coefficients, Golomb–Rice). Enforces exact length and all-zero trailing
/// padding. Returns the salt byte range start (always 0) implicitly via
/// `salt` written, and `s1` written; `false` (⊥) on malformed input.
pub fn decode_signature<'a>(sig: &'a [u8], s1: &mut [i32; N]) -> Option<&'a [u8]> {
    if sig.len() != SIGNATURE_LEN {
        return None;
    }
    // salt = first SALT_LEN bytes (saltlen = 192 bits, byte-aligned).
    let salt = &sig[..SALT_LEN];

    // s1 from the byte-aligned remainder.
    let jp = decompress_gr::<N, LOW_S1, HIGH_S1>(&sig[SALT_LEN..], s1)?;
    let j = jp + SALT_LEN * 8;

    // All remaining bits must be zero padding.
    if padding_all_zero(sig, j) {
        Some(salt)
    } else {
        None
    }
}

/// `sym-break(w)` (spec §3.5.2): `true` iff `w` is non-zero and its first
/// non-zero coefficient is positive. The all-zero polynomial is `false`.
pub fn sym_break(w: &[i32; N]) -> bool {
    for &x in w.iter() {
        if x > 0 {
            return true;
        }
        if x < 0 {
            return false;
        }
    }
    false
}

/// `hpub ← SHAKE256(pub)[0 : HPUB_LEN]` (Alg 20 line 9).
pub fn compute_hpub(pub_: &[u8]) -> [u8; HPUB_LEN] {
    let mut s = Shake256::new();
    s.absorb(pub_);
    s.finalize();
    let mut out = [0u8; HPUB_LEN];
    s.squeeze(&mut out);
    out
}

/// `M ← SHAKE256(m ‖ hpub)[0 : 512]` (Alg 20 line 10) — 64 bytes.
pub fn compute_m(message: &[u8], hpub: &[u8; HPUB_LEN]) -> [u8; 64] {
    let mut s = Shake256::new();
    s.absorb(message);
    s.absorb(hpub);
    s.finalize();
    let mut out = [0u8; 64];
    s.squeeze(&mut out);
    out
}

/// `(h0, h1) ← SHAKE256(M ‖ salt)[0 : 2n]` (Alg 20 line 11). The first
/// `n/8` squeezed bytes are the binary polynomial `h0`, the next `n/8` are
/// `h1`, both LSB-first per byte. Outputs as `{0,1}`-valued `i32` arrays so
/// they slot straight into the integer verify arithmetic (`w1 = h1 − 2s1`,
/// RebuildS0's `h0`).
/// Fuses `w1 ← h1 − 2·s1` (Alg 20 line 12) into the `h1` bit-expansion:
/// `h1` is *only* ever used to form `w1`, so it is never materialised — the
/// second squeezed half is expanded straight into `w1[i] = h1ᵢ − 2·s1[i]`.
/// Saves the `h1` array and a full N-element pass.
pub fn compute_h(m: &[u8; 64], salt: &[u8], h0: &mut [i32; N], w1: &mut [i32; N], s1: &[i32; N]) {
    let mut s = Shake256::new();
    s.absorb(m);
    s.absorb(salt);
    s.finalize();
    let mut h = [0u8; 2 * N / 8];
    s.squeeze(&mut h);
    // Expand a byte at a time: load each packed byte once and fan its 8
    // bits out to 8 `i32` slots. `chunks_exact_mut(8)` makes each chunk a
    // statically-len-8 slice, so the inner `k < 8` writes are
    // bounds-check-free (no `oct*8+k` index arithmetic, no `enumerate`).
    // (A squeeze→expand fusion via `squeeze_lanes` measured only −94 CU —
    // noise — for added complexity, so the buffered form is kept.)
    let (hb0, hb1) = h.split_at(N / 8);
    for (chunk, &byte) in h0.chunks_exact_mut(8).zip(hb0.iter()) {
        for (k, slot) in chunk.iter_mut().enumerate() {
            *slot = ((byte >> k) & 1) as i32;
        }
    }
    // h1 fused into w1 = h1 − 2·s1.
    for ((wch, sch), &byte) in w1
        .chunks_exact_mut(8)
        .zip(s1.chunks_exact(8))
        .zip(hb1.iter())
    {
        for (k, (w, &sv)) in wch.iter_mut().zip(sch.iter()).enumerate() {
            *w = ((byte >> k) & 1) as i32 - 2 * sv;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Round-trip a known integer sequence through a hand-written CompressGR
    // (spec Alg 6) and confirm decompress_gr recovers it.
    fn compress_gr(xs: &[i32], low: usize, high: usize) -> Vec<u8> {
        let k = xs.len();
        let mut bits: Vec<u8> = Vec::new();
        let mut vv: Vec<u32> = Vec::with_capacity(k);
        // sign bits
        for &x in xs {
            bits.push((x < 0) as u8);
        }
        for &x in xs {
            let s = (x < 0) as i64;
            let val = (x as i64) - s * (2 * x as i64 + 1);
            assert!(val >= 0 && val < (1i64 << high));
            vv.push(val as u32);
        }
        // low parts
        for &val in &vv {
            for t in 0..low {
                bits.push(((val >> t) & 1) as u8);
            }
        }
        // high (unary) parts
        for &val in &vv {
            let z = val >> low;
            bits.resize(bits.len() + z as usize, 0);
            bits.push(1);
        }
        // pack LSB-first into bytes
        let mut out = vec![0u8; bits.len().div_ceil(8)];
        for (i, b) in bits.iter().enumerate() {
            out[i >> 3] |= b << (i & 7);
        }
        out
    }

    #[test]
    fn gr_round_trip() {
        // Includes values whose Golomb code has a non-trivial unary run
        // (z = val >> low > 0): 32→z=1, 200→z=6, 511→z=15 for low=5.
        let xs: [i32; 13] = [0, 1, -1, 5, -5, 31, -31, 7, 32, -200, 200, 511, -511];
        let buf = compress_gr(&xs, LOW_S1, HIGH_S1);
        let mut out = [0i32; N];
        let j = decompress_gr::<13, LOW_S1, HIGH_S1>(&buf, &mut out).unwrap();
        assert_eq!(&out[..xs.len()], &xs[..]);
        assert!(j <= buf.len() * 8);

        // Truncating the buffer must be rejected (⊥), never panic.
        for cut in 1..buf.len() {
            let _ = decompress_gr::<13, LOW_S1, HIGH_S1>(&buf[..cut], &mut out);
        }
    }
}
