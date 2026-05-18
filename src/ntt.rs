//! Negacyclic NTT modulo the two HAWK primes and `PolyQnorm` — spec
//! Algorithms 19, 21, 22 (HAWK v1.1 §3.6, §4.1.1).
//!
//! `PolyQnorm` returns `n·‖w‖²_Q mod p`. HAWK verification runs it with
//! `p₁ = 2147473409` and `p₂ = 2147389441`; for a valid signature the true
//! integer `n·‖w‖²_Q` is far below both primes, so the two residues must be
//! equal (and equal to the true value). The NTT ordering convention is
//! irrelevant to the final scalar as long as `NTTadj` matches it — here
//! `NTT` is the classic bit-reversal transform (twiddle `Γ[i]=γ^rev(i)`,
//! `γ` a primitive 2n-th root) and `NTTadj` is whole-array reversal.
//!
//! Coefficients are kept in `[0, p) ⊂ [0, 2³¹)` so they fit `u32`; only
//! the multiply uses a `u64` temporary. All 512-element buffers are
//! caller-owned scratch (Solana SBF caps each stack frame at 4 KiB); the
//! twiddle tables are `static` (data segment, not stack).

use crate::{LOGN, N};

pub const P1: u64 = 2147473409;
pub const P2: u64 = 2147389441;

// Measured on Mollusk SBF: this target has a **native 64-bit div/mod
// opcode**, so a literal `% p` is a single cheap instruction — it beats
// both u128 Barrett (~3.5×) and 64-bit Montgomery (extra mul/shift +
// per-call prime-selector branch). So all modular arithmetic is plain
// `(a·b) % p`; `a, b < p < 2³¹ ⇒ a·b < 2⁶²`, no overflow.
#[inline(always)]
const fn mulmod(a: u64, b: u64, p: u64) -> u64 {
    (a * b) % p
}

const fn powmod(mut base: u64, mut exp: u64, p: u64) -> u64 {
    base %= p;
    let mut acc = 1u64;
    while exp > 0 {
        if exp & 1 == 1 {
            acc = mulmod(acc, base, p);
        }
        base = mulmod(base, base, p);
        exp >>= 1;
    }
    acc
}

/// Modular inverse via Fermat (p prime). `None` if `x ≡ 0` (q00 not
/// invertible mod p ⇒ reject the signature).
#[inline]
fn inv(x: u64, p: u64) -> Option<u64> {
    if x == 0 {
        return None;
    }
    Some(powmod(x, p - 2, p))
}

const fn bitrev(x: usize, l: usize) -> usize {
    let mut y = 0;
    let mut i = 0;
    while i < l {
        y |= ((x >> i) & 1) << (l - i - 1);
        i += 1;
    }
    y
}

/// Primitive 2n-th root of unity mod `p` (smallest base whose
/// `((p-1)/2n)`-th power has order exactly 2n), per `p_ntt_find_h`.
const fn find_root(p: u64) -> u64 {
    let two_n = (2 * N) as u64;
    let r = (p - 1) / two_n;
    let mut x = 2u64;
    loop {
        let y = powmod(x, r, p);
        if powmod(y, N as u64, p) == p - 1 {
            return y;
        }
        x += 1;
    }
}

/// Twiddle table `Γ[i] = γ^rev_logn(i) mod p`, `i ∈ [0, n)`.
const fn calc_w(p: u64) -> [u32; N] {
    let h = find_root(p);
    let mut w = [0u32; N];
    let mut i = 0;
    while i < N {
        w[i] = powmod(h, bitrev(i, LOGN) as u64, p) as u32;
        i += 1;
    }
    w
}

static W1: [u32; N] = calc_w(P1);
static W2: [u32; N] = calc_w(P2);

#[inline(always)]
fn w_table(p: u64) -> &'static [u32; N] {
    if p == P1 { &W1 } else { &W2 }
}

/// Reduce a signed coefficient into `[0, p)`. Every coefficient fed to
/// `PolyQnorm` (decoded q00/q01/s1, w1 = h1−2s1, w0 from RebuildS0) is
/// bounded well under 2¹⁶ ≪ p, so `|x| < p` always holds and the reduction
/// is a single sign-conditional add — no division.
#[inline(always)]
fn red(x: i32, p: u64) -> u32 {
    let x = x as i64;
    (if x >= 0 { x } else { x + p as i64 }) as u32
}

/// One NTT level with the half-block size `$l` as a **compile-time
/// constant**. That makes the inner butterfly count (`$l`) and the block
/// stride (`2·$l`) constant, so LLVM unrolls the inner loop and
/// constant-folds the addressing — eliminating the per-block / per-butterfly
/// branch overhead that dominates the many-tiny-block inner levels. SBF has
/// a cheap native 64-bit `mod`, so a single `% p` still beats conditional
/// subtraction (measured ~8% slower); only the per-jump bookkeeping is
/// removed here, not the arithmetic.
macro_rules! ntt_level {
    ($f:expr, $w:expr, $p:expr, $wi:ident, $l:expr, $red:expr) => {{
        const L: usize = $l;
        let p = $p;
        // `red(v, p)` is either `v % p` (full level) or `v` (lazy level —
        // the additive reduction is deferred). It is a trivial local
        // closure so LLVM inlines it to nothing.
        let red = $red;
        let mut i = 0usize;
        while i < N {
            $wi += 1;
            // `wi` runs 1..=N−1 over a whole NTT (Σ blocks = N−1); `i+2L ≤ N`
            // since `i` steps by `2L | N`. Assert both so the static-table
            // read and the block slice drop their bounds checks.
            unsafe {
                core::hint::assert_unchecked($wi < N);
                core::hint::assert_unchecked(i + 2 * L <= N);
            }
            let z = $w[$wi] as u64;
            // With `L` a compile-time constant the 2-way zip has a constant
            // trip count, so LLVM unrolls it optimally and elides the bounds
            // checks via `split_at_mut`. (A hand ×4 unroll and a raw
            // two-pointer walk both measured byte-for-byte identical — LLVM
            // canonicalises the loop form on SBF — so the clean, `unsafe`-
            // free iterator is kept.)
            let (lo, hi) = $f[i..i + 2 * L].split_at_mut(L);
            for (a, b) in lo.iter_mut().zip(hi.iter_mut()) {
                let x = *a as u64;
                let y = (*b as u64 * z) % p;
                *a = red(x + y, p) as u32;
                *b = red(x + p - y, p) as u32;
            }
            i += 2 * L;
        }
    }};
}

#[inline(always)]
fn full(v: u64, p: u64) -> u64 {
    v % p
}
#[inline(always)]
fn lazy(v: u64, _p: u64) -> u64 {
    v
}

/// Forward negacyclic NTT in place (spec Alg 21, `p_ntt` convention).
///
/// The 9 levels (`l = 256, 128, … , 1` for `N = 512`) are emitted with `l`
/// constant so each is fully addressing-folded ([`ntt_level`]).
///
/// **Lazy reduction.** The twiddle product is always reduced
/// (`y = b·z mod p ∈ [0, p)`), but the two *additive* reductions are
/// deferred on alternate levels. Inputs to a lazy level are in `[0, p)`
/// (it always follows a `full` level / the `red()` init), so its outputs
/// `x+y` and `x+p−y` lie in `[0, 2p)`. With the HAWK primes
/// `2p < 2³²` (`2·p₁ = 4 294 946 818`), so the lazy values still fit the
/// `u32` lane *exactly*; the next (`full`) level reduces them before the
/// bound could grow again, and its multiplicand stays `< 2p`, so
/// `b·z < 2p·p < 2⁶⁴`. Level 9 is `full`, so the result is the canonical
/// `[0, p)` — **bit-identical** to reducing every level (deferred modular
/// reduction is exact when no overflow occurs), leaving every downstream
/// consumer unchanged. Saves the two additive `% p` on 4 of 9 levels.
#[inline(never)]
fn ntt(f: &mut [u32; N], p: u64) {
    let w = w_table(p);
    let mut wi = 0usize;
    ntt_level!(f, w, p, wi, 256, lazy);
    ntt_level!(f, w, p, wi, 128, full);
    ntt_level!(f, w, p, wi, 64, lazy);
    ntt_level!(f, w, p, wi, 32, full);
    ntt_level!(f, w, p, wi, 16, lazy);
    ntt_level!(f, w, p, wi, 8, full);
    ntt_level!(f, w, p, wi, 4, lazy);
    ntt_level!(f, w, p, wi, 2, full);
    ntt_level!(f, w, p, wi, 1, full);
}

/// First NTT level reading the **signed** source with `red` applied on the
/// fly (level 1 is `lazy`, `L = N/2`, a single block). Fuses the
/// `c[i] = red(src[i], p)` conversion pass into the first butterfly so the
/// working buffer is written once, not twice — saves a full N-element
/// write+read per NTT (×6 on-chain NTTs).
macro_rules! ntt_level_first {
    ($src:expr, $f:expr, $w:expr, $p:expr, $wi:ident) => {{
        const L: usize = N / 2;
        let p = $p;
        $wi += 1;
        // Single block (`2L = N`); `wi = 1`.
        unsafe { core::hint::assert_unchecked($wi < N) };
        let z = $w[$wi] as u64;
        let (slo, shi) = $src.split_at(L);
        let (flo, fhi) = $f.split_at_mut(L);
        for (((fa, fb), &sa), &sb) in flo
            .iter_mut()
            .zip(fhi.iter_mut())
            .zip(slo.iter())
            .zip(shi.iter())
        {
            let x = red(sa, p) as u64;
            let y = (red(sb, p) as u64 * z) % p;
            // Lazy (level 1): defer the additive `% p`; x,y ∈ [0,p) ⇒
            // results ∈ [0,2p) < 2³², fits the u32 lane.
            *fa = (x + y) as u32;
            *fb = (x + p - y) as u32;
        }
    }};
}

/// Fused conversion + NTT: equivalent to `for i { f[i] = red(src[i], p) }`
/// then [`ntt`], but the first level reads `src` directly (one fewer
/// full-array pass). `src`/`f` are distinct buffers (no aliasing).
#[inline(never)]
fn ntt_conv(src: &[i32; N], f: &mut [u32; N], p: u64) {
    let w = w_table(p);
    let mut wi = 0usize;
    ntt_level_first!(src, f, w, p, wi); // L1 (lazy, reads src + red)
    ntt_level!(f, w, p, wi, 128, full); // L2
    ntt_level!(f, w, p, wi, 64, lazy); // L3
    ntt_level!(f, w, p, wi, 32, full); // L4
    ntt_level!(f, w, p, wi, 16, lazy); // L5
    ntt_level!(f, w, p, wi, 8, full); // L6
    ntt_level!(f, w, p, wi, 4, lazy); // L7
    ntt_level!(f, w, p, wi, 2, full); // L8
    ntt_level!(f, w, p, wi, 1, full); // L9
}

// Shoup / precomputed-quotient Barrett reduction was measured here and is
// **dramatically slower on SBF** (all-`full` Shoup: prepared ~516k vs
// native ~435k): SBF's native 64-bit `%`/`/` is a single ~1-CU op, while
// Shoup needs 3 multiplies + shift + subtract + a conditional (SBF has no
// hardware multiply-high to make Barrett cheap). Kept native everywhere.

/// `PolyQnorm` (spec Alg 19): `n·‖w‖²_Q mod p`, or `None` if `q̂00` has a
/// zero NTT coefficient.
///
/// Five `u32×512` (2 KiB) NTT buffers must be live simultaneously
/// (`a=q̂00`, `b=q̂01`, `c=ŵ0→ê`, `d=ŵ1`, `e=d̂`). Solana SBF caps a single
/// stack frame at 4 KiB, so each buffer is the sole large local of its own
/// `#[inline(never)]` frame, threaded inward by reference
/// (`pq_a`→`pq_b`→`pq_c`→`pq_d`→`pq_e`).
#[inline(never)]
fn poly_qnorm(q00: &[i32; N], q01: &[i32; N], w0: &[i32; N], w1: &[i32; N], p: u64) -> Option<u64> {
    pq_a(q00, q01, w0, w1, p)
}

/// Owns `a = q̂00`.
#[inline(never)]
fn pq_a(q00: &[i32; N], q01: &[i32; N], w0: &[i32; N], w1: &[i32; N], p: u64) -> Option<u64> {
    let mut a = [0u32; N];
    ntt_conv(q00, &mut a, p);
    pq_b(q01, w0, w1, p, &a)
}

/// Owns `b = q̂01`.
#[inline(never)]
fn pq_b(q01: &[i32; N], w0: &[i32; N], w1: &[i32; N], p: u64, a: &[u32; N]) -> Option<u64> {
    let mut b = [0u32; N];
    ntt_conv(q01, &mut b, p);
    pq_c(w0, w1, p, a, &b)
}

/// Owns `c = ŵ0` (later overwritten with `ê`).
#[inline(never)]
fn pq_c(w0: &[i32; N], w1: &[i32; N], p: u64, a: &[u32; N], b: &[u32; N]) -> Option<u64> {
    let mut c = [0u32; N];
    ntt_conv(w0, &mut c, p);
    pq_d(w1, p, a, b, &mut c)
}

/// Owns `d = ŵ1`.
#[inline(never)]
fn pq_d(w1: &[i32; N], p: u64, a: &[u32; N], b: &[u32; N], c: &mut [u32; N]) -> Option<u64> {
    let mut d = [0u32; N];
    ntt_conv(w1, &mut d, p);
    pq_e(p, a, b, c, &d)
}

/// Owns `e = d̂`; computes `ê`, the `ĉ` sum, and returns `Σ ĉ[i] mod p`.
#[inline(never)]
fn pq_e(p: u64, a: &[u32; N], b: &[u32; N], c: &mut [u32; N], d: &[u32; N]) -> Option<u64> {
    let mut e = [0u32; N];

    // d̂ ← ŵ1 / q̂00, via batch inversion (Montgomery's trick): instead of
    // N Fermat inverses (≈ N·log p modmuls), one Fermat inverse plus two
    // linear passes. `e` doubles as the prefix-product scratch (each slot
    // overwritten with d̂[i] only after it is last read), so no extra
    // stack frame is needed.
    let mut acc = 1u64;
    for (ei, &ai) in e.iter_mut().zip(a.iter()) {
        acc = mulmod(acc, ai as u64, p);
        *ei = acc as u32; // e[i] = Π_{k≤i} q̂00[k]
    }
    // A zero product ⇒ some q̂00[i] = 0 (p prime) ⇒ q00 not invertible
    // mod p ⇒ reject.
    let mut acc = inv(acc, p)?; // inverse of the full product
    let mut i = N;
    while i > 0 {
        i -= 1;
        // i ∈ [0, N) here; tell the optimizer so e[i-1]/a[i]/d[i]/e[i]
        // need no bounds checks.
        unsafe { core::hint::assert_unchecked(i < N) };
        let prefix = if i == 0 { 1 } else { e[i - 1] as u64 };
        let inv_ai = mulmod(acc, prefix, p); // = q̂00[i]⁻¹
        acc = mulmod(acc, a[i] as u64, p); // fold out a[i]
        let dh = mulmod(d[i] as u64, inv_ai, p); // d̂[i]
        // Fuse ê[i] ← ŵ0[i] + d̂[i]·q̂01[i] into this backward pass: it only
        // needs d̂[i]/b[i]/c[i] (all in hand), and reads `e[i-1]` (still the
        // prefix product, overwritten only at the future step i-1) — so
        // writing e[i]=d̂[i] here is safe and saves a whole N-pass. ê is
        // left lazily reduced in `[0, 2p) < 2³²` (it is only ever read
        // inside a `mulmod` in the ĉ sum), saving N reductions.
        e[i] = dh as u32;
        c[i] = (c[i] as u64 + mulmod(dh, b[i] as u64, p)) as u32;
    }
    // ĉ ← q̂00·ê·adj(ê) + d̂·adj(ŵ1);  r ← Σ ĉ[i]   (NTTadj = reversal,
    // i.e. the `.rev()` iterators give the [N−1−i] terms).
    // Sum of 2N reduced terms (each < p) stays < 2N·p ≈ 2⁴¹: accumulate
    // without per-iteration reduction, one exact `% p` at the end.
    let mut r = 0u64;
    for ((((&ai, &ci), &ei), &adj_e), &adj_w1) in a
        .iter()
        .zip(c.iter())
        .zip(e.iter())
        .zip(c.iter().rev())
        .zip(d.iter().rev())
    {
        let t0 = mulmod(mulmod(ai as u64, ci as u64, p), adj_e as u64, p);
        let t1 = mulmod(ei as u64, adj_w1 as u64, p);
        r += t0 + t1;
    }
    Some(r % p)
}

/// Final step of `HawkVerify` (spec Alg 20, lines 18–24). `true` iff the
/// dual-prime `PolyQnorm` results agree, the common value is the true
/// integer `n·‖w‖²_Q` (divisible by `n`), and `‖w‖²_Q` is within the
/// `8n·σ²_verify` bound — checked exactly as `1600·r ≤ 13307904`
/// (σ_verify = 57/40, 8n = 4096 ⇒ 8n·σ² = 13307904/1600 = 8317.44).
/// The two `PolyQnorm` calls run sequentially, so their per-prime frame
/// chains never coexist.
#[inline(never)]
pub fn qnorm_in_bound(q00: &[i32; N], q01: &[i32; N], w0: &[i32; N], w1: &[i32; N]) -> bool {
    let Some(r1) = poly_qnorm(q00, q01, w0, w1, P1) else {
        return false;
    };
    let Some(r2) = poly_qnorm(q00, q01, w0, w1, P2) else {
        return false;
    };
    if r1 != r2 {
        return false;
    }
    let r = r1;
    if !r.is_multiple_of(N as u64) {
        return false;
    }
    let r = r / (N as u64);
    1600 * (r as u128) <= 13_307_904
}

// ---- Prepared-pubkey path -------------------------------------------------
//
// q00/q01 are pubkey-only, so their per-prime NTT forms and q̂00⁻¹ can be
// precomputed once at registration (on-chain via `prepare_into`, written
// into an account) and reused. Every later verify then only NTTs the
// signature-dependent w0/w1 (2 NTTs/prime instead of 4) and skips the batch
// inversion entirely.

/// Precompute `q̂00`, `q̂00⁻¹`, `q̂01` mod `p`. `false` if `q̂00` has a zero
/// coefficient (q00 not invertible mod p — the key is unusable).
pub fn prepare_ntt(
    q00: &[i32; N],
    q01: &[i32; N],
    p: u64,
    q00n: &mut [u32; N],
    q00inv: &mut [u32; N],
    q01n: &mut [u32; N],
) -> bool {
    for (d, &s) in q00n.iter_mut().zip(q00.iter()) {
        *d = red(s, p);
    }
    ntt(q00n, p);
    for (d, &s) in q01n.iter_mut().zip(q01.iter()) {
        *d = red(s, p);
    }
    ntt(q01n, p);
    // q00inv ← batch inverse of q00n (prefix products, one Fermat inverse).
    let mut acc = 1u64;
    for (qi, &v) in q00inv.iter_mut().zip(q00n.iter()) {
        acc = mulmod(acc, v as u64, p);
        *qi = acc as u32;
    }
    let Some(mut acc) = inv(acc, p) else {
        return false;
    };
    let mut i = N;
    while i > 0 {
        i -= 1;
        unsafe { core::hint::assert_unchecked(i < N) };
        let prefix = if i == 0 { 1 } else { q00inv[i - 1] as u64 };
        let invi = mulmod(acc, prefix, p);
        acc = mulmod(acc, q00n[i] as u64, p);
        q00inv[i] = invi as u32;
    }
    true
}

/// `PolyQnorm` with the pubkey factors precomputed: returns `n·‖w‖²_Q mod p`.
/// Two signature-dependent NTTs (`ŵ0`, `ŵ1`), no batch inversion.
#[inline(never)]
fn qnorm_prepared(
    q00n: &[u32; N],
    q00inv: &[u32; N],
    q01n: &[u32; N],
    w0: &[i32; N],
    w1: &[i32; N],
    p: u64,
) -> u64 {
    qp_a(q00n, q00inv, q01n, w0, w1, p)
}

/// Owns `c = ŵ0` (→ `ê`).
#[inline(never)]
fn qp_a(
    q00n: &[u32; N],
    q00inv: &[u32; N],
    q01n: &[u32; N],
    w0: &[i32; N],
    w1: &[i32; N],
    p: u64,
) -> u64 {
    let mut c = [0u32; N];
    ntt_conv(w0, &mut c, p);
    qp_b(q00n, q00inv, q01n, w1, p, &mut c)
}

/// Owns `d = ŵ1`.
#[inline(never)]
fn qp_b(
    q00n: &[u32; N],
    q00inv: &[u32; N],
    q01n: &[u32; N],
    w1: &[i32; N],
    p: u64,
    c: &mut [u32; N],
) -> u64 {
    let mut d = [0u32; N];
    ntt_conv(w1, &mut d, p);
    qp_c(q00n, q00inv, q01n, p, c, &d)
}

/// Owns `e = d̂`; computes `ê` and the `ĉ` sum.
#[inline(never)]
fn qp_c(
    q00n: &[u32; N],
    q00inv: &[u32; N],
    q01n: &[u32; N],
    p: u64,
    c: &mut [u32; N],
    d: &[u32; N],
) -> u64 {
    let mut e = [0u32; N];
    // Fused d̂ + ê pass: d̂[i] = ŵ1[i]·q̂00⁻¹[i] (q̂00⁻¹ precomputed), then
    // ê[i] ← ŵ0[i] + d̂[i]·q̂01[i] (overwrites c). One traversal instead of
    // two — the `ĉ` loop below needs all of `ê`/`d̂` materialised first
    // (it reads them reversed), but these two don't. ê is left **lazily
    // reduced** in `[0, 2p) < 2³²` (sum of two `< p` values, still fits
    // u32): every downstream read of ê is inside a `mulmod`, so the extra
    // factor is absorbed and the final `Σ ĉ mod p` is unchanged — saving N
    // reductions here.
    for (((ei, ci), (&di, &qiv)), &qi) in e
        .iter_mut()
        .zip(c.iter_mut())
        .zip(d.iter().zip(q00inv.iter()))
        .zip(q01n.iter())
    {
        let dh = mulmod(di as u64, qiv as u64, p);
        *ei = dh as u32;
        *ci = (*ci as u64 + mulmod(dh, qi as u64, p)) as u32;
    }
    // ĉ ← q̂00·ê·adj(ê) + d̂·adj(ŵ1);  r ← Σ ĉ[i]. Each of the 2N added
    // terms is a reduced `mulmod` result (< p < 2³¹), so the running sum
    // stays < 2N·p ≈ 2⁴¹ — no u64 overflow, one final `% p` is exact and
    // saves N per-iteration reductions.
    // (An indexed `0..N` form replacing the two `.rev()` iterators measured
    // byte-for-byte identical — LLVM folds the reverse zip fine here — so
    // the cleaner iterator form is kept.)
    let mut r = 0u64;
    for ((((&qi, &ci), &ei), &adj_e), &adj_w1) in q00n
        .iter()
        .zip(c.iter())
        .zip(e.iter())
        .zip(c.iter().rev())
        .zip(d.iter().rev())
    {
        let t0 = mulmod(mulmod(qi as u64, ci as u64, p), adj_e as u64, p);
        let t1 = mulmod(ei as u64, adj_w1 as u64, p);
        r += t0 + t1;
    }
    r % p
}

/// Prepared analogue of [`qnorm_in_bound`]. `pN_*` are the precomputed
/// per-prime factors for P1 / P2.
#[inline(never)]
#[allow(clippy::too_many_arguments)]
pub fn qnorm_in_bound_prepared(
    p1_q00: &[u32; N],
    p1_q00inv: &[u32; N],
    p1_q01: &[u32; N],
    p2_q00: &[u32; N],
    p2_q00inv: &[u32; N],
    p2_q01: &[u32; N],
    w0: &[i32; N],
    w1: &[i32; N],
) -> bool {
    let r1 = qnorm_prepared(p1_q00, p1_q00inv, p1_q01, w0, w1, P1);
    let r2 = qnorm_prepared(p2_q00, p2_q00inv, p2_q01, w0, w1, P2);
    if r1 != r2 {
        return false;
    }
    let r = r1;
    if !r.is_multiple_of(N as u64) {
        return false;
    }
    let r = r / (N as u64);
    1600 * (r as u128) <= 13_307_904
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn primes_are_ntt_friendly() {
        assert_eq!((P1 - 1) % (2 * N as u64), 0);
        assert_eq!((P2 - 1) % (2 * N as u64), 0);
    }

    #[test]
    fn root_has_order_2n() {
        for &p in &[P1, P2] {
            let h = find_root(p);
            assert_eq!(powmod(h, (2 * N) as u64, p), 1);
            assert_eq!(powmod(h, N as u64, p), p - 1);
        }
    }

    #[test]
    fn ntt_is_negacyclic_convolution() {
        // (x)·(x) = x² in Z[x]/(xⁿ+1): forward `ntt`, pointwise square,
        // manual inverse NTT (spec Alg 22), ·n⁻¹.
        let p = P1;
        let mut t = [0u32; N];
        t[1] = 1; // polynomial "x"
        ntt(&mut t, p);
        for v in t.iter_mut() {
            *v = mulmod(*v as u64, *v as u64, p) as u32;
        }
        let w = w_table(p);
        let mut l = 1usize;
        let mut wi = N;
        while l < N {
            let mut i = 0;
            while i < N {
                wi -= 1;
                let z = w[wi] as u64;
                for j in i..(i + l) {
                    let x = t[j] as u64;
                    let y = t[j + l] as u64;
                    t[j] = ((x + y) % p) as u32;
                    t[j + l] = mulmod(z, (y + p - x) % p, p) as u32;
                }
                i += 2 * l;
            }
            l <<= 1;
        }
        let ninv = powmod(N as u64, p - 2, p);
        for v in t.iter_mut() {
            *v = mulmod(*v as u64, ninv, p) as u32;
        }
        for (i, &v) in t.iter().enumerate() {
            assert_eq!(v as u64, (i == 2) as u64, "coeff {i}");
        }
    }

    /// Every NTT-side scalar pinned in `formal_verification/Hawk512/Defs.lean`
    /// or `formal_verification/Hawk512/NTT.lean` is re-asserted here. Plus
    /// the algebraic relationships that justify the bit-reversed `W1`/`W2`
    /// twiddle tables: each entry is independently recomputed via
    /// `pow(find_root(p), bitrev(i, LOGN), p)` and compared element-by-element.
    /// Drift in `find_root`, `calc_w`, or the constants surfaces here.
    #[test]
    fn lean_ntt_constants_drift_check() {
        // ── Prime values ───────────────────────────────────────────────────
        // Lean: Hawk512.Spec.{P1, P2}.
        assert_eq!(P1, 2_147_473_409);
        assert_eq!(P2, 2_147_389_441);
        // Both primes lie below 2³¹; `lazy_*_fits_u32` rests on this.
        assert!(P1 < 1u64 << 31);
        assert!(P2 < 1u64 << 31);
        // NTT-friendliness: (p−1) ≡ 0 (mod 2N). (Already in
        // `primes_are_ntt_friendly`; re-stated here as a Lean-side mirror.)
        assert_eq!((P1 - 1) % (2 * N as u64), 0);
        assert_eq!((P2 - 1) % (2 * N as u64), 0);

        // ── find_root outputs (PSI1, PSI2 in Lean NTT.lean) ────────────────
        // The Lean primitive-2N-root facts are `native_decide`d on these
        // specific values; if `find_root` ever returns something else, the
        // Lean theorems no longer describe the running code.
        assert_eq!(find_root(P1), 2_094_155_704);
        assert_eq!(find_root(P2), 1_133_102_181);

        // ── bitrev sanity (used to populate W1/W2 via calc_w) ──────────────
        // A bitrev bug would change the W tables but the test that recomputes
        // W via the same bitrev would also be wrong, so a few hardcoded pairs
        // pin the function itself.
        assert_eq!(bitrev(0, LOGN), 0);
        assert_eq!(bitrev(1, LOGN), 256);   // 000000001 → 100000000
        assert_eq!(bitrev(2, LOGN), 128);   // 000000010 → 010000000
        assert_eq!(bitrev(3, LOGN), 384);   // 000000011 → 110000000
        assert_eq!(bitrev(255, LOGN), 510); // 011111111 → 111111110
        assert_eq!(bitrev(511, LOGN), 511); // 111111111 → 111111111

        // ── W1 / W2 twiddle tables ─────────────────────────────────────────
        // Spec: W[i] = h^bitrev(i, LOGN) mod p, h the primitive 2N-th root.
        // We recompute independently from the pinned PSI values; any drift
        // in `calc_w`'s loop, indexing, or modular exponentiation surfaces.
        const PSI1_EXPECTED: u64 = 2_094_155_704;
        const PSI2_EXPECTED: u64 = 1_133_102_181;
        for i in 0..N {
            let exp = bitrev(i, LOGN) as u64;
            let expected_p1 = powmod(PSI1_EXPECTED, exp, P1) as u32;
            let expected_p2 = powmod(PSI2_EXPECTED, exp, P2) as u32;
            assert_eq!(W1[i], expected_p1, "W1[{}] drift", i);
            assert_eq!(W2[i], expected_p2, "W2[{}] drift", i);
        }

        // ── Bound check constants (qnorm_in_bound) ─────────────────────────
        // Lean: Hawk512.Spec.{BOUND_NUM, BOUND_DEN}.  Spec ties these to
        // `8n · σ²_verify` with `n = 512`, `σ_verify = 57/40`:
        //   8·512·(57)²/(40)² = 4096·3249/1600 = 13_307_904/1600.
        // The Rust `qnorm_in_bound` literal compares `1600·r ≤ 13_307_904`.
        assert_eq!(8u128 * 512 * 57 * 57, 13_307_904 * (40 * 40 / 1600));
        assert_eq!(4096u128 * 3249, 13_307_904);
        // Sanity: r = 8317 passes, r = 8318 fails (bound is a strict ⌊x⌋).
        assert!(1600u128 * 8317 <= 13_307_904);
        assert!(1600u128 * 8318  > 13_307_904);
    }
}
