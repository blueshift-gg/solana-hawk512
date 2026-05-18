//! Fixed-point FFT, inverse FFT, and `RebuildS0` — spec Algorithms 16, 17,
//! 18 (HAWK v1.1 §3.6), ported **exactly**. This is the consensus-critical
//! reconstruction of the signature's `s0` half: the spec mandates that
//! implementations "should follow the steps of RebuildS0 exactly" so that
//! every verifier agrees bit-for-bit on borderline inputs.
//!
//! All arithmetic is integer. Coefficients are signed 32-bit with two's
//! complement and **truncation** on overflow — `trunc(z) = ((z + 2³¹) mod
//! 2³²) − 2³¹`, which is exactly Rust's wrapping `as i32`. Uppercase
//! temporaries (`T_re`, `X_re`, …) are 64-bit. Divisions by powers of two
//! are arithmetic right shifts (floor, toward −∞); the two true divisions
//! in RebuildS0 use non-negative dividends and positive divisors.
//!
//! Every working buffer is supplied by the caller's scratch arena so that
//! no function holds a 512-element array in its own stack frame (Solana
//! SBF caps each frame at 4 KiB).

use crate::delta_table::DELTA;
use crate::{HIGH_S0, N};

// HAWK-512 RebuildS0 fixed-point scaling constants (spec §3.6, derived from
// the bit-length parameters high_s1 = high_00 = 9, high_01 = 12, n = 512).
const C_W1: i64 = 1 << 19; // 2^(29-(1+high_s1))
const C_Q00: i64 = 1 << 20; // 2^(29-high_00)
const C_Q01: i64 = 1 << 17; // 2^(29-high_01)
const C_S0: i64 = 256; // (2*C_W1*C_Q01)/(n*C_Q00) = 2^8

/// Floor division by a **positive** divisor (`⌊a/b⌋`, toward −∞).
///
/// Used off the hot path (the `α` precompute). On the hot path use
/// [`udiv`] (non-negative dividend) or an arithmetic shift (power-of-two
/// divisor) instead — `i64::div_euclid` lowers to an expensive signed
/// software division on SBF.
#[inline(always)]
fn floordiv(a: i64, b: i64) -> i64 {
    debug_assert!(b > 0);
    a.div_euclid(b)
}

/// `⌊a / b⌋` for a **non-negative** dividend and **positive** divisor.
///
/// Exactly `floordiv(a, b)` when `a ≥ 0, b > 0`, but lowered to the SBF
/// native *unsigned* 64-bit divide — measured ~7× cheaper than the signed
/// `div_euclid` the general `floordiv` emits. The RebuildS0 divide loop
/// runs this 512× per verify, so the difference is ~80k CU.
#[inline(always)]
fn udiv(a: i64, b: i64) -> i64 {
    debug_assert!(a >= 0 && b > 0);
    (a as u64 / b as u64) as i64
}

/// `log2(2·C_S0)` — the RebuildS0 `s0` rounding divides by `2·c_s0`, which
/// for HAWK-512 is `512 = 2⁹`, so the floor division is an arithmetic
/// right shift (correct toward −∞ for the negative `t[u]` case too).
const LOG2_TWO_C_S0: u32 = 9;
const _: () = assert!(2 * C_S0 == 1 << LOG2_TWO_C_S0);

/// One FFT/InvFFT level with the block size `$t` and twiddle stride `$m`
/// as **compile-time constants**, so the twiddle count (`$m/2`), the block
/// stride (`$t`) and the inner butterfly count (`$t/2`) are constant: LLVM
/// unrolls the inner loop and constant-folds all addressing, removing the
/// per-block / per-butterfly branch overhead (the same win as the NTT).
/// `$bfly` is the butterfly body (forward vs conjugate-inverse) given the
/// four lane refs and the i64 twiddle `(tw_re, tw_im)`.
macro_rules! fft_level {
    ($re:expr, $im:expr, $m:expr, $t:expr, |$x1r:ident,$x2r:ident,$x1i:ident,$x2i:ident,$tw_re:ident,$tw_im:ident| $bfly:block) => {{
        const M: usize = $m;
        const T: usize = $t;
        const HALF: usize = T / 2;
        let mut v0 = 0usize;
        let mut u = 0usize;
        while u < M / 2 {
            // u < M/2, M ≤ N/2 ⇒ u+M ≤ 383 < N = DELTA.len(); and
            // v0 + T ≤ N/2 since v0 steps by T and (M/2)·T = N/2.
            unsafe {
                core::hint::assert_unchecked(u + M < N);
                core::hint::assert_unchecked(v0 + T <= N / 2);
            }
            let (de_re, de_im) = DELTA[u + M];
            let $tw_re = de_re as i64;
            let $tw_im = de_im as i64;
            // 4-way zip over the constant-length (`HALF`) `split_at_mut`
            // halves: bounds-check-free, and measured slightly faster than
            // an indexed `0..HALF` loop here.
            let (r_lo, r_hi) = $re[v0..v0 + T].split_at_mut(HALF);
            let (i_lo, i_hi) = $im[v0..v0 + T].split_at_mut(HALF);
            for ((($x1r, $x2r), $x1i), $x2i) in r_lo
                .iter_mut()
                .zip(r_hi.iter_mut())
                .zip(i_lo.iter_mut())
                .zip(i_hi.iter_mut())
                $bfly
            v0 += T;
            u += 1;
        }
    }};
}

/// Fused scaling + forward FFT into the **`i64`** FFT-domain split buffers
/// `re`/`im` (each `[i64; N/2]`, in their own ≤4 KiB frames). Equivalent to
/// `for i { d[i] = (C·src[i]) as i32 }` (with `d[0]=0` if `ZERO_FIRST`,
/// i.e. `z00[0]=0`) then the spec FFT, but level 1 applies the scale on the
/// fly. Storing the FFT domain as `i64` (the wrapped `as i32` value
/// sign-extended) lets every subsequent load skip the SBPF-v1
/// `lsh;arsh` sign-extension; bit-identical to the old `i32` form.
#[inline(never)]
fn fft_conv<const C: i64, const ZERO_FIRST: bool>(
    src: &[i32; N],
    re: &mut [i64; N / 2],
    im: &mut [i64; N / 2],
) {
    // Level 1: m = 2, t = 256, single twiddle DELTA[2]; the old `a[0..256]`
    // is `re`, `a[256..512]` is `im`; butterfly pairs (j, j+N/4).
    {
        let (de_re, de_im) = DELTA[2];
        let e_re = de_re as i64;
        let e_im = de_im as i64;
        let s = |idx: usize| -> i64 { ((C.wrapping_mul(src[idx] as i64)) as i32) as i64 };
        let mut j = 0usize;
        while j < N / 4 {
            // SAFETY: j < N/4 ⇒ j, j+N/4 < N/2 = re.len() = im.len().
            unsafe {
                core::hint::assert_unchecked(j + N / 4 < N / 2);
            }
            let x1_re = if ZERO_FIRST && j == 0 { 0 } else { s(j) };
            let x2_re = s(j + N / 4);
            let x1_im = s(N / 2 + j);
            let x2_im = s(N / 2 + j + N / 4);
            let tt_re = x2_re * e_re - x2_im * e_im;
            let tt_im = x2_re * e_im + x2_im * e_re;
            re[j] = ((((x1_re << 31) + tt_re) >> 32) as i32) as i64;
            im[j] = ((((x1_im << 31) + tt_im) >> 32) as i32) as i64;
            re[j + N / 4] = ((((x1_re << 31) - tt_re) >> 32) as i32) as i64;
            im[j + N / 4] = ((((x1_im << 31) - tt_im) >> 32) as i32) as i64;
            j += 1;
        }
    }
    // Levels 2..8 on the i64 `re`/`im` (no per-load sign-extension; the
    // `as i32 as i64` keeps the spec's wrapped value).
    macro_rules! lvl {
        ($m:expr, $t:expr) => {
            fft_level!(re, im, $m, $t, |x1r, x2r, x1i, x2i, e_re, e_im| {
                let x1_re = *x1r;
                let x1_im = *x1i;
                let x2_re = *x2r;
                let x2_im = *x2i;
                let tt_re = x2_re * e_re - x2_im * e_im;
                let tt_im = x2_re * e_im + x2_im * e_re;
                *x1r = ((((x1_re << 31) + tt_re) >> 32) as i32) as i64;
                *x1i = ((((x1_im << 31) + tt_im) >> 32) as i32) as i64;
                *x2r = ((((x1_re << 31) - tt_re) >> 32) as i32) as i64;
                *x2i = ((((x1_im << 31) - tt_im) >> 32) as i32) as i64;
            })
        };
    }
    lvl!(4, 128);
    lvl!(8, 64);
    lvl!(16, 32);
    lvl!(32, 16);
    lvl!(64, 8);
    lvl!(128, 4);
    lvl!(256, 2);
}

/// `InvFFT` (spec Algorithm 17; inverse roots are the conjugates of the
/// forward ones) then `w0[u] = h0[u] − 2·⌊(c_s0·h0[u] + t[u] + c_s0)/2c_s0⌋`,
/// **fused**: the last InvFFT level (m=2, t=256) writes `w0` directly from
/// each butterfly output instead of storing `t` to `qh01` and re-reading
/// it in a separate pass — saves 512 `qh01` stores + a full read pass per
/// RebuildS0. `false` (⊥) if any `s0` is out of `[−2^HIGH_S0, 2^HIGH_S0)`
/// (same reject set as the separate loop; bit-identical `w0`).
#[inline(never)]
fn inv_fft_to_w0(
    re: &mut [i64; N / 2],
    im: &mut [i64; N / 2],
    h0: &[i32; N],
    w0: &mut [i32; N],
) -> bool {
    // InvFFT levels 1..7 on the i64 split buffers (the last level is fused
    // below). No per-load sign-extension; `as i32 as i64` keeps the spec
    // wrapped value.
    {
        macro_rules! lvl {
            ($m:expr, $t:expr) => {
                fft_level!(re, im, $m, $t, |x1r, x2r, x1i, x2i, n_re, n_im| {
                    let x1_re = *x1r;
                    let x1_im = *x1i;
                    let x2_re = *x2r;
                    let x2_im = *x2i;
                    let t1_re = x1_re + x2_re;
                    let t1_im = x1_im + x2_im;
                    let t2_re = x1_re - x2_re;
                    let t2_im = x1_im - x2_im;
                    *x1r = ((t1_re >> 1) as i32) as i64;
                    *x1i = ((t1_im >> 1) as i32) as i64;
                    *x2r = (((t2_re * n_re + t2_im * n_im) >> 32) as i32) as i64;
                    *x2i = (((t2_im * n_re - t2_re * n_im) >> 32) as i32) as i64;
                })
            };
        }
        lvl!(256, 2);
        lvl!(128, 4);
        lvl!(64, 8);
        lvl!(32, 16);
        lvl!(16, 32);
        lvl!(8, 64);
        lvl!(4, 128);
    }
    // Fused last level (m=2, t=256, DELTA[2], conjugate): compute each
    // butterfly output `t` and fold it straight into `w0` (no store/re-read).
    // `re` = old `qh01[0..256]`, `im` = old `qh01[256..512]`; the four
    // global indices (j, j+N/4, N/2+j, N/2+j+N/4) cover 0..N exactly.
    let (de_re, de_im) = DELTA[2];
    let n_re = de_re as i64;
    let n_im = de_im as i64;
    let mut j = 0usize;
    while j < N / 4 {
        // SAFETY: j < N/4 ⇒ j, j+N/4 < N/2 = re.len() = im.len().
        unsafe { core::hint::assert_unchecked(j + N / 4 < N / 2) };
        let x1_re = re[j];
        let x2_re = re[j + N / 4];
        let x1_im = im[j];
        let x2_im = im[j + N / 4];
        let t1_re = x1_re + x2_re;
        let t1_im = x1_im + x2_im;
        let t2_re = x1_re - x2_re;
        let t2_im = x1_im - x2_im;
        let o1r = t1_re >> 1;
        let o1i = t1_im >> 1;
        let o2r = (t2_re * n_re + t2_im * n_im) >> 32;
        let o2i = (t2_im * n_re - t2_re * n_im) >> 32;
        macro_rules! finalize {
            ($idx:expr, $t:expr) => {{
                let idx = $idx;
                unsafe { core::hint::assert_unchecked(idx < N) };
                let v = C_S0 * h0[idx] as i64 + $t;
                let z = (v + C_S0) >> LOG2_TWO_C_S0;
                if !(-(1i64 << HIGH_S0)..(1i64 << HIGH_S0)).contains(&z) {
                    return false;
                }
                w0[idx] = (h0[idx] as i64 - 2 * z) as i32;
            }};
        }
        finalize!(j, o1r);
        finalize!(N / 2 + j, o1i);
        finalize!(j + N / 4, o2r);
        finalize!(N / 2 + j + N / 4, o2i);
        j += 1;
    }
    true
}

/// One RebuildS0 divide-loop iteration: `q̂01·ŵ1 / v` with sign handling.
/// `$qre`/`$qim` are the in/out q̂01 split halves at index u, `$wre`/`$wim`
/// the ŵ1 halves, `$v` the (positive, `< 2³⁰`) divisor, `$bnd` the
/// `2³²·v` magnitude bound. On `|X| ≥ bnd` it `return false`s the caller.
macro_rules! divide_step {
    ($qre:expr, $qim:expr, $wre:expr, $wim:expr, $v:expr, $bnd:expr) => {{
        let qa = $qre;
        let qb = $qim;
        let wa = $wre;
        let wb = $wim;
        let x_re = qa * wa - qb * wb;
        let x_im = qa * wb + qb * wa;
        let z_re = (x_re < 0) as i64;
        let z_im = (x_im < 0) as i64;
        let x_re = x_re.unsigned_abs() as i64;
        let x_im = x_im.unsigned_abs() as i64;
        if x_re >= $bnd || x_im >= $bnd {
            return false;
        }
        let v = $v;
        let y_re = udiv(x_re, v);
        let y_im = udiv(x_im, v);
        (
            ((y_re - 2 * z_re * y_re) as i32) as i64,
            ((y_im - 2 * z_im * y_im) as i32) as i64,
        )
    }};
}

/// `RebuildS0` — spec Algorithm 18. Inputs `q00`, `q01`, `w1 = h1 − 2·s1`,
/// `h0`; output `w0 = h0 − 2·s0`. Returns `false` (⊥) on a violated
/// fixed-point bound.
///
/// The FFT-domain working buffers (`ŵ1`, `q̂00`, `q̂01`) are now **`i64`**
/// (no per-load sign-extension on SBPF-v1). Each is split into two
/// `[i64; N/2]` halves (`_re`/`_im`), and every 2 KiB half is the sole
/// large local of its own `#[inline(never)]` frame (the 4 KiB SBF frame
/// cap forbids a single `[i64; N]`), threaded inward by reference.
#[inline(never)]
pub fn rebuild_s0(
    q00: &[i32; N],
    q01: &[i32; N],
    w1: &[i32; N],
    h0: &[i32; N],
    w0: &mut [i32; N],
) -> bool {
    if q00[0] < 0 {
        return false;
    }
    let mut wh1_re = [0i64; N / 2];
    rb_a(q00, q01, w1, h0, w0, &mut wh1_re)
}

/// Owns `ŵ1_im`; fills `ŵ1 = FFT(c_w1·w1)` (`_re` from the caller).
#[inline(never)]
fn rb_a(
    q00: &[i32; N],
    q01: &[i32; N],
    w1: &[i32; N],
    h0: &[i32; N],
    w0: &mut [i32; N],
    wh1_re: &mut [i64; N / 2],
) -> bool {
    let mut wh1_im = [0i64; N / 2];
    fft_conv::<C_W1, false>(w1, wh1_re, &mut wh1_im);
    rb_c(q00, q01, h0, w0, wh1_re, &wh1_im)
}

/// Owns `q̂00_re`.
#[inline(never)]
fn rb_c(
    q00: &[i32; N],
    q01: &[i32; N],
    h0: &[i32; N],
    w0: &mut [i32; N],
    wh1_re: &[i64; N / 2],
    wh1_im: &[i64; N / 2],
) -> bool {
    let mut qh00_re = [0i64; N / 2];
    rb_d(q00, q01, h0, w0, wh1_re, wh1_im, &mut qh00_re)
}

/// Owns `q̂00_im` (transient — only `q̂00_re` feeds the divide loop).
#[inline(never)]
fn rb_d(
    q00: &[i32; N],
    q01: &[i32; N],
    h0: &[i32; N],
    w0: &mut [i32; N],
    wh1_re: &[i64; N / 2],
    wh1_im: &[i64; N / 2],
    qh00_re: &mut [i64; N / 2],
) -> bool {
    let mut qh00_im = [0i64; N / 2];
    fft_conv::<C_Q00, true>(q00, qh00_re, &mut qh00_im); // z00[0] = 0
    // α ← (2·c_q00·q00[0]) / n  (original q00[0]; exact for HAWK-512)
    let alpha = floordiv(2 * C_Q00 * q00[0] as i64, N as i64);
    rb_e(q01, h0, w0, wh1_re, wh1_im, qh00_re, alpha)
}

/// Owns `q̂01_re`.
#[inline(never)]
fn rb_e(
    q01: &[i32; N],
    h0: &[i32; N],
    w0: &mut [i32; N],
    wh1_re: &[i64; N / 2],
    wh1_im: &[i64; N / 2],
    qh00_re: &[i64; N / 2],
    alpha: i64,
) -> bool {
    let mut qh01_re = [0i64; N / 2];
    rb_f(q01, h0, w0, wh1_re, wh1_im, qh00_re, alpha, &mut qh01_re)
}

/// Owns `q̂01_im`; FFT(c_q01·q01), the divide loop, then `InvFFT`+`s0`→`w0`.
#[inline(never)]
#[allow(clippy::too_many_arguments)]
fn rb_f(
    q01: &[i32; N],
    h0: &[i32; N],
    w0: &mut [i32; N],
    wh1_re: &[i64; N / 2],
    wh1_im: &[i64; N / 2],
    qh00_re: &[i64; N / 2],
    alpha: i64,
    qh01_re: &mut [i64; N / 2],
) -> bool {
    let mut qh01_im = [0i64; N / 2];
    fft_conv::<C_Q01, false>(q01, qh01_re, &mut qh01_im);
    {
        let mut u = 0usize;
        while u < N / 2 {
            // SAFETY: u < N/2 = every split half's length.
            unsafe { core::hint::assert_unchecked(u < N / 2) };
            let v = alpha + qh00_re[u];
            if v <= 0 || v >= (1 << 30) {
                return false;
            }
            let (r, i) = divide_step!(
                qh01_re[u],
                qh01_im[u],
                wh1_re[u],
                wh1_im[u],
                v,
                (1i64 << 32) * v
            );
            qh01_re[u] = r;
            qh01_im[u] = i;
            u += 1;
        }
    }
    inv_fft_to_w0(qh01_re, &mut qh01_im, h0, w0)
}

// ---- Prepared-pubkey path -------------------------------------------------
//
// `q̂00 = FFT(c_q00·z00)` and `q̂01 = FFT(c_q01·q01)` plus `α` depend only on
// the pubkey, so they are precomputed once. On-chain RebuildS0 then needs
// only `ŵ1 = FFT(c_w1·w1)` (signature-dependent) — 1 FFT instead of 3.

/// Precompute the RebuildS0 FFT-domain pubkey factors. `q̂00` is returned in
/// the split halves `fq00_re`/`fq00_im` (each `[i64; N/2]`) — only the real
/// half survives (it feeds [`prepare_divisor`]); the imaginary half is pure
/// transform scratch. `q̂01` is written into the caller's packed `fq01`
/// (`[i64; N]`: re = `[0,N/2)`, im = `[N/2,N)`), which on-chain is an
/// account field, never a stack value. Returns `alpha`; `None` if
/// `q00[0] < 0`. Splitting `q̂00` into two `[i64; N/2]` halves (instead of a
/// packed `[i64; N]`) keeps every buffer ≤ 2 KiB so it fits an SBF stack
/// frame — a single `[i64; N]` is 4 KiB and overflows the frame.
pub fn prepare_fft(
    q00: &[i32; N],
    q01: &[i32; N],
    fq00_re: &mut [i64; N / 2],
    fq00_im: &mut [i64; N / 2],
    fq01: &mut [i64; N],
) -> Option<i64> {
    if q00[0] < 0 {
        return None;
    }
    fft_conv::<C_Q00, true>(q00, fq00_re, fq00_im);
    {
        let (re, im) = fq01.split_at_mut(N / 2);
        fft_conv::<C_Q01, false>(q01, re.try_into().unwrap(), im.try_into().unwrap());
    }
    Some(floordiv(2 * C_Q00 * q00[0] as i64, N as i64))
}

/// Precompute the RebuildS0 divide-loop bounds. For `u ∈ [0, n/2)` the
/// divisor is the pubkey-only integer `v = α + q̂00[u]`; the spec rejects
/// unless `0 < v < 2³⁰` and `|X| < 2³²·v`. The first part is pubkey-only,
/// so validate it here (reject the *pubkey*) and store `pvbound[u] =
/// (1≪32)·v` — the runtime magnitude bound, and `pvbound[u] ≫ 32 = v` the
/// divisor. `false` if any `v` is out of range. `fq00_re` is the `i64`
/// real half of `q̂00` from [`prepare_fft`].
pub fn prepare_divisor(fq00_re: &[i64; N / 2], alpha: i64, pvbound: &mut [i64; N / 2]) -> bool {
    for (pb, &qh00u) in pvbound.iter_mut().zip(fq00_re.iter()) {
        let v = alpha + qh00u;
        if v <= 0 || v >= (1 << 30) {
            return false;
        }
        *pb = (1i64 << 32) * v;
    }
    true
}

/// Prepared analogue of [`rebuild_s0`]: `q̂01` (the `i64` packed `fq01`) and
/// the divide-loop bounds `pvbound` precomputed, so only `ŵ1 =
/// FFT(c_w1·w1)` is computed on-chain. Same `i64` two-half frame-split.
#[inline(never)]
pub fn rebuild_s0_prepared(
    pvbound: &[i64; N / 2],
    fq01: &[i64; N],
    w1: &[i32; N],
    h0: &[i32; N],
    w0: &mut [i32; N],
) -> bool {
    let mut wh1_re = [0i64; N / 2];
    rp_a(pvbound, fq01, w1, h0, w0, &mut wh1_re)
}

/// Owns `ŵ1_im`; fills `ŵ1 = FFT(c_w1·w1)`.
#[inline(never)]
fn rp_a(
    pvbound: &[i64; N / 2],
    fq01: &[i64; N],
    w1: &[i32; N],
    h0: &[i32; N],
    w0: &mut [i32; N],
    wh1_re: &mut [i64; N / 2],
) -> bool {
    let mut wh1_im = [0i64; N / 2];
    fft_conv::<C_W1, false>(w1, wh1_re, &mut wh1_im);
    rp_c(pvbound, fq01, h0, w0, wh1_re, &wh1_im)
}

/// Owns `q̂01_re`.
#[inline(never)]
fn rp_c(
    pvbound: &[i64; N / 2],
    fq01: &[i64; N],
    h0: &[i32; N],
    w0: &mut [i32; N],
    wh1_re: &[i64; N / 2],
    wh1_im: &[i64; N / 2],
) -> bool {
    let mut qh01_re = [0i64; N / 2];
    rp_d(pvbound, fq01, h0, w0, wh1_re, wh1_im, &mut qh01_re)
}

/// Owns `q̂01_im`; copies the precomputed `fq01` in, runs the divide loop,
/// then `InvFFT`+`s0`→`w0`.
#[inline(never)]
#[allow(clippy::too_many_arguments)]
fn rp_d(
    pvbound: &[i64; N / 2],
    fq01: &[i64; N],
    h0: &[i32; N],
    w0: &mut [i32; N],
    wh1_re: &[i64; N / 2],
    wh1_im: &[i64; N / 2],
    qh01_re: &mut [i64; N / 2],
) -> bool {
    let mut qh01_im = [0i64; N / 2];
    {
        let mut u = 0usize;
        while u < N / 2 {
            // SAFETY: u < N/2 ⇒ u, u+N/2 < N (fq01), u < N/2 (halves).
            unsafe { core::hint::assert_unchecked(u + N / 2 < N) };
            // q̂01 working copy from the precomputed packed `fq01`.
            let qa = fq01[u];
            let qb = fq01[u + N / 2];
            let vb = pvbound[u];
            // vb = (1≪32)·v, v = α+q̂00[u] ∈ (0,2³⁰) (validated at prepare);
            // divisor v = vb ≫ 32.
            let (r, i) = divide_step!(qa, qb, wh1_re[u], wh1_im[u], vb >> 32, vb);
            qh01_re[u] = r;
            qh01_im[u] = i;
            u += 1;
        }
    }
    inv_fft_to_w0(qh01_re, &mut qh01_im, h0, w0)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every FFT-side scalar pinned in `formal_verification/Hawk512/Defs.lean`
    /// or `formal_verification/Hawk512/FFT.lean` is re-asserted here, plus
    /// the spec relationship `2·C_W1·C_Q01 = n·C_Q00·C_S0` and the
    /// dead-slot zero-out of `DELTA[0]`/`DELTA[1]`. The full DELTA table
    /// is checked against a stable polynomial-hash checksum so any drift
    /// in the auto-generated values is caught.
    #[test]
    fn lean_fft_constants_drift_check() {
        // ── Fixed-point scaling constants (Lean Defs.lean) ─────────────────
        assert_eq!(C_W1, 1i64 << 19); //  524_288
        assert_eq!(C_Q00, 1i64 << 20); // 1_048_576
        assert_eq!(C_Q01, 1i64 << 17); //   131_072
        assert_eq!(C_S0, 256);
        assert_eq!(LOG2_TWO_C_S0, 9);
        // 2·C_S0 is exactly 2^LOG2_TWO_C_S0 (Lean: `two_c_s0_is_pow_two`),
        // which is what justifies replacing the floor-division by an
        // arithmetic shift in the `s0` rounding.
        assert_eq!(2 * C_S0, 1i64 << LOG2_TWO_C_S0);
        // Spec relationship (Lean: `c_s0_spec`):
        //   2·C_W1·C_Q01 = n·C_Q00·C_S0.
        assert_eq!(2 * C_W1 * C_Q01, (N as i64) * C_Q00 * C_S0);

        // ── DELTA dead slots (Lean: `fft_index_at_least_2`) ────────────────
        // The FFT only ever indexes DELTA[u+m] with m ≥ 2, so DELTA[0] and
        // DELTA[1] are never read and are zeroed (their true value 2³¹
        // doesn't fit `i32`).
        assert_eq!(DELTA[0], (0, 0));
        assert_eq!(DELTA[1], (0, 0));

        // ── First-read DELTA entry ─────────────────────────────────────────
        // DELTA[2] = round(2³¹·delta^rev9(2)) with delta = e^{iπ/N} and
        // rev9(2) = 128, so DELTA[2] = round(2³¹·e^{iπ/4}) =
        // round(2³¹·(√2/2, √2/2)) = (1_518_500_250, 1_518_500_250).
        assert_eq!(DELTA[2], (1_518_500_250, 1_518_500_250));

        // ── Full-table stable checksum ────────────────────────────────────
        // Polynomial hash; any drift in the auto-generated table changes
        // this value. The hash itself is computed via the same formula in
        // Python over the source-of-truth `delta_table.rs`.
        let mut h: u64 = 0;
        for &(re, im) in DELTA.iter() {
            h = h.wrapping_mul(1_000_003).wrapping_add(re as i64 as u64);
            h = h.wrapping_mul(1_000_003).wrapping_add(im as i64 as u64);
        }
        // Hardcoded once from a successful run; re-pinning this number
        // requires a separate Lean / spec review.
        assert_eq!(h, DELTA_POLYHASH_EXPECTED);
    }

    /// Expected polynomial-hash of the full DELTA table. Computed once
    /// from the canonical auto-generated table; subsequent runs check
    /// stability — any drift (regenerated table, edited entry) changes
    /// this number.
    const DELTA_POLYHASH_EXPECTED: u64 = 0x35b0_5991_cdb8_d12f;
}
