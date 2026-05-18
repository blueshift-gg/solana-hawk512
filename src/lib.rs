//! Pure-Rust **HAWK-512 signature verification**, optimised for Solana SBF.
//!
//! Implements [HAWK] v1.1 signature verification (`HawkVerify`, spec
//! Algorithm 20). The crate is `no_std`, allocation-free, and every
//! primitive — SHAKE256, Golomb–Rice decompression, the fixed-point FFT
//! `RebuildS0`, and the dual-prime NTT `PolyQnorm` — is hand-written with
//! no non-essential dependencies.
//!
//! HAWK verification is **entirely integer arithmetic** (no floating
//! point): the spec defines an exact fixed-point `RebuildS0`, and
//! implementations are required to follow it step-for-step so that all
//! verifiers agree bit-for-bit — essential for on-chain consensus.
//!
//! [HAWK]: https://hawk-sign.info
//!
//! # Quick start
//!
//! ```ignore
//! use solana_hawk512::{Hawk512Pubkey, Hawk512Signature};
//!
//! let pubkey = Hawk512Pubkey::try_from(&pk_bytes[..])?;
//! let signature = Hawk512Signature::try_from(&sig_bytes[..])?;
//! let ok = signature.verify(message, &pubkey);
//! ```
//!
//! # Compatibility
//!
//! - **HAWK-512 only** (NIST-I parameter set). HAWK-256 / HAWK-1024 are not
//!   supported.
//! - **Verify only.** Key generation and signing are out of scope; produce
//!   keys and signatures with the HAWK reference implementation.
//! - HAWK v1.0 and v1.1 are algorithmically identical (v1.1 changed only
//!   security proofs), so v1.0 KAT vectors apply unchanged.
//!
//! # Security notes
//!
//! - This crate is **not audited**. Use at your own risk for protecting
//!   anything of value.
//! - Verification operates on **public data only** (signature, pubkey,
//!   message) and is deliberately **not** constant-time — it short-circuits
//!   on decode / bound failures, none of which leak secret information.

#![cfg_attr(not(test), no_std)]

use solana_program_error::ProgramError;

mod codec;
mod delta_table;
mod fft;
mod ntt;

#[cfg(kani)]
#[path = "../internal-tests/kani_proofs.rs"]
mod kani_proofs;

// ---- HAWK-512 parameters (spec Table 4) ----------------------------------

pub(crate) const LOGN: usize = 9;
pub(crate) const N: usize = 1 << LOGN; // 512

/// Wire-encoded HAWK-512 public key length (`q00 ‖ q01`, padded).
pub const HAWK_512_PUBKEY_LEN: usize = 1024;
/// Wire-encoded HAWK-512 signature length (`salt ‖ Compress(s1)`, padded).
pub const HAWK_512_SIGNATURE_LEN: usize = 555;
/// Serialised length of a [`Hawk512PreparedPubkey`] (18 464 bytes): the
/// RebuildS0 divide-loop bounds (`(1≪32)·(α+q̂00[u])`, `n/2` `i64`), the
/// FFT-domain `q̂01` (`n` `i64` — stored 64-bit so the on-chain divide
/// loop avoids per-load sign-extension), the per-prime NTT factors (`q̂00`,
/// `q̂00⁻¹`, `q̂01` for `p₁` and `p₂`), and the precomputed
/// `hpub = SHAKE256(pub)`. See [`Hawk512PreparedPubkey`].
pub const HAWK_512_PREPARED_PUBKEY_LEN: usize = (N / 2) * 8 + N * 8 + 6 * (N * 4) + HPUB_LEN;

pub(crate) const PUBKEY_LEN: usize = HAWK_512_PUBKEY_LEN;
pub(crate) const SIGNATURE_LEN: usize = HAWK_512_SIGNATURE_LEN;
pub(crate) const SALT_LEN: usize = 24; // saltlen = 192 bits
pub(crate) const HPUB_LEN: usize = 32; // hpublen = 256 bits

pub(crate) const LOW_00: usize = 5;
pub(crate) const HIGH_00: usize = 9;
pub(crate) const LOW_01: usize = 9;
pub(crate) const HIGH_01: usize = 12;
pub(crate) const LOW_S1: usize = 5;
pub(crate) const HIGH_S1: usize = 9;
pub(crate) const HIGH_S0: usize = 13;

// ---- Public API types ----------------------------------------------------

/// Wire-encoded HAWK-512 public key (1024 bytes: Golomb–Rice-compressed
/// `q00 ‖ q01`, zero-padded to the fixed size).
///
/// `#[repr(transparent)]` so a `&[u8; HAWK_512_PUBKEY_LEN]` can be
/// re-borrowed as a `&Hawk512Pubkey` without a copy via
/// [`Hawk512Pubkey::from_ref`].
#[derive(Clone, Eq, PartialEq)]
#[repr(transparent)]
pub struct Hawk512Pubkey([u8; HAWK_512_PUBKEY_LEN]);

impl From<[u8; HAWK_512_PUBKEY_LEN]> for Hawk512Pubkey {
    fn from(value: [u8; HAWK_512_PUBKEY_LEN]) -> Self {
        Self(value)
    }
}

impl TryFrom<&[u8]> for Hawk512Pubkey {
    type Error = ProgramError;
    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        let bytes: [u8; HAWK_512_PUBKEY_LEN] = value
            .try_into()
            .map_err(|_| ProgramError::InvalidArgument)?;
        Ok(Self(bytes))
    }
}

impl Hawk512Pubkey {
    /// Borrow a fixed-size array as a `&Hawk512Pubkey` with no copy.
    pub const fn from_ref(bytes: &[u8; HAWK_512_PUBKEY_LEN]) -> &Self {
        // SAFETY: `#[repr(transparent)]` over `[u8; HAWK_512_PUBKEY_LEN]`.
        unsafe { &*(bytes as *const [u8; HAWK_512_PUBKEY_LEN] as *const Self) }
    }

    /// Borrow an arbitrary slice as a `&Hawk512Pubkey`, length-checked.
    pub fn try_from_slice(bytes: &[u8]) -> Result<&Self, ProgramError> {
        let array: &[u8; HAWK_512_PUBKEY_LEN] = bytes
            .try_into()
            .map_err(|_| ProgramError::InvalidArgument)?;
        Ok(Self::from_ref(array))
    }

    /// Wrap a 1024-byte buffer without validation (validated at verify time).
    pub const fn from_bytes(value: [u8; HAWK_512_PUBKEY_LEN]) -> Self {
        Self(value)
    }

    /// Borrow the raw 1024-byte wire encoding.
    pub const fn as_bytes(&self) -> &[u8; HAWK_512_PUBKEY_LEN] {
        &self.0
    }
}

/// Wire-encoded HAWK-512 signature (555 bytes: 24-byte `salt` followed by
/// Golomb–Rice-compressed `s1`, zero-padded to the fixed size).
///
/// `#[repr(transparent)]` so a `&[u8; HAWK_512_SIGNATURE_LEN]` can be
/// re-borrowed as a `&Hawk512Signature` without a copy via
/// [`Hawk512Signature::from_ref`].
#[derive(Clone, Eq, PartialEq)]
#[repr(transparent)]
pub struct Hawk512Signature([u8; HAWK_512_SIGNATURE_LEN]);

impl From<[u8; HAWK_512_SIGNATURE_LEN]> for Hawk512Signature {
    fn from(value: [u8; HAWK_512_SIGNATURE_LEN]) -> Self {
        Self(value)
    }
}

impl TryFrom<&[u8]> for Hawk512Signature {
    type Error = ProgramError;
    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        let bytes: [u8; HAWK_512_SIGNATURE_LEN] = value
            .try_into()
            .map_err(|_| ProgramError::InvalidArgument)?;
        Ok(Self(bytes))
    }
}

impl Hawk512Signature {
    /// Borrow a fixed-size array as a `&Hawk512Signature` with no copy —
    /// skips the 555-byte memcpy in Solana entrypoints.
    pub const fn from_ref(bytes: &[u8; HAWK_512_SIGNATURE_LEN]) -> &Self {
        // SAFETY: `#[repr(transparent)]` over `[u8; HAWK_512_SIGNATURE_LEN]`.
        unsafe { &*(bytes as *const [u8; HAWK_512_SIGNATURE_LEN] as *const Self) }
    }

    /// Borrow an arbitrary slice as a `&Hawk512Signature`, length-checked.
    pub fn try_from_slice(bytes: &[u8]) -> Result<&Self, ProgramError> {
        let array: &[u8; HAWK_512_SIGNATURE_LEN] = bytes
            .try_into()
            .map_err(|_| ProgramError::InvalidArgument)?;
        Ok(Self::from_ref(array))
    }

    /// Wrap a 555-byte buffer without validation.
    pub const fn from_bytes(value: [u8; HAWK_512_SIGNATURE_LEN]) -> Self {
        Self(value)
    }

    /// Borrow the raw 555-byte wire encoding.
    pub const fn as_bytes(&self) -> &[u8; HAWK_512_SIGNATURE_LEN] {
        &self.0
    }

    /// Verify this signature over `message` against `pubkey`.
    ///
    /// Returns `false` on any failure mode — malformed signature/pubkey
    /// encoding, `sym-break` violation, `RebuildS0` out of fixed-point
    /// range, dual-prime `PolyQnorm` mismatch, or the `Q`-norm exceeding
    /// the HAWK-512 bound. Never panics. Distinguishing the failure reason
    /// is intentionally unsupported.
    #[inline(never)]
    pub fn verify(&self, message: &[u8], pubkey: &Hawk512Pubkey) -> bool {
        verify(&pubkey.0, message, &self.0)
    }

    /// Verify against a [`Hawk512PreparedPubkey`].
    ///
    /// Semantically identical to [`verify`](Self::verify) but skips all
    /// pubkey-only work — `DecodePublic`, `SHAKE256(pub)`, the two
    /// `RebuildS0` FFTs of `q00`/`q01`, and the two per-prime `PolyQnorm`
    /// NTTs of `q00`/`q01` plus the `q̂00⁻¹` batch inversion — because those
    /// were precomputed into the prepared pubkey. Returns `false` on any
    /// failure mode; never panics.
    #[inline(never)]
    pub fn verify_with_prepared(&self, message: &[u8], prepared: &Hawk512PreparedPubkey) -> bool {
        verify_prepared(prepared, message, &self.0)
    }
}

/// Precomputed, verification-ready form of a HAWK-512 public key.
///
/// A standard HAWK verifier decodes the wire pubkey and re-derives its
/// FFT/NTT forms on **every** verification. On a blockchain the same pubkey
/// is verified many times over its lifetime and storage is rent-paid, so it
/// pays to do that pubkey-only work once and store the result. This holds:
///
/// - `α`, `q̂00 = FFT(c_q00·z00)`, `q̂01 = FFT(c_q01·q01)` — the `RebuildS0`
///   fixed-point FFT factors (2 of its 3 forward FFTs);
/// - per prime `p ∈ {p₁, p₂}`: `q̂00`, `q̂00⁻¹`, `q̂01` in NTT form — 2 of
///   `PolyQnorm`'s 4 NTTs and its whole batch inversion;
/// - `hpub = SHAKE256(pub)[0:32]` — so `verify_with_prepared` skips hashing
///   the 1024-byte pubkey.
///
/// `verify_with_prepared` then only transforms the signature-dependent
/// halves. Produce one with [`Hawk512Pubkey::prepare_into`] (on-chain at
/// registration, written straight into an account, or off-chain) or
/// [`Hawk512PreparedPubkey::from_bytes`] for a previously serialised /
/// compile-time-baked blob. The wire format
/// ([`HAWK_512_PREPARED_PUBKEY_LEN`] bytes, little-endian) is **specific to
/// this crate** — it is not interoperable with other HAWK implementations.
///
/// `#[repr(C, align(8))]` with the `i64` array first keeps the layout
/// padding-free and 8-byte aligned, so [`as_bytes`](Self::as_bytes) /
/// [`from_ref`](Self::from_ref) are zero-copy.
///
/// `α` and `q̂00` (the RebuildS0 FFT form of the pubkey) are *not* stored:
/// their only on-chain use was the divide-loop divisor `v = α + q̂00[u]`
/// and its validity bound, which are fully pubkey-determined — so
/// `pvbound[u] = (1≪32)·v` is precomputed instead (and `0 < v < 2³⁰`
/// validated at prepare time). That folds an add, two comparisons and two
/// multiplies out of every divide-loop iteration *and* is 8 bytes smaller
/// than storing `α` + `q̂00`.
// No `#[derive(Clone)]`: cloning would return the 18 KiB struct by value,
// a frame the 4 KiB SBF stack cannot hold (it would trip the linker's
// stack-offset check the same way an owned `prepare` result does). The
// prepared pubkey is always borrowed in place (`from_ref`/`try_from_slice`)
// or written through `&mut` (`prepare_into`) — never moved by value.
#[repr(C, align(8))]
pub struct Hawk512PreparedPubkey {
    pvbound: [i64; N / 2],
    fq01: [i64; N],
    p1_q00n: [u32; N],
    p1_q00inv: [u32; N],
    p1_q01n: [u32; N],
    p2_q00n: [u32; N],
    p2_q00inv: [u32; N],
    p2_q01n: [u32; N],
    hpub: [u8; HPUB_LEN],
}

const _: () = assert!(
    core::mem::size_of::<Hawk512PreparedPubkey>() == HAWK_512_PREPARED_PUBKEY_LEN,
    "prepared pubkey layout has unexpected padding",
);

impl Hawk512PreparedPubkey {
    /// Serialise to the canonical [`HAWK_512_PREPARED_PUBKEY_LEN`]-byte
    /// little-endian blob (zero-copy: a borrow of the in-memory layout).
    ///
    /// On a little-endian target (every Solana SBF target is LE) this is the
    /// exact byte image; round-trips through [`from_bytes`](Self::from_bytes).
    pub const fn as_bytes(&self) -> &[u8; HAWK_512_PREPARED_PUBKEY_LEN] {
        // SAFETY: `#[repr(C, align(8))]`, no padding (static-asserted above),
        // every field is plain integers — a valid byte image of any
        // alignment ≤ 8.
        unsafe { &*(self as *const Self as *const [u8; HAWK_512_PREPARED_PUBKEY_LEN]) }
    }

    /// Reconstruct an **owned** prepared pubkey from a
    /// [`HAWK_512_PREPARED_PUBKEY_LEN`]-byte blob produced by
    /// [`as_bytes`](Self::as_bytes). No validation (the bytes are trusted
    /// crate output); a corrupt blob simply fails to verify.
    ///
    /// This materialises the full ~18 KiB struct by value. That is fine in a
    /// `const` context (evaluated at compile time — no stack frame) or off
    /// the SBF target (a host has a large stack), **but it must not be
    /// called at SBF runtime**: 18 KiB exceeds the 4 KiB SBF stack frame.
    /// On-chain, borrow the bytes in place instead —
    /// [`from_ref`](Self::from_ref) / [`try_from_slice`](Self::try_from_slice)
    /// for an account blob, or, for a fixed compile-time-baked key, an
    /// 8-aligned `static` borrowed zero-copy:
    ///
    /// ```ignore
    /// #[repr(C, align(8))]
    /// struct Aligned([u8; HAWK_512_PREPARED_PUBKEY_LEN]);
    /// static PK: Aligned = Aligned(*include_bytes!("hawk.prepared"));
    /// let prepared = unsafe { Hawk512PreparedPubkey::from_ref(&PK.0) };
    /// ```
    ///
    /// (`#[inline]` so this large-by-value function is codegen'd only at the
    /// host/const call sites that use it, and is never emitted as an SBF
    /// symbol — its mere presence would otherwise trip the linker's
    /// stack-offset check.) Arbitrary keys registered at runtime use
    /// [`Hawk512Pubkey::prepare_into`] on-chain instead.
    #[inline]
    pub const fn from_bytes(bytes: [u8; HAWK_512_PREPARED_PUBKEY_LEN]) -> Self {
        // Manual LE decode (const fn can't transmute a byte array whose
        // alignment it can't prove). `o` walks the blob field by field.
        let mut p = Self {
            pvbound: [0; N / 2],
            fq01: [0; N],
            p1_q00n: [0; N],
            p1_q00inv: [0; N],
            p1_q01n: [0; N],
            p2_q00n: [0; N],
            p2_q00inv: [0; N],
            p2_q01n: [0; N],
            hpub: [0; HPUB_LEN],
        };
        let mut o = 0usize;
        o = fill_i64(&bytes, o, &mut p.pvbound);
        o = fill_i64(&bytes, o, &mut p.fq01);
        o = fill_u32(&bytes, o, &mut p.p1_q00n);
        o = fill_u32(&bytes, o, &mut p.p1_q00inv);
        o = fill_u32(&bytes, o, &mut p.p1_q01n);
        o = fill_u32(&bytes, o, &mut p.p2_q00n);
        o = fill_u32(&bytes, o, &mut p.p2_q00inv);
        o = fill_u32(&bytes, o, &mut p.p2_q01n);
        let mut k = 0;
        while k < HPUB_LEN {
            p.hpub[k] = bytes[o + k];
            k += 1;
        }
        p
    }

    /// Borrow a fixed-size byte blob as a `&Hawk512PreparedPubkey` with no
    /// copy.
    ///
    /// # Safety
    ///
    /// `bytes` must be **8-byte aligned**. Solana serialises both account
    /// data and instruction data on an 8-byte boundary, so a prepared blob
    /// stored at the start of either is aligned in practice; a blob at an
    /// arbitrary offset of an owned `Vec<u8>` may not be. Use
    /// [`from_bytes`](Self::from_bytes) when alignment is unknown.
    pub const unsafe fn from_ref(bytes: &[u8; HAWK_512_PREPARED_PUBKEY_LEN]) -> &Self {
        // SAFETY: caller guarantees 8-byte alignment; layout is an exact,
        // padding-free byte image of `Self` (static-asserted).
        unsafe { &*(bytes as *const [u8; HAWK_512_PREPARED_PUBKEY_LEN] as *const Self) }
    }

    /// Length-checked [`from_ref`](Self::from_ref): borrows a slice as a
    /// `&Hawk512PreparedPubkey` with no copy.
    ///
    /// # Safety
    ///
    /// Same 8-byte-alignment requirement as [`from_ref`](Self::from_ref).
    pub unsafe fn try_from_slice(bytes: &[u8]) -> Result<&Self, ProgramError> {
        let array: &[u8; HAWK_512_PREPARED_PUBKEY_LEN] = bytes
            .try_into()
            .map_err(|_| ProgramError::InvalidArgument)?;
        // SAFETY: forwarded to the caller's contract.
        Ok(unsafe { Self::from_ref(array) })
    }
}

/// const-fn LE-decode a `[u32; N]` field out of the blob; returns the new
/// offset. (`u32`/`i32` share LE byte layout, so the `i32` field reuses it
/// via a transmute-free `as` round-trip below.)
const fn fill_u32(
    bytes: &[u8; HAWK_512_PREPARED_PUBKEY_LEN],
    mut o: usize,
    out: &mut [u32; N],
) -> usize {
    let mut i = 0;
    while i < N {
        out[i] = u32::from_le_bytes([bytes[o], bytes[o + 1], bytes[o + 2], bytes[o + 3]]);
        o += 4;
        i += 1;
    }
    o
}

/// As [`fill_u32`] but for an `[i64; L]` field (`pvbound`: L = N/2;
/// `fq01`: L = N).
const fn fill_i64<const L: usize>(
    bytes: &[u8; HAWK_512_PREPARED_PUBKEY_LEN],
    mut o: usize,
    out: &mut [i64; L],
) -> usize {
    let mut i = 0;
    while i < L {
        out[i] = i64::from_le_bytes([
            bytes[o],
            bytes[o + 1],
            bytes[o + 2],
            bytes[o + 3],
            bytes[o + 4],
            bytes[o + 5],
            bytes[o + 6],
            bytes[o + 7],
        ]);
        o += 8;
        i += 1;
    }
    o
}

impl Hawk512Pubkey {
    /// Decode this wire pubkey and write its [`Hawk512PreparedPubkey`]
    /// straight into `out` (the canonical [`HAWK_512_PREPARED_PUBKEY_LEN`]-byte
    /// little-endian blob).
    ///
    /// Runs `DecodePublic`, the two pubkey-only `RebuildS0` FFTs, the two
    /// per-prime `PolyQnorm` NTTs + `q̂00⁻¹` batch inversion, and
    /// `SHAKE256(pub)`. This **is** the intended on-chain registration path:
    /// run it **once** when a key is first seen, keep `out` in an account,
    /// and every later signature then verifies via the cheap
    /// [`verify_with_prepared`](Hawk512Signature::verify_with_prepared). The
    /// ~18 KiB result is written in place into the caller's buffer (an
    /// account) and never touches the SBF stack; the transient working set
    /// is split across `#[inline(never)]` frames, each ≤ 4 KiB, exactly like
    /// [`verify`](Hawk512Signature::verify).
    ///
    /// `out` must be **8-byte aligned** (Solana account data always is).
    /// `Err(InvalidArgument)` if it is not, if the wire encoding is
    /// malformed, or if `q00` is not invertible modulo a prime. On error
    /// `out` may be left partially written and must not be trusted.
    pub fn prepare_into(
        &self,
        out: &mut [u8; HAWK_512_PREPARED_PUBKEY_LEN],
    ) -> Result<(), ProgramError> {
        // Solana serialises account data on an 8-byte boundary, so on-chain
        // this never fails; it keeps the in-place reinterpret below sound
        // for every caller (a misaligned `&mut Self` write would be UB).
        if !(out.as_ptr() as usize).is_multiple_of(8) {
            return Err(ProgramError::InvalidArgument);
        }
        // SAFETY: `out` is `HAWK_512_PREPARED_PUBKEY_LEN` bytes and (checked
        // above) 8-aligned; `Hawk512PreparedPubkey` is `#[repr(C, align(8))]`,
        // padding-free, exactly that size (static-asserted), every field a
        // plain integer. The `prep_*` chain fully writes every field before
        // it is read, so no uninitialised byte is observed as a typed value.
        let p: &mut Hawk512PreparedPubkey =
            unsafe { &mut *(out.as_mut_ptr() as *mut Hawk512PreparedPubkey) };
        prep_a(&self.0, p)
    }
}

/// `HawkVerify` pubkey-side precompute (spec Algorithm 20 lines 5–9 plus the
/// pubkey-only FFT/NTT factors). Same frame-splitting rationale as
/// [`verify`]: the transient working set (`q00`, `q01`, the two `q̂00`
/// halves) is ~8 KiB and cannot fit one 4 KiB SBF stack frame, so each
/// large buffer is the sole big local of its own `#[inline(never)]` frame
/// and is threaded inward by reference. The 18 KiB result is written
/// through `p` into the caller's off-stack buffer (an account) — it is
/// never a stack value, so this whole chain stays within the frame cap and
/// is safe to run on-chain at registration time.
///
/// `prep_a` owns `q00` (live through both `prepare_ntt`s).
#[inline(never)]
fn prep_a(pub_: &[u8; PUBKEY_LEN], p: &mut Hawk512PreparedPubkey) -> Result<(), ProgramError> {
    let mut q00 = [0i32; N];
    prep_b(pub_, p, &mut q00)
}

/// Owns `q01` (live through both `prepare_ntt`s); `DecodePublic → (q00,q01)`.
#[inline(never)]
fn prep_b(
    pub_: &[u8; PUBKEY_LEN],
    p: &mut Hawk512PreparedPubkey,
    q00: &mut [i32; N],
) -> Result<(), ProgramError> {
    let mut q01 = [0i32; N];
    // 5–8: DecodePublic → (q00, q01)
    if !codec::decode_public(pub_, q00, &mut q01) {
        return Err(ProgramError::InvalidArgument);
    }
    prep_c(pub_, p, q00, &q01)
}

/// Owns the `q̂00` real half (the only part `prepare_divisor` consumes).
#[inline(never)]
fn prep_c(
    pub_: &[u8; PUBKEY_LEN],
    p: &mut Hawk512PreparedPubkey,
    q00: &[i32; N],
    q01: &[i32; N],
) -> Result<(), ProgramError> {
    let mut fq00_re = [0i64; N / 2];
    prep_d(pub_, p, q00, q01, &mut fq00_re)
}

/// Transient owner of the `q̂00` imaginary half (pure FFT scratch, its 2 KiB
/// frame freed before the NTTs). Computes `q̂01` (→ `p.fq01`, into the
/// account) and the divide-loop bounds (→ `p.pvbound`).
#[inline(never)]
fn prep_d(
    pub_: &[u8; PUBKEY_LEN],
    p: &mut Hawk512PreparedPubkey,
    q00: &[i32; N],
    q01: &[i32; N],
    fq00_re: &mut [i64; N / 2],
) -> Result<(), ProgramError> {
    let mut fq00_im = [0i64; N / 2];
    let Some(alpha) = fft::prepare_fft(q00, q01, fq00_re, &mut fq00_im, &mut p.fq01) else {
        return Err(ProgramError::InvalidArgument);
    };
    if !fft::prepare_divisor(fq00_re, alpha, &mut p.pvbound) {
        return Err(ProgramError::InvalidArgument);
    }
    prep_e(pub_, p, q00, q01)
}

/// No large local: the two per-prime NTT precomputes (the `[u32; N]` factors
/// written straight into the account) and `hpub = SHAKE256(pub)`.
#[inline(never)]
fn prep_e(
    pub_: &[u8; PUBKEY_LEN],
    p: &mut Hawk512PreparedPubkey,
    q00: &[i32; N],
    q01: &[i32; N],
) -> Result<(), ProgramError> {
    if !ntt::prepare_ntt(
        q00,
        q01,
        ntt::P1,
        &mut p.p1_q00n,
        &mut p.p1_q00inv,
        &mut p.p1_q01n,
    ) {
        return Err(ProgramError::InvalidArgument);
    }
    if !ntt::prepare_ntt(
        q00,
        q01,
        ntt::P2,
        &mut p.p2_q00n,
        &mut p.p2_q00inv,
        &mut p.p2_q01n,
    ) {
        return Err(ProgramError::InvalidArgument);
    }
    p.hpub = codec::compute_hpub(pub_);
    Ok(())
}

/// `HawkVerify` with the pubkey factors precomputed (spec Algorithm 20 with
/// lines 5–9 and the pubkey-side FFT/NTT precomputed). Same frame-splitting
/// rationale as [`verify`]; the long-lived `w1` lives in `vp_a`'s frame.
fn verify_prepared(p: &Hawk512PreparedPubkey, message: &[u8], sig: &[u8; SIGNATURE_LEN]) -> bool {
    let mut w1 = [0i32; N];
    vp_a(p, message, sig, &mut w1)
}

/// Owns `h0` (live through `RebuildS0`); fills `w1`/`h0`, then `sym-break`.
#[inline(never)]
fn vp_a(
    p: &Hawk512PreparedPubkey,
    message: &[u8],
    sig: &[u8; SIGNATURE_LEN],
    w1: &mut [i32; N],
) -> bool {
    let mut h0 = [0i32; N];
    if !fill_w1_h0_prepared(&p.hpub, message, sig, w1, &mut h0) {
        return false;
    }
    if !codec::sym_break(w1) {
        return false;
    }
    vp_b(p, w1, &h0)
}

/// `DecodeSignature`, `M ← SHAKE256(m‖hpub)`, then the transient `s1`/`h1`
/// frames (freed before `RebuildS0`). `hpub` is precomputed.
#[inline(never)]
fn fill_w1_h0_prepared(
    hpub: &[u8; HPUB_LEN],
    message: &[u8],
    sig: &[u8; SIGNATURE_LEN],
    w1: &mut [i32; N],
    h0: &mut [i32; N],
) -> bool {
    let mut s1 = [0i32; N];
    let Some(salt) = codec::decode_signature(sig, &mut s1) else {
        return false;
    };
    let mut salt_buf = [0u8; SALT_LEN];
    salt_buf.copy_from_slice(salt);
    let m = codec::compute_m(message, hpub);
    fill_w1_h0_2(&m, &salt_buf, &s1, w1, h0)
}

/// Owns `w0`. Prepared `RebuildS0` (1 FFT), then prepared dual-prime
/// `PolyQnorm` + bound.
#[inline(never)]
fn vp_b(p: &Hawk512PreparedPubkey, w1: &[i32; N], h0: &[i32; N]) -> bool {
    let mut w0 = [0i32; N];
    if !fft::rebuild_s0_prepared(&p.pvbound, &p.fq01, w1, h0, &mut w0) {
        return false;
    }
    ntt::qnorm_in_bound_prepared(
        &p.p1_q00n,
        &p.p1_q00inv,
        &p.p1_q01n,
        &p.p2_q00n,
        &p.p2_q00inv,
        &p.p2_q01n,
        &w0,
        w1,
    )
}

/// `HawkVerify` (spec Algorithm 20).
///
/// The verification working set (`q00`, `q01`, `w1`, `w0`, plus transient
/// `s1`/`h0`/`h1`) is ~14 KiB and cannot fit one Solana SBF stack frame
/// (capped at 4 KiB), and SBF forbids writable globals. So the "arena"
/// lives **on the stack, split across frames**: each 2 KiB polynomial is
/// the sole large local of its own `#[inline(never)]` frame and is
/// threaded inward by reference. SBF allows deep call chains (≤64 frames),
/// so the long-lived buffers simply sit in ancestor frames while the
/// inner phases run. `fft::rebuild_s0` and `ntt::qnorm_in_bound` apply the
/// same frame-splitting to their own scratch.
fn verify(pub_: &[u8; PUBKEY_LEN], message: &[u8], sig: &[u8; SIGNATURE_LEN]) -> bool {
    let mut q00 = [0i32; N];
    v_a(pub_, message, sig, &mut q00)
}

/// Owns `q00`; decodes the public key (also yielding `q01`).
#[inline(never)]
fn v_a(
    pub_: &[u8; PUBKEY_LEN],
    message: &[u8],
    sig: &[u8; SIGNATURE_LEN],
    q00: &mut [i32; N],
) -> bool {
    let mut q01 = [0i32; N];
    // 5–8: DecodePublic → (q00, q01)
    if !codec::decode_public(pub_, q00, &mut q01) {
        return false;
    }
    v_b(pub_, message, sig, q00, &q01)
}

/// Owns `w1` (live through `PolyQnorm`).
#[inline(never)]
fn v_b(
    pub_: &[u8; PUBKEY_LEN],
    message: &[u8],
    sig: &[u8; SIGNATURE_LEN],
    q00: &[i32; N],
    q01: &[i32; N],
) -> bool {
    let mut w1 = [0i32; N];
    v_c(pub_, message, sig, q00, q01, &mut w1)
}

/// Owns `h0` (live through `RebuildS0`); fills `w1` and `h0`, then
/// `sym-break`.
#[inline(never)]
fn v_c(
    pub_: &[u8; PUBKEY_LEN],
    message: &[u8],
    sig: &[u8; SIGNATURE_LEN],
    q00: &[i32; N],
    q01: &[i32; N],
    w1: &mut [i32; N],
) -> bool {
    let mut h0 = [0i32; N];
    if !fill_w1_h0(pub_, message, sig, w1, &mut h0) {
        return false;
    }
    // 13–14: sym-break(w1)
    if !codec::sym_break(w1) {
        return false;
    }
    v_d(q00, q01, w1, &h0)
}

/// Transient owner of `s1`. Decodes the signature, hashes `hpub`/`M`, then
/// delegates so its (and `h1`'s) 2 KiB frame is freed before `RebuildS0`.
#[inline(never)]
fn fill_w1_h0(
    pub_: &[u8; PUBKEY_LEN],
    message: &[u8],
    sig: &[u8; SIGNATURE_LEN],
    w1: &mut [i32; N],
    h0: &mut [i32; N],
) -> bool {
    // 1–4: DecodeSignature → (salt, s1)
    let mut s1 = [0i32; N];
    let Some(salt) = codec::decode_signature(sig, &mut s1) else {
        return false;
    };
    let mut salt_buf = [0u8; SALT_LEN];
    salt_buf.copy_from_slice(salt);
    // 9–11: hpub = SHAKE256(pub); M = SHAKE256(m ‖ hpub)
    let hpub = codec::compute_hpub(pub_);
    let m = codec::compute_m(message, &hpub);
    fill_w1_h0_2(&m, &salt_buf, &s1, w1, h0)
}

/// Transient owner of `h1`. `(h0,h1) ← SHAKE256(M‖salt)`; `w1 ← h1 − 2·s1`.
#[inline(never)]
fn fill_w1_h0_2(
    m: &[u8; 64],
    salt: &[u8],
    s1: &[i32; N],
    w1: &mut [i32; N],
    h0: &mut [i32; N],
) -> bool {
    // `compute_h` expands `h0` and fuses `w1 ← h1 − 2·s1` directly (no
    // separate `h1` buffer / pass).
    codec::compute_h(m, salt, h0, w1, s1);
    true
}

/// Owns `w0`. `RebuildS0` then the dual-prime `PolyQnorm` + bound check.
#[inline(never)]
fn v_d(q00: &[i32; N], q01: &[i32; N], w1: &[i32; N], h0: &[i32; N]) -> bool {
    let mut w0 = [0i32; N];
    // 15–17: w0 ← RebuildS0(q00, q01, w1, h0)
    if !fft::rebuild_s0(q00, q01, w1, h0, &mut w0) {
        return false;
    }
    // 18–25: dual-prime PolyQnorm + the 8n·σ²_verify bound
    ntt::qnorm_in_bound(q00, q01, &w0, w1)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_wrong_length_inputs() {
        assert!(Hawk512Pubkey::try_from(&[0u8; 10][..]).is_err());
        assert!(Hawk512Signature::try_from(&[0u8; 10][..]).is_err());
    }

    #[test]
    fn rejects_all_zero_inputs() {
        // An all-zero signature decodes s1 = 0; w1 = h1 (random) — almost
        // surely fails sym-break or the norm bound. Must never panic / accept.
        let pk = Hawk512Pubkey::from_bytes([0u8; HAWK_512_PUBKEY_LEN]);
        let sig = Hawk512Signature::from_bytes([0u8; HAWK_512_SIGNATURE_LEN]);
        assert!(!sig.verify(b"msg", &pk));
    }

    /// Every scalar pinned in `formal_verification/Hawk512/Defs.lean` is
    /// re-asserted here. If you change a Rust constant without updating the
    /// Lean side, the per-element refinement proofs are talking about a
    /// different setting than the running code — this test breaks loudly to
    /// flag that.
    #[test]
    fn lean_scalar_constants_drift_check() {
        // ── Polynomial / log degree ────────────────────────────────────────
        // Lean: Hawk512.Spec.N, Hawk512.Spec.LOGN.
        assert_eq!(LOGN, 9);
        assert_eq!(N, 512);

        // ── Wire-format byte lengths ───────────────────────────────────────
        // Lean: Hawk512.Spec.{PUBKEY_LEN, SIGNATURE_LEN, SALT_LEN, HPUB_LEN}.
        assert_eq!(HAWK_512_PUBKEY_LEN, 1024);
        assert_eq!(HAWK_512_SIGNATURE_LEN, 555);
        assert_eq!(PUBKEY_LEN, 1024);
        assert_eq!(SIGNATURE_LEN, 555);
        assert_eq!(SALT_LEN, 24);
        assert_eq!(HPUB_LEN, 32);
        // Prepared-pubkey size formula must match the field layout.
        assert_eq!(
            HAWK_512_PREPARED_PUBKEY_LEN,
            (N / 2) * 8 + N * 8 + 6 * (N * 4) + HPUB_LEN
        );
        assert_eq!(HAWK_512_PREPARED_PUBKEY_LEN, 18_464);

        // ── Golomb–Rice parameters (per Lean Defs.lean) ────────────────────
        // Lean: LOW_00, HIGH_00, LOW_01, HIGH_01, LOW_S1, HIGH_S1, HIGH_S0.
        assert_eq!(LOW_00, 5);
        assert_eq!(HIGH_00, 9);
        assert_eq!(LOW_01, 9);
        assert_eq!(HIGH_01, 12);
        assert_eq!(LOW_S1, 5);
        assert_eq!(HIGH_S1, 9);
        assert_eq!(HIGH_S0, 13);
        // The "extra precision bits on q00[0]" count derived in `decode_public`
        // is 16 − HIGH_00 = 7.
        assert_eq!(16 - HIGH_00, 7);
    }
}
