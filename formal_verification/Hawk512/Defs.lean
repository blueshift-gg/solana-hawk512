/-
  Hawk512.Defs — Core definitions for HAWK-512 formal verification.

  Defines the two NTT primes `p₁`, `p₂`; the polynomial degree `N = 512`;
  the Rust Golomb–Rice parameters; the fixed-point RebuildS0 scaling
  constants; the spec-equivalent `1600·r ≤ 13_307_904` bound; and the
  butterfly operations (CT for the forward NTT, GS for the inverse —
  HAWK only uses GS-style for the test code, but we model both for
  completeness).

  HAWK-512 differs from Falcon-512 in three structural ways that show
  up here:
    1. Two NTT primes (`p₁`, `p₂`), each near `2³¹`. The dual-prime CRT
       reconstruction is what makes `PolyQnorm` exact.
    2. Both lazy and reduced butterfly variants on the *additive* side
       only (the twiddle product is always reduced to `[0, p)`).
    3. No analogue of Falcon's "fused last forward + pointwise + first
       inverse" — HAWK's `PolyQnorm` does not run an inverse NTT, just
       a single sum of pointwise products. The corresponding fused
       structure here is the conversion-and-first-level FFT fusion
       (covered in `Hawk512.FFT`).
-/

namespace Hawk512.Spec

-- ============================================================================
-- Constants
-- ============================================================================

/-- HAWK-512 NTT prime p₁. Prime, ≡ 1 mod 2N, fits `u32` (in fact
    < 2³¹). -/
def P1 : Nat := 2147473409

/-- HAWK-512 NTT prime p₂. Prime, ≡ 1 mod 2N, fits `u32` (in fact
    < 2³¹). -/
def P2 : Nat := 2147389441

/-- Polynomial degree. -/
def N : Nat := 512

/-- log₂ N. -/
def LOGN : Nat := 9

-- ----------------------------------------------------------------------------
-- Golomb–Rice parameters (mirror `src/lib.rs` constants)
-- ----------------------------------------------------------------------------

/-- q00 Golomb-Rice low bits (5). -/
def LOW_00 : Nat := 5
/-- q00 Golomb-Rice high (= maximum unary count, in `low + 4` form). -/
def HIGH_00 : Nat := 9

/-- q01 Golomb-Rice low bits (9). -/
def LOW_01 : Nat := 9
/-- q01 Golomb-Rice high. -/
def HIGH_01 : Nat := 12

/-- s1 Golomb-Rice low bits (5). -/
def LOW_S1 : Nat := 5
/-- s1 Golomb-Rice high. -/
def HIGH_S1 : Nat := 9

/-- s0 rejection magnitude exponent (|s0| < 2^HIGH_S0). -/
def HIGH_S0 : Nat := 13

-- ----------------------------------------------------------------------------
-- Wire/format constants
-- ----------------------------------------------------------------------------

/-- Wire-encoded HAWK-512 public key length (bytes). -/
def PUBKEY_LEN : Nat := 1024
/-- Wire-encoded HAWK-512 signature length (bytes). -/
def SIGNATURE_LEN : Nat := 555
/-- Salt length (bytes). -/
def SALT_LEN : Nat := 24
/-- `hpub` SHAKE256 output length (bytes). -/
def HPUB_LEN : Nat := 32

-- ----------------------------------------------------------------------------
-- Verification bound (spec §3.5.3 / Alg 20 lines 22-24)
-- ----------------------------------------------------------------------------

/-- The spec's `8n·σ²_verify` with `n = 512`, `σ_verify = 57/40` is
    exactly `13_307_904/1600`. The Rust code checks
    `1600 · r ≤ 13_307_904` (`r` is the per-prime PolyQnorm result
    divided by `n`), avoiding the rational. -/
def BOUND_NUM : Nat := 13307904
/-- The multiplier the Rust check applies to `r` before comparison
    with [`BOUND_NUM`]. -/
def BOUND_DEN : Nat := 1600

-- ----------------------------------------------------------------------------
-- RebuildS0 fixed-point scaling constants (`src/fft.rs`, derived from
-- the spec's `high_s1 = high_00 = 9`, `high_01 = 12`, `n = 512`).
-- ----------------------------------------------------------------------------

/-- `C_W1 = 2^(29-(1+high_s1)) = 2^19`. -/
def C_W1 : Nat := 1 <<< 19
/-- `C_Q00 = 2^(29-high_00) = 2^20`. -/
def C_Q00 : Nat := 1 <<< 20
/-- `C_Q01 = 2^(29-high_01) = 2^17`. -/
def C_Q01 : Nat := 1 <<< 17
/-- `C_S0 = (2·C_W1·C_Q01)/(n·C_Q00) = 2^8`. -/
def C_S0 : Nat := 256
/-- `log₂(2·C_S0) = 9` — the spec's `s0` rounding divisor is a power of
    two, so the floor-division becomes an arithmetic shift. -/
def LOG2_TWO_C_S0 : Nat := 9

-- ============================================================================
-- Modular arithmetic
-- ============================================================================

/-- Reduce a natural number modulo `p`. -/
@[inline] def modP (p : Nat) (a : Nat) : Nat := a % p

/-- Modular addition. -/
@[inline] def addP (p : Nat) (a b : Nat) : Nat := (a + b) % p

/-- Modular subtraction via the `+ p - b` Rust idiom. -/
@[inline] def subP (p : Nat) (a b : Nat) : Nat := (a + p - b) % p

/-- Modular multiplication. -/
@[inline] def mulP (p : Nat) (a b : Nat) : Nat := (a * b) % p

/-- Modular exponentiation by repeated squaring. -/
def powP (p base exp : Nat) : Nat :=
  if exp = 0 then 1
  else if exp % 2 = 0 then
    let half := powP p base (exp / 2)
    mulP p half half
  else
    mulP p (base % p) (powP p base (exp - 1))
termination_by exp
decreasing_by all_goals omega

-- ============================================================================
-- Basic modular arithmetic properties
-- ============================================================================

theorem p1_pos : P1 > 0 := by unfold P1; omega
theorem p2_pos : P2 > 0 := by unfold P2; omega

theorem modP_lt (p : Nat) (hp : p > 0) (a : Nat) : modP p a < p := Nat.mod_lt a hp
theorem addP_lt (p : Nat) (hp : p > 0) (a b : Nat) : addP p a b < p := Nat.mod_lt _ hp
theorem subP_lt (p : Nat) (hp : p > 0) (a b : Nat) : subP p a b < p := Nat.mod_lt _ hp
theorem mulP_lt (p : Nat) (hp : p > 0) (a b : Nat) : mulP p a b < p := Nat.mod_lt _ hp

-- ============================================================================
-- CT (Cooley–Tukey) butterfly — used by the forward NTT in `src/ntt.rs`
-- ============================================================================

/-- A CT butterfly output (or any forward / inverse butterfly output). -/
structure ButterflyResult where
  lo : Nat
  hi : Nat

/-- CT butterfly with **full** reduction on every output. -/
def ctButterflyFull (p a b zeta : Nat) : ButterflyResult :=
  let y := mulP p b zeta
  { lo := addP p a y, hi := subP p a y }

/-- CT butterfly with **lazy** additive reduction: the twiddle product
    `y = b·zeta mod p` is reduced (so `y < p`), but the two additive
    outputs are stored as `a + y` and `a + p − y` without `% p`. With
    `a < p` (inputs to a lazy level always come from a `full` level, so
    they are reduced) and `y < p`, both stored values are `< 2p < 2³²`. -/
def ctButterflyLazy (p a b zeta : Nat) : ButterflyResult :=
  let y := mulP p b zeta
  { lo := a + y, hi := a + p - y }

-- ============================================================================
-- GS (Gentleman–Sande) butterfly — used by the inverse NTT test code
-- (`ntt_is_negacyclic_convolution` in `src/ntt.rs`). HAWK's verify path
-- does **not** run a GS-based inverse NTT (PolyQnorm sums NTT-domain
-- products instead of inverting), but we model GS for completeness so
-- the round-trip lemma in `Hawk512.NTT` can quote both.
-- ============================================================================

/-- GS butterfly with full reduction. -/
def gsButterflyFull (p a b zeta : Nat) : ButterflyResult :=
  { lo := addP p a b, hi := mulP p (subP p a b) zeta }

end Hawk512.Spec
