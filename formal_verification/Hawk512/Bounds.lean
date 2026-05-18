/-
  Hawk512.Bounds — Arithmetic safety lemmas under the lazy-reduction
  invariants.

  Each theorem here takes the lazy-NTT level invariant as a *hypothesis*
  and proves that, under that invariant, the arithmetic in `src/ntt.rs`
  does not overflow its storage type. The structural fact — that the
  invariant actually holds level-by-level over the actual NTT loop — is
  checked operationally by the proptests / KAT cross-check / Mollusk SBF
  tests, exactly as in Falcon. The lemmas here are the "if the invariant
  holds, the arithmetic is safe" half of the picture.

  The HAWK invariant is qualitatively simpler than Falcon's `(K+1)·Q`
  level invariant: HAWK only ever defers the *additive* reductions
  (never the multiply), so a lazy level's outputs are in `[0, 2p)` —
  with `p < 2³¹` that's `< 2³²`, comfortably inside `u32`, regardless
  of how many lazy levels precede a `full` one (in practice they
  always alternate, see `src/ntt.rs::ntt`). So the bounds here are
  per-level, not cumulative.
-/

import Hawk512.Defs

namespace Hawk512.Spec.Bounds

open Hawk512.Spec

-- ============================================================================
-- Per-prime upper bounds
-- ============================================================================

/-- Both HAWK primes are below `2³¹`. -/
theorem p1_lt_2_31 : P1 < 2^31 := by unfold P1; omega
theorem p2_lt_2_31 : P2 < 2^31 := by unfold P2; omega

/-- Consequently `2·p < 2³²` for both primes — the structural fact that
    lets the lazy CT/GS outputs (`a + y`, `a + p − y` with `a < p, y < p`)
    fit a `u32` lane without `% p`. -/
theorem two_p1_lt_2_32 : 2 * P1 < 2^32 := by unfold P1; omega
theorem two_p2_lt_2_32 : 2 * P2 < 2^32 := by unfold P2; omega

-- ============================================================================
-- Theorem: u32 storage of reduced and lazy coefficients
-- ============================================================================

/-- Any reduced coefficient (`< p`) fits `u32` for `p ∈ {P1, P2}`. -/
theorem reduced_fits_u32_p1 (a : Nat) (h : a < P1) : a < 2^32 := by
  have := p1_lt_2_31; unfold P1 at *; omega
theorem reduced_fits_u32_p2 (a : Nat) (h : a < P2) : a < 2^32 := by
  have := p2_lt_2_31; unfold P2 at *; omega

/-- A lazy-level CT output sum `a + y` with `a < p, y < p` fits `u32`. -/
theorem lazy_sum_fits_u32_p1 (a y : Nat) (ha : a < P1) (hy : y < P1) :
    a + y < 2^32 := by
  have := p1_lt_2_31; unfold P1 at *; omega
theorem lazy_sum_fits_u32_p2 (a y : Nat) (ha : a < P2) (hy : y < P2) :
    a + y < 2^32 := by
  have := p2_lt_2_31; unfold P2 at *; omega

/-- A lazy-level CT output diff `a + p − y` (with `a < p, y < p`, so
    `a + p ≥ y`) is non-negative and fits `u32`. -/
theorem lazy_diff_fits_u32_p1 (a y : Nat) (ha : a < P1) (hy : y < P1) :
    a + P1 - y < 2^32 := by
  have := p1_lt_2_31; unfold P1 at *; omega
theorem lazy_diff_fits_u32_p2 (a y : Nat) (ha : a < P2) (hy : y < P2) :
    a + P2 - y < 2^32 := by
  have := p2_lt_2_31; unfold P2 at *; omega

-- ============================================================================
-- Theorem: u64 storage of the multiply temporary
-- ============================================================================

/-- The full-level NTT multiply `b · zeta` (both `< p`) fits `u64`. The
    Rust code keeps `(a · b) % p` (the `mulmod`); the intermediate
    product `a·b` is the only u64 temporary in the hot path. -/
theorem mul_fits_u64_p1 (b zeta : Nat) (hb : b < P1) (hz : zeta < P1) :
    b * zeta < 2^64 := by
  have hb' : b ≤ P1 - 1 := by omega
  have hz' : zeta ≤ P1 - 1 := by omega
  calc b * zeta ≤ (P1 - 1) * (P1 - 1) := Nat.mul_le_mul hb' hz'
    _ < 2^64 := by unfold P1; omega
theorem mul_fits_u64_p2 (b zeta : Nat) (hb : b < P2) (hz : zeta < P2) :
    b * zeta < 2^64 := by
  have hb' : b ≤ P2 - 1 := by omega
  have hz' : zeta ≤ P2 - 1 := by omega
  calc b * zeta ≤ (P2 - 1) * (P2 - 1) := Nat.mul_le_mul hb' hz'
    _ < 2^64 := by unfold P2; omega

/-- The lazy-level multiply consumer (multiplier is a fully reduced
    twiddle, multiplicand is a lazy-level output `< 2p`) still fits
    `u64`: `2p · p < 2·2³¹·2³¹ = 2⁶³`. So `% p` after the multiply is
    sound on either lane. -/
theorem lazy_mul_fits_u64_p1 (a zeta : Nat) (ha : a < 2 * P1) (hz : zeta < P1) :
    a * zeta < 2^64 := by
  have ha' : a ≤ 2 * P1 - 1 := by omega
  have hz' : zeta ≤ P1 - 1 := by omega
  calc a * zeta ≤ (2 * P1 - 1) * (P1 - 1) := Nat.mul_le_mul ha' hz'
    _ < 2^64 := by unfold P1; omega
theorem lazy_mul_fits_u64_p2 (a zeta : Nat) (ha : a < 2 * P2) (hz : zeta < P2) :
    a * zeta < 2^64 := by
  have ha' : a ≤ 2 * P2 - 1 := by omega
  have hz' : zeta ≤ P2 - 1 := by omega
  calc a * zeta ≤ (2 * P2 - 1) * (P2 - 1) := Nat.mul_le_mul ha' hz'
    _ < 2^64 := by unfold P2; omega

-- ============================================================================
-- Theorem: `Σ ĉ[i]` final sum fits u64 with one terminal `% p`
-- ============================================================================
--
-- The Rust hot loop (see `pq_e` / `qp_c`) accumulates 2N reduced
-- products (each `< p`) into a u64 running sum and then applies one
-- `% p`. We confirm `2N · p < 2⁶⁴` so the accumulation never overflows.

/-- `2N · p₁ < 2⁶⁴`, so the `Σ ĉ` accumulator's `2N` reduced terms
    (each `< p`) never overflow `u64`. -/
theorem sum_qhat_fits_u64_p1 : 2 * N * P1 < 2^64 := by
  unfold N P1; omega
/-- `2N · p₂ < 2⁶⁴`. -/
theorem sum_qhat_fits_u64_p2 : 2 * N * P2 < 2^64 := by
  unfold N P2; omega

-- ============================================================================
-- Theorem: the signed coefficient reduction `red()` is in-range
-- ============================================================================
--
-- `src/ntt.rs::red` reduces a signed i32 input into [0, p) without
-- division, by `x ≥ 0 ? x : x + p`. Soundness relies on `|x| < p` for
-- every input — which holds because all signed inputs (decoded
-- q00/q01/s1 with `|·| ≤ 2^HIGH_S1 = 512`, and w0/w1 from RebuildS0
-- with `|·| ≤ 2^HIGH_S0 = 8192`) are well under `p`.

/-- A signed integer of magnitude `≤ M` with `M < p` has `red(x) ∈ [0, p)`.
    Stated as a pure-Nat predicate: the "lifted" value (`x` if `x ≥ 0`,
    `p − |x|` if `x < 0`) lies in `[0, p)` whenever `|x| ≤ M < p`.

    We don't model `Int` here; instead we case-split on whether the
    input is non-negative (`x : Nat`) or strictly negative
    (`x : ℕ⁺`, i.e. the magnitude is at least 1). The proofs of both
    branches reduce to `omega` once `M < p`. -/
theorem red_nonneg_in_range_p1 (M : Nat) (hM : M < P1) (x : Nat) (h : x ≤ M) :
    x < P1 := by omega
theorem red_nonneg_in_range_p2 (M : Nat) (hM : M < P2) (x : Nat) (h : x ≤ M) :
    x < P2 := by omega

/-- The negative branch: `red(x) = p − |x|` with `1 ≤ |x| ≤ M < p` is
    in `(0, p)`, hence `< p`. -/
theorem red_neg_in_range_p1 (M absx : Nat) (hM : M < P1)
    (h1 : 1 ≤ absx) (h2 : absx ≤ M) :
    P1 - absx < P1 := by have := p1_pos; omega
theorem red_neg_in_range_p2 (M absx : Nat) (hM : M < P2)
    (h1 : 1 ≤ absx) (h2 : absx ≤ M) :
    P2 - absx < P2 := by have := p2_pos; omega

-- ============================================================================
-- Theorem: `r` and `1600·r` in the final bound check fit Lean Nat / Int
-- ============================================================================

/-- The Rust verify computes `r = (n·‖w‖²_Q) / n` and checks
    `1600·r ≤ 13_307_904`. The worst-case `r` allowed is
    `13_307_904 / 1600 = 8317` (= ⌊8317.44⌋), so `1600·r` stays well
    within the `u128` Rust uses (and the Nat we use here). This lemma
    is a small but useful sanity check: the bound's RHS itself is
    consistent. -/
theorem bound_rhs_consistent :
    BOUND_NUM = 1600 * 8317 + 704 := by
  unfold BOUND_NUM; omega

/-- `BOUND_NUM` and `BOUND_DEN` are both positive. -/
theorem bound_pos : BOUND_NUM > 0 ∧ BOUND_DEN > 0 := by
  unfold BOUND_NUM BOUND_DEN; omega

end Hawk512.Spec.Bounds
