/-
  Hawk512.PolyQnorm — Dual-prime cross-check, N-divisibility, and the
  `1600·r ≤ 13_307_904` bound.

  The Rust function `qnorm_in_bound` (see `src/ntt.rs`) decides
  acceptance of a candidate `w = (w0, w1)` by:

    1. Compute `r₁ = PolyQnorm(w, p₁)`, `r₂ = PolyQnorm(w, p₂)`.
    2. Reject if `r₁ ≠ r₂`.
    3. Reject if `r₁` is not divisible by `N`.
    4. Set `r := r₁ / N`. Accept iff `1600 · r ≤ 13_307_904`.

  This file proves the algebraic soundness of that pipeline:
    - **Why the dual-prime cross-check is sufficient.** PolyQnorm
      computes `n·‖w‖²_Q mod p` per prime. The true integer
      `R = n·‖w‖²_Q` is at most `512·(Q/2)·Q` (… much smaller than
      `p₁·p₂ ≈ 2⁶²`) for any HAWK-valid `w`, so by CRT a matching pair
      `(r₁, r₂)` uniquely identifies `R` and therefore `R = r₁ = r₂`.
    - **Why the `N`-divisibility check is the right one.** `R` is `N`
      times an integer (the `‖w‖²_Q`), so it must be a multiple of `N`.
    - **The bound is meaningful.** The bound `1600·r ≤ 13_307_904`
      matches the spec's `r ≤ 8n·σ²_verify` (with `8n·σ²_verify =
      13_307_904/1600 = 8317.44`). It is a non-trivial discriminator
      (some `r` pass, some `r` fail).

  Loop-level correctness — that `pq_a..pq_e` correctly compute
  `n·‖w‖²_Q mod p` on the actual coefficient sequence — is checked
  operationally by the proptests / KAT cross-check.
-/

import Hawk512.Defs
import Hawk512.NTT
import Hawk512.Bounds
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith

namespace Hawk512.Spec.PolyQnorm

open Hawk512.Spec

-- ============================================================================
-- The Rust decision predicate (clean Nat model)
-- ============================================================================

/-- Mirror of `qnorm_in_bound` in `src/ntt.rs`. `r1`, `r2` are the two
    per-prime PolyQnorm results (each in `[0, p)`); accept iff they
    match, the common value is divisible by `N`, and the quotient
    satisfies the bound. -/
def accept (r1 r2 : Nat) : Bool :=
  decide (r1 = r2) && decide (r1 % N = 0) && decide (1600 * (r1 / N) ≤ BOUND_NUM)

-- ============================================================================
-- CRT recovery: matching residues + small value ⇒ equal true value
-- ============================================================================

/-- If a single integer `R` is in `[0, min(p₁, p₂))`, then both its
    residues are equal to `R` itself. (Trivial direction of CRT: a
    value smaller than either prime is its own residue.) -/
theorem true_value_recovery (R : Nat)
    (h1 : R < P1) (h2 : R < P2) :
    R % P1 = R ∧ R % P2 = R :=
  ⟨Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2⟩

/-- The dual-prime check is sound *if both residues equal the same value
    `< min(p₁, p₂)`*: in that range, matching residues collapse to a
    single integer. -/
theorem dual_prime_sound (R r1 r2 : Nat)
    (h1 : R < P1) (h2 : R < P2)
    (hr1 : r1 = R % P1) (hr2 : r2 = R % P2) :
    r1 = r2 ∧ r1 = R := by
  obtain ⟨e1, e2⟩ := true_value_recovery R h1 h2
  refine ⟨?_, ?_⟩
  · rw [hr1, hr2, e1, e2]
  · rw [hr1, e1]

-- ============================================================================
-- CRT separation: distinct true values in [0, p₁·p₂) ⇒ different residue pair
-- ============================================================================

/-- **CRT separation in HAWK range.** If two non-negative integers
    `A, B < p₁ · p₂` are distinct, they cannot agree on *both* residues
    `mod p₁` and `mod p₂`. This is a standard CRT consequence for coprime
    moduli (`p₁ ≠ p₂` and both prime ⇒ coprime); we state the
    contrapositive as the load-bearing fact and reduce to Mathlib's
    `Nat.chineseRemainder` machinery.

    We use a clean Mathlib-style proof: `p₁ * p₂ ∣ (A - B)` (working in
    `Int`) follows from coprime moduli + same residues, and the bound
    `|A - B| < p₁ * p₂` forces `A = B`. -/
theorem dual_prime_separation (A B : Nat)
    (hA : A < P1 * P2) (hB : B < P1 * P2)
    (h1 : A % P1 = B % P1) (h2 : A % P2 = B % P2) :
    A = B := by
  have hp1p : Nat.Prime P1 := NTT.p1_prime
  have hp2p : Nat.Prime P2 := NTT.p2_prime
  have hcop : Nat.Coprime P1 P2 := by
    apply (Nat.coprime_primes hp1p hp2p).mpr
    unfold P1 P2; decide
  -- A ≡ B (mod p₁) and A ≡ B (mod p₂) ⇒ A ≡ B (mod p₁ · p₂).
  have hmod : A % (P1 * P2) = B % (P1 * P2) := by
    have hcong : Nat.ModEq (P1 * P2) A B := by
      apply (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp
      exact ⟨h1, h2⟩
    exact hcong
  -- A, B < p₁ · p₂ ⇒ A % (p₁ · p₂) = A and B % (p₁ · p₂) = B.
  rw [Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt hB] at hmod
  exact hmod

-- ============================================================================
-- N-divisibility
-- ============================================================================
--
-- The Rust check `r.is_multiple_of(N)` rejects unless `r₁ % N = 0`.
-- The spec defines `PolyQnorm` as returning `n · ‖w‖²_Q mod p`, so
-- the true integer is `n · ‖w‖²_Q`, divisible by `n` by construction.
-- For a *valid* `w`, `r₁ = (n · ‖w‖²_Q) mod p₁`; since
-- `n · ‖w‖²_Q < min(p₁, p₂)` in the HAWK working range, the reduction
-- is the identity, and `r₁ % N = 0` follows from
-- `(n · ‖w‖²_Q) % N = 0`.

/-- For any valid integer `R = N · x`, the residue `R % N = 0`. This
    is the spec-level justification for the Rust `is_multiple_of(N)`
    check on the (recovered) true value. -/
theorem true_value_n_divisible (x : Nat) : (N * x) % N = 0 := by
  exact Nat.mul_mod_right N x

-- ============================================================================
-- Bound check meaningfulness
-- ============================================================================
--
-- 8n·σ²_verify with n = 512, σ_verify = 57/40:
--   8·512·(57/40)² = 4096·3249/1600 = 13_307_904/1600 = 8317.44
-- The Rust check `1600·r ≤ 13_307_904` is the rational-free form.

/-- The HAWK-512 bound matches the spec parameters: the largest `r`
    that passes is exactly `⌊8n·σ²⌋ = 8317`. -/
theorem max_passing_r_is_8317 :
    ∀ r : Nat, 1600 * r ≤ BOUND_NUM ↔ r ≤ 8317 := by
  intro r
  unfold BOUND_NUM
  omega

/-- The bound is **non-trivial**: `r = 0` passes (the all-zero
    polynomial), and `r = 8318` fails (`1600·8318 = 13_308_800 > BOUND_NUM`).
    So the predicate is neither always-true nor always-false. -/
theorem bound_is_meaningful :
    (1600 * 0 ≤ BOUND_NUM) ∧ ¬(1600 * 8318 ≤ BOUND_NUM) := by
  unfold BOUND_NUM; omega

-- ============================================================================
-- End-to-end correctness of the decision predicate (clean spec)
-- ============================================================================

/-- The clean-spec `accept` predicate: a candidate `R` (the integer
    `n · ‖w‖²_Q` in `[0, p₁·p₂)`, computed *exactly*, not mod p) is
    accepted iff:
      1. `R < min(p₁, p₂)` (so the dual-prime residues collapse to `R`)
      2. `R` is divisible by `N`
      3. `R/N` is within the bound
    The Rust `accept` on the residue pair `(R mod p₁, R mod p₂)` is
    equivalent to this whenever (1) holds. -/
theorem accept_matches_spec (R : Nat) (h1 : R < P1) (h2 : R < P2) :
    accept (R % P1) (R % P2) =
      (decide (R % N = 0) && decide (1600 * (R / N) ≤ BOUND_NUM)) := by
  unfold accept
  obtain ⟨e1, e2⟩ := true_value_recovery R h1 h2
  rw [e1, e2]
  simp [decide_true, Bool.true_and]

end Hawk512.Spec.PolyQnorm
