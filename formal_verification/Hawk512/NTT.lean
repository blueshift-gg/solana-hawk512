/-
  Hawk512.NTT — Per-prime structural facts for the HAWK-512 NTT.

  Proves, for each of the two HAWK primes `p ∈ {P1, P2}`:

    1. `p` is prime.
    2. `(p − 1) ∣ 2N` — the standard NTT-friendliness condition. Phrased
       here as `(p − 1) % (2N) = 0` so `native_decide` discharges it.
    3. A specific `h(p)` (the value `find_root` constructs in `src/ntt.rs`
       for that prime) is a primitive 2N-th root of unity: `h^N ≡ p − 1`
       and `h^(2N) ≡ 1`. These two scalar facts are what makes
       `Z_p[x]/(x^N + 1) ≅ Z_p^N` (the negacyclic NTT-as-CRT
       construction).
    4. CT and GS butterflies with twiddle `z` and inverse twiddle `z⁻¹`
       are mutual inverses up to the factor 2 (which the `n⁻¹` global
       scaling cleans up — only relevant if HAWK's verify path ever
       inverted, which it does not; the lemma is stated for
       completeness since the round-trip test in `src/ntt.rs` relies on
       it).

  The pipeline-level claim — that the 9-level loop in `src/ntt.rs::ntt`
  realises the ring isomorphism for the actual coefficient sequence —
  is checked operationally by `ntt_is_negacyclic_convolution` in
  `src/ntt.rs` and the KAT cross-check.
-/

import Hawk512.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic

namespace Hawk512.Spec.NTT

open Hawk512.Spec

-- ============================================================================
-- Primality
-- ============================================================================

theorem p1_prime : Nat.Prime P1 := by unfold P1; native_decide
theorem p2_prime : Nat.Prime P2 := by unfold P2; native_decide

-- ============================================================================
-- NTT-friendliness: (p − 1) ∣ 2N
-- ============================================================================

theorem p1_ntt_friendly : (P1 - 1) % (2 * N) = 0 := by
  unfold P1 N; native_decide
theorem p2_ntt_friendly : (P2 - 1) % (2 * N) = 0 := by
  unfold P2 N; native_decide

/-- Reformulated as a divisibility statement. -/
theorem two_n_dvd_p1_sub_one : 2 * N ∣ P1 - 1 :=
  Nat.dvd_of_mod_eq_zero p1_ntt_friendly
theorem two_n_dvd_p2_sub_one : 2 * N ∣ P2 - 1 :=
  Nat.dvd_of_mod_eq_zero p2_ntt_friendly

-- ============================================================================
-- N_INV correctness (per-prime — `n` is invertible mod each prime)
-- ============================================================================
--
-- HAWK's PolyQnorm does not divide by `n` in the NTT domain (the
-- n-divisibility check is done in `Z`, not mod p). But the `n`-inverse
-- is what would cancel the implicit forward-NTT factor of `n` if the
-- inverse NTT were ever called — and the test
-- `ntt_is_negacyclic_convolution` in `src/ntt.rs` uses it. So we
-- include it for parity with the Falcon proof.

/-- `N_INV(p) = p − ((p − 1)/N)` is the modular inverse of `N` mod `p`
    (using Fermat for prime `p`, and the fact that `p ≡ 1 mod N` from
    NTT-friendliness ⇒ `(p − 1)/N` exists and `N · (p−1)/N + 1 ≡ 0`). -/
def N_INV (p : Nat) : Nat := p - (p - 1) / N

theorem n_inv_correct_p1 : (N_INV P1 * N) % P1 = 1 := by
  unfold N_INV P1 N; native_decide
theorem n_inv_correct_p2 : (N_INV P2 * N) % P2 = 1 := by
  unfold N_INV P2 N; native_decide

-- ============================================================================
-- Primitive 2N-th root of unity for each prime
-- ============================================================================
--
-- The values below are the outputs of `src/ntt.rs::find_root` (which
-- searches `x = 2, 3, …` for the smallest base whose `(p−1)/(2N)`-th
-- power has order exactly 2N). For HAWK the base used is `x = 3` for
-- p₁ and `x = 11` for p₂; the corresponding roots are:

/-- Primitive 2N-th root of unity mod P1 (= `3^((P1-1)/(2N)) mod P1`). -/
def PSI1 : Nat := 2094155704
/-- Primitive 2N-th root of unity mod P2 (= `11^((P2-1)/(2N)) mod P2`). -/
def PSI2 : Nat := 1133102181

/-- `PSI1^N ≡ P1 − 1 (mod P1)`. -/
theorem psi1_pow_N_eq_neg_one : powP P1 PSI1 N = P1 - 1 := by
  unfold powP PSI1 P1 N; native_decide

/-- `PSI1^(2N) ≡ 1 (mod P1)`. -/
theorem psi1_pow_2N_eq_one : powP P1 PSI1 (2 * N) = 1 := by
  unfold powP PSI1 P1 N; native_decide

/-- `PSI2^N ≡ P2 − 1 (mod P2)`. -/
theorem psi2_pow_N_eq_neg_one : powP P2 PSI2 N = P2 - 1 := by
  unfold powP PSI2 P2 N; native_decide

/-- `PSI2^(2N) ≡ 1 (mod P2)`. -/
theorem psi2_pow_2N_eq_one : powP P2 PSI2 (2 * N) = 1 := by
  unfold powP PSI2 P2 N; native_decide

/-- `PSI1` has order exactly 2N in `Z_{P1}*` — the two scalar facts
    that make it a primitive 2N-th root of unity, the precondition for
    the NTT-as-ring-isomorphism construction
    (`Z_p[x]/(x^N + 1) ↔ Z_p^N` via CRT). -/
theorem psi1_has_order_2N :
    powP P1 PSI1 N = P1 - 1 ∧ powP P1 PSI1 (2 * N) = 1 :=
  ⟨psi1_pow_N_eq_neg_one, psi1_pow_2N_eq_one⟩

/-- `PSI2` has order exactly 2N in `Z_{P2}*`. -/
theorem psi2_has_order_2N :
    powP P2 PSI2 N = P2 - 1 ∧ powP P2 PSI2 (2 * N) = 1 :=
  ⟨psi2_pow_N_eq_neg_one, psi2_pow_2N_eq_one⟩

-- ============================================================================
-- CT/GS butterfly inverse relationship (per prime, in ZMod p)
-- ============================================================================
--
-- A CT butterfly followed by a GS butterfly with the inverse twiddle
-- factor recovers the original pair scaled by 2. HAWK's verify path
-- does not run a GS inverse, but the algebraic fact is the standard
-- justification for the negacyclic NTT round-trip and parallels the
-- Falcon proof. We state it abstractly over any ZMod q (it does not
-- depend on the specific prime), and instantiate it for both HAWK
-- primes.

/-- General CT/GS butterfly inverse relationship in `ZMod q`. -/
theorem ct_gs_inverse_zmod (q : Nat) (a b z : ZMod q)
    (hz : z * z⁻¹ = 1) :
    let lo := a + b * z
    let hi := a - b * z
    lo + hi = 2 * a ∧ (lo - hi) * z⁻¹ = 2 * b := by
  refine ⟨by ring, ?_⟩
  have : (a + b * z - (a - b * z)) * z⁻¹ = 2 * b * (z * z⁻¹) := by ring
  rw [this, hz, mul_one]

/-- Specialisation to ZMod P1. -/
theorem ct_gs_inverse_p1 (a b z : ZMod P1) (hz : z * z⁻¹ = 1) :
    let lo := a + b * z
    let hi := a - b * z
    lo + hi = 2 * a ∧ (lo - hi) * z⁻¹ = 2 * b :=
  ct_gs_inverse_zmod P1 a b z hz

/-- Specialisation to ZMod P2. -/
theorem ct_gs_inverse_p2 (a b z : ZMod P2) (hz : z * z⁻¹ = 1) :
    let lo := a + b * z
    let hi := a - b * z
    lo + hi = 2 * a ∧ (lo - hi) * z⁻¹ = 2 * b :=
  ct_gs_inverse_zmod P2 a b z hz

end Hawk512.Spec.NTT
