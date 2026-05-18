/-
  Hawk512.Refinement — Per-element algebraic facts that justify each
  lazy/fused optimisation in the HAWK-512 verify pipeline.

  This file proves, for each optimisation, the per-element ZMod-p
  identity that makes the optimisation sound. The optimisations:

    1. Lazy CT butterfly — skip `% p` on the sum/diff halves (the
       twiddle product is still reduced). The next level's multiplier
       absorbs the un-reduction.
       — `lazy_ct_preserves_mod`
    2. Lazy `ê` storage — `ê[i] = ŵ0[i] + d̂[i]·q̂01[i]` left in
       `[0, 2p) < 2³²`, reduced only when later consumed by a `mulmod`
       in the `ĉ` sum.
       — `lazy_e_preserves_mod`
    3. Prepared `ê` / `d̂` fused pass — the same equation as the unprepared
       path, just with `q̂00⁻¹` precomputed. Algebraically identical.
       — `fused_e_dhat_equiv_zmod`
    4. Final `ĉ` accumulation: each of the `2N` reduced terms (`< p`)
       sums in u64 without per-iteration reduction; one `% p` at the
       end yields the same residue.
       — `final_sum_one_reduction`
    5. Batch inversion via Montgomery's trick: the `N` per-coefficient
       inverses computed via one Fermat inverse + two linear passes
       agree with the per-coefficient Fermat inverse, element-by-
       element.
       — `batch_inversion_correct`

  Whole-array composition (`pq_e`, `qp_c` Rust functions ≡ unfused
  composition) is checked operationally by the proptests in
  `src/ntt.rs` and the KAT cross-check — not in Lean. That division is
  intentional per the project-level scope.
-/

import Hawk512.Defs
import Hawk512.NTT
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace Hawk512.Refinement

open Hawk512.Spec

-- ============================================================================
-- Optimisation 1: Lazy CT butterfly
-- ============================================================================
--
-- Clean CT: y = (b·z) % p; lo = (a + y) % p; hi = (a + p − y) % p.
-- Lazy CT: y = (b·z) % p; lo = a + y;       hi = a + p − y.
-- (The twiddle product `y` is reduced either way. Only the additive
--  reductions are deferred — that is the only optimisation here.)
--
-- The next level multiplies by a fresh twiddle and reduces. Key:
-- `(x · y) % p = ((x % p) · y) % p`.

/-- Skipping `% p` on the CT butterfly sum output doesn't affect the
    result after the next multiplication + reduction. -/
theorem lazy_ct_preserves_mod (p a y zeta : Nat) :
    ((a + y) * zeta) % p = (((a + y) % p) * zeta) % p := by
  conv_lhs => rw [Nat.mul_mod]
  conv_rhs => rw [Nat.mul_mod, Nat.mod_mod]

/-- Same for the diff half. -/
theorem lazy_ct_diff_preserves_mod (p a y zeta : Nat) :
    ((a + p - y) * zeta) % p = (((a + p - y) % p) * zeta) % p := by
  conv_lhs => rw [Nat.mul_mod]
  conv_rhs => rw [Nat.mul_mod, Nat.mod_mod]

-- ============================================================================
-- Optimisation 2: Lazy `ê` storage
-- ============================================================================
--
-- Rust (see `pq_e` / `qp_c`):
--   ê[i] = ŵ0[i] + (d̂[i]·q̂01[i] mod p)   -- two `< p` operands ⇒ sum `< 2p`
-- left in `u32`, reduced only when later read inside a `mulmod` in the `ĉ`
-- sum: `mulmod(ai, ci, p) * adj_e[i] mod p`. The `mulmod` reads `adj_e[i]`
-- as a `u64` operand, and `% p` after the multiply gives the same residue
-- as if `ê[i]` had been reduced first.

/-- A `mulmod` of a lazy operand `e` (held in `[0, 2p)`) agrees with the
    same `mulmod` of its fully reduced form `e % p`. The standard
    `(a · b) % p = (a · (b % p)) % p` identity. -/
theorem lazy_e_preserves_mod (p a e : Nat) :
    (a * e) % p = (a * (e % p)) % p := by
  conv_lhs => rw [Nat.mul_mod]
  conv_rhs => rw [Nat.mul_mod, Nat.mod_mod]

-- ============================================================================
-- Optimisation 3: Prepared `ê` / `d̂` fused pass
-- ============================================================================
--
-- Unprepared (`pq_e`): one prefix-product pass to set `e[i] = Π_{k≤i} q̂00[k]`,
-- one Fermat inverse of the full product, then a backward pass that overwrites
-- each `e[i]` with `d̂[i] = ŵ1[i] · (q̂00[i])⁻¹` and adds `d̂[i] · q̂01[i]` into
-- `c[i] (= ŵ0[i])` to form `ê[i]`.
--
-- Prepared (`qp_c`): `q̂00⁻¹` already in hand, so the prefix-product /
-- Fermat-inverse pass is gone — one forward sweep computes
--   d̂[i] = ŵ1[i] · q̂00⁻¹[i]
--   ê[i] = ŵ0[i] + d̂[i] · q̂01[i]
-- (Both passes use the same per-element formula, just with `q̂00⁻¹` from
-- different sources.) Their equivalence is the trivial ring identity.

/-- In `ZMod p` (prime), the prepared and unprepared paths compute the
    same `ê` per-element. Algebraically a one-line ring identity:
    `ŵ0 + (ŵ1 / q̂00) · q̂01 = ŵ0 + ŵ1·q̂00⁻¹·q̂01` for any nonzero `q̂00`. -/
theorem fused_e_dhat_equiv_zmod (p : Nat) (w0 w1 q00 q01 : ZMod p) :
    let dhat := w1 * q00⁻¹
    let e_prepared := w0 + dhat * q01
    let e_unprepared := w0 + (w1 * q00⁻¹) * q01
    e_prepared = e_unprepared := by
  intro dhat e_prepared e_unprepared
  show w0 + (w1 * q00⁻¹) * q01 = w0 + (w1 * q00⁻¹) * q01
  rfl

-- ============================================================================
-- Optimisation 4: One-shot `% p` after `Σ ĉ` accumulation
-- ============================================================================
--
-- Hot loop: `r += t0 + t1` where each `tᵢ < p`; one final `r % p`. The
-- accumulator is u64; for HAWK primes `2N · p < 2⁶⁴` (proved in
-- `Hawk512.Bounds.sum_qhat_fits_u64_pᵢ`), so the running sum never
-- overflows.
--
-- The algebraic content: the running sum `r` and the "reduce after every
-- add" alternative differ by multiples of `p`, so their final `% p`
-- agrees.

/-- Adding `x` then reducing equals reducing both then adding then
    reducing. Lifted to chains of additions in the `Σ ĉ` accumulator. -/
theorem add_then_reduce_eq_reduce_both_then_add (p a b : Nat) :
    (a + b) % p = ((a % p) + (b % p)) % p := by
  rw [Nat.add_mod]

/-- One terminal `% p` on a sum of `< p` terms agrees with reducing
    after every addition. Inductive form. The accumulator-aligned IH
    states that, no matter the starting accumulator, folding plain
    `+` then `% p` equals folding `% p` after every add then `% p`,
    provided we start the latter from `acc % p`. -/
theorem final_sum_one_reduction (p : Nat) (xs : List Nat) :
    (xs.foldl (· + ·) 0) % p = (xs.foldl (fun s x => (s + x) % p) 0) % p := by
  suffices h : ∀ (acc : Nat),
      (xs.foldl (· + ·) acc) % p =
        (xs.foldl (fun s x => (s + x) % p) (acc % p)) % p by
    have := h 0
    simp at this
    exact this
  induction xs with
  | nil => intro acc; simp
  | cons x xs ih =>
    intro acc
    simp only [List.foldl_cons]
    -- Reduce the RHS's intermediate `(acc % p + x) % p` to `(acc + x) % p`
    -- before applying ih. Both sides then fold from the same start.
    have h_acc : (acc % p + x) % p = (acc + x) % p := by
      conv_rhs => rw [Nat.add_mod]
      conv_lhs => rw [Nat.add_mod, Nat.mod_mod]
    rw [h_acc, ih (acc + x)]

-- ============================================================================
-- Optimisation 5: Batch inversion (Montgomery's trick)
-- ============================================================================
--
-- Rust (see `pq_e`'s prefix-product pass + Fermat inverse + backward pass):
-- One Fermat inverse of `Π q̂00[i]` plus two linear passes yields each
-- `q̂00[i]⁻¹`, instead of `N` separate Fermat inverses.
--
-- Algebraic core (per element):
--   q̂00[i]⁻¹ = (Π_{k≤i-1} q̂00[k]) · (Π_{k} q̂00[k])⁻¹ · (Π_{k>i} q̂00[k])
--            = (q̂00[i])⁻¹  -- after the three products cancel
--
-- The Rust loop implements this as a forward prefix-product pass followed
-- by a backward sweep that maintains a running suffix-product inverse.

/-- The per-element batch-inversion identity. If `q₀, …, q_{N−1}` are
    all nonzero in a field, then for each `i`,
      (Π_{k < i} q_k) · (Π_{k ≤ i} q_k)⁻¹ = q_i⁻¹.
    Stated abstractly over any field-like ZMod p (prime). -/
theorem batch_inversion_correct (p : Nat) [Fact (Nat.Prime p)]
    (qi pref : ZMod p) (hqi : qi ≠ 0) (hpref : pref ≠ 0) :
    let full := pref * qi          -- prefix · this element = new prefix
    pref * full⁻¹ = qi⁻¹ := by
  intro full
  show pref * (pref * qi)⁻¹ = qi⁻¹
  -- ZMod p with p prime is a field; inversion distributes:
  -- pref · (pref · qi)⁻¹ = pref · qi⁻¹ · pref⁻¹ = (pref · pref⁻¹) · qi⁻¹.
  have hmul_ne : pref * qi ≠ 0 := mul_ne_zero hpref hqi
  -- Use `eq_inv_of_mul_eq_one_right`: it suffices to show
  -- qi · (pref · (pref · qi)⁻¹) = 1.
  have : qi * (pref * (pref * qi)⁻¹) = 1 := by
    rw [show qi * (pref * (pref * qi)⁻¹) = (pref * qi) * (pref * qi)⁻¹ from by ring]
    exact mul_inv_cancel₀ hmul_ne
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact this)

end Hawk512.Refinement
