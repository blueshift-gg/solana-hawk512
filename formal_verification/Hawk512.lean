-- HAWK-512 Formal Verification (Lean 4 / Mathlib).
--
-- Lean's scope here is the math: we verify the algebraic facts each
-- Rust optimization rests on, plus the structural facts about the two
-- HAWK primes (NTT-friendliness, primitive-root, lazy-reduction
-- u32/u64 safety), and the abstract byte-level codec canonicality.
-- Pipeline-level correctness — that the 9-level NTT loop realizes the
-- negacyclic ring isomorphism mod p, that the prepared `qnorm` path
-- agrees with the unprepared `qnorm` bit-for-bit across the whole
-- array, and that the fixed-point FFT in `RebuildS0` matches the spec
-- step-for-step — is checked operationally (Rust kernel-vs-spec proptests,
-- KAT cross-check, Mollusk SBF tests) rather than in Lean.
--
-- That division is intentional: the dual-prime NTT and the lazy-reduction
-- schedule are textbook math; Lean's job is to check the math holds in our
-- specific setting (P1 = 2147473409, P2 = 2147389441, N = 512, the Rust
-- bound constants and HAWK Golomb–Rice parameters), not to re-prove
-- textbook theorems.
--
-- What Lean covers:
--   1. Per-prime structural facts (`p` is prime, `(p-1) ∣ 2N`, the Rust
--      `find_root` constructs a primitive 2N-th root, CT/GS butterflies
--      are mutual inverses in ZMod p).
--   2. Lazy-reduction u32/u64 bounds: `2·p_max < 2³²` justifies storing
--      lazy values in u32; `p·p < 2⁶²` justifies the u64 multiply temp.
--   3. Per-element ZMod-p identities for each lazy/fused Rust optimisation
--      (lazy CT/GS additive reductions, deferred ê reduction, prepared
--      fused `ê[i] ← ŵ0[i] + d̂[i]·q̂01[i]` pass).
--   4. PolyQnorm dual-prime soundness: the (r1 == r2) cross-check is
--      meaningful (rejects mismatched residues), the n-divisibility
--      check matches the spec, and the `1600·r ≤ 13_307_904` bound is
--      a non-trivial discriminator.
--   5. Minimal FFT facts: DELTA[0] / DELTA[1] are dead (never read),
--      the FFT is in-place, and the fused-conversion-with-L1
--      composition matches the unfused (scale then transform) at the
--      per-pair level.
--   6. Abstract byte-level codec canonicality: Golomb–Rice encoding
--      injectivity for HAWK parameters (LOW_00/HIGH_00 = 5/9,
--      LOW_01/HIGH_01 = 9/12, LOW_S1/HIGH_S1 = 5/9), the self-adjoint
--      q00 reconstruction (q00[i] = -q00[N-i], q00[N/2] = 0), and the
--      pubkey/signature zero-pad canonicality.

import Hawk512.Defs            -- Core spec definitions (P1, P2, N, GR params, butterflies)
import Hawk512.Bounds          -- Arithmetic safety under lazy invariants (u32/u64)
import Hawk512.NTT             -- Per-prime: NTT-friendly, primitive root, CT/GS inverse
import Hawk512.Refinement      -- Per-element refinement for lazy/fused Rust paths
import Hawk512.PolyQnorm       -- Dual-prime cross-check + n-divisibility + bound
import Hawk512.FFT             -- Minimal fixed-point FFT structural facts
import Hawk512.Canonicality    -- Golomb–Rice + self-adjoint q00 byte-level canonicality
