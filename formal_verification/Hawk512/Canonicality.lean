/-
  Hawk512.Canonicality — Abstract byte-level codec canonicality.

  Adapts Falcon-512's `Canonicality.lean` to HAWK's parameter sets:

    - `s1` in the signature: LOW = 5, HIGH = 9, K = N        (`LOW_S1`, `HIGH_S1`)
    - `q00` in the pubkey:   LOW = 5, HIGH = 9, K = N / 2    (`LOW_00`, `HIGH_00`)
    - `q01` in the pubkey:   LOW = 9, HIGH = 12, K = N       (`LOW_01`, `HIGH_01`)

  The two shapes used in HAWK-512 are LOW = 5 (for `s1` and `q00`) and
  LOW = 9 (for `q01`); we define them with explicit fixed-length
  pattern-match decoders (mirroring Falcon's `lsb7Bits` / `lsb7Decode`),
  then prove per-coefficient encoding injectivity and prefix-freeness,
  and lift to whole-sequence injectivity. The proof shape is identical
  for both LOW values.

  We also prove the q00 self-adjoint extension is *injective* — a
  different half-prefix yields a different full polynomial — so the
  GR encoding of the first `N/2` coefficients is a canonical wire form
  for the whole `q00`.

  Whole-pipeline (wire-format byte-level) canonicality including the
  zero-pad cancellation is handled by `append_replicate_false_inj`
  exactly as in Falcon.
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Hawk512.Defs

namespace Hawk512.Spec.Canonicality

open Hawk512.Spec

/-! ## §1. Coefficient type

A valid HAWK Golomb–Rice coefficient: sign bit + magnitude in
`[0, 2^HIGH)`, excluding the malleable `(sign = true, mag = 0)` form
(the only such form is the same as `(sign = false, mag = 0)`). -/

/-- A valid HAWK GR coefficient with magnitude bound `2^high`. -/
structure Coeff (high : Nat) where
  sign : Bool
  mag : Nat
  hmag : mag < 2 ^ high
  hno_neg_zero : ¬(sign = true ∧ mag = 0)

theorem Coeff.ext_iff {high : Nat} (c1 c2 : Coeff high) :
    c1 = c2 ↔ c1.sign = c2.sign ∧ c1.mag = c2.mag := by
  constructor
  · intro h; rw [h]; exact ⟨rfl, rfl⟩
  · intro ⟨hs, hm⟩
    cases c1; cases c2
    simp_all

/-! ## §2. Per-coefficient bit encoding (LOW = 5: `s1` and `q00`)

Encoding: `sign :: 5-bit-MSB(mag % 32) ++ unary(mag / 32) ++ [true]`. -/

/-- 5 LSB bits of `mag`, MSB-first. -/
private def lsb5Bits (mag : Nat) : List Bool :=
  [(mag / 16) % 2 = 1,
   (mag / 8)  % 2 = 1,
   (mag / 4)  % 2 = 1,
   (mag / 2)  % 2 = 1,
   mag        % 2 = 1]

private theorem lsb5Bits_length (mag : Nat) : (lsb5Bits mag).length = 5 := by
  unfold lsb5Bits; rfl

/-- Length-5 list pattern-match decoder, mirror of `lsb5Bits`. -/
private def lsb5Decode : List Bool → Nat
  | [b4, b3, b2, b1, b0] =>
      (if b4 then 16 else 0) + (if b3 then 8 else 0) +
      (if b2 then 4  else 0) + (if b1 then 2 else 0) +
      (if b0 then 1  else 0)
  | _ => 0

private theorem lsb5Bits_roundtrip (mag : Nat) (h : mag < 32) :
    lsb5Decode (lsb5Bits mag) = mag := by
  have key : ∀ m : Fin 32, lsb5Decode (lsb5Bits m.val) = m.val := by native_decide
  exact key ⟨mag, h⟩

private theorem lsb5Bits_injective {a b : Nat} (ha : a < 32) (hb : b < 32)
    (h : lsb5Bits a = lsb5Bits b) : a = b := by
  rw [← lsb5Bits_roundtrip a ha, h, lsb5Bits_roundtrip b hb]

/-- Encoding of one LOW=5 coefficient as a bit list (MSB first):
      [sign] ++ lsb5Bits(mag % 32) ++ replicate(mag/32, false) ++ [true]
    Length = `7 + mag/32`. -/
def encodeCoeff5 {high : Nat} (c : Coeff high) : List Bool :=
  c.sign :: lsb5Bits (c.mag % 32) ++
  List.replicate (c.mag / 32) false ++
  [true]

theorem encodeCoeff5_length {high : Nat} (c : Coeff high) :
    (encodeCoeff5 c).length = 7 + c.mag / 32 := by
  unfold encodeCoeff5
  simp [List.length_cons, List.length_append, lsb5Bits_length,
        List.length_replicate]
  omega

theorem encodeCoeff5_ne_nil {high : Nat} (c : Coeff high) :
    encodeCoeff5 c ≠ [] := by
  intro h
  have : (encodeCoeff5 c).length = 0 := by rw [h]; rfl
  rw [encodeCoeff5_length] at this
  omega

private theorem encodeCoeff5_head {high : Nat} (c : Coeff high) :
    ∃ rest, encodeCoeff5 c = c.sign :: rest :=
  ⟨_, rfl⟩

private theorem encodeCoeff5_tail_eq {high : Nat} (c : Coeff high) :
    (encodeCoeff5 c).tail =
      lsb5Bits (c.mag % 32) ++ List.replicate (c.mag / 32) false ++ [true] :=
  rfl

private theorem encodeCoeff5_drop6 {high : Nat} (c : Coeff high) :
    (encodeCoeff5 c).drop 6 =
      List.replicate (c.mag / 32) false ++ [true] := by
  show (c.sign :: (lsb5Bits (c.mag % 32) ++
        List.replicate (c.mag / 32) false ++ [true])).drop (1 + 5) = _
  rw [List.drop_succ_cons, List.append_assoc,
      List.drop_left' (lsb5Bits_length _)]

/-- **Per-coefficient encoding injectivity (LOW = 5).** -/
theorem encodeCoeff5_injective {high : Nat} (c1 c2 : Coeff high)
    (h : encodeCoeff5 c1 = encodeCoeff5 c2) : c1 = c2 := by
  have hlen : (encodeCoeff5 c1).length = (encodeCoeff5 c2).length := by rw [h]
  rw [encodeCoeff5_length, encodeCoeff5_length] at hlen
  have hdiv : c1.mag / 32 = c2.mag / 32 := by omega
  obtain ⟨r1, hr1⟩ := encodeCoeff5_head c1
  obtain ⟨r2, hr2⟩ := encodeCoeff5_head c2
  rw [hr1, hr2] at h
  have hsign : c1.sign = c2.sign := List.head_eq_of_cons_eq h
  have htail : (encodeCoeff5 c1).tail = (encodeCoeff5 c2).tail := by
    rw [hr1, hr2]; exact List.tail_eq_of_cons_eq h
  rw [encodeCoeff5_tail_eq, encodeCoeff5_tail_eq] at htail
  have hlsb_match : lsb5Bits (c1.mag % 32) = lsb5Bits (c2.mag % 32) := by
    have h5 := congrArg (List.take 5) htail
    rw [List.append_assoc, List.append_assoc,
        List.take_left' (lsb5Bits_length _),
        List.take_left' (lsb5Bits_length _)] at h5
    exact h5
  have hmod : c1.mag % 32 = c2.mag % 32 :=
    lsb5Bits_injective (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) hlsb_match
  have hmag_eq : c1.mag = c2.mag := by
    have e1 := Nat.div_add_mod c1.mag 32
    have e2 := Nat.div_add_mod c2.mag 32
    omega
  exact (Coeff.ext_iff c1 c2).mpr ⟨hsign, hmag_eq⟩

/-! ## §3. Per-coefficient bit encoding (LOW = 9: `q01`) -/

/-- 9 LSB bits of `mag`, MSB-first. -/
private def lsb9Bits (mag : Nat) : List Bool :=
  [(mag / 256) % 2 = 1,
   (mag / 128) % 2 = 1,
   (mag / 64)  % 2 = 1,
   (mag / 32)  % 2 = 1,
   (mag / 16)  % 2 = 1,
   (mag / 8)   % 2 = 1,
   (mag / 4)   % 2 = 1,
   (mag / 2)   % 2 = 1,
   mag         % 2 = 1]

private theorem lsb9Bits_length (mag : Nat) : (lsb9Bits mag).length = 9 := by
  unfold lsb9Bits; rfl

private def lsb9Decode : List Bool → Nat
  | [b8, b7, b6, b5, b4, b3, b2, b1, b0] =>
      (if b8 then 256 else 0) + (if b7 then 128 else 0) +
      (if b6 then 64  else 0) + (if b5 then 32  else 0) +
      (if b4 then 16  else 0) + (if b3 then 8   else 0) +
      (if b2 then 4   else 0) + (if b1 then 2   else 0) +
      (if b0 then 1   else 0)
  | _ => 0

private theorem lsb9Bits_roundtrip (mag : Nat) (h : mag < 512) :
    lsb9Decode (lsb9Bits mag) = mag := by
  have key : ∀ m : Fin 512, lsb9Decode (lsb9Bits m.val) = m.val := by native_decide
  exact key ⟨mag, h⟩

private theorem lsb9Bits_injective {a b : Nat} (ha : a < 512) (hb : b < 512)
    (h : lsb9Bits a = lsb9Bits b) : a = b := by
  rw [← lsb9Bits_roundtrip a ha, h, lsb9Bits_roundtrip b hb]

/-- Encoding of one LOW=9 coefficient. Length = `11 + mag/512`. -/
def encodeCoeff9 {high : Nat} (c : Coeff high) : List Bool :=
  c.sign :: lsb9Bits (c.mag % 512) ++
  List.replicate (c.mag / 512) false ++
  [true]

theorem encodeCoeff9_length {high : Nat} (c : Coeff high) :
    (encodeCoeff9 c).length = 11 + c.mag / 512 := by
  unfold encodeCoeff9
  simp [List.length_cons, List.length_append, lsb9Bits_length,
        List.length_replicate]
  omega

theorem encodeCoeff9_ne_nil {high : Nat} (c : Coeff high) :
    encodeCoeff9 c ≠ [] := by
  intro h
  have : (encodeCoeff9 c).length = 0 := by rw [h]; rfl
  rw [encodeCoeff9_length] at this
  omega

private theorem encodeCoeff9_head {high : Nat} (c : Coeff high) :
    ∃ rest, encodeCoeff9 c = c.sign :: rest :=
  ⟨_, rfl⟩

private theorem encodeCoeff9_tail_eq {high : Nat} (c : Coeff high) :
    (encodeCoeff9 c).tail =
      lsb9Bits (c.mag % 512) ++ List.replicate (c.mag / 512) false ++ [true] :=
  rfl

private theorem encodeCoeff9_drop10 {high : Nat} (c : Coeff high) :
    (encodeCoeff9 c).drop 10 =
      List.replicate (c.mag / 512) false ++ [true] := by
  show (c.sign :: (lsb9Bits (c.mag % 512) ++
        List.replicate (c.mag / 512) false ++ [true])).drop (1 + 9) = _
  rw [List.drop_succ_cons, List.append_assoc,
      List.drop_left' (lsb9Bits_length _)]

theorem encodeCoeff9_injective {high : Nat} (c1 c2 : Coeff high)
    (h : encodeCoeff9 c1 = encodeCoeff9 c2) : c1 = c2 := by
  have hlen : (encodeCoeff9 c1).length = (encodeCoeff9 c2).length := by rw [h]
  rw [encodeCoeff9_length, encodeCoeff9_length] at hlen
  have hdiv : c1.mag / 512 = c2.mag / 512 := by omega
  obtain ⟨r1, hr1⟩ := encodeCoeff9_head c1
  obtain ⟨r2, hr2⟩ := encodeCoeff9_head c2
  rw [hr1, hr2] at h
  have hsign : c1.sign = c2.sign := List.head_eq_of_cons_eq h
  have htail : (encodeCoeff9 c1).tail = (encodeCoeff9 c2).tail := by
    rw [hr1, hr2]; exact List.tail_eq_of_cons_eq h
  rw [encodeCoeff9_tail_eq, encodeCoeff9_tail_eq] at htail
  have hlsb_match : lsb9Bits (c1.mag % 512) = lsb9Bits (c2.mag % 512) := by
    have h9 := congrArg (List.take 9) htail
    rw [List.append_assoc, List.append_assoc,
        List.take_left' (lsb9Bits_length _),
        List.take_left' (lsb9Bits_length _)] at h9
    exact h9
  have hmod : c1.mag % 512 = c2.mag % 512 :=
    lsb9Bits_injective (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) hlsb_match
  have hmag_eq : c1.mag = c2.mag := by
    have e1 := Nat.div_add_mod c1.mag 512
    have e2 := Nat.div_add_mod c2.mag 512
    omega
  exact (Coeff.ext_iff c1 c2).mpr ⟨hsign, hmag_eq⟩

/-! ## §4. Prefix-freeness and sequence injectivity (LOW = 5) -/

private theorem unary_concat_inj :
    ∀ {k1 k2 : Nat} {rest1 rest2 : List Bool},
      List.replicate k1 false ++ true :: rest1 =
        List.replicate k2 false ++ true :: rest2 →
      k1 = k2 ∧ rest1 = rest2
  | 0, 0, _, _, h => by simp at h; exact ⟨rfl, h⟩
  | 0, _ + 1, _, _, h => by simp [List.replicate_succ] at h
  | _ + 1, 0, _, _, h => by simp [List.replicate_succ] at h
  | _ + 1, _ + 1, _, _, h => by
      simp [List.replicate_succ] at h
      have ih := unary_concat_inj h
      exact ⟨by omega, ih.2⟩

theorem encodeCoeff5_prefix_free {high : Nat} (c1 c2 : Coeff high)
    (tail1 tail2 : List Bool)
    (h : encodeCoeff5 c1 ++ tail1 = encodeCoeff5 c2 ++ tail2) :
    c1 = c2 ∧ tail1 = tail2 := by
  have h6a : 6 ≤ (encodeCoeff5 c1).length := by rw [encodeCoeff5_length]; omega
  have h6b : 6 ≤ (encodeCoeff5 c2).length := by rw [encodeCoeff5_length]; omega
  have hd : (encodeCoeff5 c1).drop 6 ++ tail1 =
            (encodeCoeff5 c2).drop 6 ++ tail2 := by
    have hh := congrArg (List.drop 6) h
    rwa [List.drop_append_of_le_length h6a,
         List.drop_append_of_le_length h6b] at hh
  rw [encodeCoeff5_drop6, encodeCoeff5_drop6,
      List.append_assoc, List.append_assoc] at hd
  obtain ⟨hkeq, htail⟩ := unary_concat_inj hd
  have hlen : (encodeCoeff5 c1).length = (encodeCoeff5 c2).length := by
    rw [encodeCoeff5_length, encodeCoeff5_length, hkeq]
  refine ⟨encodeCoeff5_injective c1 c2 ?_, htail⟩
  have hh := congrArg (List.take (encodeCoeff5 c1).length) h
  rwa [List.take_left, hlen, List.take_left] at hh

theorem encodeCoeff9_prefix_free {high : Nat} (c1 c2 : Coeff high)
    (tail1 tail2 : List Bool)
    (h : encodeCoeff9 c1 ++ tail1 = encodeCoeff9 c2 ++ tail2) :
    c1 = c2 ∧ tail1 = tail2 := by
  have h10a : 10 ≤ (encodeCoeff9 c1).length := by rw [encodeCoeff9_length]; omega
  have h10b : 10 ≤ (encodeCoeff9 c2).length := by rw [encodeCoeff9_length]; omega
  have hd : (encodeCoeff9 c1).drop 10 ++ tail1 =
            (encodeCoeff9 c2).drop 10 ++ tail2 := by
    have hh := congrArg (List.drop 10) h
    rwa [List.drop_append_of_le_length h10a,
         List.drop_append_of_le_length h10b] at hh
  rw [encodeCoeff9_drop10, encodeCoeff9_drop10,
      List.append_assoc, List.append_assoc] at hd
  obtain ⟨hkeq, htail⟩ := unary_concat_inj hd
  have hlen : (encodeCoeff9 c1).length = (encodeCoeff9 c2).length := by
    rw [encodeCoeff9_length, encodeCoeff9_length, hkeq]
  refine ⟨encodeCoeff9_injective c1 c2 ?_, htail⟩
  have hh := congrArg (List.take (encodeCoeff9 c1).length) h
  rwa [List.take_left, hlen, List.take_left] at hh

/-! ## §5. Whole-sequence encoding -/

/-- LOW = 5 sequence encoding. -/
def encodeAll5 {high : Nat} : List (Coeff high) → List Bool
  | []      => []
  | c :: cs => encodeCoeff5 c ++ encodeAll5 cs

/-- LOW = 9 sequence encoding. -/
def encodeAll9 {high : Nat} : List (Coeff high) → List Bool
  | []      => []
  | c :: cs => encodeCoeff9 c ++ encodeAll9 cs

@[simp] theorem encodeAll5_nil {high : Nat} :
    encodeAll5 ([] : List (Coeff high)) = [] := rfl

@[simp] theorem encodeAll5_cons {high : Nat} (c : Coeff high) (cs : List (Coeff high)) :
    encodeAll5 (c :: cs) = encodeCoeff5 c ++ encodeAll5 cs := rfl

@[simp] theorem encodeAll9_nil {high : Nat} :
    encodeAll9 ([] : List (Coeff high)) = [] := rfl

@[simp] theorem encodeAll9_cons {high : Nat} (c : Coeff high) (cs : List (Coeff high)) :
    encodeAll9 (c :: cs) = encodeCoeff9 c ++ encodeAll9 cs := rfl

theorem encodeAll5_injective {high : Nat} :
    ∀ (cs1 cs2 : List (Coeff high)), encodeAll5 cs1 = encodeAll5 cs2 → cs1 = cs2
  | [], [], _ => rfl
  | [], c2 :: _, h => by
      simp [encodeAll5] at h
      exact absurd h.1 (encodeCoeff5_ne_nil c2)
  | c1 :: _, [], h => by
      simp [encodeAll5] at h
      exact absurd h.1 (encodeCoeff5_ne_nil c1)
  | c1 :: cs1, c2 :: cs2, h => by
      change encodeCoeff5 c1 ++ encodeAll5 cs1 =
             encodeCoeff5 c2 ++ encodeAll5 cs2 at h
      obtain ⟨hc, htail⟩ := encodeCoeff5_prefix_free c1 c2 _ _ h
      rw [hc, encodeAll5_injective cs1 cs2 htail]

theorem encodeAll9_injective {high : Nat} :
    ∀ (cs1 cs2 : List (Coeff high)), encodeAll9 cs1 = encodeAll9 cs2 → cs1 = cs2
  | [], [], _ => rfl
  | [], c2 :: _, h => by
      simp [encodeAll9] at h
      exact absurd h.1 (encodeCoeff9_ne_nil c2)
  | c1 :: _, [], h => by
      simp [encodeAll9] at h
      exact absurd h.1 (encodeCoeff9_ne_nil c1)
  | c1 :: cs1, c2 :: cs2, h => by
      change encodeCoeff9 c1 ++ encodeAll9 cs1 =
             encodeCoeff9 c2 ++ encodeAll9 cs2 at h
      obtain ⟨hc, htail⟩ := encodeCoeff9_prefix_free c1 c2 _ _ h
      rw [hc, encodeAll9_injective cs1 cs2 htail]

/-! ## §6. HAWK-specific instances -/

/-- Signature `s1`: N coefficients with `(LOW_S1, HIGH_S1) = (5, 9)`. -/
abbrev S1Coeff := Coeff HIGH_S1
/-- Pubkey `q00` (first half): N/2 coefficients with `(LOW_00, HIGH_00) = (5, 9)`. -/
abbrev Q00Coeff := Coeff HIGH_00
/-- Pubkey `q01`: N coefficients with `(LOW_01, HIGH_01) = (9, 12)`. -/
abbrev Q01Coeff := Coeff HIGH_01

def S1Payload   := { cs : List S1Coeff   // cs.length = N }
def Q00Payload  := { cs : List Q00Coeff  // cs.length = N / 2 }
def Q01Payload  := { cs : List Q01Coeff  // cs.length = N }

def encodeS1   (p : S1Payload)  : List Bool := encodeAll5 p.val
def encodeQ00  (p : Q00Payload) : List Bool := encodeAll5 p.val
def encodeQ01  (p : Q01Payload) : List Bool := encodeAll9 p.val

theorem encodeS1_injective (p1 p2 : S1Payload)
    (h : encodeS1 p1 = encodeS1 p2) : p1 = p2 :=
  Subtype.ext (encodeAll5_injective p1.val p2.val h)

theorem encodeQ00_injective (p1 p2 : Q00Payload)
    (h : encodeQ00 p1 = encodeQ00 p2) : p1 = p2 :=
  Subtype.ext (encodeAll5_injective p1.val p2.val h)

theorem encodeQ01_injective (p1 p2 : Q01Payload)
    (h : encodeQ01 p1 = encodeQ01 p2) : p1 = p2 :=
  Subtype.ext (encodeAll9_injective p1.val p2.val h)

/-! ## §7. Zero-pad cancellation (whole-buffer canonicality)

Both signatures and pubkeys are zero-padded to a fixed byte length.
If two streams both end in `true` (the unary terminator) and are
followed by equal padding, the streams agree and the pad lengths
agree. Same proof as Falcon's. -/

private theorem encodeCoeff5_getLast?_eq_some_true {high : Nat} (c : Coeff high) :
    (encodeCoeff5 c).getLast? = some true := by
  show ((c.sign :: lsb5Bits (c.mag % 32)) ++
        List.replicate (c.mag / 32) false ++ [true]).getLast? = some true
  exact List.getLast?_concat _

private theorem encodeCoeff9_getLast?_eq_some_true {high : Nat} (c : Coeff high) :
    (encodeCoeff9 c).getLast? = some true := by
  show ((c.sign :: lsb9Bits (c.mag % 512)) ++
        List.replicate (c.mag / 512) false ++ [true]).getLast? = some true
  exact List.getLast?_concat _

private theorem encodeAll5_ne_nil_of_ne_nil {high : Nat}
    (cs : List (Coeff high)) (h : cs ≠ []) : encodeAll5 cs ≠ [] := by
  cases cs with
  | nil => exact absurd rfl h
  | cons c _ =>
    rw [encodeAll5_cons]
    exact fun heq => encodeCoeff5_ne_nil c (List.append_eq_nil.mp heq).1

private theorem encodeAll9_ne_nil_of_ne_nil {high : Nat}
    (cs : List (Coeff high)) (h : cs ≠ []) : encodeAll9 cs ≠ [] := by
  cases cs with
  | nil => exact absurd rfl h
  | cons c _ =>
    rw [encodeAll9_cons]
    exact fun heq => encodeCoeff9_ne_nil c (List.append_eq_nil.mp heq).1

theorem encodeAll5_getLast?_eq_some_true {high : Nat}
    (cs : List (Coeff high)) (h : cs ≠ []) :
    (encodeAll5 cs).getLast? = some true := by
  induction cs with
  | nil => exact absurd rfl h
  | cons c cs ih =>
    by_cases hcs : cs = []
    · subst hcs
      rw [encodeAll5_cons, encodeAll5_nil, List.append_nil]
      exact encodeCoeff5_getLast?_eq_some_true c
    · rw [encodeAll5_cons,
          List.getLast?_append_of_ne_nil _ (encodeAll5_ne_nil_of_ne_nil cs hcs)]
      exact ih hcs

theorem encodeAll9_getLast?_eq_some_true {high : Nat}
    (cs : List (Coeff high)) (h : cs ≠ []) :
    (encodeAll9 cs).getLast? = some true := by
  induction cs with
  | nil => exact absurd rfl h
  | cons c cs ih =>
    by_cases hcs : cs = []
    · subst hcs
      rw [encodeAll9_cons, encodeAll9_nil, List.append_nil]
      exact encodeCoeff9_getLast?_eq_some_true c
    · rw [encodeAll9_cons,
          List.getLast?_append_of_ne_nil _ (encodeAll9_ne_nil_of_ne_nil cs hcs)]
      exact ih hcs

/-- **Zero-pad cancellation.** Identical to Falcon's lemma — the bit-stream
    pre-pad and the pad length are each separately determined. -/
theorem append_replicate_false_inj
    {bs1 bs2 : List Bool} {z1 z2 : Nat}
    (h1 : bs1.getLast? = some true) (h2 : bs2.getLast? = some true)
    (h : bs1 ++ List.replicate z1 false = bs2 ++ List.replicate z2 false) :
    bs1 = bs2 ∧ z1 = z2 := by
  suffices hwlog : ∀ (b1 b2 : List Bool) (n1 n2 : Nat),
      b1.getLast? = some true → b2.getLast? = some true →
      b1.length ≤ b2.length →
      b1 ++ List.replicate n1 false = b2 ++ List.replicate n2 false →
      b1 = b2 ∧ n1 = n2 by
    rcases le_total bs1.length bs2.length with hle | hle
    · exact hwlog bs1 bs2 z1 z2 h1 h2 hle h
    · obtain ⟨he, hn⟩ := hwlog bs2 bs1 z2 z1 h2 h1 hle h.symm
      exact ⟨he.symm, hn.symm⟩
  intro b1 b2 n1 n2 _ hb2 hlen heq
  have hprefix : b1 = b2.take b1.length := by
    have := congrArg (List.take b1.length) heq
    rwa [List.take_left, List.take_append_of_le_length hlen] at this
  have hsplit : b2 = b1 ++ b2.drop b1.length := by
    conv_lhs => rw [← List.take_append_drop b1.length b2]
    rw [← hprefix]
  have hdrop_all_false : ∀ x ∈ b2.drop b1.length, x = false := by
    have heq' : List.replicate n1 false =
                b2.drop b1.length ++ List.replicate n2 false := by
      have htmp := heq
      rw [hsplit, List.append_assoc] at htmp
      exact List.append_inj_right htmp rfl
    intro x hx
    have hmem : x ∈ b2.drop b1.length ++ List.replicate n2 false :=
      List.mem_append_left _ hx
    rw [← heq'] at hmem
    exact List.eq_of_mem_replicate hmem
  have hdrop_nil : b2.drop b1.length = [] := by
    by_contra hne
    have hlast : b2.getLast? = (b2.drop b1.length).getLast? := by
      conv_lhs => rw [hsplit]
      rw [List.getLast?_append_of_ne_nil _ hne]
    rw [hlast] at hb2
    obtain ⟨head, tail, hd⟩ : ∃ head tail, b2.drop b1.length = head :: tail := by
      rcases hl : b2.drop b1.length with _ | ⟨head, tail⟩
      · exact absurd hl hne
      · exact ⟨head, tail, rfl⟩
    rw [hd] at hb2 hdrop_all_false
    have hlast_in : (head :: tail).getLast (List.cons_ne_nil _ _) ∈ head :: tail :=
      List.getLast_mem _
    have hf : (head :: tail).getLast (List.cons_ne_nil _ _) = false :=
      hdrop_all_false _ hlast_in
    rw [List.getLast?_eq_getLast _ (List.cons_ne_nil _ _), hf] at hb2
    exact (by decide : (true : Bool) ≠ false) (Option.some.inj hb2).symm
  have heq_bs : b1 = b2 := by rw [hsplit, hdrop_nil, List.append_nil]
  refine ⟨heq_bs, ?_⟩
  have := congrArg List.length heq
  simp [List.length_append, List.length_replicate, heq_bs] at this
  exact this

/-! ## §8. q00 self-adjoint extension

`q00` is stored on the wire as only its first `N/2` coefficients; the
spec extends it as `q00[N/2] = 0` and `q00[i] = -q00[N − i]` for
`i ∈ (N/2, N)`. The map from half-prefix to full polynomial is
*injective* — a different half-prefix yields a different full
polynomial — so the wire form of the half is canonical for the whole. -/

/-- Helper: for `i.val ∈ (N/2, N)`, the reflected index `N - i.val` is
    in `(0, N/2)`. Stated as a standalone lemma so `extendQ00` can take
    it as a precondition argument rather than building it inline (the
    inline `have ... := by` form trips Lean's term-mode parser). -/
private theorem reflected_in_range (i : Fin N)
    (hne_lt : ¬ i.val < N / 2) (hne_eq : i.val ≠ N / 2) :
    N - i.val < N / 2 := by
  have : N = 512 := rfl
  have := i.isLt
  omega

/-- The adjoint extension as a function `Fin N → Int`, derived from a
    half-prefix `p : Fin (N/2) → Int`. -/
def extendQ00 (p : Fin (N / 2) → Int) (i : Fin N) : Int :=
  if h_lt : i.val < N / 2 then
    p ⟨i.val, h_lt⟩
  else if h_eq : i.val = N / 2 then
    0
  else
    Neg.neg (p ⟨N - i.val, reflected_in_range i h_lt h_eq⟩)

/-- Injectivity: different half-prefixes ⇒ different full polynomials. -/
theorem extendQ00_injective (p1 p2 : Fin (N / 2) → Int)
    (h : extendQ00 p1 = extendQ00 p2) : p1 = p2 := by
  funext i
  have hi_lt_N : i.val < N := by
    have := i.isLt
    have hN : N = 512 := rfl
    omega
  have hh := congrFun h ⟨i.val, hi_lt_N⟩
  unfold extendQ00 at hh
  rw [dif_pos i.isLt, dif_pos i.isLt] at hh
  exact hh

/-- The self-adjoint extension is `0` at the centre. -/
theorem extendQ00_centre (p : Fin (N / 2) → Int)
    (i : Fin N) (hi : i.val = N / 2) :
    extendQ00 p i = 0 := by
  unfold extendQ00
  have h_not_lt : ¬ i.val < N / 2 := by omega
  rw [dif_neg h_not_lt, dif_pos hi]

end Hawk512.Spec.Canonicality
