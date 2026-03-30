/-
  Trust-Lean v4.3.0 — VecSpecialOp: Non-Lane-Wise SIMD Operations
  N29.1: FUNDACIONAL — VecSpecialOp inductive + evalVecSpecialOp + soundness.

  Three operations that cross lanes or change word width:
  - mulHigh: multiply-high for Montgomery REDC
  - satDoublingMulHigh: saturating doubling multiply-high (NEON vqdmulhq_s32)
  - horizAdd: horizontal pairwise addition

  Semantics are pure functions on List Int — no fuel, no side effects.
-/
import TrustLean.Core.Value

set_option autoImplicit false

namespace TrustLean

/-! ## VecSpecialOp Inductive -/

/-- SIMD operations that are NOT simple lane-wise BinOp application. -/
inductive VecSpecialOp where
  /-- Multiply-high: result[i] = (a[i] * b[i]) / 2^shift.
      Maps to: NEON vmulhq_s32, AVX2 emulation. -/
  | mulHigh (shift : Nat := 32)
  /-- Saturating doubling multiply-high: sat((a[i] * b[i] * 2) / 2^32).
      Maps to: NEON vqdmulhq_s32. -/
  | satDoublingMulHigh
  /-- Horizontal pairwise add: [a,b,c,d] → [a+b, c+d].
      Maps to: NEON vpaddlq_s32, AVX2 _mm256_hadd_epi32. -/
  | horizAdd
  deriving Repr, BEq, DecidableEq, Inhabited

/-! ## Helper: Signed 32-bit Saturation -/

/-- Signed 32-bit saturation: clamp to [-2^31, 2^31 - 1].
    Models the saturation behavior of NEON vqdmulhq_s32. -/
def saturateInt32 (x : Int) : Int :=
  min (max x (-(2^31 : Int))) (2^31 - 1 : Int)

/-! ## List Access Helper -/

/-- Safe list access with default 0. -/
private def getI (l : List Int) (i : Nat) : Int := l.getD i 0

/-! ## Evaluation -/

/-- Evaluate a VecSpecialOp on concrete integer lists.
    Returns none if input lists are too short. -/
def evalVecSpecialOp : VecSpecialOp → List Int → List Int → Nat → Option (List Int)
  | .mulHigh shift, a, b, lanes =>
    if a.length < lanes ∨ b.length < lanes then none
    else some ((List.range lanes).map fun i => (getI a i * getI b i) / (2 ^ shift : Int))
  | .satDoublingMulHigh, a, b, lanes =>
    if a.length < lanes ∨ b.length < lanes then none
    else some ((List.range lanes).map fun i =>
      saturateInt32 ((getI a i * getI b i * 2) / (2^32 : Int)))
  | .horizAdd, a, _, lanes =>
    if a.length < lanes then none
    else some ((List.range (lanes / 2)).map fun i => getI a (2*i) + getI a (2*i+1))

/-! ## Soundness Theorems -/

theorem mulHigh_sound (shift : Nat) (a b : List Int) (lanes : Nat)
    (ha : a.length ≥ lanes) (hb : b.length ≥ lanes)
    (result : List Int)
    (h : evalVecSpecialOp (.mulHigh shift) a b lanes = some result) :
    result = (List.range lanes).map fun i => (getI a i * getI b i) / (2 ^ shift : Int) := by
  simp only [evalVecSpecialOp, show ¬(a.length < lanes ∨ b.length < lanes) from by omega,
    ite_false, Option.some.injEq] at h
  exact h.symm

theorem satDoublingMulHigh_sound (a b : List Int) (lanes : Nat)
    (ha : a.length ≥ lanes) (hb : b.length ≥ lanes)
    (result : List Int)
    (h : evalVecSpecialOp .satDoublingMulHigh a b lanes = some result) :
    result = (List.range lanes).map fun i =>
      saturateInt32 ((getI a i * getI b i * 2) / (2^32 : Int)) := by
  simp only [evalVecSpecialOp, show ¬(a.length < lanes ∨ b.length < lanes) from by omega,
    ite_false, Option.some.injEq] at h
  exact h.symm

theorem horizAdd_sound (a : List Int) (lanes : Nat)
    (ha : a.length ≥ lanes) (result : List Int)
    (h : evalVecSpecialOp .horizAdd a [] lanes = some result) :
    result = (List.range (lanes / 2)).map fun i => getI a (2*i) + getI a (2*i+1) := by
  simp only [evalVecSpecialOp, show ¬(a.length < lanes) from by omega,
    ite_false, Option.some.injEq] at h
  exact h.symm

/-! ## saturateInt32 Properties -/

/-- saturateInt32 is bounded — witnessed concretely. -/
example : saturateInt32 0 = 0 := by native_decide
example : saturateInt32 (2^31 : Int) = 2^31 - 1 := by native_decide
example : saturateInt32 (-(2^31 : Int) - 1) = -(2^31 : Int) := by native_decide
example : saturateInt32 (2^40 : Int) = 2^31 - 1 := by native_decide
example : saturateInt32 (-(2^40 : Int)) = -(2^31 : Int) := by native_decide

/-! ## Non-Vacuity -/

-- mulHigh: small numbers truncate to 0
example : evalVecSpecialOp (.mulHigh 32) [3, 5] [7, 11] 2 = some [0, 0] := by native_decide

-- mulHigh with shift=1: (6*7)/2=21, (10*3)/2=15
example : evalVecSpecialOp (.mulHigh 1) [6, 10] [7, 3] 2 = some [21, 15] := by native_decide

-- horizAdd: [10,20,30,40] → [30,70]
example : evalVecSpecialOp .horizAdd [10, 20, 30, 40] [] 4 = some [30, 70] := by native_decide

-- horizAdd: 8 lanes → 4 results
example : evalVecSpecialOp .horizAdd [1, 2, 3, 4, 5, 6, 7, 8] [] 8 =
    some [3, 7, 11, 15] := by native_decide

-- satDoublingMulHigh: (1073741824 * 2 * 2) / 2^32 = 1
example : evalVecSpecialOp .satDoublingMulHigh [1073741824] [2] 1 = some [1] := by native_decide

-- saturateInt32: in-range identity
example : saturateInt32 42 = 42 := by native_decide
example : saturateInt32 (-(2^31 : Int)) = -(2^31 : Int) := by native_decide

-- saturateInt32: clamping
example : saturateInt32 (2^31 : Int) = 2^31 - 1 := by native_decide
example : saturateInt32 (-(2^31 : Int) - 1) = -(2^31 : Int) := by native_decide

end TrustLean
