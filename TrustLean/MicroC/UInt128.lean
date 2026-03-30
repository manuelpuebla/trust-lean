/-
  Trust-Lean v4.1.0 — UInt128 Wrapping Foundation
  N27.1: FUNDACIONAL — wrapUInt128, InUInt128Range, addUInt128/sub/mul.

  Extends Unsigned.lean's parametric wrapWidth to 128-bit.
  All properties (nonneg, lt, idempotent, of_inRange, composition) inherited
  from wrapWidth in Unsigned.lean — NO redefinition, NO reproof.

  Design decision: shift modulus = % 128 (see UInt128Eval.lean).
-/
import TrustLean.MicroC.Unsigned

set_option autoImplicit false

namespace TrustLean

/-! ## Wrapping Functions -/

/-- Unsigned 128-bit wrapping. -/
abbrev wrapUInt128 (x : Int) : Int := wrapWidth 128 x

/-! ## Range Predicates -/

/-- A value is in unsigned 128-bit range: [0, 2^128). -/
def InUInt128Range (n : Int) : Prop := 0 ≤ n ∧ n < (2 ^ 128 : Int)

/-! ## @[simp] Lemmas (delegating to wrapWidth) -/

@[simp] theorem wrapUInt128_nonneg (x : Int) : 0 ≤ wrapUInt128 x :=
  wrapWidth_nonneg 128 x

@[simp] theorem wrapUInt128_lt (x : Int) : wrapUInt128 x < 2 ^ 128 :=
  wrapWidth_lt 128 x

@[simp] theorem wrapUInt128_idempotent (x : Int) :
    wrapUInt128 (wrapUInt128 x) = wrapUInt128 x :=
  wrapWidth_idempotent 128 x

/-! ## Arithmetic Operations -/

def addUInt128 (a b : Int) : Int := wrapUInt128 (a + b)
def subUInt128 (a b : Int) : Int := wrapUInt128 (a - b)
def mulUInt128 (a b : Int) : Int := wrapUInt128 (a * b)

/-! ## Non-Vacuity: Boundary Examples -/

-- wrapUInt128 boundary tests
example : wrapUInt128 0 = 0 := by native_decide
example : wrapUInt128 (2^128 - 1) = 2^128 - 1 := by native_decide
example : wrapUInt128 (2^128) = 0 := by native_decide
example : wrapUInt128 (-1) = 2^128 - 1 := by native_decide
example : wrapUInt128 (2^128 + 7) = 7 := by native_decide

-- Negative wrapping tests
example : wrapUInt128 (-(2^128 : Int)) = 0 := by native_decide
example : wrapUInt128 (-(2^128 + 1 : Int)) = 2^128 - 1 := by native_decide

-- Arithmetic composition tests
example : addUInt128 (2^128 - 1) 1 = 0 := by native_decide
example : subUInt128 0 1 = 2^128 - 1 := by native_decide
example : mulUInt128 (2^64) (2^64) = 0 := by native_decide

-- UInt128 holds uint64 products
example : mulUInt128 (2^64 - 1) (2^64 - 1) = (2^64 - 1) * (2^64 - 1) := by native_decide

end TrustLean
