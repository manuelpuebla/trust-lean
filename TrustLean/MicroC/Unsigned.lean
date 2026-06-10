/-
  Trust-Lean v3.1 — Unsigned Integer Wrapping Foundation
  N19.1: FUNDACIONAL — wrapWidth, wrapUInt32/64, InUInt32/64Range, properties.

  Design: wrapWidth w x = x % (2^w : Int) using Lean 4's Euclidean mod (always non-negative
  for positive divisor). Verified: (-1) % 2^32 = 4294967295.

  Key properties:
  - wrapWidth_nonneg: 0 ≤ wrapWidth w x
  - wrapWidth_lt: wrapWidth w x < 2^w
  - wrapWidth_idempotent: wrapWidth w (wrapWidth w x) = wrapWidth w x
  - wrapWidth_of_inRange: in-range values are unchanged
  - wrapWidth_add/sub/mul: composition with arithmetic
-/
import Mathlib.Data.Int.Bitwise
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace TrustLean

/-! ## Wrapping Functions -/

/-- Unsigned wrapping at width w. Uses Euclidean mod (non-negative for positive divisor). -/
def wrapWidth (w : Nat) (x : Int) : Int := x % (2 ^ w : Int)

/-- Unsigned 32-bit wrapping. -/
abbrev wrapUInt32 (x : Int) : Int := wrapWidth 32 x

/-- Unsigned 64-bit wrapping. -/
abbrev wrapUInt64 (x : Int) : Int := wrapWidth 64 x

/-! ## Range Predicates -/

/-- A value is in unsigned 32-bit range: [0, 2^32). -/
def InUInt32Range (n : Int) : Prop := 0 ≤ n ∧ n < (2 ^ 32 : Int)

/-- A value is in unsigned 64-bit range: [0, 2^64). -/
def InUInt64Range (n : Int) : Prop := 0 ≤ n ∧ n < (2 ^ 64 : Int)

/-- A value is in unsigned w-bit range: [0, 2^w). -/
def InUIntRange (w : Nat) (n : Int) : Prop := 0 ≤ n ∧ n < (2 ^ w : Int)

/-! ## Core Properties -/

/-- 2^w is positive for any w. -/
private theorem two_pow_pos (w : Nat) : (0 : Int) < 2 ^ w := by positivity

/-- wrapWidth always produces a non-negative value. -/
theorem wrapWidth_nonneg (w : Nat) (x : Int) : 0 ≤ wrapWidth w x :=
  Int.emod_nonneg x (ne_of_gt (two_pow_pos w))

/-- wrapWidth always produces a value less than 2^w. -/
theorem wrapWidth_lt (w : Nat) (x : Int) : wrapWidth w x < 2 ^ w :=
  Int.emod_lt_of_pos x (two_pow_pos w)

/-- wrapWidth output is always in unsigned range. -/
theorem wrapWidth_inRange (w : Nat) (x : Int) : InUIntRange w (wrapWidth w x) :=
  ⟨wrapWidth_nonneg w x, wrapWidth_lt w x⟩

/-- wrapWidth is idempotent: wrapping twice = wrapping once. -/
theorem wrapWidth_idempotent (w : Nat) (x : Int) :
    wrapWidth w (wrapWidth w x) = wrapWidth w x := by
  simp [wrapWidth, Int.emod_emod_of_dvd]

/-- wrapWidth is identity on values already in range. -/
theorem wrapWidth_of_inRange (w : Nat) (x : Int) (h0 : 0 ≤ x) (h1 : x < 2 ^ w) :
    wrapWidth w x = x :=
  Int.emod_eq_of_lt h0 h1

/-! ## Composition Properties -/

/-- wrapWidth distributes over addition. -/
theorem wrapWidth_add (w : Nat) (a b : Int) :
    wrapWidth w (wrapWidth w a + wrapWidth w b) = wrapWidth w (a + b) := by
  simp [wrapWidth, Int.emod_emod_of_dvd, Int.add_emod]

/-- wrapWidth distributes over subtraction. -/
theorem wrapWidth_sub (w : Nat) (a b : Int) :
    wrapWidth w (wrapWidth w a - wrapWidth w b) = wrapWidth w (a - b) := by
  simp [wrapWidth, Int.emod_emod_of_dvd, Int.sub_emod]

/-- wrapWidth distributes over multiplication. -/
theorem wrapWidth_mul (w : Nat) (a b : Int) :
    wrapWidth w (wrapWidth w a * wrapWidth w b) = wrapWidth w (a * b) := by
  simp [wrapWidth, Int.emod_emod_of_dvd, Int.mul_emod]

/-! ## UInt32/UInt64 Specific Properties -/

@[simp] theorem wrapUInt32_nonneg (x : Int) : 0 ≤ wrapUInt32 x :=
  wrapWidth_nonneg 32 x

@[simp] theorem wrapUInt64_nonneg (x : Int) : 0 ≤ wrapUInt64 x :=
  wrapWidth_nonneg 64 x

@[simp] theorem wrapUInt32_lt (x : Int) : wrapUInt32 x < 2 ^ 32 :=
  wrapWidth_lt 32 x

@[simp] theorem wrapUInt64_lt (x : Int) : wrapUInt64 x < 2 ^ 64 :=
  wrapWidth_lt 64 x

@[simp] theorem wrapUInt32_idempotent (x : Int) :
    wrapUInt32 (wrapUInt32 x) = wrapUInt32 x :=
  wrapWidth_idempotent 32 x

@[simp] theorem wrapUInt64_idempotent (x : Int) :
    wrapUInt64 (wrapUInt64 x) = wrapUInt64 x :=
  wrapWidth_idempotent 64 x

/-! ## Arithmetic Operations with Unsigned Wrapping -/

def addUInt32 (a b : Int) : Int := wrapUInt32 (a + b)
def subUInt32 (a b : Int) : Int := wrapUInt32 (a - b)
def mulUInt32 (a b : Int) : Int := wrapUInt32 (a * b)

def addUInt64 (a b : Int) : Int := wrapUInt64 (a + b)
def subUInt64 (a b : Int) : Int := wrapUInt64 (a - b)
def mulUInt64 (a b : Int) : Int := wrapUInt64 (a * b)

/-! ## Non-Vacuity: Boundary Examples -/

-- wrapUInt32 boundary tests
example : wrapUInt32 0 = 0 := by native_decide
example : wrapUInt32 (2^32 - 1) = 2^32 - 1 := by native_decide
example : wrapUInt32 (2^32) = 0 := by native_decide
example : wrapUInt32 (-1) = 2^32 - 1 := by native_decide
example : wrapUInt32 (2^32 + 7) = 7 := by native_decide

-- wrapUInt64 boundary tests
example : wrapUInt64 0 = 0 := by native_decide
example : wrapUInt64 (2^64 - 1) = 2^64 - 1 := by native_decide
example : wrapUInt64 (2^64) = 0 := by native_decide

-- Additional negative wrapping tests
example : wrapUInt32 (-(2^32 : Int)) = 0 := by native_decide
example : wrapUInt32 (-(2^32 + 1 : Int)) = 2^32 - 1 := by native_decide
example : wrapUInt64 (-1) = 2^64 - 1 := by native_decide

-- Composition tests
example : addUInt32 (2^32 - 1) 1 = 0 := by native_decide
example : subUInt32 0 1 = 2^32 - 1 := by native_decide
example : mulUInt32 (2^16) (2^16) = 0 := by native_decide

-- UInt64 composition tests
example : addUInt64 (2^64 - 1) 1 = 0 := by native_decide
example : subUInt64 0 1 = 2^64 - 1 := by native_decide
example : mulUInt64 (2^32) (2^32) = 0 := by native_decide

end TrustLean
