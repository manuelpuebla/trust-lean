/-
  Trust-Lean — Verified Code Generation Framework
  MicroC/Int64.lean: Two's Complement Int64 Foundation (v3.0.0)

  N14.1: Int64 wrapping arithmetic types and properties.

  Key definitions:
  - wrapInt64: two's complement signed wrapping (mod 2^64)
  - InInt64Range: predicate for values in [-2^63, 2^63-1]

  Key theorems:
  - wrapInt64_idempotent: wrapping twice = wrapping once
  - wrapInt64_of_inRange: wrapping is identity on in-range values
  - InInt64Range_wrapInt64: wrapping always produces in-range output
  - Boundary: overflow wraps to min, underflow wraps to max
-/

set_option autoImplicit false

namespace TrustLean

/-! ## Constants -/

/-- 2^64 = 18446744073709551616. -/
def twoPow64 : Int := 18446744073709551616

/-- Maximum signed Int64 value: 2^63 - 1 = 9223372036854775807. -/
def maxInt64 : Int := 9223372036854775807

/-- Minimum signed Int64 value: -2^63 = -9223372036854775808. -/
def minInt64 : Int := -9223372036854775808

/-! ## Core Definitions -/

/-- Two's complement signed wrapping for Int64.
    Maps any Int to the range [minInt64, maxInt64].
    Uses Lean's Euclidean mod (non-negative for positive divisor). -/
def wrapInt64 (n : Int) : Int :=
  let n' := n % twoPow64
  if n' > maxInt64 then n' - twoPow64 else n'

/-- A value is in the signed Int64 range: [-2^63, 2^63-1]. -/
def InInt64Range (n : Int) : Prop :=
  minInt64 ≤ n ∧ n ≤ maxInt64

instance (n : Int) : Decidable (InInt64Range n) :=
  if h1 : minInt64 ≤ n then
    if h2 : n ≤ maxInt64 then .isTrue ⟨h1, h2⟩
    else .isFalse (fun ⟨_, h⟩ => h2 h)
  else .isFalse (fun ⟨h, _⟩ => h1 h)

/-! ## Boundary Theorems (concrete values, via native_decide) -/

theorem wrapInt64_zero : wrapInt64 0 = 0 := by native_decide
theorem wrapInt64_one : wrapInt64 1 = 1 := by native_decide
theorem wrapInt64_neg_one : wrapInt64 (-1) = -1 := by native_decide
theorem wrapInt64_maxInt64 : wrapInt64 maxInt64 = maxInt64 := by native_decide
theorem wrapInt64_minInt64 : wrapInt64 minInt64 = minInt64 := by native_decide

/-- Overflow: maxInt64 + 1 wraps to minInt64. -/
theorem wrapInt64_overflow : wrapInt64 (maxInt64 + 1) = minInt64 := by native_decide

/-- Underflow: minInt64 - 1 wraps to maxInt64. -/
theorem wrapInt64_underflow : wrapInt64 (minInt64 - 1) = maxInt64 := by native_decide

/-! ## Universal Theorems -/

/-- wrapInt64 output is always in the signed Int64 range. -/
theorem InInt64Range_wrapInt64 (n : Int) : InInt64Range (wrapInt64 n) := by
  unfold InInt64Range wrapInt64 minInt64 maxInt64 twoPow64
  simp only
  have hnn := Int.emod_nonneg n (show (18446744073709551616 : Int) ≠ 0 by omega)
  have hlt := Int.emod_lt_of_pos n (show (0 : Int) < 18446744073709551616 by omega)
  split
  · constructor <;> omega
  · constructor <;> omega

/-- wrapInt64 is identity on values already in Int64 range. -/
theorem wrapInt64_of_inRange (n : Int) (h : InInt64Range n) : wrapInt64 n = n := by
  obtain ⟨hlo, hhi⟩ := h
  simp only [wrapInt64, minInt64, maxInt64, twoPow64] at *
  have hnn := Int.emod_nonneg n (show (18446744073709551616 : Int) ≠ 0 by omega)
  have hlt := Int.emod_lt_of_pos n (show (0 : Int) < 18446744073709551616 by omega)
  have hadd := Int.emod_add_mul_ediv n 18446744073709551616
  by_cases hn : 0 ≤ n
  · -- n ≥ 0: n % 2^64 = n (since 0 ≤ n < 2^64)
    have heq : n % 18446744073709551616 = n :=
      Int.emod_eq_of_lt hn (by omega)
    simp [heq]; omega
  · -- n < 0: ediv = -1, so n % 2^64 = n + 2^64 > maxInt64
    have hn' : n < 0 := by omega
    have hdiv : n / 18446744073709551616 = -1 := by omega
    have heq : n % 18446744073709551616 = n + 18446744073709551616 := by omega
    simp [heq]; omega

/-- wrapInt64 is idempotent: wrapping twice equals wrapping once. -/
theorem wrapInt64_idempotent (n : Int) : wrapInt64 (wrapInt64 n) = wrapInt64 n :=
  wrapInt64_of_inRange (wrapInt64 n) (InInt64Range_wrapInt64 n)

/-! ## Arithmetic Wrapping Operations -/

/-- Wrapping addition for Int64. -/
def addInt64 (a b : Int) : Int := wrapInt64 (a + b)

/-- Wrapping subtraction for Int64. -/
def subInt64 (a b : Int) : Int := wrapInt64 (a - b)

/-- Wrapping multiplication for Int64. -/
def mulInt64 (a b : Int) : Int := wrapInt64 (a * b)

/-- Wrapping negation for Int64. -/
def negInt64 (a : Int) : Int := wrapInt64 (-a)

/-! ## Arithmetic Properties -/

theorem addInt64_inRange (a b : Int) : InInt64Range (addInt64 a b) :=
  InInt64Range_wrapInt64 _

theorem subInt64_inRange (a b : Int) : InInt64Range (subInt64 a b) :=
  InInt64Range_wrapInt64 _

theorem mulInt64_inRange (a b : Int) : InInt64Range (mulInt64 a b) :=
  InInt64Range_wrapInt64 _

theorem negInt64_inRange (a : Int) : InInt64Range (negInt64 a) :=
  InInt64Range_wrapInt64 _

/-- Wrapping add is commutative. -/
theorem addInt64_comm (a b : Int) : addInt64 a b = addInt64 b a := by
  unfold addInt64; rw [Int.add_comm]

/-- Wrapping add with 0 is identity (when result is in range). -/
theorem addInt64_zero (a : Int) (h : InInt64Range a) : addInt64 a 0 = a := by
  unfold addInt64; simp; exact wrapInt64_of_inRange a h

/-! ## Smoke Tests -/

#eval wrapInt64 0                    -- 0
#eval wrapInt64 42                   -- 42
#eval wrapInt64 (-10)                -- -10
#eval wrapInt64 maxInt64             -- 9223372036854775807
#eval wrapInt64 minInt64             -- -9223372036854775808
#eval wrapInt64 (maxInt64 + 1)       -- -9223372036854775808 (overflow → min)
#eval wrapInt64 (minInt64 - 1)       -- 9223372036854775807 (underflow → max)
#eval addInt64 maxInt64 1            -- -9223372036854775808 (overflow)
#eval mulInt64 maxInt64 2            -- -2 (overflow wrapping)

end TrustLean
