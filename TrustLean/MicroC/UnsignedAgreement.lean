/-
  Trust-Lean v3.1 — Unsigned Agreement Theorems
  N19.3: CRITICO — per-op agreement + non-vacuity.

  Split pattern (L-630):
  - Arithmetic (add/sub/mul): CONDITIONAL on InUInt32Range(result)
  - Bitwise (band/bor/bxor/bshl/bshr): CONDITIONAL on InUInt32Range(result)
    (For well-formed unsigned programs where inputs are in [0, 2^32),
     AND/OR/XOR results are always in range since these ops can only clear bits.
     SHL may exceed range if shift amount is large. SHR always reduces.)
  - Comparison/logical (eqOp/ltOp/land/lor): UNCONDITIONAL (produce Bool)
  - Casting (widen/trunc): CONDITIONAL on InUInt32Range(result)
-/
import TrustLean.MicroC.UnsignedEval

set_option autoImplicit false

namespace TrustLean

/-! ## UInt32 Per-Operator Agreement -/

/-! ### Arithmetic: CONDITIONAL -/

/-- UInt32 addition agrees with unbounded when result is in range. -/
theorem evalMicroCBinOp_uint32_agree_add (a b : Int) (h : InUInt32Range (a + b)) :
    evalMicroCBinOp_uint32 .add (.int a) (.int b) =
    evalMicroCBinOp .add (.int a) (.int b) := by
  simp only [evalMicroCBinOp_uint32_add, evalMicroCBinOp, evalBinOp, microCBinOpToCore,
             addUInt32, wrapWidth_of_inRange 32 _ h.1 h.2]

/-- UInt32 subtraction agrees with unbounded when result is in range. -/
theorem evalMicroCBinOp_uint32_agree_sub (a b : Int) (h : InUInt32Range (a - b)) :
    evalMicroCBinOp_uint32 .sub (.int a) (.int b) =
    evalMicroCBinOp .sub (.int a) (.int b) := by
  simp only [evalMicroCBinOp_uint32_sub, evalMicroCBinOp, evalBinOp, microCBinOpToCore,
             subUInt32, wrapWidth_of_inRange 32 _ h.1 h.2]

/-- UInt32 multiplication agrees with unbounded when result is in range. -/
theorem evalMicroCBinOp_uint32_agree_mul (a b : Int) (h : InUInt32Range (a * b)) :
    evalMicroCBinOp_uint32 .mul (.int a) (.int b) =
    evalMicroCBinOp .mul (.int a) (.int b) := by
  simp only [evalMicroCBinOp_uint32_mul, evalMicroCBinOp, evalBinOp, microCBinOpToCore,
             mulUInt32, wrapWidth_of_inRange 32 _ h.1 h.2]

/-! ### Comparison/Logical: UNCONDITIONAL -/

theorem evalMicroCBinOp_uint32_agree_eqOp (a b : Int) :
    evalMicroCBinOp_uint32 .eqOp (.int a) (.int b) =
    evalMicroCBinOp .eqOp (.int a) (.int b) := by
  simp [evalMicroCBinOp_uint32, evalMicroCBinOp, evalBinOp, microCBinOpToCore]

theorem evalMicroCBinOp_uint32_agree_ltOp (a b : Int) :
    evalMicroCBinOp_uint32 .ltOp (.int a) (.int b) =
    evalMicroCBinOp .ltOp (.int a) (.int b) := by
  simp [evalMicroCBinOp_uint32, evalMicroCBinOp, evalBinOp, microCBinOpToCore]

theorem evalMicroCBinOp_uint32_agree_land (a b : Bool) :
    evalMicroCBinOp_uint32 .land (.bool a) (.bool b) =
    evalMicroCBinOp .land (.bool a) (.bool b) := by
  simp [evalMicroCBinOp_uint32, evalMicroCBinOp, evalBinOp, microCBinOpToCore]

theorem evalMicroCBinOp_uint32_agree_lor (a b : Bool) :
    evalMicroCBinOp_uint32 .lor (.bool a) (.bool b) =
    evalMicroCBinOp .lor (.bool a) (.bool b) := by
  simp [evalMicroCBinOp_uint32, evalMicroCBinOp, evalBinOp, microCBinOpToCore]

/-! ### Bitwise: CONDITIONAL on InUInt32Range(result)
    These agree when the unbounded result is already in UInt32 range.
    For well-formed unsigned programs where both inputs are in [0, 2^32):
    - AND/OR/XOR: result ≤ max(a, b) < 2^32, so hypothesis is always satisfiable
    - SHL: result may exceed 2^32 for large shift amounts
    - SHR: result ≤ a < 2^32, so hypothesis is always satisfiable -/

theorem evalMicroCBinOp_uint32_agree_band (a b : Int) (h : InUInt32Range (Int.land a b)) :
    evalMicroCBinOp_uint32 .band (.int a) (.int b) =
    evalMicroCBinOp .band (.int a) (.int b) := by
  simp only [evalMicroCBinOp_uint32_band, evalMicroCBinOp, evalBinOp, microCBinOpToCore,
             wrapWidth_of_inRange 32 _ h.1 h.2]

theorem evalMicroCBinOp_uint32_agree_bor (a b : Int) (h : InUInt32Range (Int.lor a b)) :
    evalMicroCBinOp_uint32 .bor (.int a) (.int b) =
    evalMicroCBinOp .bor (.int a) (.int b) := by
  simp only [evalMicroCBinOp_uint32_bor, evalMicroCBinOp, evalBinOp, microCBinOpToCore,
             wrapWidth_of_inRange 32 _ h.1 h.2]

theorem evalMicroCBinOp_uint32_agree_bxor (a b : Int) (h : InUInt32Range (Int.xor a b)) :
    evalMicroCBinOp_uint32 .bxor (.int a) (.int b) =
    evalMicroCBinOp .bxor (.int a) (.int b) := by
  simp only [evalMicroCBinOp_uint32_bxor, evalMicroCBinOp, evalBinOp, microCBinOpToCore,
             wrapWidth_of_inRange 32 _ h.1 h.2]

theorem evalMicroCBinOp_uint32_agree_bshl (a b : Int)
    (h : InUInt32Range (Int.shiftLeft a (b.toNat % 64))) :
    evalMicroCBinOp_uint32 .bshl (.int a) (.int b) =
    evalMicroCBinOp .bshl (.int a) (.int b) := by
  simp only [evalMicroCBinOp_uint32_bshl, evalMicroCBinOp, evalBinOp, microCBinOpToCore,
             wrapWidth_of_inRange 32 _ h.1 h.2]

theorem evalMicroCBinOp_uint32_agree_bshr (a b : Int)
    (h : InUInt32Range (Int.shiftRight a (b.toNat % 64))) :
    evalMicroCBinOp_uint32 .bshr (.int a) (.int b) =
    evalMicroCBinOp .bshr (.int a) (.int b) := by
  simp only [evalMicroCBinOp_uint32_bshr, evalMicroCBinOp, evalBinOp, microCBinOpToCore,
             wrapWidth_of_inRange 32 _ h.1 h.2]

/-! ## General UInt32 BinOp Agreement -/

/-- General BinOp agreement: if every Int result of the unbounded evaluator
    is in UInt32 range, the uint32 evaluator agrees. -/
theorem evalMicroCBinOp_uint32_agree (op : MicroCBinOp) (v1 v2 : Value)
    (h : ∀ n, evalMicroCBinOp op v1 v2 = some (.int n) → InUInt32Range n) :
    evalMicroCBinOp_uint32 op v1 v2 = evalMicroCBinOp op v1 v2 := by
  cases op <;> cases v1 <;> cases v2 <;>
    simp_all [evalMicroCBinOp_uint32, evalMicroCBinOp, evalBinOp, microCBinOpToCore,
              addUInt32, subUInt32, mulUInt32]
  all_goals (rename_i h; exact wrapWidth_of_inRange 32 _ h.1 h.2)

/-! ## UnaryOp Agreement -/

/-- Negation agrees when result is in UInt32 range.
    NOTE: For unsigned values (n ≥ 0), InUInt32Range(-n) requires n ≤ 0,
    so only n = 0 satisfies. This is by design: unsigned negation of any
    positive value always wraps, so there is no agreement with the unbounded
    evaluator. The theorem is correct but vacuous for n > 0. -/
theorem evalMicroCUnaryOp_uint32_agree_neg (n : Int) (h : InUInt32Range (-n)) :
    evalMicroCUnaryOp_uint32 .neg (.int n) =
    evalMicroCUnaryOp .neg (.int n) := by
  simp only [evalMicroCUnaryOp_uint32_neg, evalMicroCUnaryOp, evalUnaryOp, microCUnaryOpToCore,
             wrapWidth_of_inRange 32 _ h.1 h.2]

/-- Non-vacuity: negation agreement IS satisfiable for n = 0. -/
example : InUInt32Range (-(0 : Int)) := by native_decide
/-- Non-vacuity: negation agreement IS satisfiable for n ≤ 0 (e.g., n = -42). -/
example : InUInt32Range (-(-42 : Int)) := by native_decide

/-- Logical not always agrees. -/
theorem evalMicroCUnaryOp_uint32_agree_lnot (b : Bool) :
    evalMicroCUnaryOp_uint32 .lnot (.bool b) =
    evalMicroCUnaryOp .lnot (.bool b) := by
  simp [evalMicroCUnaryOp_uint32, evalMicroCUnaryOp, evalUnaryOp, microCUnaryOpToCore]

/-- General UnaryOp agreement. -/
theorem evalMicroCUnaryOp_uint32_agree (op : MicroCUnaryOp) (v : Value)
    (h : ∀ n, evalMicroCUnaryOp op v = some (.int n) → InUInt32Range n) :
    evalMicroCUnaryOp_uint32 op v = evalMicroCUnaryOp op v := by
  cases op <;> cases v <;>
    simp_all [evalMicroCUnaryOp_uint32, evalMicroCUnaryOp, evalUnaryOp, microCUnaryOpToCore]
  all_goals (rename_i h; exact wrapWidth_of_inRange 32 _ h.1 h.2)

/-! ## Non-Vacuity -/

/-- Non-vacuity: UInt32 overflow-free program agreement -/
example :
    (do let (_, e) ← evalMicroC_uint32 10 MicroCEnv.default
          (.assign "x" (.binOp .add (.litInt 3) (.litInt 4)))
        pure (e "x")) =
    (do let (_, e) ← evalMicroC 10 MicroCEnv.default
          (.assign "x" (.binOp .add (.litInt 3) (.litInt 4)))
        pure (e "x")) := by native_decide

/-- Non-vacuity: UInt32 overflow wraps correctly -/
example :
    (do let (_, e) ← evalMicroC_uint32 10 MicroCEnv.default
          (.assign "x" (.binOp .add (.litInt (2^32 - 1)) (.litInt 1)))
        pure (e "x")) = some (.int 0) := by native_decide

/-- Non-vacuity: Bitwise AND masking -/
example :
    (do let (_, e) ← evalMicroC_uint32 10 MicroCEnv.default
          (.assign "x" (.binOp .band (.litInt 0xDEADBEEF) (.litInt 0x0000FFFF)))
        pure (e "x")) = some (.int 0xBEEF) := by native_decide

/-- Non-vacuity: Mersenne31 reduce pattern (lo + hi where x = 2^31 + 42) -/
example :
    (do let (_, e) ← evalMicroC_uint32 10 MicroCEnv.default
          (.seq (.assign "lo" (.binOp .band (.litInt (2^31 + 42)) (.litInt 0x7FFFFFFF)))
          (.seq (.assign "hi" (.binOp .bshr (.litInt (2^31 + 42)) (.litInt 31)))
                (.assign "result" (.binOp .add (.varRef "lo") (.varRef "hi")))))
        pure (e "result")) = some (.int 43) := by native_decide

/-- Non-vacuity: 43 = (2^31 + 42) % (2^31 - 1) — verifying the reduce computes correct mod -/
example : (2^31 + 42) % (2^31 - 1 : Int) = 43 := by native_decide

end TrustLean
