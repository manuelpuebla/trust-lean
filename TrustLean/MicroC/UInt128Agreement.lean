/-
  Trust-Lean v4.1.0 — UInt128 Agreement Theorems
  N27.3: CRITICO — per-op agreement + non-vacuity.

  Split pattern (L-630):
  - Arithmetic (add/sub/mul): CONDITIONAL on InUInt128Range(result)
  - Bitwise non-shift (band/bor/bxor): CONDITIONAL on InUInt128Range(result)
  - Bitwise shift (bshl/bshr): CONDITIONAL on InUInt128Range + shift modulus match
    (core evaluator uses % 64, uint128 evaluator uses % 128 — agreement requires
     b.toNat % 128 = b.toNat % 64, which holds when shift amount < 64)
  - Comparison/logical (eqOp/ltOp/land/lor): UNCONDITIONAL (produce Bool)

  Design: evalMicroCBinOp_uint128 uses % 128 for shifts (modeling __uint128_t).
  The core evalBinOp uses % 64. Agreement for shifts holds when amounts < 64.
-/
import TrustLean.MicroC.UInt128Eval

set_option autoImplicit false

namespace TrustLean

/-! ## UInt128 Per-Operator Agreement -/

/-! ### Arithmetic: CONDITIONAL -/

theorem evalMicroCBinOp_uint128_agree_add (a b : Int) (h : InUInt128Range (a + b)) :
    evalMicroCBinOp_uint128 .add (.int a) (.int b) =
    evalMicroCBinOp .add (.int a) (.int b) := by
  simp only [evalMicroCBinOp_uint128_add, evalMicroCBinOp, evalBinOp, microCBinOpToCore,
             addUInt128, wrapWidth_of_inRange 128 _ h.1 h.2]

theorem evalMicroCBinOp_uint128_agree_sub (a b : Int) (h : InUInt128Range (a - b)) :
    evalMicroCBinOp_uint128 .sub (.int a) (.int b) =
    evalMicroCBinOp .sub (.int a) (.int b) := by
  simp only [evalMicroCBinOp_uint128_sub, evalMicroCBinOp, evalBinOp, microCBinOpToCore,
             subUInt128, wrapWidth_of_inRange 128 _ h.1 h.2]

theorem evalMicroCBinOp_uint128_agree_mul (a b : Int) (h : InUInt128Range (a * b)) :
    evalMicroCBinOp_uint128 .mul (.int a) (.int b) =
    evalMicroCBinOp .mul (.int a) (.int b) := by
  simp only [evalMicroCBinOp_uint128_mul, evalMicroCBinOp, evalBinOp, microCBinOpToCore,
             mulUInt128, wrapWidth_of_inRange 128 _ h.1 h.2]

/-! ### Comparison/Logical: UNCONDITIONAL -/

theorem evalMicroCBinOp_uint128_agree_eqOp (a b : Int) :
    evalMicroCBinOp_uint128 .eqOp (.int a) (.int b) =
    evalMicroCBinOp .eqOp (.int a) (.int b) := by
  simp [evalMicroCBinOp_uint128, evalMicroCBinOp, evalBinOp, microCBinOpToCore]

theorem evalMicroCBinOp_uint128_agree_ltOp (a b : Int) :
    evalMicroCBinOp_uint128 .ltOp (.int a) (.int b) =
    evalMicroCBinOp .ltOp (.int a) (.int b) := by
  simp [evalMicroCBinOp_uint128, evalMicroCBinOp, evalBinOp, microCBinOpToCore]

theorem evalMicroCBinOp_uint128_agree_land (a b : Bool) :
    evalMicroCBinOp_uint128 .land (.bool a) (.bool b) =
    evalMicroCBinOp .land (.bool a) (.bool b) := by
  simp [evalMicroCBinOp_uint128, evalMicroCBinOp, evalBinOp, microCBinOpToCore]

theorem evalMicroCBinOp_uint128_agree_lor (a b : Bool) :
    evalMicroCBinOp_uint128 .lor (.bool a) (.bool b) =
    evalMicroCBinOp .lor (.bool a) (.bool b) := by
  simp [evalMicroCBinOp_uint128, evalMicroCBinOp, evalBinOp, microCBinOpToCore]

/-! ### Bitwise non-shift: CONDITIONAL -/

theorem evalMicroCBinOp_uint128_agree_band (a b : Int) (h : InUInt128Range (Int.land a b)) :
    evalMicroCBinOp_uint128 .band (.int a) (.int b) =
    evalMicroCBinOp .band (.int a) (.int b) := by
  simp only [evalMicroCBinOp_uint128_band, evalMicroCBinOp, evalBinOp, microCBinOpToCore,
             wrapWidth_of_inRange 128 _ h.1 h.2]

theorem evalMicroCBinOp_uint128_agree_bor (a b : Int) (h : InUInt128Range (Int.lor a b)) :
    evalMicroCBinOp_uint128 .bor (.int a) (.int b) =
    evalMicroCBinOp .bor (.int a) (.int b) := by
  simp only [evalMicroCBinOp_uint128_bor, evalMicroCBinOp, evalBinOp, microCBinOpToCore,
             wrapWidth_of_inRange 128 _ h.1 h.2]

theorem evalMicroCBinOp_uint128_agree_bxor (a b : Int) (h : InUInt128Range (Int.xor a b)) :
    evalMicroCBinOp_uint128 .bxor (.int a) (.int b) =
    evalMicroCBinOp .bxor (.int a) (.int b) := by
  simp only [evalMicroCBinOp_uint128_bxor, evalMicroCBinOp, evalBinOp, microCBinOpToCore,
             wrapWidth_of_inRange 128 _ h.1 h.2]

/-! ### Bitwise shift: CONDITIONAL + modulus match
    Core evalBinOp uses b.toNat % 64; uint128 evaluator uses b.toNat % 128.
    Agreement requires shift amounts to coincide (true when b.toNat < 64). -/

theorem evalMicroCBinOp_uint128_agree_bshl (a b : Int)
    (hmod : b.toNat % 128 = b.toNat % 64)
    (h : InUInt128Range (Int.shiftLeft a (b.toNat % 128))) :
    evalMicroCBinOp_uint128 .bshl (.int a) (.int b) =
    evalMicroCBinOp .bshl (.int a) (.int b) := by
  rw [hmod] at h
  simp only [evalMicroCBinOp_uint128_bshl, evalMicroCBinOp, evalBinOp, microCBinOpToCore,
             hmod, wrapWidth_of_inRange 128 _ h.1 h.2]

theorem evalMicroCBinOp_uint128_agree_bshr (a b : Int)
    (hmod : b.toNat % 128 = b.toNat % 64)
    (h : InUInt128Range (Int.shiftRight a (b.toNat % 128))) :
    evalMicroCBinOp_uint128 .bshr (.int a) (.int b) =
    evalMicroCBinOp .bshr (.int a) (.int b) := by
  rw [hmod] at h
  simp only [evalMicroCBinOp_uint128_bshr, evalMicroCBinOp, evalBinOp, microCBinOpToCore,
             hmod, wrapWidth_of_inRange 128 _ h.1 h.2]

/-- Non-vacuity: shift modulus match holds for shift amounts < 64. -/
example : (4 : Int).toNat % 128 = (4 : Int).toNat % 64 := by native_decide
example : (63 : Int).toNat % 128 = (63 : Int).toNat % 64 := by native_decide

/-! ## General BinOp Agreement (non-shift ops)

    For bshl/bshr, use the per-op theorems with hmod hypothesis.
    This general theorem covers all 10 non-shift binary operators. -/

theorem evalMicroCBinOp_uint128_agree_nonshift (op : MicroCBinOp)
    (hop : op ≠ .bshl ∧ op ≠ .bshr) (v1 v2 : Value)
    (h : ∀ n, evalMicroCBinOp op v1 v2 = some (.int n) → InUInt128Range n) :
    evalMicroCBinOp_uint128 op v1 v2 = evalMicroCBinOp op v1 v2 := by
  cases op <;> cases v1 <;> cases v2 <;>
    simp_all [evalMicroCBinOp_uint128, evalMicroCBinOp, evalBinOp, microCBinOpToCore,
              addUInt128, subUInt128, mulUInt128]
  all_goals (rename_i h; exact wrapWidth_of_inRange 128 _ h.1 h.2)

/-! ## UnaryOp Agreement -/

theorem evalMicroCUnaryOp_uint128_agree_neg (n : Int) (h : InUInt128Range (-n)) :
    evalMicroCUnaryOp_uint128 .neg (.int n) =
    evalMicroCUnaryOp .neg (.int n) := by
  simp only [evalMicroCUnaryOp_uint128_neg, evalMicroCUnaryOp, evalUnaryOp, microCUnaryOpToCore,
             wrapWidth_of_inRange 128 _ h.1 h.2]

theorem evalMicroCUnaryOp_uint128_agree_lnot (b : Bool) :
    evalMicroCUnaryOp_uint128 .lnot (.bool b) =
    evalMicroCUnaryOp .lnot (.bool b) := by
  simp [evalMicroCUnaryOp_uint128, evalMicroCUnaryOp, evalUnaryOp, microCUnaryOpToCore]

theorem evalMicroCUnaryOp_uint128_agree (op : MicroCUnaryOp) (v : Value)
    (h : ∀ n, evalMicroCUnaryOp op v = some (.int n) → InUInt128Range n) :
    evalMicroCUnaryOp_uint128 op v = evalMicroCUnaryOp op v := by
  cases op <;> cases v <;>
    simp_all [evalMicroCUnaryOp_uint128, evalMicroCUnaryOp, evalUnaryOp, microCUnaryOpToCore]
  all_goals (rename_i h; exact wrapWidth_of_inRange 128 _ h.1 h.2)

/-! ## Non-Vacuity -/

/-- Non-vacuity: UInt128 overflow-free program agreement -/
example :
    (do let (_, e) ← evalMicroC_uint128 10 MicroCEnv.default
          (.assign "x" (.binOp .add (.litInt 3) (.litInt 4)))
        pure (e "x")) =
    (do let (_, e) ← evalMicroC 10 MicroCEnv.default
          (.assign "x" (.binOp .add (.litInt 3) (.litInt 4)))
        pure (e "x")) := by native_decide

/-- Non-vacuity: UInt128 overflow wraps correctly -/
example :
    (do let (_, e) ← evalMicroC_uint128 10 MicroCEnv.default
          (.assign "x" (.binOp .add (.litInt (2^128 - 1)) (.litInt 1)))
        pure (e "x")) = some (.int 0) := by native_decide

/-- Non-vacuity: Bitwise AND masking -/
example :
    (do let (_, e) ← evalMicroC_uint128 10 MicroCEnv.default
          (.assign "x" (.binOp .band (.litInt 0xDEADBEEF) (.litInt 0x0000FFFF)))
        pure (e "x")) = some (.int 0xBEEF) := by native_decide

/-- Non-vacuity: 64-bit product fits in uint128 — agreement with unbounded -/
example :
    (do let (_, e) ← evalMicroC_uint128 10 MicroCEnv.default
          (.assign "x" (.binOp .mul (.litInt (2^64 - 1)) (.litInt (2^64 - 1))))
        pure (e "x")) =
    (do let (_, e) ← evalMicroC 10 MicroCEnv.default
          (.assign "x" (.binOp .mul (.litInt (2^64 - 1)) (.litInt (2^64 - 1))))
        pure (e "x")) := by native_decide

end TrustLean
