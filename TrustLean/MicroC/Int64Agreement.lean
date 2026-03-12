/-
  Trust-Lean — Verified Code Generation Framework
  MicroC/Int64Agreement.lean: Int64-Unbounded Agreement Theorems (v3.0.0)

  N14.3: Proves that when arithmetic results are in Int64 range,
  the int64 evaluator agrees with the unbounded evaluator.

  Key theorems:
  - evalMicroCBinOp_int64_agree: general BinOp agreement
  - evalMicroCUnaryOp_int64_agree: general UnaryOp agreement
  - Per-operator convenience theorems for add/sub/mul
  - Non-vacuity example: concrete overflow-free program agreement
-/

import TrustLean.MicroC.Int64Eval

set_option autoImplicit false

namespace TrustLean

/-! ## Per-Operator BinOp Agreement -/

/-- Addition agrees when result is in Int64 range. -/
theorem evalMicroCBinOp_int64_agree_add (a b : Int) (h : InInt64Range (a + b)) :
    evalMicroCBinOp_int64 .add (.int a) (.int b) =
    evalMicroCBinOp .add (.int a) (.int b) := by
  simp only [evalMicroCBinOp_int64_add, evalMicroCBinOp, microCBinOpToCore, evalBinOp_add,
             addInt64, wrapInt64_of_inRange _ h]

/-- Subtraction agrees when result is in Int64 range. -/
theorem evalMicroCBinOp_int64_agree_sub (a b : Int) (h : InInt64Range (a - b)) :
    evalMicroCBinOp_int64 .sub (.int a) (.int b) =
    evalMicroCBinOp .sub (.int a) (.int b) := by
  simp only [evalMicroCBinOp_int64_sub, evalMicroCBinOp, microCBinOpToCore, evalBinOp_sub,
             subInt64, wrapInt64_of_inRange _ h]

/-- Multiplication agrees when result is in Int64 range. -/
theorem evalMicroCBinOp_int64_agree_mul (a b : Int) (h : InInt64Range (a * b)) :
    evalMicroCBinOp_int64 .mul (.int a) (.int b) =
    evalMicroCBinOp .mul (.int a) (.int b) := by
  simp only [evalMicroCBinOp_int64_mul, evalMicroCBinOp, microCBinOpToCore, evalBinOp_mul,
             mulInt64, wrapInt64_of_inRange _ h]

/-! ## Non-Arithmetic BinOp Agreement (Unconditional) -/

/-- Equality comparison always agrees (produces Bool, no wrapping). -/
theorem evalMicroCBinOp_int64_agree_eqOp (a b : Int) :
    evalMicroCBinOp_int64 .eqOp (.int a) (.int b) =
    evalMicroCBinOp .eqOp (.int a) (.int b) := by
  simp [evalMicroCBinOp_int64, evalMicroCBinOp, evalBinOp, microCBinOpToCore]

/-- Less-than comparison always agrees (produces Bool, no wrapping). -/
theorem evalMicroCBinOp_int64_agree_ltOp (a b : Int) :
    evalMicroCBinOp_int64 .ltOp (.int a) (.int b) =
    evalMicroCBinOp .ltOp (.int a) (.int b) := by
  simp [evalMicroCBinOp_int64, evalMicroCBinOp, evalBinOp, microCBinOpToCore]

/-- Logical AND always agrees (operates on Bool). -/
theorem evalMicroCBinOp_int64_agree_land (a b : Bool) :
    evalMicroCBinOp_int64 .land (.bool a) (.bool b) =
    evalMicroCBinOp .land (.bool a) (.bool b) := by
  simp [evalMicroCBinOp_int64, evalMicroCBinOp, evalBinOp, microCBinOpToCore]

/-- Logical OR always agrees (operates on Bool). -/
theorem evalMicroCBinOp_int64_agree_lor (a b : Bool) :
    evalMicroCBinOp_int64 .lor (.bool a) (.bool b) =
    evalMicroCBinOp .lor (.bool a) (.bool b) := by
  simp [evalMicroCBinOp_int64, evalMicroCBinOp, evalBinOp, microCBinOpToCore]

/-! ## General BinOp Agreement -/

/-- General BinOp agreement: if every Int result of the unbounded evaluator
    is in Int64 range, the int64 evaluator agrees.
    For comparison/logical ops, the hypothesis is vacuously satisfied
    (they produce Bool, not Int). -/
theorem evalMicroCBinOp_int64_agree (op : MicroCBinOp) (v1 v2 : Value)
    (h : ∀ n, evalMicroCBinOp op v1 v2 = some (.int n) → InInt64Range n) :
    evalMicroCBinOp_int64 op v1 v2 = evalMicroCBinOp op v1 v2 := by
  cases op <;> cases v1 <;> cases v2 <;>
    simp_all [evalMicroCBinOp_int64, evalMicroCBinOp, evalBinOp, microCBinOpToCore,
              addInt64, subInt64, mulInt64, wrapInt64_of_inRange]

/-! ## UnaryOp Agreement -/

/-- Negation agrees when result is in Int64 range. -/
theorem evalMicroCUnaryOp_int64_agree_neg (n : Int) (h : InInt64Range (-n)) :
    evalMicroCUnaryOp_int64 .neg (.int n) =
    evalMicroCUnaryOp .neg (.int n) := by
  simp only [evalMicroCUnaryOp_int64_neg, evalMicroCUnaryOp, evalUnaryOp, microCUnaryOpToCore,
             negInt64, wrapInt64_of_inRange _ h]

/-- Logical not always agrees (operates on Bool). -/
theorem evalMicroCUnaryOp_int64_agree_lnot (b : Bool) :
    evalMicroCUnaryOp_int64 .lnot (.bool b) =
    evalMicroCUnaryOp .lnot (.bool b) := by
  simp [evalMicroCUnaryOp_int64, evalMicroCUnaryOp, evalUnaryOp, microCUnaryOpToCore]

/-- General UnaryOp agreement. -/
theorem evalMicroCUnaryOp_int64_agree (op : MicroCUnaryOp) (v : Value)
    (h : ∀ n, evalMicroCUnaryOp op v = some (.int n) → InInt64Range n) :
    evalMicroCUnaryOp_int64 op v = evalMicroCUnaryOp op v := by
  cases op <;> cases v <;>
    simp_all [evalMicroCUnaryOp_int64, evalMicroCUnaryOp, evalUnaryOp, microCUnaryOpToCore,
              negInt64, wrapInt64_of_inRange]

/-! ## Non-Vacuity: Overflow-Free Program Agreement -/

/-- Non-vacuity: simple assignment x = 3 + 4 produces x = 7 under both evaluators.
    This demonstrates that the BinOp agreement hypotheses are jointly satisfiable. -/
example :
    let stmt := MicroCStmt.assign "x" (.binOp .add (.litInt 3) (.litInt 4))
    let env := MicroCEnv.default
    -- Int64 evaluator produces x = 7
    (do let (_, e) ← evalMicroC_int64 10 env stmt; pure (e "x")) =
    some (.int 7) ∧
    -- Unbounded evaluator produces x = 7
    (do let (_, e) ← evalMicroC 10 env stmt; pure (e "x")) =
    some (.int 7) := by
  constructor <;> native_decide

/-- Non-vacuity: multi-step program x = 3 + 4; y = x * 2; z = y - 5.
    All intermediate results (7, 14, 9) are in Int64 range.
    Both evaluators produce z = 9. -/
example :
    let prog := MicroCStmt.seq
      (MicroCStmt.assign "x" (.binOp .add (.litInt 3) (.litInt 4)))
      (MicroCStmt.seq
        (MicroCStmt.assign "y" (.binOp .mul (.varRef "x") (.litInt 2)))
        (MicroCStmt.assign "z" (.binOp .sub (.varRef "y") (.litInt 5))))
    let env := MicroCEnv.default
    -- Both evaluators produce z = 9
    (do let (_, e) ← evalMicroC_int64 10 env prog; pure (e "z")) =
    some (.int 9) ∧
    (do let (_, e) ← evalMicroC 10 env prog; pure (e "z")) =
    some (.int 9) := by
  constructor <;> native_decide

/-- Non-vacuity: while loop agreement.
    sum = 0; i = 0; while (i < 3) { sum = sum + 10; i = i + 1 }
    Both evaluators produce sum = 30, verifying overflow-free agreement
    across multiple loop iterations. -/
example :
    let body := MicroCStmt.seq
      (MicroCStmt.assign "sum" (.binOp .add (.varRef "sum") (.litInt 10)))
      (MicroCStmt.assign "i" (.binOp .add (.varRef "i") (.litInt 1)))
    let loop := MicroCStmt.while_ (.binOp .ltOp (.varRef "i") (.litInt 3)) body
    let init := MicroCStmt.seq
      (MicroCStmt.assign "sum" (.litInt 0))
      (MicroCStmt.seq (MicroCStmt.assign "i" (.litInt 0)) loop)
    let env := MicroCEnv.default
    -- Both evaluators produce sum = 30
    (do let (_, e) ← evalMicroC_int64 10 env init; pure (e "sum")) =
    some (.int 30) ∧
    (do let (_, e) ← evalMicroC 10 env init; pure (e "sum")) =
    some (.int 30) := by
  constructor <;> native_decide

end TrustLean
