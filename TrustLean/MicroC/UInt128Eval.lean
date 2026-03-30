/-
  Trust-Lean v4.1.0 — UInt128 Evaluator
  N27.2: CRITICO — evalMicroC_uint128 + @[simp] lemmas.

  Mirrors UnsignedEval.lean structure exactly.
  Wraps at operation boundaries only.
  Dedicated @[simp] lemmas per constructor.

  Key difference from uint32/uint64: shift modulus = % 128 (not % 64),
  modeling __uint128_t hardware behavior.
-/
import TrustLean.MicroC.Eval
import TrustLean.MicroC.UInt128

set_option autoImplicit false

namespace TrustLean

/-! ## UInt128 BinOp/UnaryOp Evaluators -/

/-- Evaluate a MicroC binary operator with UInt128 wrapping.
    Arithmetic results (add, sub, mul) are wrapped via wrapUInt128.
    Bitwise results are wrapped via wrapUInt128.
    Shift amounts use % 128 (modeling __uint128_t behavior).
    Comparison and logical operations return Bool, unchanged. -/
def evalMicroCBinOp_uint128 (op : MicroCBinOp) (v1 v2 : Value) : Option Value :=
  match op, v1, v2 with
  | .add, .int a, .int b => some (.int (addUInt128 a b))
  | .sub, .int a, .int b => some (.int (subUInt128 a b))
  | .mul, .int a, .int b => some (.int (mulUInt128 a b))
  | .eqOp, .int a, .int b => some (.bool (a == b))
  | .ltOp, .int a, .int b => some (.bool (decide (a < b)))
  | .land, .bool a, .bool b => some (.bool (a && b))
  | .lor, .bool a, .bool b => some (.bool (a || b))
  | .band, .int a, .int b => some (.int (wrapUInt128 (Int.land a b)))
  | .bor, .int a, .int b => some (.int (wrapUInt128 (Int.lor a b)))
  | .bxor, .int a, .int b => some (.int (wrapUInt128 (Int.xor a b)))
  | .bshl, .int a, .int b => some (.int (wrapUInt128 (Int.shiftLeft a (b.toNat % 128))))
  | .bshr, .int a, .int b => some (.int (wrapUInt128 (Int.shiftRight a (b.toNat % 128))))
  | _, _, _ => none

/-- Evaluate a MicroC unary operator with UInt128 wrapping. -/
def evalMicroCUnaryOp_uint128 (op : MicroCUnaryOp) (v : Value) : Option Value :=
  match op, v with
  | .neg, .int n => some (.int (wrapUInt128 (-n)))
  | .lnot, .bool b => some (.bool (!b))
  | .widen32to64, .int n => some (.int (wrapUInt128 (n % (2^32 : Int))))
  | .trunc64to32, .int n => some (.int (wrapUInt128 (n % (2^32 : Int))))
  | _, _ => none

/-! ## UInt128 @[simp] Lemmas -/

@[simp] theorem evalMicroCBinOp_uint128_add (a b : Int) :
    evalMicroCBinOp_uint128 .add (.int a) (.int b) = some (.int (addUInt128 a b)) := rfl
@[simp] theorem evalMicroCBinOp_uint128_sub (a b : Int) :
    evalMicroCBinOp_uint128 .sub (.int a) (.int b) = some (.int (subUInt128 a b)) := rfl
@[simp] theorem evalMicroCBinOp_uint128_mul (a b : Int) :
    evalMicroCBinOp_uint128 .mul (.int a) (.int b) = some (.int (mulUInt128 a b)) := rfl
@[simp] theorem evalMicroCBinOp_uint128_eqOp (a b : Int) :
    evalMicroCBinOp_uint128 .eqOp (.int a) (.int b) = some (.bool (a == b)) := rfl
@[simp] theorem evalMicroCBinOp_uint128_ltOp (a b : Int) :
    evalMicroCBinOp_uint128 .ltOp (.int a) (.int b) = some (.bool (decide (a < b))) := rfl
@[simp] theorem evalMicroCBinOp_uint128_land (a b : Bool) :
    evalMicroCBinOp_uint128 .land (.bool a) (.bool b) = some (.bool (a && b)) := rfl
@[simp] theorem evalMicroCBinOp_uint128_lor (a b : Bool) :
    evalMicroCBinOp_uint128 .lor (.bool a) (.bool b) = some (.bool (a || b)) := rfl
@[simp] theorem evalMicroCBinOp_uint128_band (a b : Int) :
    evalMicroCBinOp_uint128 .band (.int a) (.int b) = some (.int (wrapUInt128 (Int.land a b))) := rfl
@[simp] theorem evalMicroCBinOp_uint128_bor (a b : Int) :
    evalMicroCBinOp_uint128 .bor (.int a) (.int b) = some (.int (wrapUInt128 (Int.lor a b))) := rfl
@[simp] theorem evalMicroCBinOp_uint128_bxor (a b : Int) :
    evalMicroCBinOp_uint128 .bxor (.int a) (.int b) = some (.int (wrapUInt128 (Int.xor a b))) := rfl
@[simp] theorem evalMicroCBinOp_uint128_bshl (a b : Int) :
    evalMicroCBinOp_uint128 .bshl (.int a) (.int b) =
    some (.int (wrapUInt128 (Int.shiftLeft a (b.toNat % 128)))) := rfl
@[simp] theorem evalMicroCBinOp_uint128_bshr (a b : Int) :
    evalMicroCBinOp_uint128 .bshr (.int a) (.int b) =
    some (.int (wrapUInt128 (Int.shiftRight a (b.toNat % 128)))) := rfl

@[simp] theorem evalMicroCUnaryOp_uint128_neg (n : Int) :
    evalMicroCUnaryOp_uint128 .neg (.int n) = some (.int (wrapUInt128 (-n))) := rfl
@[simp] theorem evalMicroCUnaryOp_uint128_lnot (b : Bool) :
    evalMicroCUnaryOp_uint128 .lnot (.bool b) = some (.bool (!b)) := rfl
@[simp] theorem evalMicroCUnaryOp_uint128_widen (n : Int) :
    evalMicroCUnaryOp_uint128 .widen32to64 (.int n) =
    some (.int (wrapUInt128 (n % (2^32 : Int)))) := rfl
@[simp] theorem evalMicroCUnaryOp_uint128_trunc (n : Int) :
    evalMicroCUnaryOp_uint128 .trunc64to32 (.int n) =
    some (.int (wrapUInt128 (n % (2^32 : Int)))) := rfl

/-! ## Expression Evaluator -/

/-- Evaluate a MicroC expression with UInt128 wrapping at operation boundaries. -/
def evalMicroCExpr_uint128 (env : MicroCEnv) : MicroCExpr → Option Value
  | .litInt n => some (.int n)
  | .litBool b => some (.bool b)
  | .varRef name => some (env name)
  | .binOp op lhs rhs =>
    match evalMicroCExpr_uint128 env lhs, evalMicroCExpr_uint128 env rhs with
    | some v1, some v2 => evalMicroCBinOp_uint128 op v1 v2
    | _, _ => none
  | .unaryOp op e =>
    match evalMicroCExpr_uint128 env e with
    | some v => evalMicroCUnaryOp_uint128 op v
    | none => none
  | .powCall base n =>
    match evalMicroCExpr_uint128 env base with
    | some (.int i) => some (.int (wrapUInt128 (i ^ n)))
    | _ => none
  | .arrayAccess base idx =>
    match base with
    | .varRef name =>
      match evalMicroCExpr_uint128 env idx with
      | some (.int i) => some (env (name ++ "[" ++ toString i ++ "]"))
      | _ => none
    | _ => none

/-! ## Statement Evaluator -/

/-- Helper to get MicroC array name (shared with UnsignedEval). -/
private def getMicroCArrayName_uint128 : MicroCExpr → Option String
  | .varRef name => some name
  | _ => none

/-- Evaluate a MicroC statement with UInt128 wrapping. Fuel-based.
    Termination: lexicographic on (fuel, sizeOf stmt). -/
def evalMicroC_uint128 (fuel : Nat) (env : MicroCEnv) (stmt : MicroCStmt) :
    Option (Outcome × MicroCEnv) :=
  match stmt with
  | .skip => some (.normal, env)
  | .break_ => some (.break_, env)
  | .continue_ => some (.continue_, env)
  | .return_ re =>
    match re with
    | some e =>
      match evalMicroCExpr_uint128 env e with
      | some v => some (.return_ (some v), env)
      | none => none
    | none => some (.return_ none, env)
  | .assign name expr =>
    match evalMicroCExpr_uint128 env expr with
    | some v => some (.normal, env.update name v)
    | none => none
  | .store base idx val =>
    match getMicroCArrayName_uint128 base, evalMicroCExpr_uint128 env idx, evalMicroCExpr_uint128 env val with
    | some name, some (.int i), some v =>
      some (.normal, env.update (name ++ "[" ++ toString i ++ "]") v)
    | _, _, _ => none
  | .load var base idx =>
    match getMicroCArrayName_uint128 base, evalMicroCExpr_uint128 env idx with
    | some name, some (.int i) =>
      some (.normal, env.update var (env (name ++ "[" ++ toString i ++ "]")))
    | _, _ => none
  | .call _ _ _ => none
  | .seq s1 s2 =>
    match evalMicroC_uint128 fuel env s1 with
    | some (.normal, env') => evalMicroC_uint128 fuel env' s2
    | other => other
  | .ite cond thenB elseB =>
    match evalMicroCExpr_uint128 env cond with
    | some (.bool true) => evalMicroC_uint128 fuel env thenB
    | some (.bool false) => evalMicroC_uint128 fuel env elseB
    | _ => none
  | .while_ cond body =>
    match fuel with
    | 0 => some (.outOfFuel, env)
    | fuel' + 1 =>
      match evalMicroCExpr_uint128 env cond with
      | some (.bool false) => some (.normal, env)
      | some (.bool true) =>
        match evalMicroC_uint128 fuel' env body with
        | some (.normal, env') => evalMicroC_uint128 fuel' env' (.while_ cond body)
        | some (.continue_, env') => evalMicroC_uint128 fuel' env' (.while_ cond body)
        | some (.break_, env') => some (.normal, env')
        | some (.return_ rv, env') => some (.return_ rv, env')
        | some (.outOfFuel, env') => some (.outOfFuel, env')
        | none => none
      | _ => none
termination_by (fuel, sizeOf stmt)

/-! ## Skip equation lemma -/

@[simp] theorem evalMicroC_uint128_skip (fuel : Nat) (env : MicroCEnv) :
    evalMicroC_uint128 fuel env .skip = some (.normal, env) := by
  simp [evalMicroC_uint128]

/-! ## Non-Vacuity -/

/-- UInt128 evaluation: x = 0xFF & 0x0F produces x = 15 -/
example :
    (do let (_, e) ← evalMicroC_uint128 10 MicroCEnv.default
          (.assign "x" (.binOp .band (.litInt 0xFF) (.litInt 0x0F)))
        pure (e "x")) = some (.int 15) := by native_decide

/-- UInt128 evaluation: 128-bit overflow wraps to 0 -/
example :
    (do let (_, e) ← evalMicroC_uint128 10 MicroCEnv.default
          (.assign "x" (.binOp .add (.litInt (2^128 - 1)) (.litInt 1)))
        pure (e "x")) = some (.int 0) := by native_decide

/-- UInt128 evaluation: x = 3 << 4 produces x = 48 -/
example :
    (do let (_, e) ← evalMicroC_uint128 10 MicroCEnv.default
          (.assign "x" (.binOp .bshl (.litInt 3) (.litInt 4)))
        pure (e "x")) = some (.int 48) := by native_decide

/-- Shift modulus = % 128: shift by 127 works -/
example :
    (do let (_, e) ← evalMicroC_uint128 10 MicroCEnv.default
          (.assign "x" (.binOp .bshl (.litInt 1) (.litInt 127)))
        pure (e "x")) = some (.int (2^127)) := by native_decide

/-- Shift modulus = % 128: shift by 128 wraps to shift by 0 -/
example :
    (do let (_, e) ← evalMicroC_uint128 10 MicroCEnv.default
          (.assign "x" (.binOp .bshl (.litInt 1) (.litInt 128)))
        pure (e "x")) = some (.int 1) := by native_decide

/-- Shift by 64 works correctly in uint128 (key for Goldilocks fold) -/
example :
    (do let (_, e) ← evalMicroC_uint128 10 MicroCEnv.default
          (.assign "x" (.binOp .bshr (.litInt (2^64 + 42)) (.litInt 64)))
        pure (e "x")) = some (.int 1) := by native_decide

/-- UInt128 Goldilocks-style: lo = x & mask64, hi = x >> 64, sum = lo + hi * C -/
example :
    let mask64 := (2^64 - 1 : Int)
    let goldi_C := (4294967295 : Int) -- 2^32 - 1
    let x := (2^64 + 42 : Int)
    (do let (_, e) ← evalMicroC_uint128 10 MicroCEnv.default
          (.seq (.assign "lo" (.binOp .band (.litInt x) (.litInt mask64)))
          (.seq (.assign "hi" (.binOp .bshr (.litInt x) (.litInt 64)))
                (.assign "sum" (.binOp .add (.varRef "lo")
                  (.binOp .mul (.varRef "hi") (.litInt goldi_C))))))
        pure (e "sum")) = some (.int (42 + 1 * goldi_C)) := by native_decide

end TrustLean
