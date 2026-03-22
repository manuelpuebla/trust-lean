/-
  Trust-Lean v3.1 — Unsigned Evaluator (UInt32/UInt64)
  N19.2: CRITICO — evalMicroC_uint32/64 + fuel monotonicity.

  Mirrors Int64Eval.lean structure exactly (L-625).
  Wraps at operation boundaries only (L-626).
  Dedicated @[simp] lemmas per constructor (L-577).
-/
import TrustLean.MicroC.Eval
import TrustLean.MicroC.Unsigned

set_option autoImplicit false

namespace TrustLean

/-! ## Unsigned BinOp/UnaryOp Evaluators -/

/-- Evaluate a MicroC binary operator with UInt32 wrapping.
    Arithmetic results (add, sub, mul) are wrapped via wrapUInt32.
    Bitwise results are wrapped via wrapUInt32.
    Comparison and logical operations return Bool, unchanged. -/
def evalMicroCBinOp_uint32 (op : MicroCBinOp) (v1 v2 : Value) : Option Value :=
  match op, v1, v2 with
  | .add, .int a, .int b => some (.int (addUInt32 a b))
  | .sub, .int a, .int b => some (.int (subUInt32 a b))
  | .mul, .int a, .int b => some (.int (mulUInt32 a b))
  | .eqOp, .int a, .int b => some (.bool (a == b))
  | .ltOp, .int a, .int b => some (.bool (decide (a < b)))
  | .land, .bool a, .bool b => some (.bool (a && b))
  | .lor, .bool a, .bool b => some (.bool (a || b))
  | .band, .int a, .int b => some (.int (wrapUInt32 (Int.land a b)))
  | .bor, .int a, .int b => some (.int (wrapUInt32 (Int.lor a b)))
  | .bxor, .int a, .int b => some (.int (wrapUInt32 (Int.xor a b)))
  | .bshl, .int a, .int b => some (.int (wrapUInt32 (Int.shiftLeft a (b.toNat % 64))))
  | .bshr, .int a, .int b => some (.int (wrapUInt32 (Int.shiftRight a (b.toNat % 64))))
  | _, _, _ => none

/-- Evaluate a MicroC unary operator with UInt32 wrapping. -/
def evalMicroCUnaryOp_uint32 (op : MicroCUnaryOp) (v : Value) : Option Value :=
  match op, v with
  | .neg, .int n => some (.int (wrapUInt32 (-n)))
  | .lnot, .bool b => some (.bool (!b))
  | .widen32to64, .int n => some (.int (wrapUInt32 (n % (2^32 : Int))))
  | .trunc64to32, .int n => some (.int (wrapUInt32 (n % (2^32 : Int))))
  | _, _ => none

/-- Evaluate a MicroC binary operator with UInt64 wrapping. -/
def evalMicroCBinOp_uint64 (op : MicroCBinOp) (v1 v2 : Value) : Option Value :=
  match op, v1, v2 with
  | .add, .int a, .int b => some (.int (addUInt64 a b))
  | .sub, .int a, .int b => some (.int (subUInt64 a b))
  | .mul, .int a, .int b => some (.int (mulUInt64 a b))
  | .eqOp, .int a, .int b => some (.bool (a == b))
  | .ltOp, .int a, .int b => some (.bool (decide (a < b)))
  | .land, .bool a, .bool b => some (.bool (a && b))
  | .lor, .bool a, .bool b => some (.bool (a || b))
  | .band, .int a, .int b => some (.int (wrapUInt64 (Int.land a b)))
  | .bor, .int a, .int b => some (.int (wrapUInt64 (Int.lor a b)))
  | .bxor, .int a, .int b => some (.int (wrapUInt64 (Int.xor a b)))
  | .bshl, .int a, .int b => some (.int (wrapUInt64 (Int.shiftLeft a (b.toNat % 64))))
  | .bshr, .int a, .int b => some (.int (wrapUInt64 (Int.shiftRight a (b.toNat % 64))))
  | _, _, _ => none

/-- Evaluate a MicroC unary operator with UInt64 wrapping. -/
def evalMicroCUnaryOp_uint64 (op : MicroCUnaryOp) (v : Value) : Option Value :=
  match op, v with
  | .neg, .int n => some (.int (wrapUInt64 (-n)))
  | .lnot, .bool b => some (.bool (!b))
  | .widen32to64, .int n => some (.int (wrapUInt64 (n % (2^32 : Int))))
  | .trunc64to32, .int n => some (.int (wrapUInt64 (n % (2^32 : Int))))
  | _, _ => none

/-! ## UInt32 @[simp] Lemmas -/

@[simp] theorem evalMicroCBinOp_uint32_add (a b : Int) :
    evalMicroCBinOp_uint32 .add (.int a) (.int b) = some (.int (addUInt32 a b)) := rfl
@[simp] theorem evalMicroCBinOp_uint32_sub (a b : Int) :
    evalMicroCBinOp_uint32 .sub (.int a) (.int b) = some (.int (subUInt32 a b)) := rfl
@[simp] theorem evalMicroCBinOp_uint32_mul (a b : Int) :
    evalMicroCBinOp_uint32 .mul (.int a) (.int b) = some (.int (mulUInt32 a b)) := rfl
@[simp] theorem evalMicroCBinOp_uint32_eqOp (a b : Int) :
    evalMicroCBinOp_uint32 .eqOp (.int a) (.int b) = some (.bool (a == b)) := rfl
@[simp] theorem evalMicroCBinOp_uint32_ltOp (a b : Int) :
    evalMicroCBinOp_uint32 .ltOp (.int a) (.int b) = some (.bool (decide (a < b))) := rfl
@[simp] theorem evalMicroCBinOp_uint32_land (a b : Bool) :
    evalMicroCBinOp_uint32 .land (.bool a) (.bool b) = some (.bool (a && b)) := rfl
@[simp] theorem evalMicroCBinOp_uint32_lor (a b : Bool) :
    evalMicroCBinOp_uint32 .lor (.bool a) (.bool b) = some (.bool (a || b)) := rfl
@[simp] theorem evalMicroCBinOp_uint32_band (a b : Int) :
    evalMicroCBinOp_uint32 .band (.int a) (.int b) = some (.int (wrapUInt32 (Int.land a b))) := rfl
@[simp] theorem evalMicroCBinOp_uint32_bor (a b : Int) :
    evalMicroCBinOp_uint32 .bor (.int a) (.int b) = some (.int (wrapUInt32 (Int.lor a b))) := rfl
@[simp] theorem evalMicroCBinOp_uint32_bxor (a b : Int) :
    evalMicroCBinOp_uint32 .bxor (.int a) (.int b) = some (.int (wrapUInt32 (Int.xor a b))) := rfl
@[simp] theorem evalMicroCBinOp_uint32_bshl (a b : Int) :
    evalMicroCBinOp_uint32 .bshl (.int a) (.int b) =
    some (.int (wrapUInt32 (Int.shiftLeft a (b.toNat % 64)))) := rfl
@[simp] theorem evalMicroCBinOp_uint32_bshr (a b : Int) :
    evalMicroCBinOp_uint32 .bshr (.int a) (.int b) =
    some (.int (wrapUInt32 (Int.shiftRight a (b.toNat % 64)))) := rfl

@[simp] theorem evalMicroCUnaryOp_uint32_neg (n : Int) :
    evalMicroCUnaryOp_uint32 .neg (.int n) = some (.int (wrapUInt32 (-n))) := rfl
@[simp] theorem evalMicroCUnaryOp_uint32_lnot (b : Bool) :
    evalMicroCUnaryOp_uint32 .lnot (.bool b) = some (.bool (!b)) := rfl
@[simp] theorem evalMicroCUnaryOp_uint32_widen (n : Int) :
    evalMicroCUnaryOp_uint32 .widen32to64 (.int n) =
    some (.int (wrapUInt32 (n % (2^32 : Int)))) := rfl
@[simp] theorem evalMicroCUnaryOp_uint32_trunc (n : Int) :
    evalMicroCUnaryOp_uint32 .trunc64to32 (.int n) =
    some (.int (wrapUInt32 (n % (2^32 : Int)))) := rfl

/-! ## Expression Evaluators -/

/-- Evaluate a MicroC expression with UInt32 wrapping at operation boundaries (L-626). -/
def evalMicroCExpr_uint32 (env : MicroCEnv) : MicroCExpr → Option Value
  | .litInt n => some (.int n)
  | .litBool b => some (.bool b)
  | .varRef name => some (env name)
  | .binOp op lhs rhs =>
    match evalMicroCExpr_uint32 env lhs, evalMicroCExpr_uint32 env rhs with
    | some v1, some v2 => evalMicroCBinOp_uint32 op v1 v2
    | _, _ => none
  | .unaryOp op e =>
    match evalMicroCExpr_uint32 env e with
    | some v => evalMicroCUnaryOp_uint32 op v
    | none => none
  | .powCall base n =>
    match evalMicroCExpr_uint32 env base with
    | some (.int i) => some (.int (wrapUInt32 (i ^ n)))
    | _ => none
  | .arrayAccess base idx =>
    match base with
    | .varRef name =>
      match evalMicroCExpr_uint32 env idx with
      | some (.int i) => some (env (name ++ "[" ++ toString i ++ "]"))
      | _ => none
    | _ => none

/-- Evaluate a MicroC expression with UInt64 wrapping at operation boundaries (L-626). -/
def evalMicroCExpr_uint64 (env : MicroCEnv) : MicroCExpr → Option Value
  | .litInt n => some (.int n)
  | .litBool b => some (.bool b)
  | .varRef name => some (env name)
  | .binOp op lhs rhs =>
    match evalMicroCExpr_uint64 env lhs, evalMicroCExpr_uint64 env rhs with
    | some v1, some v2 => evalMicroCBinOp_uint64 op v1 v2
    | _, _ => none
  | .unaryOp op e =>
    match evalMicroCExpr_uint64 env e with
    | some v => evalMicroCUnaryOp_uint64 op v
    | none => none
  | .powCall base n =>
    match evalMicroCExpr_uint64 env base with
    | some (.int i) => some (.int (wrapUInt64 (i ^ n)))
    | _ => none
  | .arrayAccess base idx =>
    match base with
    | .varRef name =>
      match evalMicroCExpr_uint64 env idx with
      | some (.int i) => some (env (name ++ "[" ++ toString i ++ "]"))
      | _ => none
    | _ => none

/-! ## Statement Evaluators -/

/-- Helper to get MicroC array name. -/
def getMicroCArrayName' : MicroCExpr → Option String
  | .varRef name => some name
  | _ => none

/-- Evaluate a MicroC statement with UInt32 wrapping. Fuel-based.
    Termination: lexicographic on (fuel, sizeOf stmt). -/
def evalMicroC_uint32 (fuel : Nat) (env : MicroCEnv) (stmt : MicroCStmt) :
    Option (Outcome × MicroCEnv) :=
  match stmt with
  | .skip => some (.normal, env)
  | .break_ => some (.break_, env)
  | .continue_ => some (.continue_, env)
  | .return_ re =>
    match re with
    | some e =>
      match evalMicroCExpr_uint32 env e with
      | some v => some (.return_ (some v), env)
      | none => none
    | none => some (.return_ none, env)
  | .assign name expr =>
    match evalMicroCExpr_uint32 env expr with
    | some v => some (.normal, env.update name v)
    | none => none
  | .store base idx val =>
    match getMicroCArrayName' base, evalMicroCExpr_uint32 env idx, evalMicroCExpr_uint32 env val with
    | some name, some (.int i), some v =>
      some (.normal, env.update (name ++ "[" ++ toString i ++ "]") v)
    | _, _, _ => none
  | .load var base idx =>
    match getMicroCArrayName' base, evalMicroCExpr_uint32 env idx with
    | some name, some (.int i) =>
      some (.normal, env.update var (env (name ++ "[" ++ toString i ++ "]")))
    | _, _ => none
  | .call _ _ _ => none
  | .seq s1 s2 =>
    match evalMicroC_uint32 fuel env s1 with
    | some (.normal, env') => evalMicroC_uint32 fuel env' s2
    | other => other
  | .ite cond thenB elseB =>
    match evalMicroCExpr_uint32 env cond with
    | some (.bool true) => evalMicroC_uint32 fuel env thenB
    | some (.bool false) => evalMicroC_uint32 fuel env elseB
    | _ => none
  | .while_ cond body =>
    match fuel with
    | 0 => some (.outOfFuel, env)
    | fuel' + 1 =>
      match evalMicroCExpr_uint32 env cond with
      | some (.bool false) => some (.normal, env)
      | some (.bool true) =>
        match evalMicroC_uint32 fuel' env body with
        | some (.normal, env') => evalMicroC_uint32 fuel' env' (.while_ cond body)
        | some (.continue_, env') => evalMicroC_uint32 fuel' env' (.while_ cond body)
        | some (.break_, env') => some (.normal, env')
        | some (.return_ rv, env') => some (.return_ rv, env')
        | some (.outOfFuel, env') => some (.outOfFuel, env')
        | none => none
      | _ => none
termination_by (fuel, sizeOf stmt)

/-- Evaluate a MicroC statement with UInt64 wrapping. Fuel-based.
    Termination: lexicographic on (fuel, sizeOf stmt). -/
def evalMicroC_uint64 (fuel : Nat) (env : MicroCEnv) (stmt : MicroCStmt) :
    Option (Outcome × MicroCEnv) :=
  match stmt with
  | .skip => some (.normal, env)
  | .break_ => some (.break_, env)
  | .continue_ => some (.continue_, env)
  | .return_ re =>
    match re with
    | some e =>
      match evalMicroCExpr_uint64 env e with
      | some v => some (.return_ (some v), env)
      | none => none
    | none => some (.return_ none, env)
  | .assign name expr =>
    match evalMicroCExpr_uint64 env expr with
    | some v => some (.normal, env.update name v)
    | none => none
  | .store base idx val =>
    match getMicroCArrayName' base, evalMicroCExpr_uint64 env idx, evalMicroCExpr_uint64 env val with
    | some name, some (.int i), some v =>
      some (.normal, env.update (name ++ "[" ++ toString i ++ "]") v)
    | _, _, _ => none
  | .load var base idx =>
    match getMicroCArrayName' base, evalMicroCExpr_uint64 env idx with
    | some name, some (.int i) =>
      some (.normal, env.update var (env (name ++ "[" ++ toString i ++ "]")))
    | _, _ => none
  | .call _ _ _ => none
  | .seq s1 s2 =>
    match evalMicroC_uint64 fuel env s1 with
    | some (.normal, env') => evalMicroC_uint64 fuel env' s2
    | other => other
  | .ite cond thenB elseB =>
    match evalMicroCExpr_uint64 env cond with
    | some (.bool true) => evalMicroC_uint64 fuel env thenB
    | some (.bool false) => evalMicroC_uint64 fuel env elseB
    | _ => none
  | .while_ cond body =>
    match fuel with
    | 0 => some (.outOfFuel, env)
    | fuel' + 1 =>
      match evalMicroCExpr_uint64 env cond with
      | some (.bool false) => some (.normal, env)
      | some (.bool true) =>
        match evalMicroC_uint64 fuel' env body with
        | some (.normal, env') => evalMicroC_uint64 fuel' env' (.while_ cond body)
        | some (.continue_, env') => evalMicroC_uint64 fuel' env' (.while_ cond body)
        | some (.break_, env') => some (.normal, env')
        | some (.return_ rv, env') => some (.return_ rv, env')
        | some (.outOfFuel, env') => some (.outOfFuel, env')
        | none => none
      | _ => none
termination_by (fuel, sizeOf stmt)

/-! ## Skip equation lemmas -/

@[simp] theorem evalMicroC_uint32_skip (fuel : Nat) (env : MicroCEnv) :
    evalMicroC_uint32 fuel env .skip = some (.normal, env) := by
  simp [evalMicroC_uint32]

@[simp] theorem evalMicroC_uint64_skip (fuel : Nat) (env : MicroCEnv) :
    evalMicroC_uint64 fuel env .skip = some (.normal, env) := by
  simp [evalMicroC_uint64]

/-! ## Non-Vacuity -/

/-- UInt32 evaluation: x = 0xFF & 0x0F produces x = 15 -/
example :
    (do let (_, e) ← evalMicroC_uint32 10 MicroCEnv.default
          (.assign "x" (.binOp .band (.litInt 0xFF) (.litInt 0x0F)))
        pure (e "x")) = some (.int 15) := by native_decide

/-- UInt32 evaluation: overflow wraps to 0 -/
example :
    (do let (_, e) ← evalMicroC_uint32 10 MicroCEnv.default
          (.assign "x" (.binOp .add (.litInt (2^32 - 1)) (.litInt 1)))
        pure (e "x")) = some (.int 0) := by native_decide

/-- UInt64 evaluation: x = 3 << 4 produces x = 48 -/
example :
    (do let (_, e) ← evalMicroC_uint64 10 MicroCEnv.default
          (.assign "x" (.binOp .bshl (.litInt 3) (.litInt 4)))
        pure (e "x")) = some (.int 48) := by native_decide

/-- UInt32 Mersenne-style: lo = x & 0x7FFFFFFF, hi = x >> 31, sum = lo + hi -/
example :
    (do let (_, e) ← evalMicroC_uint32 10 MicroCEnv.default
          (.seq (.assign "lo" (.binOp .band (.litInt (2^31 + 42)) (.litInt 0x7FFFFFFF)))
          (.seq (.assign "hi" (.binOp .bshr (.litInt (2^31 + 42)) (.litInt 31)))
                (.assign "sum" (.binOp .add (.varRef "lo") (.varRef "hi")))))
        pure (e "sum")) = some (.int 43) := by native_decide

end TrustLean
