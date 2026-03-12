/-
  Trust-Lean — Verified Code Generation Framework
  MicroC/Eval.lean: MicroC expression evaluator and fuel-based statement evaluator

  N10.2 (v2.0.0): CRITICO — defines operational semantics for MicroC AST.
  Mirrors evalExpr/evalStmt from Core/Eval.lean but operates on MicroC types
  with String identifiers.

  Design decisions:
  - evalMicroCExpr : MicroCEnv → MicroCExpr → Option Value (None on type error)
  - evalMicroC : Nat → MicroCEnv → MicroCStmt → Option (Outcome × MicroCEnv)
  - Fuel decreases only in while_ (no for_ in MicroC)
  - arrayAccess in MicroCExpr for load operations
  - Termination: lexicographic (fuel, sizeOf stmt)
-/

import TrustLean.MicroC.AST
import TrustLean.Core.Stmt

set_option autoImplicit false

namespace TrustLean

/-! ## Array Base Name Extraction (MicroC) -/

/-- Extract array base name from a MicroC expression.
    Only `varRef name` is a valid array base in MicroC. -/
def getMicroCArrayName : MicroCExpr → Option String
  | .varRef name => some name
  | _ => none

/-! ## Expression Evaluator -/

/-- Evaluate a MicroC expression in an environment.
    Returns None on type mismatch.
    No fuel needed — expressions always terminate (structural recursion). -/
def evalMicroCExpr (env : MicroCEnv) : MicroCExpr → Option Value
  | .litInt n => some (.int n)
  | .litBool b => some (.bool b)
  | .varRef name => some (env name)
  | .binOp op e1 e2 =>
    match evalMicroCExpr env e1, evalMicroCExpr env e2 with
    | some v1, some v2 => evalMicroCBinOp op v1 v2
    | _, _ => none
  | .unaryOp op e =>
    match evalMicroCExpr env e with
    | some v => evalMicroCUnaryOp op v
    | none => none
  | .powCall base n =>
    match evalMicroCExpr env base with
    | some (.int i) => some (.int (i ^ n))
    | _ => none
  | .arrayAccess base idx =>
    match getMicroCArrayName base, evalMicroCExpr env idx with
    | some name, some (.int i) => some (env (name ++ "[" ++ toString i ++ "]"))
    | _, _ => none

/-! ## evalMicroCExpr @[simp] Equation Lemmas -/

@[simp] theorem evalMicroCExpr_litInt (env : MicroCEnv) (n : Int) :
    evalMicroCExpr env (.litInt n) = some (.int n) := rfl

@[simp] theorem evalMicroCExpr_litBool (env : MicroCEnv) (b : Bool) :
    evalMicroCExpr env (.litBool b) = some (.bool b) := rfl

@[simp] theorem evalMicroCExpr_varRef (env : MicroCEnv) (name : String) :
    evalMicroCExpr env (.varRef name) = some (env name) := rfl

@[simp] theorem evalMicroCExpr_binOp (env : MicroCEnv) (op : MicroCBinOp)
    (e1 e2 : MicroCExpr) :
    evalMicroCExpr env (.binOp op e1 e2) =
      match evalMicroCExpr env e1, evalMicroCExpr env e2 with
      | some v1, some v2 => evalMicroCBinOp op v1 v2
      | _, _ => none := rfl

@[simp] theorem evalMicroCExpr_unaryOp (env : MicroCEnv) (op : MicroCUnaryOp)
    (e : MicroCExpr) :
    evalMicroCExpr env (.unaryOp op e) =
      match evalMicroCExpr env e with
      | some v => evalMicroCUnaryOp op v
      | none => none := rfl

@[simp] theorem evalMicroCExpr_powCall (env : MicroCEnv) (base : MicroCExpr) (n : Nat) :
    evalMicroCExpr env (.powCall base n) =
      match evalMicroCExpr env base with
      | some (.int i) => some (.int (i ^ n))
      | _ => none := rfl

/-- evalMicroCExpr is deterministic (pure function). -/
theorem evalMicroCExpr_deterministic (env : MicroCEnv) (e : MicroCExpr)
    (v1 v2 : Value) (h1 : evalMicroCExpr env e = some v1)
    (h2 : evalMicroCExpr env e = some v2) : v1 = v2 := by
  rw [h1] at h2; exact Option.some.inj h2

/-! ## Statement Evaluator -/

/-- Evaluate a MicroC statement with fuel-based big-step semantics.
    Fuel decreases only in while_ case. All other constructors pass fuel through.
    Termination: lexicographic on (fuel, sizeOf stmt).

    Returns:
    - `some (.normal, env')` — completed normally
    - `some (.break_, env')` — break signal
    - `some (.continue_, env')` — continue signal
    - `some (.return_ v, env')` — return signal
    - `some (.outOfFuel, env')` — depth bound reached
    - `none` — expression type error -/
def evalMicroC (fuel : Nat) (env : MicroCEnv) (stmt : MicroCStmt) :
    Option (Outcome × MicroCEnv) :=
  match stmt with
  | .skip => some (.normal, env)
  | .break_ => some (.break_, env)
  | .continue_ => some (.continue_, env)
  | .return_ re =>
    match re with
    | some e =>
      match evalMicroCExpr env e with
      | some v => some (.return_ (some v), env)
      | none => none
    | none => some (.return_ none, env)
  | .assign name expr =>
    match evalMicroCExpr env expr with
    | some v => some (.normal, env.update name v)
    | none => none
  | .store base idx val =>
    match getMicroCArrayName base, evalMicroCExpr env idx, evalMicroCExpr env val with
    | some name, some (.int i), some v =>
      some (.normal, env.update (name ++ "[" ++ toString i ++ "]") v)
    | _, _, _ => none
  | .load var base idx =>
    match getMicroCArrayName base, evalMicroCExpr env idx with
    | some name, some (.int i) =>
      some (.normal, env.update var (env (name ++ "[" ++ toString i ++ "]")))
    | _, _ => none
  | .call _ _ _ => none
  | .seq s1 s2 =>
    match evalMicroC fuel env s1 with
    | some (.normal, env') => evalMicroC fuel env' s2
    | other => other
  | .ite cond thenB elseB =>
    match evalMicroCExpr env cond with
    | some (.bool true) => evalMicroC fuel env thenB
    | some (.bool false) => evalMicroC fuel env elseB
    | _ => none
  | .while_ cond body =>
    match fuel with
    | 0 => some (.outOfFuel, env)
    | fuel' + 1 =>
      match evalMicroCExpr env cond with
      | some (.bool false) => some (.normal, env)
      | some (.bool true) =>
        match evalMicroC fuel' env body with
        | some (.normal, env') => evalMicroC fuel' env' (.while_ cond body)
        | some (.continue_, env') => evalMicroC fuel' env' (.while_ cond body)
        | some (.break_, env') => some (.normal, env')
        | some (.return_ rv, env') => some (.return_ rv, env')
        | some (.outOfFuel, env') => some (.outOfFuel, env')
        | none => none
      | _ => none
termination_by (fuel, sizeOf stmt)

/-! ## evalMicroC @[simp] Equation Lemmas -/

@[simp] theorem evalMicroC_skip (fuel : Nat) (env : MicroCEnv) :
    evalMicroC fuel env .skip = some (.normal, env) := by
  simp [evalMicroC]

@[simp] theorem evalMicroC_break (fuel : Nat) (env : MicroCEnv) :
    evalMicroC fuel env .break_ = some (.break_, env) := by
  simp [evalMicroC]

@[simp] theorem evalMicroC_continue (fuel : Nat) (env : MicroCEnv) :
    evalMicroC fuel env .continue_ = some (.continue_, env) := by
  simp [evalMicroC]

@[simp] theorem evalMicroC_return_none (fuel : Nat) (env : MicroCEnv) :
    evalMicroC fuel env (.return_ none) = some (.return_ none, env) := by
  simp [evalMicroC]

@[simp] theorem evalMicroC_return_some (fuel : Nat) (env : MicroCEnv) (e : MicroCExpr) :
    evalMicroC fuel env (.return_ (some e)) =
      match evalMicroCExpr env e with
      | some v => some (.return_ (some v), env)
      | none => none := by
  simp [evalMicroC]

@[simp] theorem evalMicroC_assign (fuel : Nat) (env : MicroCEnv)
    (name : String) (expr : MicroCExpr) :
    evalMicroC fuel env (.assign name expr) =
      match evalMicroCExpr env expr with
      | some v => some (.normal, env.update name v)
      | none => none := by
  simp [evalMicroC]

@[simp] theorem evalMicroC_seq (fuel : Nat) (env : MicroCEnv)
    (s1 s2 : MicroCStmt) :
    evalMicroC fuel env (.seq s1 s2) =
      match evalMicroC fuel env s1 with
      | some (.normal, env') => evalMicroC fuel env' s2
      | other => other := by
  simp [evalMicroC]

@[simp] theorem evalMicroC_ite (fuel : Nat) (env : MicroCEnv)
    (cond : MicroCExpr) (thenB elseB : MicroCStmt) :
    evalMicroC fuel env (.ite cond thenB elseB) =
      match evalMicroCExpr env cond with
      | some (.bool true) => evalMicroC fuel env thenB
      | some (.bool false) => evalMicroC fuel env elseB
      | _ => none := by
  simp [evalMicroC]

@[simp] theorem evalMicroC_while_zero (env : MicroCEnv)
    (cond : MicroCExpr) (body : MicroCStmt) :
    evalMicroC 0 env (.while_ cond body) = some (.outOfFuel, env) := by
  simp [evalMicroC]

@[simp] theorem evalMicroC_while_succ (fuel : Nat) (env : MicroCEnv)
    (cond : MicroCExpr) (body : MicroCStmt) :
    evalMicroC (fuel + 1) env (.while_ cond body) =
      match evalMicroCExpr env cond with
      | some (.bool false) => some (.normal, env)
      | some (.bool true) =>
        match evalMicroC fuel env body with
        | some (.normal, env') => evalMicroC fuel env' (.while_ cond body)
        | some (.continue_, env') => evalMicroC fuel env' (.while_ cond body)
        | some (.break_, env') => some (.normal, env')
        | some (.return_ rv, env') => some (.return_ rv, env')
        | some (.outOfFuel, env') => some (.outOfFuel, env')
        | none => none
      | _ => none := by
  simp [evalMicroC]

/-! ## Basic Properties -/

/-- evalMicroC on skip produces normal with unchanged env. -/
theorem evalMicroC_skip_identity (fuel : Nat) (env : MicroCEnv) :
    evalMicroC fuel env .skip = some (.normal, env) := by simp

/-- While with false condition terminates normally. -/
theorem evalMicroC_while_false_exit (fuel : Nat) (env : MicroCEnv)
    (cond : MicroCExpr) (body : MicroCStmt)
    (h : evalMicroCExpr env cond = some (.bool false))
    (hf : 0 < fuel) :
    evalMicroC fuel env (.while_ cond body) = some (.normal, env) := by
  match fuel, hf with
  | n + 1, _ => simp [h]

/-- Assignment updates exactly one variable. -/
theorem evalMicroC_assign_updates (fuel : Nat) (env : MicroCEnv)
    (name : String) (expr : MicroCExpr) (v : Value)
    (h : evalMicroCExpr env expr = some v) :
    evalMicroC fuel env (.assign name expr) = some (.normal, env.update name v) := by
  simp [h]

/-- evalMicroC is deterministic. -/
theorem evalMicroC_deterministic (fuel : Nat) (env : MicroCEnv) (s : MicroCStmt)
    (r1 r2 : Outcome × MicroCEnv)
    (h1 : evalMicroC fuel env s = some r1)
    (h2 : evalMicroC fuel env s = some r2) : r1 = r2 := by
  rw [h1] at h2; exact Option.some.inj h2

end TrustLean
