/-
  Trust-Lean — Verified Code Generation Framework
  Core/Eval.lean: Expression evaluator and fuel-based statement evaluator

  N1.3: CRITICO — first proof-bearing node. Defines operational semantics
  for the Core IR via evalExpr and evalStmt.

  Key design decisions:
  - evalExpr : LowLevelEnv → LowLevelExpr → Option Value (None on type error)
  - evalStmt : Nat → LowLevelEnv → Stmt → Option (Outcome × LowLevelEnv)
    - Option None = expression type error during evaluation
    - Outcome.outOfFuel = fuel exhausted (depth bound reached)
  - Fuel decreases in while/for_ only (LeanScribe-proven model)
  - for_ desugars to while in evaluation (definitional, per Clight)
  - while Outcome propagation: normal/continue_ → re-enter, break_ → exit, return_ → propagate
  - NOTA: continue_ inside for_ body skips the step statement (naive desugaring).
    In C, `continue` in `for` executes the increment. CompCert Clight uses a dedicated
    for rule. Trust-Lean uses the simpler desugaring — frontends must be aware.
  - Termination: lexicographic (fuel, sizeOf stmt)
-/

import TrustLean.Core.Value
import TrustLean.Core.Stmt

set_option autoImplicit false

namespace TrustLean

/-! ## Array Base Name Extraction -/

/-- Extract array base name from a LowLevelExpr.
    Only `varRef (.user name)` and `varRef (.array name _)` are valid array bases. -/
def getArrayName : LowLevelExpr → Option String
  | .varRef (.user name) => some name
  | .varRef (.array name _) => some name
  | _ => none

/-! ## Expression Evaluator -/

/-- Evaluate a low-level expression in an environment.
    Returns None on type mismatch (e.g., adding Bool to Int).
    No fuel needed — expressions always terminate (structural recursion). -/
def evalExpr (env : LowLevelEnv) : LowLevelExpr → Option Value
  | .litInt n => some (.int n)
  | .litBool b => some (.bool b)
  | .varRef name => some (env name)
  | .binOp op e1 e2 =>
    match evalExpr env e1, evalExpr env e2 with
    | some v1, some v2 => evalBinOp op v1 v2
    | _, _ => none
  | .unaryOp op e =>
    match evalExpr env e with
    | some v => evalUnaryOp op v
    | none => none
  | .powCall base n =>
    match evalExpr env base with
    | some (.int i) => some (.int (i ^ n))
    | _ => none

@[simp] theorem evalExpr_litInt (env : LowLevelEnv) (n : Int) :
    evalExpr env (.litInt n) = some (.int n) := rfl

@[simp] theorem evalExpr_litBool (env : LowLevelEnv) (b : Bool) :
    evalExpr env (.litBool b) = some (.bool b) := rfl

@[simp] theorem evalExpr_varRef (env : LowLevelEnv) (name : VarName) :
    evalExpr env (.varRef name) = some (env name) := rfl

@[simp] theorem evalExpr_binOp (env : LowLevelEnv) (op : BinOp)
    (e1 e2 : LowLevelExpr) :
    evalExpr env (.binOp op e1 e2) =
      match evalExpr env e1, evalExpr env e2 with
      | some v1, some v2 => evalBinOp op v1 v2
      | _, _ => none := rfl

@[simp] theorem evalExpr_unaryOp (env : LowLevelEnv) (op : UnaryOp) (e : LowLevelExpr) :
    evalExpr env (.unaryOp op e) =
      match evalExpr env e with
      | some v => evalUnaryOp op v
      | none => none := rfl

@[simp] theorem evalExpr_powCall (env : LowLevelEnv) (base : LowLevelExpr) (n : Nat) :
    evalExpr env (.powCall base n) =
      match evalExpr env base with
      | some (.int i) => some (.int (i ^ n))
      | _ => none := rfl

/-! ## Statement Evaluator -/

/-- Evaluate a statement with fuel-based big-step semantics.
    Fuel decreases only in while/for_ cases. All other constructors pass fuel through.
    Termination: lexicographic on (fuel, sizeOf stmt).

    Returns:
    - `some (.normal, env')` — completed normally, continue with env'
    - `some (.break_, env')` — break signal, exit innermost loop
    - `some (.continue_, env')` — continue signal, skip to next iteration
    - `some (.return_ v, env')` — return signal with optional value
    - `some (.outOfFuel, env')` — depth bound reached
    - `none` — expression type error during evaluation -/
def evalStmt (fuel : Nat) (env : LowLevelEnv) (stmt : Stmt) :
    Option (Outcome × LowLevelEnv) :=
  match stmt with
  | .skip => some (.normal, env)
  | .break_ => some (.break_, env)
  | .continue_ => some (.continue_, env)
  | .return_ re =>
    match re with
    | some e =>
      match evalExpr env e with
      | some v => some (.return_ (some v), env)
      | none => none
    | none => some (.return_ none, env)
  | .assign name expr =>
    match evalExpr env expr with
    | some v => some (.normal, env.update name v)
    | none => none
  | .store base idx val =>
    match getArrayName base, evalExpr env idx, evalExpr env val with
    | some name, some (.int i), some v => some (.normal, env.update (.array name i) v)
    | _, _, _ => none
  | .load var base idx =>
    match getArrayName base, evalExpr env idx with
    | some name, some (.int i) => some (.normal, env.update var (env (.array name i)))
    | _, _ => none
  | .call _ _ _ => none
  | .seq s1 s2 =>
    match evalStmt fuel env s1 with
    | some (.normal, env') => evalStmt fuel env' s2
    | other => other
  | .ite cond thenB elseB =>
    match evalExpr env cond with
    | some (.bool true) => evalStmt fuel env thenB
    | some (.bool false) => evalStmt fuel env elseB
    | _ => none
  | .while cond body =>
    match fuel with
    | 0 => some (.outOfFuel, env)
    | fuel' + 1 =>
      match evalExpr env cond with
      | some (.bool false) => some (.normal, env)
      | some (.bool true) =>
        match evalStmt fuel' env body with
        | some (.normal, env') => evalStmt fuel' env' (.while cond body)
        | some (.continue_, env') => evalStmt fuel' env' (.while cond body)
        | some (.break_, env') => some (.normal, env')
        | some (.return_ rv, env') => some (.return_ rv, env')
        | some (.outOfFuel, env') => some (.outOfFuel, env')
        | none => none
      | _ => none
  | .for_ init cond step body =>
    match fuel with
    | 0 => some (.outOfFuel, env)
    | fuel' + 1 =>
      match evalStmt fuel' env init with
      | some (.normal, env') => evalStmt fuel' env' (.while cond (.seq body step))
      | some (o, env') => some (o, env')
      | none => none
termination_by (fuel, sizeOf stmt)

/-! ## evalStmt @[simp] Equation Lemmas -/

@[simp] theorem evalStmt_skip (fuel : Nat) (env : LowLevelEnv) :
    evalStmt fuel env .skip = some (.normal, env) := by
  simp [evalStmt]

@[simp] theorem evalStmt_break (fuel : Nat) (env : LowLevelEnv) :
    evalStmt fuel env .break_ = some (.break_, env) := by
  simp [evalStmt]

@[simp] theorem evalStmt_continue (fuel : Nat) (env : LowLevelEnv) :
    evalStmt fuel env .continue_ = some (.continue_, env) := by
  simp [evalStmt]

@[simp] theorem evalStmt_return_none (fuel : Nat) (env : LowLevelEnv) :
    evalStmt fuel env (.return_ none) = some (.return_ none, env) := by
  simp [evalStmt]

@[simp] theorem evalStmt_return_some (fuel : Nat) (env : LowLevelEnv) (e : LowLevelExpr) :
    evalStmt fuel env (.return_ (some e)) =
      match evalExpr env e with
      | some v => some (.return_ (some v), env)
      | none => none := by
  simp [evalStmt]

@[simp] theorem evalStmt_assign (fuel : Nat) (env : LowLevelEnv)
    (name : VarName) (expr : LowLevelExpr) :
    evalStmt fuel env (.assign name expr) =
      match evalExpr env expr with
      | some v => some (.normal, env.update name v)
      | none => none := by
  simp [evalStmt]

@[simp] theorem evalStmt_store (fuel : Nat) (env : LowLevelEnv)
    (base idx val : LowLevelExpr) :
    evalStmt fuel env (.store base idx val) =
      match getArrayName base, evalExpr env idx, evalExpr env val with
      | some name, some (.int i), some v => some (.normal, env.update (.array name i) v)
      | _, _, _ => none := by
  simp [evalStmt]

@[simp] theorem evalStmt_load (fuel : Nat) (env : LowLevelEnv)
    (var : VarName) (base idx : LowLevelExpr) :
    evalStmt fuel env (.load var base idx) =
      match getArrayName base, evalExpr env idx with
      | some name, some (.int i) => some (.normal, env.update var (env (.array name i)))
      | _, _ => none := by
  simp [evalStmt]

@[simp] theorem evalStmt_call (fuel : Nat) (env : LowLevelEnv)
    (var : VarName) (fname : String) (args : List LowLevelExpr) :
    evalStmt fuel env (.call var fname args) = none := by
  simp [evalStmt]

@[simp] theorem evalStmt_seq (fuel : Nat) (env : LowLevelEnv) (s1 s2 : Stmt) :
    evalStmt fuel env (.seq s1 s2) =
      match evalStmt fuel env s1 with
      | some (.normal, env') => evalStmt fuel env' s2
      | other => other := by
  simp [evalStmt]

@[simp] theorem evalStmt_ite (fuel : Nat) (env : LowLevelEnv)
    (cond : LowLevelExpr) (thenB elseB : Stmt) :
    evalStmt fuel env (.ite cond thenB elseB) =
      match evalExpr env cond with
      | some (.bool true) => evalStmt fuel env thenB
      | some (.bool false) => evalStmt fuel env elseB
      | _ => none := by
  simp [evalStmt]

@[simp] theorem evalStmt_while_zero (env : LowLevelEnv)
    (cond : LowLevelExpr) (body : Stmt) :
    evalStmt 0 env (.while cond body) = some (.outOfFuel, env) := by
  simp [evalStmt]

@[simp] theorem evalStmt_while_succ (fuel : Nat) (env : LowLevelEnv)
    (cond : LowLevelExpr) (body : Stmt) :
    evalStmt (fuel + 1) env (.while cond body) =
      match evalExpr env cond with
      | some (.bool false) => some (.normal, env)
      | some (.bool true) =>
        match evalStmt fuel env body with
        | some (.normal, env') => evalStmt fuel env' (.while cond body)
        | some (.continue_, env') => evalStmt fuel env' (.while cond body)
        | some (.break_, env') => some (.normal, env')
        | some (.return_ rv, env') => some (.return_ rv, env')
        | some (.outOfFuel, env') => some (.outOfFuel, env')
        | none => none
      | _ => none := by
  simp [evalStmt]

@[simp] theorem evalStmt_for_zero (env : LowLevelEnv)
    (init : Stmt) (cond : LowLevelExpr) (step body : Stmt) :
    evalStmt 0 env (.for_ init cond step body) = some (.outOfFuel, env) := by
  simp [evalStmt]

@[simp] theorem evalStmt_for_succ (fuel : Nat) (env : LowLevelEnv)
    (init : Stmt) (cond : LowLevelExpr) (step body : Stmt) :
    evalStmt (fuel + 1) env (.for_ init cond step body) =
      match evalStmt fuel env init with
      | some (.normal, env') => evalStmt fuel env' (.while cond (.seq body step))
      | some (o, env') => some (o, env')
      | none => none := by
  simp [evalStmt]

end TrustLean
