/-
  Trust-Lean — Verified Code Generation Framework
  Frontend/ImpStmt/Syntax.lean: ImpStmt AST and semantics

  N3.2: CRIT — imperative statement frontend with while loops.
  Defines ImpExpr (integer arithmetic), ImpBoolExpr (boolean conditions),
  and ImpStmt (imperative programs with assignment, sequencing, if, while).
-/

import TrustLean.Typeclass.CodeGenerable

set_option autoImplicit false

namespace TrustLean

/-! ## Imperative Environment -/

/-- Type alias for imperative environments mapping variable IDs to integers. -/
abbrev ImpEnv := VarId → Int

/-- Update a single variable in the imperative environment. -/
def ImpEnv.update (env : ImpEnv) (v : VarId) (val : Int) : ImpEnv :=
  fun w => if w = v then val else env w

@[simp] theorem ImpEnv.update_same (env : ImpEnv) (v : VarId) (val : Int) :
    (ImpEnv.update env v val) v = val := by
  simp [ImpEnv.update]

@[simp] theorem ImpEnv.update_other (env : ImpEnv) (v w : VarId) (val : Int) (h : w ≠ v) :
    (ImpEnv.update env v val) w = env w := by
  simp [ImpEnv.update, h]

/-! ## Integer Expression AST -/

/-- Integer expressions for the imperative language.
    Same structure as ArithExpr but operates in a pure integer environment. -/
inductive ImpExpr where
  | lit : Int → ImpExpr
  | var : VarId → ImpExpr
  | add : ImpExpr → ImpExpr → ImpExpr
  | mul : ImpExpr → ImpExpr → ImpExpr
  deriving Repr, Inhabited

/-- Evaluate an integer expression. Always succeeds (total function). -/
def ImpExpr.eval (env : ImpEnv) : ImpExpr → Int
  | .lit n => n
  | .var v => env v
  | .add e1 e2 => eval env e1 + eval env e2
  | .mul e1 e2 => eval env e1 * eval env e2

@[simp] theorem ImpExpr.eval_lit (env : ImpEnv) (n : Int) :
    ImpExpr.eval env (.lit n) = n := rfl
@[simp] theorem ImpExpr.eval_var (env : ImpEnv) (v : VarId) :
    ImpExpr.eval env (.var v) = env v := rfl
@[simp] theorem ImpExpr.eval_add (env : ImpEnv) (e1 e2 : ImpExpr) :
    ImpExpr.eval env (.add e1 e2) = ImpExpr.eval env e1 + ImpExpr.eval env e2 := rfl
@[simp] theorem ImpExpr.eval_mul (env : ImpEnv) (e1 e2 : ImpExpr) :
    ImpExpr.eval env (.mul e1 e2) = ImpExpr.eval env e1 * ImpExpr.eval env e2 := rfl

/-! ## Boolean Expression AST -/

/-- Boolean expressions for conditions in if/while.
    Comparisons operate on ImpExpr (integers), logic on ImpBoolExpr (booleans). -/
inductive ImpBoolExpr where
  | lit  : Bool → ImpBoolExpr
  | eq_  : ImpExpr → ImpExpr → ImpBoolExpr
  | lt_  : ImpExpr → ImpExpr → ImpBoolExpr
  | and_ : ImpBoolExpr → ImpBoolExpr → ImpBoolExpr
  | or_  : ImpBoolExpr → ImpBoolExpr → ImpBoolExpr
  | not_ : ImpBoolExpr → ImpBoolExpr
  deriving Repr, Inhabited

/-- Evaluate a boolean expression. Always succeeds (total function). -/
def ImpBoolExpr.eval (env : ImpEnv) : ImpBoolExpr → Bool
  | .lit b => b
  | .eq_ e1 e2 => ImpExpr.eval env e1 == ImpExpr.eval env e2
  | .lt_ e1 e2 => decide (ImpExpr.eval env e1 < ImpExpr.eval env e2)
  | .and_ b1 b2 => eval env b1 && eval env b2
  | .or_ b1 b2 => eval env b1 || eval env b2
  | .not_ b => !(eval env b)

@[simp] theorem ImpBoolExpr.eval_lit (env : ImpEnv) (b : Bool) :
    ImpBoolExpr.eval env (.lit b) = b := rfl
@[simp] theorem ImpBoolExpr.eval_eq (env : ImpEnv) (e1 e2 : ImpExpr) :
    ImpBoolExpr.eval env (.eq_ e1 e2) = (ImpExpr.eval env e1 == ImpExpr.eval env e2) := rfl
@[simp] theorem ImpBoolExpr.eval_lt (env : ImpEnv) (e1 e2 : ImpExpr) :
    ImpBoolExpr.eval env (.lt_ e1 e2) = decide (ImpExpr.eval env e1 < ImpExpr.eval env e2) := rfl
@[simp] theorem ImpBoolExpr.eval_and (env : ImpEnv) (b1 b2 : ImpBoolExpr) :
    ImpBoolExpr.eval env (.and_ b1 b2) = (ImpBoolExpr.eval env b1 && ImpBoolExpr.eval env b2) := rfl
@[simp] theorem ImpBoolExpr.eval_or (env : ImpEnv) (b1 b2 : ImpBoolExpr) :
    ImpBoolExpr.eval env (.or_ b1 b2) = (ImpBoolExpr.eval env b1 || ImpBoolExpr.eval env b2) := rfl
@[simp] theorem ImpBoolExpr.eval_not (env : ImpEnv) (b : ImpBoolExpr) :
    ImpBoolExpr.eval env (.not_ b) = !(ImpBoolExpr.eval env b) := rfl

/-! ## Imperative Statement AST -/

/-- Imperative statements: the simplest Turing-complete fragment.
    Covers assignment, sequencing, conditional, and while loop.
    No store/load/for_/call/break_/continue_/return_ — those are Core IR only. -/
inductive ImpStmt where
  | skip   : ImpStmt
  | assign : VarId → ImpExpr → ImpStmt
  | seq    : ImpStmt → ImpStmt → ImpStmt
  | ite    : ImpBoolExpr → ImpStmt → ImpStmt → ImpStmt
  | while  : ImpBoolExpr → ImpStmt → ImpStmt
  deriving Repr, Inhabited

/-! ## Fuel-Based Evaluation -/

/-- Evaluate an imperative statement with fuel.
    Returns the updated environment on success, or none if fuel runs out.
    Fuel decreases only in while loops. Other constructs pass fuel through.
    Termination: lexicographic on (fuel, sizeOf s). -/
def ImpStmt.eval (fuel : Nat) (env : ImpEnv) (s : ImpStmt) : Option ImpEnv :=
  match s with
  | .skip => some env
  | .assign v e => some (env.update v (ImpExpr.eval env e))
  | .seq s1 s2 =>
    match eval fuel env s1 with
    | some env' => eval fuel env' s2
    | none => none
  | .ite c t e =>
    if ImpBoolExpr.eval env c then eval fuel env t else eval fuel env e
  | .while c body =>
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      if ImpBoolExpr.eval env c then
        match eval fuel' env body with
        | some env' => eval fuel' env' (.while c body)
        | none => none
      else some env
termination_by (fuel, sizeOf s)

@[simp] theorem ImpStmt.eval_skip (fuel : Nat) (env : ImpEnv) :
    ImpStmt.eval fuel env .skip = some env := by
  simp [ImpStmt.eval]

@[simp] theorem ImpStmt.eval_assign (fuel : Nat) (env : ImpEnv) (v : VarId) (e : ImpExpr) :
    ImpStmt.eval fuel env (.assign v e) = some (env.update v (ImpExpr.eval env e)) := by
  simp [ImpStmt.eval]

@[simp] theorem ImpStmt.eval_seq (fuel : Nat) (env : ImpEnv) (s1 s2 : ImpStmt) :
    ImpStmt.eval fuel env (.seq s1 s2) =
      match ImpStmt.eval fuel env s1 with
      | some env' => ImpStmt.eval fuel env' s2
      | none => none := by
  simp [ImpStmt.eval]

@[simp] theorem ImpStmt.eval_ite (fuel : Nat) (env : ImpEnv)
    (c : ImpBoolExpr) (t e : ImpStmt) :
    ImpStmt.eval fuel env (.ite c t e) =
      if ImpBoolExpr.eval env c then ImpStmt.eval fuel env t
      else ImpStmt.eval fuel env e := by
  simp [ImpStmt.eval]

@[simp] theorem ImpStmt.eval_while_zero (env : ImpEnv) (c : ImpBoolExpr) (body : ImpStmt) :
    ImpStmt.eval 0 env (.while c body) = none := by
  simp [ImpStmt.eval]

@[simp] theorem ImpStmt.eval_while_succ (fuel : Nat) (env : ImpEnv)
    (c : ImpBoolExpr) (body : ImpStmt) :
    ImpStmt.eval (fuel + 1) env (.while c body) =
      if ImpBoolExpr.eval env c then
        match ImpStmt.eval fuel env body with
        | some env' => ImpStmt.eval fuel env' (.while c body)
        | none => none
      else some env := by
  simp [ImpStmt.eval]

/-! ## Variable Naming -/

/-- Default variable naming for ImpStmt: "i0", "i1", etc. -/
def impVarNames : VarId → String := fun v => s!"i{v}"

end TrustLean
