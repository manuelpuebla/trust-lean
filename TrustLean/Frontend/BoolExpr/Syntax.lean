/-
  Trust-Lean — Verified Code Generation Framework
  Frontend/BoolExpr/Syntax.lean: Boolean expression AST and semantics

  N3.1: PAR — boolean expressions frontend.
  Defines BoolExpr with denotational semantics.
-/

import TrustLean.Typeclass.CodeGenerable

set_option autoImplicit false

namespace TrustLean

/-! ## Boolean Expression AST -/

/-- Boolean expressions over booleans.
    Supports literals, variables, conjunction, disjunction, and negation. -/
inductive BoolExpr where
  | lit  : Bool → BoolExpr
  | var  : VarId → BoolExpr
  | and_ : BoolExpr → BoolExpr → BoolExpr
  | or_  : BoolExpr → BoolExpr → BoolExpr
  | not_ : BoolExpr → BoolExpr
  deriving Repr, Inhabited

/-! ## Denotational Semantics -/

/-- Pure boolean evaluation of a boolean expression. -/
def BoolExpr.eval (env : VarId → Bool) : BoolExpr → Bool
  | .lit b => b
  | .var v => env v
  | .and_ e1 e2 => eval env e1 && eval env e2
  | .or_ e1 e2 => eval env e1 || eval env e2
  | .not_ e => !(eval env e)

@[simp] theorem BoolExpr.eval_lit (env : VarId → Bool) (b : Bool) :
    BoolExpr.eval env (.lit b) = b := rfl

@[simp] theorem BoolExpr.eval_var (env : VarId → Bool) (v : VarId) :
    BoolExpr.eval env (.var v) = env v := rfl

@[simp] theorem BoolExpr.eval_and (env : VarId → Bool) (e1 e2 : BoolExpr) :
    BoolExpr.eval env (.and_ e1 e2) = (eval env e1 && eval env e2) := rfl

@[simp] theorem BoolExpr.eval_or (env : VarId → Bool) (e1 e2 : BoolExpr) :
    BoolExpr.eval env (.or_ e1 e2) = (eval env e1 || eval env e2) := rfl

@[simp] theorem BoolExpr.eval_not (env : VarId → Bool) (e : BoolExpr) :
    BoolExpr.eval env (.not_ e) = !(eval env e) := rfl

/-! ## Value Extraction Helper -/

/-- Extract Bool from a Value, defaulting to false for integers. -/
def Value.getBool : Value → Bool
  | .bool b => b
  | .int _ => false

@[simp] theorem Value.getBool_bool (b : Bool) : (Value.bool b).getBool = b := rfl

/-- A Value that is known to be .bool equals .bool of its getBool. -/
theorem Value.bool_getBool {v : Value} (h : ∃ b, v = .bool b) :
    v = .bool v.getBool := by
  obtain ⟨b, rfl⟩ := h; rfl

/-! ## Variable Naming -/

/-- Default variable naming for BoolExpr: "b0", "b1", etc. -/
def boolVarNames : VarId → String := fun v => s!"b{v}"

end TrustLean
