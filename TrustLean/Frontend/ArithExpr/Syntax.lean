/-
  Trust-Lean — Verified Code Generation Framework
  Frontend/ArithExpr/Syntax.lean: Arithmetic expression AST and semantics

  N2.2: CRITICO GATE — first frontend. Defines the source language
  for integer arithmetic expressions with denotational semantics.
-/

import TrustLean.Typeclass.CodeGenerable

set_option autoImplicit false

namespace TrustLean

/-! ## Arithmetic Expression AST -/

/-- Arithmetic expressions over integers.
    The simplest DSL: constants, variables, addition, multiplication. -/
inductive ArithExpr where
  | lit : Int → ArithExpr
  | var : VarId → ArithExpr
  | add : ArithExpr → ArithExpr → ArithExpr
  | mul : ArithExpr → ArithExpr → ArithExpr
  deriving Repr, Inhabited

/-! ## Denotational Semantics -/

/-- Pure integer evaluation of an arithmetic expression. -/
def ArithExpr.eval (env : VarId → Int) : ArithExpr → Int
  | .lit n => n
  | .var v => env v
  | .add e1 e2 => eval env e1 + eval env e2
  | .mul e1 e2 => eval env e1 * eval env e2

@[simp] theorem ArithExpr.eval_lit (env : VarId → Int) (n : Int) :
    ArithExpr.eval env (.lit n) = n := rfl

@[simp] theorem ArithExpr.eval_var (env : VarId → Int) (v : VarId) :
    ArithExpr.eval env (.var v) = env v := rfl

@[simp] theorem ArithExpr.eval_add (env : VarId → Int) (e1 e2 : ArithExpr) :
    ArithExpr.eval env (.add e1 e2) = eval env e1 + eval env e2 := rfl

@[simp] theorem ArithExpr.eval_mul (env : VarId → Int) (e1 e2 : ArithExpr) :
    ArithExpr.eval env (.mul e1 e2) = eval env e1 * eval env e2 := rfl

/-! ## Value Extraction Helper -/

/-- Extract integer from a Value, defaulting to 0 for booleans.
    Used by CodeGenerable.denote to bridge VarId → Value to VarId → Int. -/
def Value.getInt : Value → Int
  | .int n => n
  | .bool _ => 0

@[simp] theorem Value.getInt_int (n : Int) : (Value.int n).getInt = n := rfl

/-- A Value that is known to be .int equals .int of its getInt. -/
theorem Value.int_getInt {v : Value} (h : ∃ n, v = .int n) :
    v = .int v.getInt := by
  obtain ⟨n, rfl⟩ := h; rfl

/-! ## Variable Naming -/

/-- Default variable naming for ArithExpr: "v0", "v1", etc. -/
def arithVarNames : VarId → String := fun v => s!"v{v}"

end TrustLean
