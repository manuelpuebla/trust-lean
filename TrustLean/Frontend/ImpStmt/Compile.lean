/-
  Trust-Lean — Verified Code Generation Framework
  Frontend/ImpStmt/Compile.lean: ImpStmt compilation to Core IR

  N3.2: Compilation is a direct structural translation — no let-lifting or
  temps needed. ImpExpr/ImpBoolExpr compile to LowLevelExpr,
  ImpStmt compiles to Stmt.
-/

import TrustLean.Frontend.ImpStmt.Syntax
import TrustLean.Core.Stmt

set_option autoImplicit false

namespace TrustLean

/-! ## Expression Compilation -/

/-- Compile an integer expression to a low-level expression.
    Direct translation: no temporaries needed. -/
def ImpExpr.compile (vn : VarId → String) : ImpExpr → LowLevelExpr
  | .lit n => .litInt n
  | .var v => .varRef (.user (vn v))
  | .add e1 e2 => .binOp .add (compile vn e1) (compile vn e2)
  | .mul e1 e2 => .binOp .mul (compile vn e1) (compile vn e2)

@[simp] theorem ImpExpr.compile_lit (vn : VarId → String) (n : Int) :
    ImpExpr.compile vn (.lit n) = .litInt n := rfl
@[simp] theorem ImpExpr.compile_var (vn : VarId → String) (v : VarId) :
    ImpExpr.compile vn (.var v) = .varRef (.user (vn v)) := rfl
@[simp] theorem ImpExpr.compile_add (vn : VarId → String) (e1 e2 : ImpExpr) :
    ImpExpr.compile vn (.add e1 e2) = .binOp .add (compile vn e1) (compile vn e2) := rfl
@[simp] theorem ImpExpr.compile_mul (vn : VarId → String) (e1 e2 : ImpExpr) :
    ImpExpr.compile vn (.mul e1 e2) = .binOp .mul (compile vn e1) (compile vn e2) := rfl

/-- Compile a boolean expression to a low-level expression.
    Comparisons use ImpExpr.compile for operands. -/
def ImpBoolExpr.compile (vn : VarId → String) : ImpBoolExpr → LowLevelExpr
  | .lit b => .litBool b
  | .eq_ e1 e2 => .binOp .eqOp (ImpExpr.compile vn e1) (ImpExpr.compile vn e2)
  | .lt_ e1 e2 => .binOp .ltOp (ImpExpr.compile vn e1) (ImpExpr.compile vn e2)
  | .and_ b1 b2 => .binOp .land (compile vn b1) (compile vn b2)
  | .or_ b1 b2 => .binOp .lor (compile vn b1) (compile vn b2)
  | .not_ b => .unaryOp .lnot (compile vn b)

@[simp] theorem ImpBoolExpr.compile_lit (vn : VarId → String) (b : Bool) :
    ImpBoolExpr.compile vn (.lit b) = .litBool b := rfl
@[simp] theorem ImpBoolExpr.compile_eq (vn : VarId → String) (e1 e2 : ImpExpr) :
    ImpBoolExpr.compile vn (.eq_ e1 e2) =
      .binOp .eqOp (ImpExpr.compile vn e1) (ImpExpr.compile vn e2) := rfl
@[simp] theorem ImpBoolExpr.compile_lt (vn : VarId → String) (e1 e2 : ImpExpr) :
    ImpBoolExpr.compile vn (.lt_ e1 e2) =
      .binOp .ltOp (ImpExpr.compile vn e1) (ImpExpr.compile vn e2) := rfl

/-! ## Statement Compilation -/

/-- Compile an imperative statement to a Core IR statement.
    Structural translation: assign→assign, seq→seq, ite→ite, while→while.
    No temps or let-lifting needed — all intermediate values stay in expressions. -/
def ImpStmt.compile (vn : VarId → String) : ImpStmt → Stmt
  | .skip => .skip
  | .assign v e => .assign (.user (vn v)) (ImpExpr.compile vn e)
  | .seq s1 s2 => .seq (compile vn s1) (compile vn s2)
  | .ite c t e => .ite (ImpBoolExpr.compile vn c) (compile vn t) (compile vn e)
  | .while c body => .while (ImpBoolExpr.compile vn c) (compile vn body)

@[simp] theorem ImpStmt.compile_skip (vn : VarId → String) :
    ImpStmt.compile vn .skip = .skip := rfl
@[simp] theorem ImpStmt.compile_assign (vn : VarId → String) (v : VarId) (e : ImpExpr) :
    ImpStmt.compile vn (.assign v e) = .assign (.user (vn v)) (ImpExpr.compile vn e) := rfl
@[simp] theorem ImpStmt.compile_seq (vn : VarId → String) (s1 s2 : ImpStmt) :
    ImpStmt.compile vn (.seq s1 s2) = .seq (compile vn s1) (compile vn s2) := rfl
@[simp] theorem ImpStmt.compile_ite (vn : VarId → String) (c : ImpBoolExpr) (t e : ImpStmt) :
    ImpStmt.compile vn (.ite c t e) = .ite (ImpBoolExpr.compile vn c) (compile vn t) (compile vn e) := rfl
@[simp] theorem ImpStmt.compile_while (vn : VarId → String) (c : ImpBoolExpr) (body : ImpStmt) :
    ImpStmt.compile vn (.while c body) = .while (ImpBoolExpr.compile vn c) (compile vn body) := rfl

end TrustLean
