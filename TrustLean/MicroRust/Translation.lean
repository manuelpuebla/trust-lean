/-
  Trust-Lean — Verified Code Generation Framework
  MicroRust/Translation.lean: Translation from Core IR (Stmt) to MicroRust AST

  N24.1 (v4.0.0): FUND — defines stmtToMicroRust and exprToMicroRust.
  Structural clone of MicroC/Translation.lean with varNameToRust replacing varNameToC.
  The AST types (MicroCExpr, MicroCStmt) are shared — only identifier sanitization changes.
-/

import TrustLean.MicroRust.Defs
import TrustLean.MicroC.AST

set_option autoImplicit false

namespace TrustLean

/-! ## Expression Translation -/

/-- Translate a Core LowLevelExpr to a MicroRust expression.
    Identical to exprToMicroC except for varNameToRust in varRef. -/
def exprToMicroRust : LowLevelExpr → MicroRustExpr
  | .litInt n => .litInt n
  | .litBool b => .litBool b
  | .varRef v => .varRef (varNameToRust v)
  | .binOp op e1 e2 => .binOp (binOpToMicroRust op) (exprToMicroRust e1) (exprToMicroRust e2)
  | .unaryOp op e => .unaryOp (unaryOpToMicroRust op) (exprToMicroRust e)
  | .powCall base n => .powCall (exprToMicroRust base) n

/-! ## exprToMicroRust @[simp] Equation Lemmas -/

@[simp] theorem exprToMicroRust_litInt (n : Int) :
    exprToMicroRust (.litInt n) = .litInt n := rfl

@[simp] theorem exprToMicroRust_litBool (b : Bool) :
    exprToMicroRust (.litBool b) = .litBool b := rfl

@[simp] theorem exprToMicroRust_varRef (v : VarName) :
    exprToMicroRust (.varRef v) = .varRef (varNameToRust v) := rfl

@[simp] theorem exprToMicroRust_binOp (op : BinOp) (e1 e2 : LowLevelExpr) :
    exprToMicroRust (.binOp op e1 e2) =
      .binOp (binOpToMicroRust op) (exprToMicroRust e1) (exprToMicroRust e2) := rfl

@[simp] theorem exprToMicroRust_unaryOp (op : UnaryOp) (e : LowLevelExpr) :
    exprToMicroRust (.unaryOp op e) =
      .unaryOp (unaryOpToMicroRust op) (exprToMicroRust e) := rfl

@[simp] theorem exprToMicroRust_powCall (base : LowLevelExpr) (n : Nat) :
    exprToMicroRust (.powCall base n) = .powCall (exprToMicroRust base) n := rfl

/-! ## Statement Translation -/

/-- Translate a Core Stmt to a MicroRust statement.
    for_ desugared to seq + while_ (same as MicroC).
    Only difference from MicroC: varNameToRust used for identifier mapping. -/
def stmtToMicroRust : Stmt → MicroRustStmt
  | .skip => .skip
  | .break_ => .break_
  | .continue_ => .continue_
  | .return_ re => .return_ (re.map exprToMicroRust)
  | .assign name expr => .assign (varNameToRust name) (exprToMicroRust expr)
  | .store base idx val => .store (exprToMicroRust base) (exprToMicroRust idx) (exprToMicroRust val)
  | .load var base idx => .load (varNameToRust var) (exprToMicroRust base) (exprToMicroRust idx)
  | .call result fname args => .call (varNameToRust result) fname (args.map exprToMicroRust)
  | .seq s1 s2 => .seq (stmtToMicroRust s1) (stmtToMicroRust s2)
  | .ite cond thenB elseB => .ite (exprToMicroRust cond) (stmtToMicroRust thenB) (stmtToMicroRust elseB)
  | .while cond body => .while_ (exprToMicroRust cond) (stmtToMicroRust body)
  | .for_ init cond step body =>
    .seq (stmtToMicroRust init) (.while_ (exprToMicroRust cond)
      (.seq (stmtToMicroRust body) (stmtToMicroRust step)))

/-! ## stmtToMicroRust @[simp] Equation Lemmas -/

@[simp] theorem stmtToMicroRust_skip : stmtToMicroRust .skip = .skip := rfl

@[simp] theorem stmtToMicroRust_break : stmtToMicroRust .break_ = .break_ := rfl

@[simp] theorem stmtToMicroRust_continue : stmtToMicroRust .continue_ = .continue_ := rfl

@[simp] theorem stmtToMicroRust_return (re : Option LowLevelExpr) :
    stmtToMicroRust (.return_ re) = .return_ (re.map exprToMicroRust) := rfl

@[simp] theorem stmtToMicroRust_assign (name : VarName) (expr : LowLevelExpr) :
    stmtToMicroRust (.assign name expr) =
      .assign (varNameToRust name) (exprToMicroRust expr) := rfl

@[simp] theorem stmtToMicroRust_store (base idx val : LowLevelExpr) :
    stmtToMicroRust (.store base idx val) =
      .store (exprToMicroRust base) (exprToMicroRust idx) (exprToMicroRust val) := rfl

@[simp] theorem stmtToMicroRust_load (var : VarName) (base idx : LowLevelExpr) :
    stmtToMicroRust (.load var base idx) =
      .load (varNameToRust var) (exprToMicroRust base) (exprToMicroRust idx) := rfl

@[simp] theorem stmtToMicroRust_call (result : VarName) (fname : String) (args : List LowLevelExpr) :
    stmtToMicroRust (.call result fname args) =
      .call (varNameToRust result) fname (args.map exprToMicroRust) := rfl

@[simp] theorem stmtToMicroRust_seq (s1 s2 : Stmt) :
    stmtToMicroRust (.seq s1 s2) =
      .seq (stmtToMicroRust s1) (stmtToMicroRust s2) := rfl

@[simp] theorem stmtToMicroRust_ite (cond : LowLevelExpr) (thenB elseB : Stmt) :
    stmtToMicroRust (.ite cond thenB elseB) =
      .ite (exprToMicroRust cond) (stmtToMicroRust thenB) (stmtToMicroRust elseB) := rfl

@[simp] theorem stmtToMicroRust_while (cond : LowLevelExpr) (body : Stmt) :
    stmtToMicroRust (.while cond body) =
      .while_ (exprToMicroRust cond) (stmtToMicroRust body) := rfl

@[simp] theorem stmtToMicroRust_for (init : Stmt) (cond : LowLevelExpr) (step body : Stmt) :
    stmtToMicroRust (.for_ init cond step body) =
      .seq (stmtToMicroRust init) (.while_ (exprToMicroRust cond)
        (.seq (stmtToMicroRust body) (stmtToMicroRust step))) := rfl

/-! ## Structural Properties -/

/-- for_ translation matches desugarFor pattern. -/
theorem stmtToMicroRust_for_eq_desugar (init : Stmt) (cond : LowLevelExpr) (step body : Stmt) :
    stmtToMicroRust (.for_ init cond step body) =
      stmtToMicroRust (Stmt.desugarFor init cond step body) := by
  simp [Stmt.desugarFor]

/-- stmtToMicroRust on skip produces MicroCStmt.skip. -/
theorem stmtToMicroRust_skip_identity : stmtToMicroRust .skip = .skip := rfl

end TrustLean
