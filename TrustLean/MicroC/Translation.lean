/-
  Trust-Lean — Verified Code Generation Framework
  MicroC/Translation.lean: Translation from Core IR (Stmt) to MicroC AST

  N11.1 (v2.0.0): CRITICO — defines stmtToMicroC and exprToMicroC.
  Converts Core IR types to MicroC types, using varNameToC for identifier
  conversion (same mapping as CBackend).

  Design decisions:
  - exprToMicroC : LowLevelExpr → MicroCExpr (structural, no fuel)
  - stmtToMicroC : Stmt → MicroCStmt (structural, no fuel)
  - for_ desugared to seq + while_ (matching CBackend.stmtToC behavior)
  - call translated structurally (both sides return none anyway)
  - Uses varNameToC from CBackend for identifier conversion
-/

import TrustLean.MicroC.AST
import TrustLean.Backend.CBackend

set_option autoImplicit false

namespace TrustLean

/-! ## Expression Translation -/

/-- Translate a Core LowLevelExpr to a MicroCExpr.
    Structural recursion, no fuel needed. -/
def exprToMicroC : LowLevelExpr → MicroCExpr
  | .litInt n => .litInt n
  | .litBool b => .litBool b
  | .varRef v => .varRef (varNameToC v)
  | .binOp op e1 e2 => .binOp (binOpToMicroC op) (exprToMicroC e1) (exprToMicroC e2)
  | .unaryOp op e => .unaryOp (unaryOpToMicroC op) (exprToMicroC e)
  | .powCall base n => .powCall (exprToMicroC base) n

/-! ## exprToMicroC @[simp] Equation Lemmas -/

@[simp] theorem exprToMicroC_litInt (n : Int) :
    exprToMicroC (.litInt n) = .litInt n := rfl

@[simp] theorem exprToMicroC_litBool (b : Bool) :
    exprToMicroC (.litBool b) = .litBool b := rfl

@[simp] theorem exprToMicroC_varRef (v : VarName) :
    exprToMicroC (.varRef v) = .varRef (varNameToC v) := rfl

@[simp] theorem exprToMicroC_binOp (op : BinOp) (e1 e2 : LowLevelExpr) :
    exprToMicroC (.binOp op e1 e2) =
      .binOp (binOpToMicroC op) (exprToMicroC e1) (exprToMicroC e2) := rfl

@[simp] theorem exprToMicroC_unaryOp (op : UnaryOp) (e : LowLevelExpr) :
    exprToMicroC (.unaryOp op e) =
      .unaryOp (unaryOpToMicroC op) (exprToMicroC e) := rfl

@[simp] theorem exprToMicroC_powCall (base : LowLevelExpr) (n : Nat) :
    exprToMicroC (.powCall base n) = .powCall (exprToMicroC base) n := rfl

/-! ## Statement Translation -/

/-- Translate a Core Stmt to a MicroCStmt.
    Key: for_ is desugared to seq + while_ (matching CBackend behavior).
    Structural recursion, no fuel needed. -/
def stmtToMicroC : Stmt → MicroCStmt
  | .skip => .skip
  | .break_ => .break_
  | .continue_ => .continue_
  | .return_ re => .return_ (re.map exprToMicroC)
  | .assign name expr => .assign (varNameToC name) (exprToMicroC expr)
  | .store base idx val => .store (exprToMicroC base) (exprToMicroC idx) (exprToMicroC val)
  | .load var base idx => .load (varNameToC var) (exprToMicroC base) (exprToMicroC idx)
  | .call result fname args => .call (varNameToC result) fname (args.map exprToMicroC)
  | .seq s1 s2 => .seq (stmtToMicroC s1) (stmtToMicroC s2)
  | .ite cond thenB elseB => .ite (exprToMicroC cond) (stmtToMicroC thenB) (stmtToMicroC elseB)
  | .while cond body => .while_ (exprToMicroC cond) (stmtToMicroC body)
  | .for_ init cond step body =>
    .seq (stmtToMicroC init) (.while_ (exprToMicroC cond)
      (.seq (stmtToMicroC body) (stmtToMicroC step)))

/-! ## stmtToMicroC @[simp] Equation Lemmas -/

@[simp] theorem stmtToMicroC_skip : stmtToMicroC .skip = .skip := rfl

@[simp] theorem stmtToMicroC_break : stmtToMicroC .break_ = .break_ := rfl

@[simp] theorem stmtToMicroC_continue : stmtToMicroC .continue_ = .continue_ := rfl

@[simp] theorem stmtToMicroC_return (re : Option LowLevelExpr) :
    stmtToMicroC (.return_ re) = .return_ (re.map exprToMicroC) := rfl

@[simp] theorem stmtToMicroC_assign (name : VarName) (expr : LowLevelExpr) :
    stmtToMicroC (.assign name expr) =
      .assign (varNameToC name) (exprToMicroC expr) := rfl

@[simp] theorem stmtToMicroC_store (base idx val : LowLevelExpr) :
    stmtToMicroC (.store base idx val) =
      .store (exprToMicroC base) (exprToMicroC idx) (exprToMicroC val) := rfl

@[simp] theorem stmtToMicroC_load (var : VarName) (base idx : LowLevelExpr) :
    stmtToMicroC (.load var base idx) =
      .load (varNameToC var) (exprToMicroC base) (exprToMicroC idx) := rfl

@[simp] theorem stmtToMicroC_call (result : VarName) (fname : String) (args : List LowLevelExpr) :
    stmtToMicroC (.call result fname args) =
      .call (varNameToC result) fname (args.map exprToMicroC) := rfl

@[simp] theorem stmtToMicroC_seq (s1 s2 : Stmt) :
    stmtToMicroC (.seq s1 s2) =
      .seq (stmtToMicroC s1) (stmtToMicroC s2) := rfl

@[simp] theorem stmtToMicroC_ite (cond : LowLevelExpr) (thenB elseB : Stmt) :
    stmtToMicroC (.ite cond thenB elseB) =
      .ite (exprToMicroC cond) (stmtToMicroC thenB) (stmtToMicroC elseB) := rfl

@[simp] theorem stmtToMicroC_while (cond : LowLevelExpr) (body : Stmt) :
    stmtToMicroC (.while cond body) =
      .while_ (exprToMicroC cond) (stmtToMicroC body) := rfl

@[simp] theorem stmtToMicroC_for (init : Stmt) (cond : LowLevelExpr) (step body : Stmt) :
    stmtToMicroC (.for_ init cond step body) =
      .seq (stmtToMicroC init) (.while_ (exprToMicroC cond)
        (.seq (stmtToMicroC body) (stmtToMicroC step))) := rfl

/-! ## Structural Properties -/

/-- for_ translation matches desugarFor pattern. -/
theorem stmtToMicroC_for_eq_desugar (init : Stmt) (cond : LowLevelExpr) (step body : Stmt) :
    stmtToMicroC (.for_ init cond step body) =
      stmtToMicroC (Stmt.desugarFor init cond step body) := by
  simp [Stmt.desugarFor]

/-- stmtToMicroC on skip produces MicroCStmt.skip. -/
theorem stmtToMicroC_skip_identity : stmtToMicroC .skip = .skip := rfl

end TrustLean
