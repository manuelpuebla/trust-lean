/-
  Trust-Lean — Verified Code Generation Framework
  Frontend/BoolExpr/Compile.lean: BoolExpr compilation to Core IR

  N3.1: Compilation via let-lifting. Binary operations (and, or) get fresh
  temps. Unary not gets a fresh temp. Literals and variables compile to skip.
-/

import TrustLean.Frontend.BoolExpr.Syntax
import TrustLean.Core.Stmt

set_option autoImplicit false

namespace TrustLean

/-! ## Compilation -/

/-- Compile a BoolExpr to Core IR statements.
    Returns (compiled statement, result expression, next available temp index).
    Uses let-lifting: each binary/unary op creates a fresh temporary. -/
def BoolExpr.compile (varNames : VarId → String) :
    BoolExpr → Nat → Stmt × LowLevelExpr × Nat
  | .lit b, next => (.skip, .litBool b, next)
  | .var v, next => (.skip, .varRef (.user (varNames v)), next)
  | .and_ e1 e2, next =>
    let (s1, r1, n1) := compile varNames e1 next
    let (s2, r2, n2) := compile varNames e2 n1
    (.seq s1 (.seq s2 (.assign (.temp n2) (.binOp .land r1 r2))),
     .varRef (.temp n2), n2 + 1)
  | .or_ e1 e2, next =>
    let (s1, r1, n1) := compile varNames e1 next
    let (s2, r2, n2) := compile varNames e2 n1
    (.seq s1 (.seq s2 (.assign (.temp n2) (.binOp .lor r1 r2))),
     .varRef (.temp n2), n2 + 1)
  | .not_ e, next =>
    let (s1, r1, n1) := compile varNames e next
    (.seq s1 (.assign (.temp n1) (.unaryOp .lnot r1)),
     .varRef (.temp n1), n1 + 1)

@[simp] theorem BoolExpr.compile_lit (vn : VarId → String) (b : Bool) (next : Nat) :
    BoolExpr.compile vn (.lit b) next = (.skip, .litBool b, next) := rfl

@[simp] theorem BoolExpr.compile_var (vn : VarId → String) (v : VarId) (next : Nat) :
    BoolExpr.compile vn (.var v) next = (.skip, .varRef (.user (vn v)), next) := rfl

/-! ## CodeGenerable Instance -/

/-- Convert BoolExpr compilation to StmtResult for the CodeGenerable interface. -/
def BoolExpr.toStmtResult (a : BoolExpr) (s : CodeGenState) : StmtResult :=
  let (stmt, resultVar, _) := BoolExpr.compile boolVarNames a s.nextVar
  { stmt, resultVar }

/-- BoolExpr is CodeGenerable: compiles boolean logic to Core IR. -/
instance : CodeGenerable BoolExpr where
  denote a env := .bool (BoolExpr.eval (fun v => (env v).getBool) a)
  lower := BoolExpr.toStmtResult
  varNames := boolVarNames

end TrustLean
