/-
  Trust-Lean — Verified Code Generation Framework
  Frontend/ArithExpr/Compile.lean: ArithExpr compilation to Core IR

  N2.2: Compilation via let-lifting. Each binary operation gets a fresh
  temporary variable. Literals and variables compile to skip + direct reference.
-/

import TrustLean.Frontend.ArithExpr.Syntax
import TrustLean.Core.Stmt

set_option autoImplicit false

namespace TrustLean

/-! ## Compilation -/

/-- Compile an ArithExpr to Core IR statements.
    Returns (compiled statement, result expression, next available temp index).
    Uses let-lifting: each binary op creates a fresh temporary. -/
def ArithExpr.compile (varNames : VarId → String) :
    ArithExpr → Nat → Stmt × LowLevelExpr × Nat
  | .lit n, next => (.skip, .litInt n, next)
  | .var v, next => (.skip, .varRef (.user (varNames v)), next)
  | .add e1 e2, next =>
    let (s1, r1, n1) := compile varNames e1 next
    let (s2, r2, n2) := compile varNames e2 n1
    (.seq s1 (.seq s2 (.assign (.temp n2) (.binOp .add r1 r2))),
     .varRef (.temp n2), n2 + 1)
  | .mul e1 e2, next =>
    let (s1, r1, n1) := compile varNames e1 next
    let (s2, r2, n2) := compile varNames e2 n1
    (.seq s1 (.seq s2 (.assign (.temp n2) (.binOp .mul r1 r2))),
     .varRef (.temp n2), n2 + 1)

@[simp] theorem ArithExpr.compile_lit (vn : VarId → String) (n : Int) (next : Nat) :
    ArithExpr.compile vn (.lit n) next = (.skip, .litInt n, next) := rfl

@[simp] theorem ArithExpr.compile_var (vn : VarId → String) (v : VarId) (next : Nat) :
    ArithExpr.compile vn (.var v) next = (.skip, .varRef (.user (vn v)), next) := rfl

/-! ## CodeGenerable Instance -/

/-- Convert ArithExpr compilation to StmtResult for the CodeGenerable interface. -/
def ArithExpr.toStmtResult (a : ArithExpr) (s : CodeGenState) : StmtResult :=
  let (stmt, resultVar, _) := ArithExpr.compile arithVarNames a s.nextVar
  { stmt, resultVar }

/-- ArithExpr is CodeGenerable: compiles integer arithmetic to Core IR. -/
instance : CodeGenerable ArithExpr where
  denote a env := .int (ArithExpr.eval (fun v => (env v).getInt) a)
  lower := ArithExpr.toStmtResult
  varNames := arithVarNames

end TrustLean
