/-
  Trust-Lean — Verified Code Generation Framework
  Tests/Integration.lean: End-to-end integration tests

  N5.1: HOJA — demonstrates the full pipeline:
  DSL source → CodeGenerable.lower → Stmt IR → BackendEmitter → C/Rust code.
  Uses #eval to show concrete output for each frontend × backend combination.
-/

import TrustLean.Pipeline
import TrustLean.Frontend.ArithExpr
import TrustLean.Frontend.BoolExpr
import TrustLean.Backend.CBackend
import TrustLean.Backend.RustBackend

set_option autoImplicit false

namespace TrustLean.Tests

/-! ## Test Expressions -/

/-- ArithExpr: (x + 3) * (y + 2), where x=var0, y=var1. -/
def arithExample : ArithExpr :=
  .mul (.add (.var 0) (.lit 3)) (.add (.var 1) (.lit 2))

/-- BoolExpr: (a && b) || (!a), where a=var0, b=var1. -/
def boolExample : BoolExpr :=
  .or_ (.and_ (.var 0) (.var 1)) (.not_ (.var 0))

/-! ## ArithExpr → C -/

#eval do
  let code := Pipeline.emit arithExample (default : CConfig) "compute"
    [("x", "int64_t"), ("y", "int64_t")]
  IO.println "=== ArithExpr → C ==="
  IO.println code

/-! ## ArithExpr → Rust -/

#eval do
  let code := Pipeline.emit arithExample (default : RustConfig) "compute"
    [("x", "i64"), ("y", "i64")]
  IO.println "=== ArithExpr → Rust ==="
  IO.println code

/-! ## BoolExpr → C -/

#eval do
  let code := Pipeline.emit boolExample (default : CConfig) "check"
    [("a", "int64_t"), ("b", "int64_t")]
  IO.println "=== BoolExpr → C ==="
  IO.println code

/-! ## BoolExpr → Rust -/

#eval do
  let code := Pipeline.emit boolExample (default : RustConfig) "check"
    [("a", "i64"), ("b", "i64")]
  IO.println "=== BoolExpr → Rust ==="
  IO.println code

/-! ## Pipeline.lower inspection -/

#eval do
  let sr := Pipeline.lower arithExample
  IO.println "=== ArithExpr → Core IR ==="
  IO.println s!"Stmt: {repr sr.stmt}"
  IO.println s!"Result: {repr sr.resultVar}"

#eval do
  let sr := Pipeline.lower boolExample
  IO.println "=== BoolExpr → Core IR ==="
  IO.println s!"Stmt: {repr sr.stmt}"
  IO.println s!"Result: {repr sr.resultVar}"

/-! ## Soundness instantiation check -/

/-- Verify that Pipeline.sound type-checks for ArithExpr.
    The fact that this compiles confirms ArithExpr has both
    CodeGenerable and CodeGenSound instances. -/
example : ∀ (a : ArithExpr) (env : VarId → Value) (llEnv : LowLevelEnv),
    CodeGenSound.wellTyped a env →
    (∀ (v : VarId), llEnv (.user (CodeGenerable.varNames (α := ArithExpr) v)) = env v) →
    ∃ (fuel : Nat) (resultEnv : LowLevelEnv),
      evalStmt fuel llEnv (Pipeline.lower a).stmt = some (.normal, resultEnv) ∧
      evalExpr resultEnv (Pipeline.lower a).resultVar = some (CodeGenerable.denote a env) ∧
      ∀ (v : VarId), resultEnv (.user (CodeGenerable.varNames (α := ArithExpr) v)) = env v :=
  fun a env llEnv hwt hb => Pipeline.sound a env llEnv hwt hb

/-- Same soundness instantiation for BoolExpr. -/
example : ∀ (a : BoolExpr) (env : VarId → Value) (llEnv : LowLevelEnv),
    CodeGenSound.wellTyped a env →
    (∀ (v : VarId), llEnv (.user (CodeGenerable.varNames (α := BoolExpr) v)) = env v) →
    ∃ (fuel : Nat) (resultEnv : LowLevelEnv),
      evalStmt fuel llEnv (Pipeline.lower a).stmt = some (.normal, resultEnv) ∧
      evalExpr resultEnv (Pipeline.lower a).resultVar = some (CodeGenerable.denote a env) ∧
      ∀ (v : VarId), resultEnv (.user (CodeGenerable.varNames (α := BoolExpr) v)) = env v :=
  fun a env llEnv hwt hb => Pipeline.sound a env llEnv hwt hb

end TrustLean.Tests
