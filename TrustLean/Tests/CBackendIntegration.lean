/-
  Trust-Lean — Verified Code Generation Framework
  Tests/CBackendIntegration.lean: CBackend v1.2.0 integration tests

  N9.4 (v1.2.0): End-to-end testing of upgraded CBackend.
  Tests Pipeline.emit, bridge programs, sanitization, regression.
-/

import TrustLean.Pipeline
import TrustLean.Frontend.ArithExpr
import TrustLean.Frontend.BoolExpr
import TrustLean.Backend.CBackend
import TrustLean.Backend.RustBackend
import TrustLean.Bridge

set_option autoImplicit false

namespace TrustLean.Tests.CBackendV12

open TrustLean.Bridge

/-! ## TC-9.4.1: ArithExpr to C -/

#eval Pipeline.emit
  (ArithExpr.mul (.add (.var 0) (.lit 3)) (.add (.var 1) (.lit 2)))
  (default : CConfig) "compute" [("x", "int64_t"), ("y", "int64_t")]

/-! ## TC-9.4.2: BoolExpr to C -/

#eval Pipeline.emit
  (BoolExpr.or_ (.and_ (.var 0) (.var 1)) (.not_ (.var 0)))
  (default : CConfig) "check" [("a", "int64_t"), ("b", "int64_t")]

/-! ## TC-9.4.3: Bridge nop to C -/

#eval stmtToC 0 (expandedSigmaToStmt .nop)

/-! ## TC-9.4.4: Bridge double to C -/

private def doubleProg' : ExpandedSigma :=
  .scalar
    { inputVars := [⟨.input, 0⟩], outputVars := [⟨.output, 0⟩]
      body := [{ target := ⟨.output, 0⟩
                 value := .add (.var ⟨.input, 0⟩) (.var ⟨.input, 0⟩) }] }
    { count := 1, baseAddr := .const 0, stride := 1 }
    { count := 1, baseAddr := .const 1, stride := 1 }

#eval stmtToC 0 (expandedSigmaToStmt doubleProg')

/-! ## TC-9.4.5: Bridge loop to C -/

private def loopDoubleProg' : ExpandedSigma :=
  .loop 4 0
    (.scalar
      { inputVars := [⟨.input, 0⟩], outputVars := [⟨.output, 0⟩]
        body := [{ target := ⟨.output, 0⟩
                   value := .add (.var ⟨.input, 0⟩) (.var ⟨.input, 0⟩) }] }
      { count := 1, baseAddr := .affine 0 1 0, stride := 1 }
      { count := 1, baseAddr := .affine 4 1 0, stride := 1 })

#eval stmtToC 0 (expandedSigmaToStmt loopDoubleProg')

/-! ## TC-9.4.6: Bridge tempSeq to C -/

private def tempSeqProg' : ExpandedSigma :=
  .temp 1
    (.seq
      (.scalar
        { inputVars := [⟨.input, 0⟩], outputVars := [⟨.temp, 0⟩]
          body := [{ target := ⟨.temp, 0⟩
                     value := .mul (.var ⟨.input, 0⟩) (.const 3) }] }
        { count := 1, baseAddr := .const 0, stride := 1 }
        { count := 1, baseAddr := .const 10, stride := 1 })
      (.scalar
        { inputVars := [⟨.temp, 0⟩], outputVars := [⟨.output, 0⟩]
          body := [{ target := ⟨.output, 0⟩
                     value := .add (.var ⟨.temp, 0⟩) (.const 1) }] }
        { count := 1, baseAddr := .const 10, stride := 1 }
        { count := 1, baseAddr := .const 1, stride := 1 }))

#eval stmtToC 0 (expandedSigmaToStmt tempSeqProg')

/-! ## TC-9.4.7: All 6 ExpandedSigma constructors -/

#eval stmtToC 0 (expandedSigmaToStmt (.seq .nop .nop))
#eval stmtToC 0 (expandedSigmaToStmt (.par .nop .nop))
#eval stmtToC 0 (expandedSigmaToStmt (.loop 3 0 .nop))
#eval stmtToC 0 (expandedSigmaToStmt (.temp 2 .nop))

/-! ## TC-9.4.8: Empty parameter list -/

#eval Pipeline.emit (ArithExpr.lit 42) (default : CConfig) "constant" []

/-! ## TC-9.4.9: Keyword parameter names -/

#eval generateCFunction (default : CConfig) "compute"
  [("int", "int64_t"), ("for", "int64_t"), ("while", "int64_t")] .skip (.litInt 0)

/-! ## TC-9.4.10: Deep nesting -/

private def deepArith : ArithExpr :=
  List.foldl (fun acc _ => .add acc (.lit 1)) (.lit 0) (List.replicate 10 ())

#eval Pipeline.emit deepArith (default : CConfig) "deep" [("x", "int64_t")]

/-! ## Stress Tests -/

-- ST-9.4.3: All VarName variants
#eval exprToC (.varRef (.user "x"))
#eval exprToC (.varRef (.temp 5))
#eval exprToC (.varRef (.array "mem" 3))

-- ST-9.4.4: long long config
#eval Pipeline.emit (ArithExpr.lit 42)
  (CConfig.mk false true) "test_ll" [("x", "long long")]

-- ST-9.4.5: no power helper
#eval generateCHeader (CConfig.mk true false)

/-! ## Edge Cases -/

-- EC-9.4.1: Just skip
#eval generateCFunction (default : CConfig) "empty" [] .skip (.litInt 0)

-- EC-9.4.2: break outside loop
#eval stmtToC 0 .break_

-- EC-9.4.3: nested return in ite in while
#eval stmtToC 0
  (.while (.litBool true)
    (.ite (.varRef (.user "x")) (.return_ (some (.litInt 0))) .skip))

-- EC-9.4.4-5: VarName.array through varNameToC
#eval varNameToC (.array "mem" 0)
#eval varNameToC (.array "I" 5)

/-! ## Regression Tests -/

-- REG-9.4.1: Pipeline.sound for ArithExpr still type-checks
example : ∀ (a : ArithExpr) (env : VarId → Value) (llEnv : LowLevelEnv),
    CodeGenSound.wellTyped a env →
    (∀ v, llEnv (.user (CodeGenerable.varNames (α := ArithExpr) v)) = env v) →
    ∃ (fuel : Nat) (resultEnv : LowLevelEnv),
      evalStmt fuel llEnv (Pipeline.lower a).stmt = some (.normal, resultEnv) ∧
      evalExpr resultEnv (Pipeline.lower a).resultVar = some (CodeGenerable.denote a env) ∧
      ∀ v, resultEnv (.user (CodeGenerable.varNames (α := ArithExpr) v)) = env v :=
  fun a env llEnv hwt hb => Pipeline.sound a env llEnv hwt hb

-- REG-9.4.2: Pipeline.sound for BoolExpr still type-checks
example : ∀ (a : BoolExpr) (env : VarId → Value) (llEnv : LowLevelEnv),
    CodeGenSound.wellTyped a env →
    (∀ v, llEnv (.user (CodeGenerable.varNames (α := BoolExpr) v)) = env v) →
    ∃ (fuel : Nat) (resultEnv : LowLevelEnv),
      evalStmt fuel llEnv (Pipeline.lower a).stmt = some (.normal, resultEnv) ∧
      evalExpr resultEnv (Pipeline.lower a).resultVar = some (CodeGenerable.denote a env) ∧
      ∀ v, resultEnv (.user (CodeGenerable.varNames (α := BoolExpr) v)) = env v :=
  fun a env llEnv hwt hb => Pipeline.sound a env llEnv hwt hb

-- REG-9.4.5: expandedSigmaToStmt_correct still type-checks
example := @expandedSigmaToStmt_correct

-- REG-9.4.7: BackendEmitter CConfig instance resolves
example : BackendEmitter CConfig := inferInstance

-- REG-9.4.8: BackendEmitter RustConfig instance resolves
example : BackendEmitter RustConfig := inferInstance

end TrustLean.Tests.CBackendV12
