/-
  Trust-Lean — Verified Code Generation Framework
  MicroC/Integration.lean: End-to-End Pipeline Integration (v2.0.0)

  N13.1 + N13.2: Operator compatibility proofs, pipeline wiring,
  non-vacuity witnesses, and oracle tests.

  Key results:
  - binOp_compat / unaryOp_compat: operator string compatibility
  - Pipeline #eval tests: stmtToMicroC → microCToString → parseMicroC roundtrip
  - Non-vacuity: stmtToMicroC_correct hypotheses are jointly satisfiable
-/

import TrustLean.MicroC.Simulation
import TrustLean.MicroC.Roundtrip

set_option autoImplicit false

namespace TrustLean

/-! ## N13.1: Operator Compatibility

    Operator string representations match between CBackend and MicroC:
    microCBinOpToString (binOpToMicroC op) = binOpToC op
    microCUnaryOpToString (unaryOpToMicroC op) = unaryOpToC op -/

/-- Binary operator strings are compatible across CBackend and MicroC. -/
theorem binOp_compat (op : BinOp) :
    microCBinOpToString (binOpToMicroC op) = binOpToC op := by
  cases op <;> rfl

/-- Unary operator strings are compatible across CBackend and MicroC. -/
theorem unaryOp_compat (op : UnaryOp) :
    microCUnaryOpToString (unaryOpToMicroC op) = unaryOpToC op := by
  cases op <;> rfl

/-! ## N13.1: Operator Roundtrip Compatibility

    BinOp/UnaryOp translation is invertible:
    binOpToMicroC is injective (already in AST) and compat with printing. -/

/-- binOpToMicroC is injective (no two BinOps map to the same MicroCBinOp). -/
theorem binOpToMicroC_compat_injective (op1 op2 : BinOp)
    (h : binOpToMicroC op1 = binOpToMicroC op2) : op1 = op2 :=
  binOpToMicroC_injective h

/-- unaryOpToMicroC is injective. -/
theorem unaryOpToMicroC_compat_injective (op1 op2 : UnaryOp)
    (h : unaryOpToMicroC op1 = unaryOpToMicroC op2) : op1 = op2 :=
  unaryOpToMicroC_injective h

/-! ## N13.1: Translation Structural Properties

    stmtToMicroC preserves all structural constructors. -/

/-- for_ desugaring matches between CBackend (stmtToC) and MicroC (stmtToMicroC). -/
theorem for_desugar_compat (init : Stmt) (cond : LowLevelExpr) (step body : Stmt) :
    stmtToMicroC (.for_ init cond step body) =
      .seq (stmtToMicroC init) (.while_ (exprToMicroC cond)
        (.seq (stmtToMicroC body) (stmtToMicroC step))) := rfl

/-! ## N13.2: Non-Vacuity Witnesses

    Demonstrate that gate theorem hypotheses are jointly satisfiable. -/

/-- Non-vacuity for stmtToMicroC_correct: skip case.
    Shows the theorem's conclusion holds concretely.
    VarNameInjective is a runtime invariant (varNameToC is not universally injective
    because sanitizeIdentifier maps "int" and "tl_int" both to "tl_int").
    We demonstrate the conclusion directly via concrete evaluation. -/
example : ∃ mcEnv',
    evalMicroC 1 MicroCEnv.default (stmtToMicroC Stmt.skip) = some (.normal, mcEnv')
    ∧ microCBridge LowLevelEnv.default mcEnv' :=
  ⟨MicroCEnv.default, by unfold stmtToMicroC evalMicroC; rfl, microCBridge_default⟩

/-- Non-vacuity: microCBridge holds for default environments. -/
example : microCBridge LowLevelEnv.default MicroCEnv.default :=
  microCBridge_default

/-- Non-vacuity: evalMicroC_fuel_mono conclusion is satisfiable.
    Concrete: skip at fuel 1 produces (.normal, env), and monotonicity
    guarantees the same at any fuel ≥ 1. -/
example : ∀ fuel' : Nat, fuel' ≥ 1 →
    evalMicroC fuel' MicroCEnv.default MicroCStmt.skip = some (.normal, MicroCEnv.default) := by
  intro fuel' hle
  exact evalMicroC_fuel_mono (fuel := 1) (by unfold evalMicroC; rfl) hle

/-- Non-vacuity: WellFormedArrayBases is satisfiable on nontrivial programs. -/
example : WellFormedArrayBases
    (.seq (.assign (.user "x") (.litInt 42))
          (.ite (.binOp .ltOp (.varRef (.user "x")) (.litInt 100))
                (.assign (.user "y") (.litInt 1))
                (.assign (.user "y") (.litInt 0)))) := by
  constructor
  · trivial
  · constructor <;> trivial

/-- Non-vacuity: evalStmt returns Some for concrete programs.
    This is the heval hypothesis of stmtToMicroC_correct. -/
example : evalStmt 1 LowLevelEnv.default Stmt.skip = some (.normal, LowLevelEnv.default) := by
  unfold evalStmt; rfl

/-- Non-vacuity: Outcome.normal ≠ .outOfFuel (the hoc hypothesis). -/
example : Outcome.normal ≠ .outOfFuel := by decide

end TrustLean

/-! ## N13.1 + N13.2: End-to-End Pipeline #eval Tests

    Demonstrate the full pipeline: Core Stmt → stmtToMicroC → microCToString → parseMicroC
    and verify the MicroC roundtrip works end-to-end. -/

open TrustLean in
/-- Pipeline test helper: translate, print, parse, verify roundtrip. -/
def pipelineTest (label : String) (stmt : TrustLean.Stmt) : String :=
  let mc := TrustLean.stmtToMicroC stmt
  let s := TrustLean.microCToString mc
  let parsed := TrustLean.parseMicroC s
  if parsed == some mc then label ++ ": OK" else label ++ ": FAIL"

open TrustLean in
#eval pipelineTest "assign"
  (.assign (.user "x") (.litInt 42))

open TrustLean in
#eval pipelineTest "ite"
  (.ite (.binOp .ltOp (.varRef (.user "x")) (.litInt 10))
        (.assign (.user "y") (.litInt 1))
        (.assign (.user "y") (.litInt 0)))

open TrustLean in
#eval pipelineTest "while"
  (.while (.binOp .ltOp (.varRef (.user "i")) (.litInt 10))
          (.assign (.user "i") (.binOp .add (.varRef (.user "i")) (.litInt 1))))

open TrustLean in
#eval pipelineTest "for_desugar"
  (.for_ (.assign (.user "i") (.litInt 0))
         (.binOp .ltOp (.varRef (.user "i")) (.litInt 10))
         (.assign (.user "i") (.binOp .add (.varRef (.user "i")) (.litInt 1)))
         (.assign (.user "sum") (.binOp .add (.varRef (.user "sum")) (.varRef (.user "i")))))

open TrustLean in
#eval pipelineTest "seq"
  (.seq (.assign (.user "x") (.litInt 1))
        (.seq (.assign (.user "y") (.litInt 2))
              (.assign (.user "z") (.binOp .add (.varRef (.user "x")) (.varRef (.user "y"))))))

open TrustLean in
#eval pipelineTest "break_continue"
  (.while (.litBool true)
    (.ite (.binOp .eqOp (.varRef (.user "x")) (.litInt 0))
      .break_
      (.seq (.assign (.user "x") (.binOp .sub (.varRef (.user "x")) (.litInt 1)))
            .continue_)))

open TrustLean in
#eval pipelineTest "return"
  (.return_ (some (.binOp .add (.varRef (.user "x")) (.litInt 1))))

open TrustLean in
#eval pipelineTest "store_load"
  (.seq (.store (.varRef (.user "arr")) (.litInt 0) (.litInt 42))
        (.load (.user "x") (.varRef (.user "arr")) (.litInt 0)))

open TrustLean in
#eval pipelineTest "call"
  (.call (.user "result") "compute" [.varRef (.user "a"), .litInt 5])

open TrustLean in
#eval pipelineTest "complex"
  (.seq (.assign (.user "sum") (.litInt 0))
        (.seq (.assign (.user "i") (.litInt 0))
              (.while (.binOp .ltOp (.varRef (.user "i")) (.litInt 100))
                (.seq (.assign (.user "sum") (.binOp .add (.varRef (.user "sum")) (.varRef (.user "i"))))
                      (.assign (.user "i") (.binOp .add (.varRef (.user "i")) (.litInt 1)))))))
