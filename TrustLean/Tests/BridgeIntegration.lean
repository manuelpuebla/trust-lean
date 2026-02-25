/-
  Trust-Lean — Verified Code Generation Framework
  Tests/BridgeIntegration.lean: Bridge integration tests

  N8.2: HOJA — end-to-end integration tests for the amo-lean bridge.
  Tests all 6 ExpandedSigma constructors, verifies the correctness theorem
  instantiates, and ensures no regressions in v1.0.0 functionality.
-/

import TrustLean.Bridge
import TrustLean.Core.Eval
import TrustLean.Pipeline
import TrustLean.Frontend.ArithExpr
import TrustLean.Frontend.BoolExpr
import TrustLean.Backend.CBackend
import TrustLean.Backend.RustBackend

set_option autoImplicit false

namespace TrustLean.Tests.BridgeIntegration

open TrustLean.Bridge

/-! ## Test Programs: concrete ExpandedSigma instances -/

/-- Simple nop program: identity on all state. -/
def nopProg : ExpandedSigma := .nop

/-- Scalar kernel: reads mem[0], doubles it, writes to mem[1].
    inputVars = [⟨.input, 0⟩], outputVars = [⟨.output, 0⟩]
    body: output_0 := input_0 + input_0 -/
def doubleProg : ExpandedSigma :=
  .scalar
    { inputVars := [⟨.input, 0⟩]
      outputVars := [⟨.output, 0⟩]
      body := [{ target := ⟨.output, 0⟩
                 value := .add (.var ⟨.input, 0⟩) (.var ⟨.input, 0⟩) }] }
    { count := 1, baseAddr := .const 0, stride := 1 }   -- gather from mem[0]
    { count := 1, baseAddr := .const 1, stride := 1 }   -- scatter to mem[1]

/-- Seq program: two sequential nops. -/
def seqNopProg : ExpandedSigma := .seq .nop .nop

/-- Par program: two parallel nops (sequential in v1.1.0). -/
def parNopProg : ExpandedSigma := .par .nop .nop

/-- Loop program: loop 3 times with nop body. -/
def loopNopProg : ExpandedSigma := .loop 3 0 .nop

/-- Temp program: 2 temp variables, nop body. -/
def tempNopProg : ExpandedSigma := .temp 2 .nop

/-- Combined program: loop over a scalar kernel.
    Loop 4 times: read mem[i], double, write to mem[i+4].
    Uses loop variable 0 for indexing. -/
def loopDoubleProg : ExpandedSigma :=
  .loop 4 0
    (.scalar
      { inputVars := [⟨.input, 0⟩]
        outputVars := [⟨.output, 0⟩]
        body := [{ target := ⟨.output, 0⟩
                   value := .add (.var ⟨.input, 0⟩) (.var ⟨.input, 0⟩) }] }
      { count := 1, baseAddr := .affine 0 1 0, stride := 1 }    -- gather from mem[i]
      { count := 1, baseAddr := .affine 4 1 0, stride := 1 })   -- scatter to mem[i+4]

/-- Nested: temp + seq of scalar kernels.
    Demonstrates temp initialization and sequential composition. -/
def tempSeqProg : ExpandedSigma :=
  .temp 1
    (.seq
      (.scalar
        { inputVars := [⟨.input, 0⟩]
          outputVars := [⟨.temp, 0⟩]
          body := [{ target := ⟨.temp, 0⟩
                     value := .mul (.var ⟨.input, 0⟩) (.const 3) }] }
        { count := 1, baseAddr := .const 0, stride := 1 }
        { count := 1, baseAddr := .const 10, stride := 1 })
      (.scalar
        { inputVars := [⟨.temp, 0⟩]
          outputVars := [⟨.output, 0⟩]
          body := [{ target := ⟨.output, 0⟩
                     value := .add (.var ⟨.temp, 0⟩) (.const 1) }] }
        { count := 1, baseAddr := .const 10, stride := 1 }
        { count := 1, baseAddr := .const 1, stride := 1 }))

/-! ## Compilation Tests: ExpandedSigma → Stmt -/

#eval do
  IO.println "=== Nop → Stmt ==="
  IO.println s!"{repr (expandedSigmaToStmt nopProg)}"

#eval do
  IO.println "=== Double → Stmt ==="
  IO.println s!"{repr (expandedSigmaToStmt doubleProg)}"

#eval do
  IO.println "=== Loop(3, nop) → Stmt ==="
  IO.println s!"{repr (expandedSigmaToStmt loopNopProg)}"

#eval do
  IO.println "=== LoopDouble(4) → Stmt ==="
  IO.println s!"{repr (expandedSigmaToStmt loopDoubleProg)}"

#eval do
  IO.println "=== TempSeq → Stmt ==="
  IO.println s!"{repr (expandedSigmaToStmt tempSeqProg)}"

/-! ## Fuel Bound Tests -/

#eval do
  IO.println "=== Fuel Bounds ==="
  IO.println s!"nop:         {fuelBound nopProg}"
  IO.println s!"double:      {fuelBound doubleProg}"
  IO.println s!"seqNop:      {fuelBound seqNopProg}"
  IO.println s!"parNop:      {fuelBound parNopProg}"
  IO.println s!"loopNop(3):  {fuelBound loopNopProg}"
  IO.println s!"tempNop:     {fuelBound tempNopProg}"
  IO.println s!"loopDouble:  {fuelBound loopDoubleProg}"
  IO.println s!"tempSeq:     {fuelBound tempSeqProg}"

/-! ## Par = Seq Equivalence (P0 Property) -/

/-- `.par` compiles to same Stmt as `.seq`. -/
example (s1 s2 : ExpandedSigma) :
    expandedSigmaToStmt (.par s1 s2) = expandedSigmaToStmt (.seq s1 s2) := rfl

/-- `.par` semantics equal `.seq` semantics. -/
example (s1 s2 : ExpandedSigma) (env : SigmaEnv) :
    evalExpandedSigma (.par s1 s2) env = evalExpandedSigma (.seq s1 s2) env := rfl

/-- `.par` fuel bound equals `.seq` fuel bound. -/
example (s1 s2 : ExpandedSigma) :
    fuelBound (.par s1 s2) = fuelBound (.seq s1 s2) := rfl

/-! ## VarName Injection Tests -/

/-- scalarVarToVarName injective. -/
example (v1 v2 : ScalarVar)
    (h : scalarVarToVarName v1 = scalarVarToVarName v2) : v1 = v2 :=
  scalarVarToVarName_injective v1 v2 h

/-- loopVarToVarName injective. -/
example (v1 v2 : LoopVar)
    (h : loopVarToVarName v1 = loopVarToVarName v2) : v1 = v2 :=
  loopVarToVarName_injective v1 v2 h

/-- Scalar and loop VarNames are disjoint. -/
example (sv : ScalarVar) (lv : LoopVar) :
    scalarVarToVarName sv ≠ loopVarToVarName lv :=
  scalarVar_loopVar_disjoint sv lv

/-! ## Correctness Theorem Instantiation -/

/-- The correctness theorem type-checks for any well-formed ExpandedSigma.
    This is the capstone: any well-formed program, when compiled via
    expandedSigmaToStmt, preserves the fullBridge predicate. -/
example (sigma : ExpandedSigma) (hWF : wellFormed sigma)
    (state : SigmaEnv) (llEnv : LowLevelEnv)
    (hBridge : fullBridge state llEnv) :
    ∃ fuel llEnv',
      evalStmt fuel llEnv (expandedSigmaToStmt sigma) = some (.normal, llEnv') ∧
      fullBridge (evalExpandedSigma sigma state) llEnv' :=
  expandedSigmaToStmt_correct sigma hWF state llEnv hBridge

/-! ## wellFormed Tests -/

/-- nop is well-formed. -/
example : wellFormed nopProg := trivial

/-- seq of nops is well-formed. -/
example : wellFormed seqNopProg := ⟨trivial, trivial⟩

/-- par of nops is well-formed. -/
example : wellFormed parNopProg := ⟨trivial, trivial⟩

/-! ## Denotational Semantics Tests -/

/-- evalExpandedSigma .nop is identity. -/
example (env : SigmaEnv) : evalExpandedSigma .nop env = env := rfl

/-- evalExpandedSigma .seq with two nops is identity. -/
example (env : SigmaEnv) :
    evalExpandedSigma (.seq .nop .nop) env = env := rfl

/-- evalExpandedSigma .par with two nops is identity. -/
example (env : SigmaEnv) :
    evalExpandedSigma (.par .nop .nop) env = env := rfl

/-! ## v1.0.0 Regression: Pipeline still works -/

/-- ArithExpr pipeline soundness still type-checks. -/
example : ∀ (a : ArithExpr) (env : VarId → Value) (llEnv : LowLevelEnv),
    CodeGenSound.wellTyped a env →
    (∀ (v : VarId), llEnv (.user (CodeGenerable.varNames (α := ArithExpr) v)) = env v) →
    ∃ (fuel : Nat) (resultEnv : LowLevelEnv),
      evalStmt fuel llEnv (Pipeline.lower a).stmt = some (.normal, resultEnv) ∧
      evalExpr resultEnv (Pipeline.lower a).resultVar = some (CodeGenerable.denote a env) ∧
      ∀ (v : VarId), resultEnv (.user (CodeGenerable.varNames (α := ArithExpr) v)) = env v :=
  fun a env llEnv hwt hb => Pipeline.sound a env llEnv hwt hb

/-- BoolExpr pipeline soundness still type-checks. -/
example : ∀ (a : BoolExpr) (env : VarId → Value) (llEnv : LowLevelEnv),
    CodeGenSound.wellTyped a env →
    (∀ (v : VarId), llEnv (.user (CodeGenerable.varNames (α := BoolExpr) v)) = env v) →
    ∃ (fuel : Nat) (resultEnv : LowLevelEnv),
      evalStmt fuel llEnv (Pipeline.lower a).stmt = some (.normal, resultEnv) ∧
      evalExpr resultEnv (Pipeline.lower a).resultVar = some (CodeGenerable.denote a env) ∧
      ∀ (v : VarId), resultEnv (.user (CodeGenerable.varNames (α := BoolExpr) v)) = env v :=
  fun a env llEnv hwt hb => Pipeline.sound a env llEnv hwt hb

-- Pipeline.emit still works for ArithExpr → C.
#eval do
  let arithExample : ArithExpr := .mul (.add (.var 0) (.lit 3)) (.add (.var 1) (.lit 2))
  let code := Pipeline.emit arithExample (default : CConfig) "compute"
    [("x", "int64_t"), ("y", "int64_t")]
  IO.println "=== v1.0.0 Regression: ArithExpr → C ==="
  IO.println code

-- Pipeline.emit still works for BoolExpr → Rust.
#eval do
  let boolExample : BoolExpr := .or_ (.and_ (.var 0) (.var 1)) (.not_ (.var 0))
  let code := Pipeline.emit boolExample (default : RustConfig) "check"
    [("a", "i64"), ("b", "i64")]
  IO.println "=== v1.0.0 Regression: BoolExpr → Rust ==="
  IO.println code

end TrustLean.Tests.BridgeIntegration
