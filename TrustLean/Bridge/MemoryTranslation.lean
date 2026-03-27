/-
  Trust-Lean — Verified Code Generation Framework
  Bridge/MemoryTranslation.lean: Memory operation translation + correctness

  N7.2: PAR — translates Gather → Stmt (loads) and Scatter → Stmt (stores),
  with correctness proofs. Uses explicit recursion on variable lists
  for clean induction. Addresses computed from IdxExpr + stride * offset.

  v1.1.0: Each load/store is fuel-independent (no loops).
-/

import TrustLean.Bridge.Types
import TrustLean.Bridge.Semantics
import TrustLean.Bridge.ExprTranslation
import TrustLean.Core.Eval
import TrustLean.Core.Foundation
import TrustLean.MicroC.Simulation

set_option autoImplicit false

namespace TrustLean.Bridge

/-! ## Address Expression Helper -/

/-- Build a LowLevelExpr for the address `evalIdxExpr(baseAddr) + stride * offset`.
    This is a compile-time expression: offset is a Nat literal, not a runtime variable. -/
def addrExpr (baseAddr : IdxExpr) (stride : Nat) (offset : Nat) : LowLevelExpr :=
  .binOp .add (idxExprToLLExpr baseAddr)
    (.binOp .mul (.litInt (Int.ofNat stride)) (.litInt (Int.ofNat offset)))

/-- The memory base expression: `.varRef (.user memArrayName)`.
    Used as the base argument for `.load` and `.store` statements. -/
def memBaseExpr : LowLevelExpr := .varRef (.user memArrayName)

@[simp] theorem getArrayName_memBaseExpr :
    getArrayName memBaseExpr = some memArrayName := rfl

/-! ## addrExpr Correctness -/

/-- addrExpr evaluates to the correct Int address under the loop bridge. -/
theorem addrExpr_correct
    (lEnv : LoopVar → Nat) (llEnv : LowLevelEnv)
    (hBridge : loopBridge lEnv llEnv)
    (baseAddr : IdxExpr) (stride offset : Nat) :
    evalExpr llEnv (addrExpr baseAddr stride offset) =
    some (.int (Int.ofNat (evalIdxExpr lEnv baseAddr + stride * offset))) := by
  simp [addrExpr, idxExprToLLExpr_correct lEnv llEnv hBridge baseAddr, evalBinOp]

/-! ## Gather Translation -/

/-- Translate gather to a sequence of load statements.
    For each variable v at position i in inputVars:
    `.load (scalarVarToVarName v) memBaseExpr (addrExpr g.baseAddr g.stride i)` -/
def gatherToStmt (inputVars : List ScalarVar) (g : Gather) : Stmt :=
  go inputVars 0
where
  go : List ScalarVar → Nat → Stmt
  | [], _ => .skip
  | v :: rest, i =>
    .seq (.load (scalarVarToVarName v) memBaseExpr (addrExpr g.baseAddr g.stride i))
         (go rest (i + 1))

/-! ## Scatter Translation -/

/-- Translate scatter to a sequence of store statements.
    For each variable v at position i in outputVars:
    `.store memBaseExpr (addrExpr s.baseAddr s.stride i) (.varRef (scalarVarToVarName v))` -/
def scatterToStmt (outputVars : List ScalarVar) (s : Scatter) : Stmt :=
  go outputVars 0
where
  go : List ScalarVar → Nat → Stmt
  | [], _ => .skip
  | v :: rest, i =>
    .seq (.store memBaseExpr (addrExpr s.baseAddr s.stride i)
                 (.varRef (scalarVarToVarName v)))
         (go rest (i + 1))

/-! ## @[simp] Lemmas -/

@[simp] theorem gatherToStmt_nil (g : Gather) :
    gatherToStmt [] g = .skip := rfl

@[simp] theorem scatterToStmt_nil (s : Scatter) :
    scatterToStmt [] s = .skip := rfl

/-! ## Single Load Correctness -/

/-- A single load from memory updates the target variable with the correct value. -/
theorem load_mem_correct
    (v : ScalarVar) (lEnv : LoopVar → Nat) (mem : Nat → Int)
    (llEnv : LowLevelEnv) (baseAddr : IdxExpr) (stride offset : Nat)
    (hLoop : loopBridge lEnv llEnv) (hMem : memBridge mem llEnv) (fuel : Nat) :
    evalStmt fuel llEnv
      (.load (scalarVarToVarName v) memBaseExpr (addrExpr baseAddr stride offset)) =
    some (.normal, llEnv.update (scalarVarToVarName v)
      (.int (mem (evalIdxExpr lEnv baseAddr + stride * offset)))) := by
  simp [evalStmt_load, getArrayName_memBaseExpr,
        addrExpr_correct lEnv llEnv hLoop baseAddr stride offset]
  congr 1
  exact hMem (evalIdxExpr lEnv baseAddr + stride * offset)

/-! ## Single Store Correctness -/

/-- A single store to memory updates the memory at the correct address. -/
theorem store_mem_correct
    (v : ScalarVar) (sEnv : ScalarVar → Int) (lEnv : LoopVar → Nat)
    (llEnv : LowLevelEnv) (baseAddr : IdxExpr) (stride offset : Nat)
    (hScalar : scalarBridge sEnv llEnv) (hLoop : loopBridge lEnv llEnv) (fuel : Nat) :
    evalStmt fuel llEnv
      (.store memBaseExpr (addrExpr baseAddr stride offset)
              (.varRef (scalarVarToVarName v))) =
    some (.normal, llEnv.update
      (.array memArrayName (Int.ofNat (evalIdxExpr lEnv baseAddr + stride * offset)))
      (.int (sEnv v))) := by
  simp [evalStmt_store, getArrayName_memBaseExpr,
        addrExpr_correct lEnv llEnv hLoop baseAddr stride offset, hScalar v]

/-! ## WellFormedArrayBases for gather/scatter (autopsy fix) -/

open TrustLean in
/-- memBaseExpr is well-formed (its name "mem" is already a valid C identifier). -/
theorem wellFormedBase_memBaseExpr : TrustLean.WellFormedBase memBaseExpr := by
  unfold TrustLean.WellFormedBase memBaseExpr memArrayName
  exact TrustLean.sanitizeIdentifier_mem

open TrustLean in
/-- gatherToStmt always produces well-formed array bases
    (all loads use memBaseExpr which is well-formed). -/
theorem gatherToStmt_wfArrayBases (vars : List ScalarVar) (g : Gather) :
    TrustLean.WellFormedArrayBases (gatherToStmt vars g) := by
  unfold gatherToStmt
  suffices h : ∀ n, TrustLean.WellFormedArrayBases (gatherToStmt.go g vars n) from h 0
  intro n; induction vars generalizing n with
  | nil => simp [gatherToStmt.go, TrustLean.WellFormedArrayBases]
  | cons v rest ih =>
    simp only [gatherToStmt.go, TrustLean.WellFormedArrayBases]
    exact ⟨wellFormedBase_memBaseExpr, ih (n + 1)⟩

open TrustLean in
/-- scatterToStmt always produces well-formed array bases
    (all stores use memBaseExpr which is well-formed). -/
theorem scatterToStmt_wfArrayBases (vars : List ScalarVar) (s : Scatter) :
    TrustLean.WellFormedArrayBases (scatterToStmt vars s) := by
  unfold scatterToStmt
  suffices h : ∀ n, TrustLean.WellFormedArrayBases (scatterToStmt.go s vars n) from h 0
  intro n; induction vars generalizing n with
  | nil => simp [scatterToStmt.go, TrustLean.WellFormedArrayBases]
  | cons v rest ih =>
    simp only [scatterToStmt.go, TrustLean.WellFormedArrayBases]
    exact ⟨wellFormedBase_memBaseExpr, ih (n + 1)⟩

end TrustLean.Bridge
