/-
  Trust-Lean — Verified Code Generation Framework
  Bridge/Compile.lean: Main bridge function ExpandedSigma → Stmt

  N7.3: CRIT — the main compilation function that translates all 6
  ExpandedSigma constructors to Trust-Lean Core IR (Stmt).
  Composes scalar, memory, and expression translations from N6.2, N7.1, N7.2.

  v1.1.0: `.par` compiles identically to `.seq` (sequential semantics).
  Variable names are deterministic from the ExpandedSigma structure —
  no CodeGenState needed for v1.1.0.
-/

import TrustLean.Bridge.ScalarTranslation
import TrustLean.Bridge.MemoryTranslation
import TrustLean.Core.Foundation

set_option autoImplicit false

namespace TrustLean.Bridge

/-! ## Temp Variable Initialization -/

/-- Generate a Stmt that initializes temp scalar variables 0..size-1 to 0.
    Produces `.assign (scalarVarToVarName ⟨.temp, i⟩) (.litInt 0)` for each i. -/
def initTempsToStmt : Nat → Nat → Stmt
  | 0, _ => .skip
  | n + 1, startIdx =>
    .seq (.assign (scalarVarToVarName ⟨.temp, startIdx⟩) (.litInt 0))
         (initTempsToStmt n (startIdx + 1))

@[simp] theorem initTempsToStmt_zero (start : Nat) :
    initTempsToStmt 0 start = .skip := rfl

/-! ## Loop Translation Helper -/

/-- The VarName for a loop variable. -/
def loopCounterVar (lv : LoopVar) : VarName := loopVarToVarName lv

/-- Build the loop condition: loop_var < n. -/
def loopCondExpr (lv : LoopVar) (n : Nat) : LowLevelExpr :=
  .binOp .ltOp (.varRef (loopCounterVar lv)) (.litInt (Int.ofNat n))

/-- Build the loop step: loop_var := loop_var + 1. -/
def loopStepStmt (lv : LoopVar) : Stmt :=
  .assign (loopCounterVar lv)
    (.binOp .add (.varRef (loopCounterVar lv)) (.litInt 1))

/-! ## Main Bridge Function -/

/-- Translate an ExpandedSigma to a Stmt.
    Handles all 6 constructors:
    - `.scalar k g s`: gather → kernel body → scatter
    - `.loop n lv body`: init counter → while (counter < n) { body; counter++ }
    - `.seq s1 s2`: `.seq (compile s1) (compile s2)`
    - `.par s1 s2`: identical to `.seq` (v1.1.0 sequential semantics)
    - `.temp size body`: init temps to 0 → compile body
    - `.nop`: `.skip` -/
def expandedSigmaToStmt : ExpandedSigma → Stmt
  | .scalar k g s =>
    .seq (gatherToStmt k.inputVars g)
      (.seq (scalarBlockToStmt k.body)
            (scatterToStmt k.outputVars s))
  | .loop n lv body =>
    .seq (.assign (loopCounterVar lv) (.litInt 0))
         (.while (loopCondExpr lv n)
                 (.seq (expandedSigmaToStmt body) (loopStepStmt lv)))
  | .seq s1 s2 =>
    .seq (expandedSigmaToStmt s1) (expandedSigmaToStmt s2)
  | .par s1 s2 =>
    .seq (expandedSigmaToStmt s1) (expandedSigmaToStmt s2)
  | .temp size body =>
    .seq (initTempsToStmt size 0) (expandedSigmaToStmt body)
  | .nop => .skip

/-! ## @[simp] Lemmas -/

@[simp] theorem expandedSigmaToStmt_nop :
    expandedSigmaToStmt .nop = .skip := rfl

@[simp] theorem expandedSigmaToStmt_seq (s1 s2 : ExpandedSigma) :
    expandedSigmaToStmt (.seq s1 s2) =
    .seq (expandedSigmaToStmt s1) (expandedSigmaToStmt s2) := rfl

@[simp] theorem expandedSigmaToStmt_par (s1 s2 : ExpandedSigma) :
    expandedSigmaToStmt (.par s1 s2) =
    .seq (expandedSigmaToStmt s1) (expandedSigmaToStmt s2) := rfl

/-- `.par` compiles identically to `.seq` (v1.1.0 sequential semantics). -/
theorem expandedSigmaToStmt_par_eq_seq (s1 s2 : ExpandedSigma) :
    expandedSigmaToStmt (.par s1 s2) = expandedSigmaToStmt (.seq s1 s2) := rfl

@[simp] theorem expandedSigmaToStmt_scalar (k : ExpandedKernel) (g : Gather) (s : Scatter) :
    expandedSigmaToStmt (.scalar k g s) =
    .seq (gatherToStmt k.inputVars g)
      (.seq (scalarBlockToStmt k.body) (scatterToStmt k.outputVars s)) := rfl

@[simp] theorem expandedSigmaToStmt_loop (n : Nat) (lv : LoopVar) (body : ExpandedSigma) :
    expandedSigmaToStmt (.loop n lv body) =
    .seq (.assign (loopCounterVar lv) (.litInt 0))
         (.while (loopCondExpr lv n)
                 (.seq (expandedSigmaToStmt body) (loopStepStmt lv))) := rfl

@[simp] theorem expandedSigmaToStmt_temp (size : Nat) (body : ExpandedSigma) :
    expandedSigmaToStmt (.temp size body) =
    .seq (initTempsToStmt size 0) (expandedSigmaToStmt body) := rfl

/-! ## Fuel Bound -/

/-- Compute a fuel bound sufficient for evaluating the compiled Stmt.
    For loops: fuel ≥ n + 1 (n iterations + termination check).
    For seq/par: max of sub-bounds (fuel composition via max).
    For scalar/temp/nop: 0 (no loops, no fuel consumption). -/
def fuelBound : ExpandedSigma → Nat
  | .scalar _ _ _ => 0
  | .loop n _ body => n + 1 + n * (fuelBound body + 1)
  | .seq s1 s2 => Nat.max (fuelBound s1) (fuelBound s2)
  | .par s1 s2 => Nat.max (fuelBound s1) (fuelBound s2)
  | .temp _ body => fuelBound body
  | .nop => 0

@[simp] theorem fuelBound_nop : fuelBound .nop = 0 := rfl
@[simp] theorem fuelBound_scalar (k : ExpandedKernel) (g : Gather) (s : Scatter) :
    fuelBound (.scalar k g s) = 0 := rfl

/-- fuelBound for .par equals fuelBound for .seq. -/
theorem fuelBound_par_eq_seq (s1 s2 : ExpandedSigma) :
    fuelBound (.par s1 s2) = fuelBound (.seq s1 s2) := rfl

end TrustLean.Bridge
