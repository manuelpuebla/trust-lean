/-
  Trust-Lean — Verified Code Generation Framework
  Bridge/ScalarTranslation.lean: Scalar assignment/block translation + correctness

  N7.1: PAR — translates ScalarAssign → Stmt and ScalarBlock → Stmt,
  with correctness proofs preserving the three-part bridge.
  Uses explicit recursion (not foldl) for clean induction.

  v1.1.0: Each assign is fuel-independent (no loops).
-/

import TrustLean.Bridge.Types
import TrustLean.Bridge.Semantics
import TrustLean.Bridge.ExprTranslation
import TrustLean.Core.Eval

set_option autoImplicit false

namespace TrustLean.Bridge

/-! ## Scalar Assignment Translation -/

/-- Translate a scalar assignment to a Stmt.
    `target := value` → `.assign (scalarVarToVarName target) (scalarExprToLLExpr value)` -/
def scalarAssignToStmt (a : ScalarAssign) : Stmt :=
  .assign (scalarVarToVarName a.target) (scalarExprToLLExpr a.value)

/-- Translate a scalar block to a Stmt via explicit recursion.
    `[]` → `.skip`, `a :: rest` → `.seq (translate a) (translate rest)` -/
def scalarBlockToStmt : ScalarBlock → Stmt
  | [] => .skip
  | a :: rest => .seq (scalarAssignToStmt a) (scalarBlockToStmt rest)

/-! ## @[simp] Lemmas -/

@[simp] theorem scalarAssignToStmt_def (a : ScalarAssign) :
    scalarAssignToStmt a =
    .assign (scalarVarToVarName a.target) (scalarExprToLLExpr a.value) := rfl

@[simp] theorem scalarBlockToStmt_nil :
    scalarBlockToStmt [] = .skip := rfl

@[simp] theorem scalarBlockToStmt_cons (a : ScalarAssign) (rest : ScalarBlock) :
    scalarBlockToStmt (a :: rest) =
    .seq (scalarAssignToStmt a) (scalarBlockToStmt rest) := rfl

/-! ## Single Assignment Correctness -/

/-- scalarAssignToStmt evaluates to a normal result with the target variable updated. -/
theorem scalarAssignToStmt_eval
    (a : ScalarAssign) (sEnv : ScalarVar → Int) (llEnv : LowLevelEnv)
    (hBridge : scalarBridge sEnv llEnv) (fuel : Nat) :
    evalStmt fuel llEnv (scalarAssignToStmt a) =
    some (.normal, llEnv.update (scalarVarToVarName a.target)
                                (.int (evalScalarExpr sEnv a.value))) := by
  simp [scalarAssignToStmt, evalStmt_assign,
        scalarExprToLLExpr_correct sEnv llEnv hBridge a.value]

/-! ## Single Assignment Bridge Preservation -/

/-- After a scalar assignment, the scalar bridge holds for the updated environments. -/
theorem scalarAssignToStmt_scalarBridge
    (a : ScalarAssign) (sEnv : ScalarVar → Int) (llEnv : LowLevelEnv)
    (hBridge : scalarBridge sEnv llEnv) :
    scalarBridge (evalScalarAssign a sEnv)
      (llEnv.update (scalarVarToVarName a.target) (.int (evalScalarExpr sEnv a.value))) := by
  intro v
  simp only [evalScalarAssign]
  by_cases hv : v = a.target
  · subst hv
    simp [LowLevelEnv.update_same]
  · rw [if_neg hv]
    exact scalarBridge_update_other sEnv llEnv v a.target
      (.int (evalScalarExpr sEnv a.value)) (Ne.symm hv) (hBridge v)

/-! ## Block Correctness (with full bridge preservation) -/

/-- scalarBlockToStmt is correct: executing the translated block produces a result
    that satisfies the scalar, loop, and memory bridges with the source-level
    evaluation of the block. -/
theorem scalarBlockToStmt_correct
    (block : ScalarBlock) (sEnv : ScalarVar → Int) (llEnv : LowLevelEnv)
    (lEnv : LoopVar → Nat) (mem : Nat → Int)
    (hScalar : scalarBridge sEnv llEnv)
    (hLoop : loopBridge lEnv llEnv)
    (hMem : memBridge mem llEnv) (fuel : Nat) :
    ∃ llEnv',
      evalStmt fuel llEnv (scalarBlockToStmt block) = some (.normal, llEnv') ∧
      scalarBridge (evalScalarBlock block sEnv) llEnv' ∧
      loopBridge lEnv llEnv' ∧
      memBridge mem llEnv' := by
  induction block generalizing sEnv llEnv with
  | nil =>
    exact ⟨llEnv, by simp [evalStmt_skip], hScalar, hLoop, hMem⟩
  | cons a rest ih =>
    simp only [scalarBlockToStmt_cons, evalStmt_seq, evalScalarBlock_cons]
    rw [scalarAssignToStmt_eval a sEnv llEnv hScalar fuel]
    simp only []
    let llEnv_mid := llEnv.update (scalarVarToVarName a.target)
                                  (.int (evalScalarExpr sEnv a.value))
    have hScalar' := scalarAssignToStmt_scalarBridge a sEnv llEnv hScalar
    have hLoop' := loopBridge_update_scalar lEnv llEnv a.target
                     (.int (evalScalarExpr sEnv a.value)) hLoop
    have hMem' := memBridge_update_scalar mem llEnv a.target
                    (.int (evalScalarExpr sEnv a.value)) hMem
    exact ih (evalScalarAssign a sEnv) llEnv_mid hScalar' hLoop' hMem'

end TrustLean.Bridge
