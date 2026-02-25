/-
  Trust-Lean — Verified Code Generation Framework
  Frontend/BoolExpr/Correctness.lean: CodeGenSound proof for BoolExpr

  N3.1: PAR — second CodeGenSound instance.
  Proves that BoolExpr compilation preserves boolean logic semantics.
-/

import TrustLean.Frontend.BoolExpr.Compile
import TrustLean.Core.Foundation
import TrustLean.Typeclass.CodeGenSound
import Mathlib.Tactic.Set

set_option autoImplicit false

namespace TrustLean

/-! ## Counter Monotonicity -/

/-- The temp counter never decreases during compilation. -/
theorem BoolExpr.compile_mono (vn : VarId → String) (a : BoolExpr) (next : Nat) :
    next ≤ (BoolExpr.compile vn a next).2.2 := by
  induction a generalizing next with
  | lit _ => exact Nat.le_refl _
  | var _ => exact Nat.le_refl _
  | and_ e1 e2 ih1 ih2 =>
    show next ≤ (compile vn e2 (compile vn e1 next).2.2).2.2 + 1
    exact Nat.le_succ_of_le (Nat.le_trans (ih1 next) (ih2 _))
  | or_ e1 e2 ih1 ih2 =>
    show next ≤ (compile vn e2 (compile vn e1 next).2.2).2.2 + 1
    exact Nat.le_succ_of_le (Nat.le_trans (ih1 next) (ih2 _))
  | not_ e ih =>
    show next ≤ (compile vn e next).2.2 + 1
    exact Nat.le_succ_of_le (ih next)

/-! ## Result Stability -/

/-- The result of compiling is stable under environment changes to temps
    outside the compilation's range. -/
private theorem BoolExpr.compile_result_eval_stable
    (vn : VarId → String) (a : BoolExpr) (boolEnv : VarId → Bool)
    (next : Nat) (env1 env2 : LowLevelEnv)
    (hresult1 : evalExpr env1 (compile vn a next).2.1 = some (.bool (BoolExpr.eval boolEnv a)))
    (hbridge1 : ∀ (v : VarId), env1 (.user (vn v)) = .bool (boolEnv v))
    (hbridge2 : ∀ (v : VarId), env2 (.user (vn v)) = .bool (boolEnv v))
    (hframe : ∀ (k : Nat), k < (compile vn a next).2.2 →
      env2 (.temp k) = env1 (.temp k)) :
    evalExpr env2 (compile vn a next).2.1 = some (.bool (BoolExpr.eval boolEnv a)) := by
  induction a generalizing next env1 env2 with
  | lit b => simp [compile] at hresult1 ⊢
  | var v => simp [compile] at hresult1 ⊢; exact hbridge2 v
  | and_ e1 e2 _ _ =>
    simp only [compile] at hresult1 ⊢
    simp only [evalExpr] at hresult1 ⊢
    rw [hframe _ (by exact Nat.lt_succ_of_le (Nat.le_refl _))]
    exact hresult1
  | or_ e1 e2 _ _ =>
    simp only [compile] at hresult1 ⊢
    simp only [evalExpr] at hresult1 ⊢
    rw [hframe _ (by exact Nat.lt_succ_of_le (Nat.le_refl _))]
    exact hresult1
  | not_ e _ =>
    simp only [compile] at hresult1 ⊢
    simp only [evalExpr] at hresult1 ⊢
    rw [hframe _ (by exact Nat.lt_succ_of_le (Nat.le_refl _))]
    exact hresult1

/-! ## Main Correctness Theorem -/

/-- BoolExpr compilation preserves semantics.
    Five-part result (same structure as ArithExpr):
    1. evalStmt terminates normally (fuel 0 suffices)
    2. Result expression evaluates to the correct boolean
    3. User variables are preserved (bridge maintained)
    4. Low temps are preserved (frame property)
    5. Counter is monotone -/
theorem BoolExpr.compile_correct
    (a : BoolExpr) (boolEnv : VarId → Bool) (next : Nat) (llEnv : LowLevelEnv)
    (hbridge : ∀ (v : VarId), llEnv (.user (boolVarNames v)) = .bool (boolEnv v)) :
    ∃ (resultEnv : LowLevelEnv),
      evalStmt 0 llEnv (compile boolVarNames a next).1 =
        some (.normal, resultEnv) ∧
      evalExpr resultEnv (compile boolVarNames a next).2.1 =
        some (.bool (eval boolEnv a)) ∧
      (∀ (v : VarId), resultEnv (.user (boolVarNames v)) = .bool (boolEnv v)) ∧
      (∀ (k : Nat), k < next → resultEnv (.temp k) = llEnv (.temp k)) ∧
      next ≤ (compile boolVarNames a next).2.2 := by
  induction a generalizing next llEnv with
  | lit b =>
    exact ⟨llEnv, by simp [compile, evalStmt_skip], by simp [compile],
      hbridge, fun _ _ => rfl, Nat.le_refl _⟩
  | var v =>
    refine ⟨llEnv, by simp [compile, evalStmt_skip], ?_, hbridge,
      fun _ _ => rfl, Nat.le_refl _⟩
    simp [compile, hbridge]
  | and_ e1 e2 ih1 ih2 =>
    obtain ⟨env1, heval1, hresult1, hbridge1, hframe1, hmono1⟩ :=
      ih1 next llEnv hbridge
    obtain ⟨env2, heval2, hresult2, hbridge2, hframe2, hmono2⟩ :=
      ih2 (compile boolVarNames e1 next).2.2 env1 hbridge1
    have hstable : evalExpr env2 (compile boolVarNames e1 next).2.1 =
        some (.bool (eval boolEnv e1)) :=
      compile_result_eval_stable boolVarNames e1 boolEnv next env1 env2
        hresult1 hbridge1 hbridge2 hframe2
    set n2 := (compile boolVarNames e2 (compile boolVarNames e1 next).2.2).2.2
    refine ⟨env2.update (.temp n2)
              (.bool (eval boolEnv e1 && eval boolEnv e2)),
            ?_, ?_, ?_, ?_, ?_⟩
    · -- 1. evalStmt terminates normally
      show evalStmt 0 llEnv (compile boolVarNames (.and_ e1 e2) next).1 = _
      simp only [compile, evalStmt_seq, heval1, heval2,
        evalStmt_assign, evalExpr_binOp, hstable, hresult2, evalBinOp_land]; rfl
    · -- 2. Result correct
      simp only [compile, evalExpr]
      exact congrArg some (LowLevelEnv.update_same _ _ _)
    · -- 3. Bridge preserved
      intro v
      exact LowLevelEnv.update_other env2 (.temp n2) (.user (boolVarNames v))
        _ VarName.user_ne_temp ▸ hbridge2 v
    · -- 4. Frame: low temps preserved
      intro k hk
      have hne : (.temp k : VarName) ≠ .temp n2 := by
        intro h; cases h; exact Nat.not_lt.mpr
          (Nat.le_trans hmono1 hmono2) hk
      rw [LowLevelEnv.update_other _ _ _ _ hne,
        hframe2 k (Nat.lt_of_lt_of_le hk hmono1),
        hframe1 k hk]
    · -- 5. Monotone
      show next ≤ (compile boolVarNames (.and_ e1 e2) next).2.2
      simp only [compile]
      exact Nat.le_succ_of_le (Nat.le_trans hmono1 hmono2)
  | or_ e1 e2 ih1 ih2 =>
    obtain ⟨env1, heval1, hresult1, hbridge1, hframe1, hmono1⟩ :=
      ih1 next llEnv hbridge
    obtain ⟨env2, heval2, hresult2, hbridge2, hframe2, hmono2⟩ :=
      ih2 (compile boolVarNames e1 next).2.2 env1 hbridge1
    have hstable : evalExpr env2 (compile boolVarNames e1 next).2.1 =
        some (.bool (eval boolEnv e1)) :=
      compile_result_eval_stable boolVarNames e1 boolEnv next env1 env2
        hresult1 hbridge1 hbridge2 hframe2
    set n2 := (compile boolVarNames e2 (compile boolVarNames e1 next).2.2).2.2
    refine ⟨env2.update (.temp n2)
              (.bool (eval boolEnv e1 || eval boolEnv e2)),
            ?_, ?_, ?_, ?_, ?_⟩
    · show evalStmt 0 llEnv (compile boolVarNames (.or_ e1 e2) next).1 = _
      simp only [compile, evalStmt_seq, heval1, heval2,
        evalStmt_assign, evalExpr_binOp, hstable, hresult2, evalBinOp_lor]; rfl
    · simp only [compile, evalExpr]
      exact congrArg some (LowLevelEnv.update_same _ _ _)
    · intro v
      exact LowLevelEnv.update_other env2 (.temp n2) (.user (boolVarNames v))
        _ VarName.user_ne_temp ▸ hbridge2 v
    · intro k hk
      have hne : (.temp k : VarName) ≠ .temp n2 := by
        intro h; cases h; exact Nat.not_lt.mpr
          (Nat.le_trans hmono1 hmono2) hk
      rw [LowLevelEnv.update_other _ _ _ _ hne,
        hframe2 k (Nat.lt_of_lt_of_le hk hmono1),
        hframe1 k hk]
    · show next ≤ (compile boolVarNames (.or_ e1 e2) next).2.2
      simp only [compile]
      exact Nat.le_succ_of_le (Nat.le_trans hmono1 hmono2)
  | not_ e ih =>
    obtain ⟨env1, heval1, hresult1, hbridge1, hframe1, hmono1⟩ :=
      ih next llEnv hbridge
    set n1 := (compile boolVarNames e next).2.2
    refine ⟨env1.update (.temp n1)
              (.bool (!(eval boolEnv e))),
            ?_, ?_, ?_, ?_, ?_⟩
    · -- 1. evalStmt terminates normally
      show evalStmt 0 llEnv (compile boolVarNames (.not_ e) next).1 = _
      simp only [compile, evalStmt_seq, heval1,
        evalStmt_assign, evalExpr_unaryOp, hresult1, evalUnaryOp_lnot]; rfl
    · -- 2. Result correct
      simp only [compile, evalExpr]
      exact congrArg some (LowLevelEnv.update_same _ _ _)
    · -- 3. Bridge preserved
      intro v
      exact LowLevelEnv.update_other env1 (.temp n1) (.user (boolVarNames v))
        _ VarName.user_ne_temp ▸ hbridge1 v
    · -- 4. Frame: low temps preserved
      intro k hk
      have hne : (.temp k : VarName) ≠ .temp n1 := by
        intro h; cases h; exact Nat.not_lt.mpr hmono1 hk
      rw [LowLevelEnv.update_other _ _ _ _ hne,
        hframe1 k hk]
    · -- 5. Monotone
      show next ≤ (compile boolVarNames (.not_ e) next).2.2
      simp only [compile]
      exact Nat.le_succ_of_le hmono1

/-! ## CodeGenSound Instance -/

/-- BoolExpr is CodeGenSound: compilation preserves boolean logic semantics.
    Well-typedness: all source variables must be booleans. -/
instance : CodeGenSound BoolExpr where
  wellTyped _ env := ∀ (v : VarId), ∃ (b : Bool), env v = .bool b
  lower_correct := by
    intro a env llEnv hwt hbridge
    have hb : ∀ (v : VarId), llEnv (.user (boolVarNames v)) = env v := hbridge
    have hbridge_bool : ∀ (v : VarId),
        llEnv (.user (boolVarNames v)) = .bool ((env v).getBool) := by
      intro v; exact (hb v).trans (Value.bool_getBool (hwt v))
    simp only [CodeGenerable.lower, CodeGenerable.denote, CodeGenerable.varNames,
      BoolExpr.toStmtResult]
    obtain ⟨resultEnv, heval, hresult, hbridge', _, _⟩ :=
      BoolExpr.compile_correct a (fun v => (env v).getBool) 0 llEnv hbridge_bool
    exact ⟨0, resultEnv, heval, hresult, fun v => by
      rw [hbridge' v]; exact (Value.bool_getBool (hwt v)).symm⟩

end TrustLean
