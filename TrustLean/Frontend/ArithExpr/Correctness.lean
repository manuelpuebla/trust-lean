/-
  Trust-Lean — Verified Code Generation Framework
  Frontend/ArithExpr/Correctness.lean: CodeGenSound proof for ArithExpr

  N2.2: CRITICO GATE — first CodeGenSound instance.
  Proves that ArithExpr compilation preserves integer arithmetic semantics.
-/

import TrustLean.Frontend.ArithExpr.Compile
import TrustLean.Core.Foundation
import TrustLean.Typeclass.CodeGenSound
import Mathlib.Tactic.Set

set_option autoImplicit false

namespace TrustLean

/-! ## Counter Monotonicity -/

/-- The temp counter never decreases during compilation. -/
theorem ArithExpr.compile_mono (vn : VarId → String) (a : ArithExpr) (next : Nat) :
    next ≤ (ArithExpr.compile vn a next).2.2 := by
  induction a generalizing next with
  | lit _ => exact Nat.le_refl _
  | var _ => exact Nat.le_refl _
  | add e1 e2 ih1 ih2 =>
    show next ≤ (compile vn e2 (compile vn e1 next).2.2).2.2 + 1
    exact Nat.le_succ_of_le (Nat.le_trans (ih1 next) (ih2 _))
  | mul e1 e2 ih1 ih2 =>
    show next ≤ (compile vn e2 (compile vn e1 next).2.2).2.2 + 1
    exact Nat.le_succ_of_le (Nat.le_trans (ih1 next) (ih2 _))

/-! ## Result Stability -/

/-- The result of compiling is stable under environment changes to temps
    outside the compilation's range. Used for sequential correctness. -/
private theorem ArithExpr.compile_result_eval_stable
    (vn : VarId → String) (a : ArithExpr) (intEnv : VarId → Int)
    (next : Nat) (env1 env2 : LowLevelEnv)
    (hresult1 : evalExpr env1 (compile vn a next).2.1 = some (.int (ArithExpr.eval intEnv a)))
    (hbridge1 : ∀ (v : VarId), env1 (.user (vn v)) = .int (intEnv v))
    (hbridge2 : ∀ (v : VarId), env2 (.user (vn v)) = .int (intEnv v))
    (hframe : ∀ (k : Nat), k < (compile vn a next).2.2 →
      env2 (.temp k) = env1 (.temp k)) :
    evalExpr env2 (compile vn a next).2.1 = some (.int (ArithExpr.eval intEnv a)) := by
  induction a generalizing next env1 env2 with
  | lit n => simp [compile] at hresult1 ⊢
  | var v => simp [compile] at hresult1 ⊢; exact hbridge2 v
  | add e1 e2 _ _ =>
    simp only [compile] at hresult1 ⊢
    simp only [evalExpr] at hresult1 ⊢
    rw [hframe _ (by exact Nat.lt_succ_of_le (Nat.le_refl _))]
    exact hresult1
  | mul e1 e2 _ _ =>
    simp only [compile] at hresult1 ⊢
    simp only [evalExpr] at hresult1 ⊢
    rw [hframe _ (by exact Nat.lt_succ_of_le (Nat.le_refl _))]
    exact hresult1

/-! ## Main Correctness Theorem -/

/-- ArithExpr compilation preserves semantics.
    Five-part result:
    1. evalStmt terminates normally (fuel 0 suffices — no loops)
    2. Result expression evaluates to the correct integer
    3. User variables are preserved (bridge maintained)
    4. Low temps are preserved (frame property)
    5. Counter is monotone -/
theorem ArithExpr.compile_correct
    (a : ArithExpr) (intEnv : VarId → Int) (next : Nat) (llEnv : LowLevelEnv)
    (hbridge : ∀ (v : VarId), llEnv (.user (arithVarNames v)) = .int (intEnv v)) :
    ∃ (resultEnv : LowLevelEnv),
      evalStmt 0 llEnv (compile arithVarNames a next).1 =
        some (.normal, resultEnv) ∧
      evalExpr resultEnv (compile arithVarNames a next).2.1 =
        some (.int (eval intEnv a)) ∧
      (∀ (v : VarId), resultEnv (.user (arithVarNames v)) = .int (intEnv v)) ∧
      (∀ (k : Nat), k < next → resultEnv (.temp k) = llEnv (.temp k)) ∧
      next ≤ (compile arithVarNames a next).2.2 := by
  induction a generalizing next llEnv with
  | lit n =>
    exact ⟨llEnv, by simp [compile, evalStmt_skip], by simp [compile],
      hbridge, fun _ _ => rfl, Nat.le_refl _⟩
  | var v =>
    refine ⟨llEnv, by simp [compile, evalStmt_skip], ?_, hbridge,
      fun _ _ => rfl, Nat.le_refl _⟩
    simp [compile, hbridge]
  | add e1 e2 ih1 ih2 =>
    -- IH for e1
    obtain ⟨env1, heval1, hresult1, hbridge1, hframe1, hmono1⟩ :=
      ih1 next llEnv hbridge
    -- IH for e2 (starts from env1, counter n1)
    obtain ⟨env2, heval2, hresult2, hbridge2, hframe2, hmono2⟩ :=
      ih2 (compile arithVarNames e1 next).2.2 env1 hbridge1
    -- Stability: r1 still evaluates correctly in env2
    have hstable : evalExpr env2 (compile arithVarNames e1 next).2.1 =
        some (.int (eval intEnv e1)) :=
      compile_result_eval_stable arithVarNames e1 intEnv next env1 env2
        hresult1 hbridge1 hbridge2 hframe2
    -- Name key subterms
    set n2 := (compile arithVarNames e2 (compile arithVarNames e1 next).2.2).2.2
    -- Build result: env2 updated with the sum
    refine ⟨env2.update (.temp n2)
              (.int (eval intEnv e1 + eval intEnv e2)),
            ?_, ?_, ?_, ?_, ?_⟩
    · -- 1. evalStmt terminates normally
      show evalStmt 0 llEnv (compile arithVarNames (.add e1 e2) next).1 = _
      simp only [compile, evalStmt_seq, heval1, heval2,
        evalStmt_assign, evalExpr_binOp, hstable, hresult2, evalBinOp_add]; rfl
    · -- 2. Result correct
      simp only [compile, evalExpr]
      exact congrArg some (LowLevelEnv.update_same _ _ _)
    · -- 3. Bridge preserved (user vars untouched)
      intro v
      exact LowLevelEnv.update_other env2 (.temp n2) (.user (arithVarNames v))
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
      show next ≤ (compile arithVarNames (.add e1 e2) next).2.2
      simp only [compile]
      exact Nat.le_succ_of_le (Nat.le_trans hmono1 hmono2)
  | mul e1 e2 ih1 ih2 =>
    obtain ⟨env1, heval1, hresult1, hbridge1, hframe1, hmono1⟩ :=
      ih1 next llEnv hbridge
    obtain ⟨env2, heval2, hresult2, hbridge2, hframe2, hmono2⟩ :=
      ih2 (compile arithVarNames e1 next).2.2 env1 hbridge1
    have hstable : evalExpr env2 (compile arithVarNames e1 next).2.1 =
        some (.int (eval intEnv e1)) :=
      compile_result_eval_stable arithVarNames e1 intEnv next env1 env2
        hresult1 hbridge1 hbridge2 hframe2
    set n2 := (compile arithVarNames e2 (compile arithVarNames e1 next).2.2).2.2
    refine ⟨env2.update (.temp n2)
              (.int (eval intEnv e1 * eval intEnv e2)),
            ?_, ?_, ?_, ?_, ?_⟩
    · show evalStmt 0 llEnv (compile arithVarNames (.mul e1 e2) next).1 = _
      simp only [compile, evalStmt_seq, heval1, heval2,
        evalStmt_assign, evalExpr_binOp, hstable, hresult2, evalBinOp_mul]; rfl
    · simp only [compile, evalExpr]
      exact congrArg some (LowLevelEnv.update_same _ _ _)
    · intro v
      exact LowLevelEnv.update_other env2 (.temp n2) (.user (arithVarNames v))
        _ VarName.user_ne_temp ▸ hbridge2 v
    · intro k hk
      have hne : (.temp k : VarName) ≠ .temp n2 := by
        intro h; cases h; exact Nat.not_lt.mpr
          (Nat.le_trans hmono1 hmono2) hk
      rw [LowLevelEnv.update_other _ _ _ _ hne,
        hframe2 k (Nat.lt_of_lt_of_le hk hmono1),
        hframe1 k hk]
    · show next ≤ (compile arithVarNames (.mul e1 e2) next).2.2
      simp only [compile]
      exact Nat.le_succ_of_le (Nat.le_trans hmono1 hmono2)

/-! ## CodeGenSound Instance -/

/-- ArithExpr is CodeGenSound: compilation preserves integer arithmetic semantics.
    Well-typedness: all source variables must be integers. -/
instance : CodeGenSound ArithExpr where
  wellTyped _ env := ∀ (v : VarId), ∃ (n : Int), env v = .int n
  lower_correct := by
    intro a env llEnv hwt hbridge
    -- Convert hbridge to use arithVarNames (defeq to CodeGenerable.varNames)
    have hb : ∀ (v : VarId), llEnv (.user (arithVarNames v)) = env v := hbridge
    -- Extract integer environment from wellTyped
    have hbridge_int : ∀ (v : VarId),
        llEnv (.user (arithVarNames v)) = .int ((env v).getInt) := by
      intro v; exact (hb v).trans (Value.int_getInt (hwt v))
    -- Apply compile_correct
    simp only [CodeGenerable.lower, CodeGenerable.denote, CodeGenerable.varNames,
      ArithExpr.toStmtResult]
    obtain ⟨resultEnv, heval, hresult, hbridge', _, _⟩ :=
      ArithExpr.compile_correct a (fun v => (env v).getInt) 0 llEnv hbridge_int
    exact ⟨0, resultEnv, heval, hresult, fun v => by
      rw [hbridge' v]; exact (Value.int_getInt (hwt v)).symm⟩

end TrustLean
