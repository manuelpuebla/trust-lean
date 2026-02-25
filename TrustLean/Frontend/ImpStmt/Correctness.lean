/-
  Trust-Lean — Verified Code Generation Framework
  Frontend/ImpStmt/Correctness.lean: Correctness proof for ImpStmt compilation

  N3.2: CRIT — proves that ImpStmt compilation preserves semantics.
  Standalone theorem (not CodeGenSound — ImpStmt is statement-oriented).

  Key properties:
  - ImpExpr/ImpBoolExpr compilation is correct (structural induction)
  - ImpStmt compilation preserves semantics (fuel + structural induction)
  - Bridge preservation: user variables track the imperative environment
  - Requires injective variable naming to distinguish user variables
-/

import TrustLean.Frontend.ImpStmt.Compile
import TrustLean.Core.Foundation

set_option autoImplicit false

namespace TrustLean

/-! ## Expression Correctness -/

/-- ImpExpr compilation is correct: evaluating the compiled expression
    in a bridged environment produces the same integer as ImpExpr.eval. -/
theorem ImpExpr.compile_correct
    (vn : VarId → String) (e : ImpExpr) (env : ImpEnv) (llEnv : LowLevelEnv)
    (hbridge : ∀ v, llEnv (.user (vn v)) = .int (env v)) :
    evalExpr llEnv (ImpExpr.compile vn e) = some (.int (ImpExpr.eval env e)) := by
  induction e with
  | lit n => simp [ImpExpr.compile]
  | var v => simp [ImpExpr.compile, hbridge]
  | add e1 e2 ih1 ih2 =>
    simp only [ImpExpr.compile, ImpExpr.eval, evalExpr_binOp, ih1, ih2, evalBinOp_add]
  | mul e1 e2 ih1 ih2 =>
    simp only [ImpExpr.compile, ImpExpr.eval, evalExpr_binOp, ih1, ih2, evalBinOp_mul]

/-- ImpBoolExpr compilation is correct: evaluating the compiled expression
    in a bridged environment produces the same boolean as ImpBoolExpr.eval. -/
theorem ImpBoolExpr.compile_correct
    (vn : VarId → String) (b : ImpBoolExpr) (env : ImpEnv) (llEnv : LowLevelEnv)
    (hbridge : ∀ v, llEnv (.user (vn v)) = .int (env v)) :
    evalExpr llEnv (ImpBoolExpr.compile vn b) = some (.bool (ImpBoolExpr.eval env b)) := by
  induction b with
  | lit b => simp [ImpBoolExpr.compile]
  | eq_ e1 e2 =>
    simp only [ImpBoolExpr.compile, ImpBoolExpr.eval, evalExpr_binOp,
      ImpExpr.compile_correct vn e1 env llEnv hbridge,
      ImpExpr.compile_correct vn e2 env llEnv hbridge, evalBinOp_eqOp]
  | lt_ e1 e2 =>
    simp only [ImpBoolExpr.compile, ImpBoolExpr.eval, evalExpr_binOp,
      ImpExpr.compile_correct vn e1 env llEnv hbridge,
      ImpExpr.compile_correct vn e2 env llEnv hbridge, evalBinOp_ltOp]
  | and_ b1 b2 ih1 ih2 =>
    simp only [ImpBoolExpr.compile, ImpBoolExpr.eval, evalExpr_binOp, ih1, ih2, evalBinOp_land]
  | or_ b1 b2 ih1 ih2 =>
    simp only [ImpBoolExpr.compile, ImpBoolExpr.eval, evalExpr_binOp, ih1, ih2, evalBinOp_lor]
  | not_ b ih =>
    simp only [ImpBoolExpr.compile, ImpBoolExpr.eval, evalExpr_unaryOp, ih, evalUnaryOp_lnot]

/-! ## Bridge Update Lemma -/

/-- After assigning to a user variable, the bridge is maintained if the naming
    is injective. This is the key lemma for the assign case. -/
private theorem bridge_after_assign
    (vn : VarId → String) (hvn : Function.Injective vn)
    (env : ImpEnv) (llEnv : LowLevelEnv)
    (hbridge : ∀ v, llEnv (.user (vn v)) = .int (env v))
    (target : VarId) (val : Int) :
    ∀ w, (llEnv.update (.user (vn target)) (.int val)) (.user (vn w)) =
      .int ((env.update target val) w) := by
  intro w
  by_cases hw : w = target
  · subst hw
    simp [LowLevelEnv.update, ImpEnv.update]
  · have hne : (vn w) ≠ (vn target) := fun h => hw (hvn h)
    simp [LowLevelEnv.update, VarName.user.injEq, hne, ImpEnv.update, hw, hbridge]

/-! ## Main Correctness Theorem -/

/-- ImpStmt compilation preserves semantics.
    If ImpStmt.eval succeeds with some env', then evalStmt on the compiled
    code terminates normally with a bridged low-level environment.

    Requires injective variable naming to ensure distinct source variables
    map to distinct low-level variables. -/
theorem ImpStmt.compile_correct
    (vn : VarId → String) (hvn : Function.Injective vn)
    (s : ImpStmt) (fuel : Nat)
    (env env' : ImpEnv) (llEnv : LowLevelEnv)
    (hbridge : ∀ v, llEnv (.user (vn v)) = .int (env v))
    (heval : ImpStmt.eval fuel env s = some env') :
    ∃ llEnv',
      evalStmt fuel llEnv (ImpStmt.compile vn s) = some (.normal, llEnv') ∧
      (∀ v, llEnv' (.user (vn v)) = .int (env' v)) := by
  induction s generalizing fuel env env' llEnv with
  | skip =>
    simp at heval
    exact ⟨llEnv, by simp [ImpStmt.compile], heval ▸ hbridge⟩
  | assign v e =>
    simp at heval
    subst heval
    exact ⟨llEnv.update (.user (vn v)) (.int (ImpExpr.eval env e)),
      by simp [ImpStmt.compile, evalStmt_assign,
              ImpExpr.compile_correct vn e env llEnv hbridge],
      bridge_after_assign vn hvn env llEnv hbridge v (ImpExpr.eval env e)⟩
  | seq s1 s2 ih1 ih2 =>
    simp at heval
    match hs1 : ImpStmt.eval fuel env s1 with
    | some env_mid =>
      simp [hs1] at heval
      obtain ⟨llMid, hll1, hbMid⟩ := ih1 fuel env env_mid llEnv hbridge hs1
      obtain ⟨llEnv', hll2, hb'⟩ := ih2 fuel env_mid env' llMid hbMid heval
      exact ⟨llEnv', by simp [ImpStmt.compile, evalStmt_seq, hll1, hll2], hb'⟩
    | none => simp [hs1] at heval
  | ite c t e ih_t ih_e =>
    simp at heval
    by_cases hc : ImpBoolExpr.eval env c
    · simp [hc] at heval
      obtain ⟨llEnv', hll, hb'⟩ := ih_t fuel env env' llEnv hbridge heval
      exact ⟨llEnv', by simp [ImpStmt.compile, evalStmt_ite,
        ImpBoolExpr.compile_correct vn c env llEnv hbridge, hc, hll], hb'⟩
    · simp [hc] at heval
      obtain ⟨llEnv', hll, hb'⟩ := ih_e fuel env env' llEnv hbridge heval
      exact ⟨llEnv', by simp [ImpStmt.compile, evalStmt_ite,
        ImpBoolExpr.compile_correct vn c env llEnv hbridge, hc, hll], hb'⟩
  | «while» c body ih_body =>
    -- Nested induction on fuel for the while case
    induction fuel generalizing env env' llEnv with
    | zero => simp at heval
    | succ n ih_fuel =>
      simp at heval
      by_cases hc : ImpBoolExpr.eval env c
      · -- Condition true: execute body then recurse
        simp [hc] at heval
        match hb : ImpStmt.eval n env body with
        | some env_mid =>
          simp [hb] at heval
          -- IH for body (structural, fuel n)
          obtain ⟨llMid, hll_body, hbMid⟩ :=
            ih_body n env env_mid llEnv hbridge hb
          -- IH for while recursion (fuel n)
          obtain ⟨llEnv', hll_while, hb'⟩ :=
            ih_fuel env_mid env' llMid hbMid heval
          -- Compose: evalStmt (n+1) on while
          refine ⟨llEnv', ?_, hb'⟩
          show evalStmt (n + 1) llEnv
            (Stmt.while (ImpBoolExpr.compile vn c) (compile vn body)) = _
          rw [evalStmt_while_succ,
            ImpBoolExpr.compile_correct vn c env llEnv hbridge]
          simp [hc, hll_body]
          exact hll_while
        | none => simp [hb] at heval
      · -- Condition false: loop exits immediately
        simp [hc] at heval
        subst heval
        refine ⟨llEnv, ?_, hbridge⟩
        simp only [ImpStmt.compile, evalStmt_while_succ,
          ImpBoolExpr.compile_correct vn c env llEnv hbridge, hc]

end TrustLean
