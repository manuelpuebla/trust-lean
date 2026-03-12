/-
  Trust-Lean — Verified Code Generation Framework
  MicroC/CallSimulation.lean: Call-aware simulation theorem (v3.0.0)

  N15.3: CRITICO — proves:
  1. evalMicroC_to_withCalls: any evalMicroC result is also evalMicroC_withCalls result
  2. stmtToMicroC_correct_withCalls: master simulation using call-aware evaluator

  Proof strategy: Instead of duplicating the 300+ line simulation proof,
  we prove a general lifting lemma (evalMicroC ⊆ evalMicroC_withCalls)
  by structural + fuel induction. The call-aware evaluator extends the
  base evaluator—it agrees on all non-call statements and adds call
  handling on top. The simulation theorem is then a 3-line corollary.

  Key insight: for the .call case, evalMicroC returns none, so the
  hypothesis evalMicroC ... = some r is vacuously false.
-/

import TrustLean.MicroC.Simulation
import TrustLean.MicroC.CallEval

set_option autoImplicit false

namespace TrustLean

/-! ## Equation Lemma: ite -/

@[simp] theorem evalMicroC_withCalls_ite (fenv : MicroCFuncEnv) (fuel : Nat) (env : MicroCEnv)
    (cond : MicroCExpr) (thenB elseB : MicroCStmt) :
    evalMicroC_withCalls fenv fuel env (.ite cond thenB elseB) =
      match evalMicroCExpr env cond with
      | some (.bool true) => evalMicroC_withCalls fenv fuel env thenB
      | some (.bool false) => evalMicroC_withCalls fenv fuel env elseB
      | _ => none := by
  simp only [evalMicroC_withCalls]
  generalize evalMicroCExpr env cond = c
  cases c with
  | none => rfl
  | some v => cases v with
    | int _ => rfl
    | bool b => cases b <;> rfl

/-! ## Lifting: while helper -/

/-- If evalMicroC returns some r for a while loop, then evalMicroC_withCalls
    returns the same. Proof by fuel induction, using structural IH for body. -/
private theorem evalMicroC_to_withCalls_while (fenv : MicroCFuncEnv)
    (cond : MicroCExpr) (body : MicroCStmt)
    (ih_body : ∀ fuel env r, evalMicroC fuel env body = some r →
      evalMicroC_withCalls fenv fuel env body = some r) :
    ∀ fuel env r, evalMicroC fuel env (.while_ cond body) = some r →
    evalMicroC_withCalls fenv fuel env (.while_ cond body) = some r := by
  intro fuel
  induction fuel with
  | zero =>
    intro env r h
    simp only [evalMicroC_while_zero] at h
    simp only [evalMicroC_withCalls_while_zero]
    exact h
  | succ n ih =>
    intro env r h
    simp only [evalMicroC_while_succ] at h
    simp only [evalMicroC_withCalls_while_succ]
    generalize hc : evalMicroCExpr env cond = c at h ⊢
    cases c with
    | none => exact h
    | some v => cases v with
      | int _ => exact h
      | bool b => cases b with
        | false => exact h
        | true =>
          generalize hb : evalMicroC n env body = rb at h
          cases rb with
          | none => simp at h
          | some p =>
            rw [ih_body n env p hb]
            cases p with | mk o e =>
              cases o with
              | normal | continue_ => exact ih e r h
              | break_ | return_ _ | outOfFuel => exact h

/-! ## Main Lifting Lemma -/

/-- Any result of evalMicroC is also a result of evalMicroC_withCalls.
    The call-aware evaluator extends the base evaluator: it agrees on
    all non-call statements and adds call handling on top.

    For .call, evalMicroC returns none, so the hypothesis is vacuously false.
    For all other constructors, the equations are structurally identical. -/
theorem evalMicroC_to_withCalls (fenv : MicroCFuncEnv) (stmt : MicroCStmt) :
    ∀ fuel env r, evalMicroC fuel env stmt = some r →
    evalMicroC_withCalls fenv fuel env stmt = some r := by
  induction stmt with
  | skip | break_ | continue_ =>
    intro fuel env r h
    simp only [evalMicroC_skip, evalMicroC_break, evalMicroC_continue] at h
    simp only [evalMicroC_withCalls_skip, evalMicroC_withCalls_break,
      evalMicroC_withCalls_continue]
    exact h
  | return_ re =>
    intro fuel env r h
    cases re with
    | none =>
      simp only [evalMicroC_return_none] at h
      simp only [evalMicroC_withCalls_return_none]; exact h
    | some e =>
      simp only [evalMicroC_return_some] at h
      simp only [evalMicroC_withCalls_return_some]; exact h
  | assign name expr =>
    intro fuel env r h
    simp only [evalMicroC_assign] at h
    simp only [evalMicroC_withCalls_assign]; exact h
  | store base idx val =>
    intro fuel env r h
    simp only [evalMicroC] at h
    simp only [evalMicroC_withCalls]; exact h
  | load var base idx =>
    intro fuel env r h
    simp only [evalMicroC] at h
    simp only [evalMicroC_withCalls]; exact h
  | call _ _ _ =>
    intro fuel env r h
    simp [evalMicroC] at h
  | seq s1 s2 ih1 ih2 =>
    intro fuel env r h
    simp only [evalMicroC_seq] at h
    simp only [evalMicroC_withCalls_seq]
    generalize hs1 : evalMicroC fuel env s1 = r1 at h
    cases r1 with
    | none => simp at h
    | some p =>
      rw [ih1 fuel env p hs1]
      cases p with | mk o e_mid =>
        cases o with
        | normal => exact ih2 fuel e_mid r h
        | _ => exact h
  | ite cond thenB elseB ih_then ih_else =>
    intro fuel env r h
    simp only [evalMicroC_ite] at h
    simp only [evalMicroC_withCalls_ite]
    generalize hc : evalMicroCExpr env cond = c at h ⊢
    cases c with
    | none => exact h
    | some v => cases v with
      | int _ => exact h
      | bool b => cases b with
        | true => exact ih_then fuel env r h
        | false => exact ih_else fuel env r h
  | while_ cond body ih_body =>
    exact evalMicroC_to_withCalls_while fenv cond body ih_body

/-! ## Master Call-Aware Simulation Theorem -/

/-- Call-aware simulation: for any Core statement, if evalStmt succeeds with
    a non-outOfFuel result, then evalMicroC_withCalls on the translated statement
    also succeeds with the same result and preserves the bridge.

    Proof: stmtToMicroC_correct gives evalMicroC result. evalMicroC_to_withCalls
    lifts it to evalMicroC_withCalls. Bridge preservation is inherited. -/
theorem stmtToMicroC_correct_withCalls
    (fenv : MicroCFuncEnv)
    {fuel : Nat} {env env' : LowLevelEnv} {mcEnv : MicroCEnv}
    {stmt : Stmt} {oc : Outcome}
    (heval : evalStmt fuel env stmt = some (oc, env'))
    (hb : microCBridge env mcEnv)
    (hinj : VarNameInjective)
    (hoc : oc ≠ .outOfFuel)
    (hwf : WellFormedArrayBases stmt) :
    ∃ mcEnv', evalMicroC_withCalls fenv fuel mcEnv (stmtToMicroC stmt) = some (oc, mcEnv')
      ∧ microCBridge env' mcEnv' := by
  obtain ⟨mcEnv', hmcEval, hb'⟩ := stmtToMicroC_correct heval hb hinj hoc hwf
  exact ⟨mcEnv', evalMicroC_to_withCalls fenv _ fuel mcEnv _ hmcEval, hb'⟩

/-! ## Non-Vacuity -/

/-- Non-vacuity: evalMicroC_to_withCalls for assign.
    Both evaluators produce x = 42 (outcome normal, variable value 42). -/
example :
    let stmt := MicroCStmt.assign "x" (.litInt 42)
    (do let (oc, e) ← evalMicroC 10 MicroCEnv.default stmt; pure (oc, e "x")) =
    some (.normal, .int 42) ∧
    (do let (oc, e) ← evalMicroC_withCalls (fun _ => none) 10 MicroCEnv.default stmt;
        pure (oc, e "x")) = some (.normal, .int 42) := by
  constructor <;> native_decide

/-- Non-vacuity: evalMicroC_to_withCalls for a while loop.
    Both evaluators return normal outcome for while(false) skip. -/
example :
    let stmt := MicroCStmt.while_ (.litBool false) .skip
    (do let (oc, _) ← evalMicroC 10 MicroCEnv.default stmt; pure oc) = some .normal ∧
    (do let (oc, _) ← evalMicroC_withCalls (fun _ => none) 10 MicroCEnv.default stmt;
        pure oc) = some .normal := by
  constructor <;> native_decide

/-- Non-vacuity: concrete Core program successfully simulated through call-aware evaluator.
    Core assign x = 7 → MicroC assign → both evaluate to normal with x = 7. -/
example :
    let stmt := Stmt.assign (.user "x") (.litInt 7)
    let fenv : MicroCFuncEnv := fun _ => none
    (do let (oc, _) ← evalStmt 10 LowLevelEnv.default stmt; pure oc) = some .normal ∧
    (do let (oc, e) ← evalMicroC_withCalls fenv 10 MicroCEnv.default (stmtToMicroC stmt);
        pure (oc, e "x")) = some (.normal, .int 7) := by
  constructor <;> native_decide

/-- Non-vacuity: lifting works for ite with call-free branches. -/
example :
    let stmt := MicroCStmt.ite (.litBool true)
      (.assign "x" (.litInt 1)) (.assign "x" (.litInt 2))
    (do let (_, e) ← evalMicroC 10 MicroCEnv.default stmt; pure (e "x")) =
    some (.int 1) ∧
    (do let (_, e) ← evalMicroC_withCalls (fun _ => none) 10 MicroCEnv.default stmt;
        pure (e "x")) = some (.int 1) := by
  constructor <;> native_decide

/-! ## Smoke Tests -/

-- Smoke test: while loop lifting — both evaluators agree on outcome.
#eval do
  let stmt := MicroCStmt.while_ (.litBool false) .skip
  let r1 ← evalMicroC 10 MicroCEnv.default stmt
  let r2 ← evalMicroC_withCalls (fun _ => none) 10 MicroCEnv.default stmt
  pure (r1.1 == r2.1)

-- Smoke test: seq + assign lifting — both evaluators agree on x and y values.
#eval do
  let stmt := MicroCStmt.seq (.assign "x" (.litInt 1)) (.assign "y" (.litInt 2))
  let r1 ← evalMicroC 10 MicroCEnv.default stmt
  let r2 ← evalMicroC_withCalls (fun _ => none) 10 MicroCEnv.default stmt
  pure (r1.1 == r2.1, r1.2 "x" == r2.2 "x", r1.2 "y" == r2.2 "y")

-- Smoke test: Core-to-MicroC simulation chain — assign x = 42.
#eval do
  let coreStmt := Stmt.assign (.user "x") (.litInt 42)
  let mcStmt := stmtToMicroC coreStmt
  let r ← evalMicroC_withCalls (fun _ => none) 10 MicroCEnv.default mcStmt
  pure (r.1, r.2 "x")

-- Smoke test: ite lifting — condition true selects then branch.
#eval do
  let stmt := MicroCStmt.ite (.litBool true)
    (.assign "x" (.litInt 1)) (.assign "x" (.litInt 2))
  let r1 ← evalMicroC 10 MicroCEnv.default stmt
  let r2 ← evalMicroC_withCalls (fun _ => none) 10 MicroCEnv.default stmt
  pure (r1.2 "x" == r2.2 "x")

end TrustLean
