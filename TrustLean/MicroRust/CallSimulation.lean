/-
  Trust-Lean — Verified Code Generation Framework
  MicroRust/CallSimulation.lean: Call-aware simulation theorem (v4.0.0)

  Structural clone of MicroC/CallSimulation.lean for MicroRust.

  Lifting pattern: stmtToMicroRust_correct gives evalMicroC result →
  evalMicroC_to_withCalls lifts it to evalMicroC_withCalls.

  Key insight: MicroRust reuses the MicroC AST and evaluators.
  stmtToMicroRust produces MicroCStmt, evaluated by evalMicroC.
  The lifting lemma evalMicroC_to_withCalls (MicroC/CallSimulation)
  is therefore directly applicable — no re-proof needed.

  For the .call case, evalMicroC returns none, so the hypothesis
  evalMicroC ... = some r is vacuously false.
-/

import TrustLean.MicroRust.Simulation
import TrustLean.MicroC.CallSimulation

set_option autoImplicit false

namespace TrustLean

/-! ## Master Call-Aware Simulation Theorem (MicroRust) -/

/-- Call-aware simulation: for any Core statement, if evalStmt succeeds with
    a non-outOfFuel result, then evalMicroC_withCalls on the Rust-translated
    statement also succeeds with the same result and preserves the bridge.

    Proof: stmtToMicroRust_correct gives evalMicroC result. evalMicroC_to_withCalls
    lifts it to evalMicroC_withCalls. Bridge preservation is inherited. -/
theorem stmtToMicroRust_correct_withCalls
    (fenv : MicroCFuncEnv)
    {fuel : Nat} {env env' : LowLevelEnv} {mcEnv : MicroRustEnv}
    {stmt : Stmt} {oc : Outcome}
    (heval : evalStmt fuel env stmt = some (oc, env'))
    (hb : microRustBridge env mcEnv)
    (hinj : VarNameInjectiveRust)
    (hoc : oc ≠ .outOfFuel)
    (hwf : WellFormedArrayBasesRust stmt) :
    ∃ mcEnv', evalMicroC_withCalls fenv fuel mcEnv (stmtToMicroRust stmt) = some (oc, mcEnv')
      ∧ microRustBridge env' mcEnv' := by
  obtain ⟨mcEnv', hmcEval, hb'⟩ := stmtToMicroRust_correct heval hb hinj hoc hwf
  exact ⟨mcEnv', evalMicroC_to_withCalls fenv _ fuel mcEnv _ hmcEval, hb'⟩

/-! ## Non-Vacuity -/

/-- Non-vacuity: evalMicroC_to_withCalls for assign via MicroRust translation.
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

/-- Non-vacuity: concrete Core program successfully simulated through
    Rust translation + call-aware evaluator.
    Core assign x = 7 → stmtToMicroRust → both evaluate to normal with x = 7. -/
example :
    let stmt := Stmt.assign (.user "x") (.litInt 7)
    let fenv : MicroCFuncEnv := fun _ => none
    (do let (oc, _) ← evalStmt 10 LowLevelEnv.default stmt; pure oc) = some .normal ∧
    (do let (oc, e) ← evalMicroC_withCalls fenv 10 MicroCEnv.default (stmtToMicroRust stmt);
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

-- Smoke test: Core-to-MicroRust simulation chain — assign x = 42.
#eval do
  let coreStmt := Stmt.assign (.user "x") (.litInt 42)
  let mcStmt := stmtToMicroRust coreStmt
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
