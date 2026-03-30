/-
  Trust-Lean v4.2.0 — VecStmt Evaluator
  N28.2: CRITICO — evalVecStmt delegates to evalStmt per lane.

  Uses List.foldl over List.range to iterate over lanes. Each lane:
  1. selectLane i vars env → create lane view
  2. evalStmt fuel laneEnv body → evaluate scalar body
  3. writeLane i vars laneEnv' env → write results back
-/
import TrustLean.Vec.Defs
import TrustLean.Core.Eval

set_option autoImplicit false

namespace TrustLean

/-! ## evalVecStmt -/

/-- Helper: execute body for one lane, updating environment.
    Returns updated environment or none on failure. -/
def evalOneLane (fuel : Nat) (vars : List String) (body : Stmt)
    (acc : Option LowLevelEnv) (i : Nat) : Option LowLevelEnv :=
  match acc with
  | none => none
  | some env =>
    match evalStmt fuel (selectLane (Int.ofNat i) vars env) body with
    | some (.normal, laneEnv') => some (writeLane (Int.ofNat i) vars laneEnv' env)
    | _ => none

/-- Evaluate a VecStmt. Delegates scalar evaluation to evalStmt.
    vecMap iterates over lanes via List.foldl.
    vecLoad/vecStore operate directly on array positions. -/
def evalVecStmt (fuel : Nat) (env : LowLevelEnv) : VecStmt → Option (Outcome × LowLevelEnv)
  | .scalar s => evalStmt fuel env s
  | .vecMap lanes vars body =>
    match (List.range lanes).foldl (evalOneLane fuel vars body) (some env) with
    | some env' => some (.normal, env')
    | none => none
  | .vecLoad dst base startIdx lanes =>
    match evalExpr env startIdx with
    | some (.int start) =>
      let env' := (List.range lanes).foldl (fun e i =>
        e.update (.array dst (Int.ofNat i)) (env (.array base (start + Int.ofNat i)))
      ) env
      some (.normal, env')
    | _ => none
  | .vecStore base startIdx src lanes =>
    match evalExpr env startIdx with
    | some (.int start) =>
      let env' := (List.range lanes).foldl (fun e i =>
        e.update (.array base (start + Int.ofNat i)) (env (.array src (Int.ofNat i)))
      ) env
      some (.normal, env')
    | _ => none
  | .vecSpecialOp op lanes dst src1 src2 =>
    let a := readVec env src1 lanes
    let b := readVec env src2 lanes
    match evalVecSpecialOp op a b lanes with
    | some result => some (.normal, writeVec env dst result)
    | none => none
  | .vecSeq s1 s2 =>
    match evalVecStmt fuel env s1 with
    | some (.normal, env') => evalVecStmt fuel env' s2
    | other => other

/-! ## @[simp] Equation Lemmas -/

@[simp] theorem evalVecStmt_scalar (fuel : Nat) (env : LowLevelEnv) (s : Stmt) :
    evalVecStmt fuel env (.scalar s) = evalStmt fuel env s := rfl

/-! ## Non-Vacuity -/

/-- Scalar passthrough: evalVecStmt on scalar skip = normal -/
example : evalVecStmt 10 LowLevelEnv.default (.scalar .skip) =
    some (.normal, LowLevelEnv.default) := by simp [evalVecStmt, evalStmt]

/-- vecMap with 0 lanes is a no-op -/
example : evalVecStmt 10 LowLevelEnv.default (.vecMap 0 ["x"] (.assign (.user "x") (.litInt 42))) =
    some (.normal, LowLevelEnv.default) := by
  simp [evalVecStmt, List.range, List.range.loop, List.foldl]

end TrustLean
