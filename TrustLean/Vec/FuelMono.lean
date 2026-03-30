/-
  Trust-Lean v4.2.0 — VecStmt Fuel Monotonicity
  N28.4: CRITICO — evalVecStmt_fuel_mono_full.

  5 VecStmt constructors. Proof delegates to evalStmt_fuel_mono_full.
-/
import TrustLean.Vec.Eval
import TrustLean.Core.FuelMono

set_option autoImplicit false

namespace TrustLean

/-! ## Helper: evalOneLane fuel monotonicity -/

private theorem evalOneLane_fuel_mono (vars : List String) (body : Stmt)
    (fuel fuel' : Nat) (hle : fuel ≤ fuel')
    (i : Nat) (env : LowLevelEnv) (env' : LowLevelEnv)
    (h : evalOneLane fuel vars body (some env) i = some env') :
    evalOneLane fuel' vars body (some env) i = some env' := by
  simp only [evalOneLane] at h ⊢
  generalize heq : evalStmt fuel (selectLane (Int.ofNat i) vars env) body = r at h
  match r with
  | some (.normal, laneEnv') =>
    have h_mono := evalStmt_fuel_mono_full heq hle (by simp)
    rw [h_mono]; exact h
  | some (.break_, _) | some (.continue_, _) | some (.return_ _, _)
  | some (.outOfFuel, _) | none => simp at h

/-- foldl of evalOneLane over none stays none. -/
private theorem foldl_none (fuel : Nat) (vars : List String) (body : Stmt) (lanes : List Nat) :
    lanes.foldl (evalOneLane fuel vars body) none = none := by
  induction lanes with
  | nil => rfl
  | cons _ _ ih => simp [List.foldl, evalOneLane]; exact ih

/-- foldl over evalOneLane is fuel-monotone. -/
private theorem foldl_fuel_mono (vars : List String) (body : Stmt)
    (fuel fuel' : Nat) (hle : fuel ≤ fuel')
    (lanes : List Nat) (env : LowLevelEnv) (env' : LowLevelEnv)
    (h : lanes.foldl (evalOneLane fuel vars body) (some env) = some env') :
    lanes.foldl (evalOneLane fuel' vars body) (some env) = some env' := by
  induction lanes generalizing env with
  | nil => simpa [List.foldl] using h
  | cons x xs ih =>
    simp only [List.foldl] at h ⊢
    match hstep : evalOneLane fuel vars body (some env) x with
    | none =>
      rw [hstep] at h; rw [foldl_none] at h; simp at h
    | some envMid =>
      rw [hstep] at h
      rw [evalOneLane_fuel_mono vars body fuel fuel' hle x env envMid hstep]
      exact ih envMid h

/-! ## Main Theorem -/

theorem evalVecStmt_fuel_mono_full {fuel fuel' : Nat} {env : LowLevelEnv}
    {vs : VecStmt} {env' : LowLevelEnv} {oc : Outcome}
    (h : evalVecStmt fuel env vs = some (oc, env'))
    (hle : fuel ≤ fuel')
    (hoc : oc ≠ .outOfFuel) :
    evalVecStmt fuel' env vs = some (oc, env') := by
  cases vs with
  | scalar s =>
    simp only [evalVecStmt] at h ⊢
    exact evalStmt_fuel_mono_full h hle hoc
  | vecMap lanes vars body =>
    simp only [evalVecStmt] at h ⊢
    generalize hfold : (List.range lanes).foldl (evalOneLane fuel vars body) (some env) = r at h
    match r with
    | some envR =>
      rw [foldl_fuel_mono vars body fuel fuel' hle (List.range lanes) env envR hfold]
      exact h
    | none => simp at h
  | vecLoad _ _ _ _ =>
    simp only [evalVecStmt] at h ⊢; exact h
  | vecStore _ _ _ _ =>
    simp only [evalVecStmt] at h ⊢; exact h
  | vecSpecialOp _ _ _ _ _ =>
    simp only [evalVecStmt] at h ⊢; exact h
  | vecSeq s1 s2 =>
    simp only [evalVecStmt] at h ⊢
    generalize hm : evalVecStmt fuel env s1 = r1 at h
    match r1 with
    | none => simp at h
    | some (.normal, env1) =>
      rw [evalVecStmt_fuel_mono_full hm hle (by simp)]
      exact evalVecStmt_fuel_mono_full h hle hoc
    | some (.break_, env1) =>
      rw [evalVecStmt_fuel_mono_full hm hle (by simp)]; exact h
    | some (.continue_, env1) =>
      rw [evalVecStmt_fuel_mono_full hm hle (by simp)]; exact h
    | some (.return_ rv, env1) =>
      rw [evalVecStmt_fuel_mono_full hm hle (by simp)]; exact h
    | some (.outOfFuel, env1) =>
      simp at h; obtain ⟨h1, _⟩ := h; subst h1; exact absurd rfl hoc

theorem evalVecStmt_fuel_mono {fuel fuel' : Nat} {env env' : LowLevelEnv} {vs : VecStmt}
    (h : evalVecStmt fuel env vs = some (.normal, env'))
    (hle : fuel ≤ fuel') :
    evalVecStmt fuel' env vs = some (.normal, env') :=
  evalVecStmt_fuel_mono_full h hle (by simp)

end TrustLean
