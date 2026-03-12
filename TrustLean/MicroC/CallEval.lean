/-
  Trust-Lean — Verified Code Generation Framework
  MicroC/CallEval.lean: Call Evaluator + Fuel Monotonicity (v3.0.0)

  N15.2: Evaluator extending evalMicroC with non-recursive function calls.
  Uses evalMicroC for function bodies (NonRecursive guarantees no nested calls).

  Key definitions:
  - evalArgs: evaluate a list of argument expressions
  - evalMicroC_withCalls: MicroC evaluator with function call support

  Key theorems:
  - evalMicroC_withCalls_call_free: agrees with evalMicroC on call-free programs
  - evalMicroC_withCalls_fuel_mono_full: fuel monotonicity
  - evalMicroC_withCalls_fuel_mono: specialized to normal outcomes
-/

import TrustLean.MicroC.CallTypes
import TrustLean.MicroC.Eval
import TrustLean.MicroC.FuelMono

set_option autoImplicit false

namespace TrustLean

/-! ## Argument Evaluation -/

/-- Evaluate a list of argument expressions in the given environment.
    Returns `none` if any argument fails to evaluate. -/
def evalArgs (env : MicroCEnv) : List MicroCExpr → Option (List Value)
  | [] => some []
  | e :: es =>
    match evalMicroCExpr env e with
    | some v =>
      match evalArgs env es with
      | some vs => some (v :: vs)
      | none => none
    | none => none

@[simp] theorem evalArgs_nil (env : MicroCEnv) : evalArgs env [] = some [] := rfl

@[simp] theorem evalArgs_cons (env : MicroCEnv) (e : MicroCExpr) (es : List MicroCExpr) :
    evalArgs env (e :: es) =
    match evalMicroCExpr env e with
    | some v =>
      match evalArgs env es with
      | some vs => some (v :: vs)
      | none => none
    | none => none := rfl

/-! ## Call-Capable Evaluator -/

/-- MicroC evaluator with non-recursive function call support.
    For `.call result fname args`:
    1. Look up `fname` in `fenv`
    2. Evaluate arguments in caller environment
    3. Create fresh callee environment (buildCallEnv)
    4. Evaluate function body with `evalMicroC` (NOT recursive — NonRecursive guarantees no calls)
    5. Handle return value: bind to `result` in caller env

    Design decision: function bodies evaluated with `evalMicroC` (not `evalMicroC_withCalls`)
    because NonRecursive prohibits calls in bodies. This avoids termination issues. -/
def evalMicroC_withCalls (fenv : MicroCFuncEnv) (fuel : Nat) (env : MicroCEnv)
    (stmt : MicroCStmt) : Option (Outcome × MicroCEnv) :=
  match stmt with
  | .skip => some (.normal, env)
  | .break_ => some (.break_, env)
  | .continue_ => some (.continue_, env)
  | .return_ re =>
    match re with
    | some e =>
      match evalMicroCExpr env e with
      | some v => some (.return_ (some v), env)
      | none => none
    | none => some (.return_ none, env)
  | .assign name expr =>
    match evalMicroCExpr env expr with
    | some v => some (.normal, env.update name v)
    | none => none
  | .store base idx val =>
    match getMicroCArrayName base, evalMicroCExpr env idx, evalMicroCExpr env val with
    | some name, some (.int i), some v =>
      some (.normal, env.update (name ++ "[" ++ toString i ++ "]") v)
    | _, _, _ => none
  | .load var base idx =>
    match getMicroCArrayName base, evalMicroCExpr env idx with
    | some name, some (.int i) =>
      some (.normal, env.update var (env (name ++ "[" ++ toString i ++ "]")))
    | _, _ => none
  | .call result fname args =>
    match fenv fname with
    | none => none
    | some fdef =>
      match evalArgs env args with
      | none => none
      | some vals =>
        let calleeEnv := buildCallEnv fdef.params vals
        match evalMicroC fuel calleeEnv fdef.body with
        | some (.return_ (some v), _) => some (.normal, env.update result v)
        | some (.return_ none, _) => some (.normal, env)
        | some (.normal, _) => some (.normal, env)
        | some (.outOfFuel, _) => some (.outOfFuel, env)
        | _ => none
  | .seq s1 s2 =>
    match evalMicroC_withCalls fenv fuel env s1 with
    | some (.normal, env') => evalMicroC_withCalls fenv fuel env' s2
    | other => other
  | .ite cond thenB elseB =>
    match evalMicroCExpr env cond with
    | some (.bool true) => evalMicroC_withCalls fenv fuel env thenB
    | some (.bool false) => evalMicroC_withCalls fenv fuel env elseB
    | _ => none
  | .while_ cond body =>
    match fuel with
    | 0 => some (.outOfFuel, env)
    | fuel' + 1 =>
      match evalMicroCExpr env cond with
      | some (.bool false) => some (.normal, env)
      | some (.bool true) =>
        match evalMicroC_withCalls fenv fuel' env body with
        | some (.normal, env') => evalMicroC_withCalls fenv fuel' env' (.while_ cond body)
        | some (.continue_, env') => evalMicroC_withCalls fenv fuel' env' (.while_ cond body)
        | some (.break_, env') => some (.normal, env')
        | some (.return_ rv, env') => some (.return_ rv, env')
        | some (.outOfFuel, env') => some (.outOfFuel, env')
        | none => none
      | _ => none
termination_by (fuel, sizeOf stmt)

/-! ## @[simp] Equation Lemmas -/

@[simp] theorem evalMicroC_withCalls_skip (fenv : MicroCFuncEnv) (fuel : Nat) (env : MicroCEnv) :
    evalMicroC_withCalls fenv fuel env .skip = some (.normal, env) := by
  simp [evalMicroC_withCalls]

@[simp] theorem evalMicroC_withCalls_break (fenv : MicroCFuncEnv) (fuel : Nat) (env : MicroCEnv) :
    evalMicroC_withCalls fenv fuel env .break_ = some (.break_, env) := by
  simp [evalMicroC_withCalls]

@[simp] theorem evalMicroC_withCalls_continue (fenv : MicroCFuncEnv) (fuel : Nat)
    (env : MicroCEnv) :
    evalMicroC_withCalls fenv fuel env .continue_ = some (.continue_, env) := by
  simp [evalMicroC_withCalls]

@[simp] theorem evalMicroC_withCalls_return_some (fenv : MicroCFuncEnv) (fuel : Nat)
    (env : MicroCEnv) (e : MicroCExpr) :
    evalMicroC_withCalls fenv fuel env (.return_ (some e)) =
    match evalMicroCExpr env e with
    | some v => some (.return_ (some v), env)
    | none => none := by
  simp [evalMicroC_withCalls]

@[simp] theorem evalMicroC_withCalls_return_none (fenv : MicroCFuncEnv) (fuel : Nat)
    (env : MicroCEnv) :
    evalMicroC_withCalls fenv fuel env (.return_ none) =
    some (.return_ none, env) := by
  simp [evalMicroC_withCalls]

@[simp] theorem evalMicroC_withCalls_assign (fenv : MicroCFuncEnv) (fuel : Nat) (env : MicroCEnv)
    (name : String) (expr : MicroCExpr) :
    evalMicroC_withCalls fenv fuel env (.assign name expr) =
    match evalMicroCExpr env expr with
    | some v => some (.normal, env.update name v)
    | none => none := by
  simp [evalMicroC_withCalls]

@[simp] theorem evalMicroC_withCalls_call (fenv : MicroCFuncEnv) (fuel : Nat) (env : MicroCEnv)
    (result fname : String) (args : List MicroCExpr) :
    evalMicroC_withCalls fenv fuel env (.call result fname args) =
    match fenv fname with
    | none => none
    | some fdef =>
      match evalArgs env args with
      | none => none
      | some vals =>
        let calleeEnv := buildCallEnv fdef.params vals
        match evalMicroC fuel calleeEnv fdef.body with
        | some (.return_ (some v), _) => some (.normal, env.update result v)
        | some (.return_ none, _) => some (.normal, env)
        | some (.normal, _) => some (.normal, env)
        | some (.outOfFuel, _) => some (.outOfFuel, env)
        | _ => none := by
  simp [evalMicroC_withCalls]

@[simp] theorem evalMicroC_withCalls_while_zero (fenv : MicroCFuncEnv) (env : MicroCEnv)
    (cond : MicroCExpr) (body : MicroCStmt) :
    evalMicroC_withCalls fenv 0 env (.while_ cond body) = some (.outOfFuel, env) := by
  simp [evalMicroC_withCalls]

@[simp] theorem evalMicroC_withCalls_while_succ (fenv : MicroCFuncEnv) (fuel : Nat)
    (env : MicroCEnv) (cond : MicroCExpr) (body : MicroCStmt) :
    evalMicroC_withCalls fenv (fuel + 1) env (.while_ cond body) =
      match evalMicroCExpr env cond with
      | some (.bool false) => some (.normal, env)
      | some (.bool true) =>
        match evalMicroC_withCalls fenv fuel env body with
        | some (.normal, env') => evalMicroC_withCalls fenv fuel env' (.while_ cond body)
        | some (.continue_, env') => evalMicroC_withCalls fenv fuel env' (.while_ cond body)
        | some (.break_, env') => some (.normal, env')
        | some (.return_ rv, env') => some (.return_ rv, env')
        | some (.outOfFuel, env') => some (.outOfFuel, env')
        | none => none
      | _ => none := by
  simp [evalMicroC_withCalls]

@[simp] theorem evalMicroC_withCalls_seq (fenv : MicroCFuncEnv) (fuel : Nat) (env : MicroCEnv)
    (s1 s2 : MicroCStmt) :
    evalMicroC_withCalls fenv fuel env (.seq s1 s2) =
      match evalMicroC_withCalls fenv fuel env s1 with
      | some (.normal, env') => evalMicroC_withCalls fenv fuel env' s2
      | other => other := by
  simp [evalMicroC_withCalls]

/-! ## Call-Free Equivalence -/

/-- Helper: while loop equivalence for call-free body. -/
private theorem callFree_while (fenv : MicroCFuncEnv) (cond : MicroCExpr) (body : MicroCStmt)
    (ihBody : ∀ fuel env, evalMicroC_withCalls fenv fuel env body = evalMicroC fuel env body) :
    ∀ fuel env, evalMicroC_withCalls fenv fuel env (.while_ cond body) =
    evalMicroC fuel env (.while_ cond body) := by
  intro fuel
  induction fuel with
  | zero =>
    intro env
    simp only [evalMicroC_withCalls_while_zero, evalMicroC_while_zero]
  | succ fuel' ih =>
    intro env
    simp only [evalMicroC_withCalls_while_succ, evalMicroC_while_succ]
    generalize hc : evalMicroCExpr env cond = c
    cases c with
    | none => rfl
    | some v => cases v with
      | int _ => rfl
      | bool b => cases b with
        | false => rfl
        | true =>
          rw [ihBody fuel' env]
          generalize evalMicroC fuel' env body = rb
          cases rb with
          | none => rfl
          | some p => cases p with | mk o e =>
            cases o with
            | normal => exact ih e
            | continue_ => exact ih e
            | break_ | return_ _ | outOfFuel => rfl

/-- If a statement has no `.call` constructors, evalMicroC_withCalls agrees with evalMicroC.
    This ensures backward compatibility: existing call-free programs behave identically. -/
theorem evalMicroC_withCalls_call_free (fenv : MicroCFuncEnv)
    (stmt : MicroCStmt) (hcf : hasCallStmt stmt = false) :
    ∀ fuel env, evalMicroC_withCalls fenv fuel env stmt = evalMicroC fuel env stmt := by
  induction stmt with
  | call _ _ _ => simp [hasCallStmt] at hcf
  | skip | break_ | continue_ =>
    intros; simp
  | return_ re =>
    intro fuel env; cases re with
    | none => simp
    | some e =>
      simp only [evalMicroC_withCalls, evalMicroC]
      generalize evalMicroCExpr env e = r; cases r <;> rfl
  | assign n e =>
    intro fuel env; simp only [evalMicroC_withCalls, evalMicroC]
    generalize evalMicroCExpr env e = r; cases r <;> rfl
  | store b i v =>
    intro fuel env; simp only [evalMicroC_withCalls, evalMicroC]
    generalize getMicroCArrayName b = r1
    generalize evalMicroCExpr env i = r2
    generalize evalMicroCExpr env v = r3
    cases r1 with
    | none => rfl
    | some name => cases r2 with
      | none => rfl
      | some val2 => cases val2 with
        | int _ => cases r3 <;> rfl
        | bool _ => rfl
  | load n b i =>
    intro fuel env; simp only [evalMicroC_withCalls, evalMicroC]
    generalize getMicroCArrayName b = r1
    generalize evalMicroCExpr env i = r2
    cases r1 with
    | none => rfl
    | some name => cases r2 with
      | none => rfl
      | some val2 => cases val2 with
        | int _ => rfl
        | bool _ => rfl
  | seq s1 s2 ih1 ih2 =>
    simp only [hasCallStmt, Bool.or_eq_false_iff] at hcf
    intro fuel env
    simp only [evalMicroC_withCalls, evalMicroC, ih1 hcf.1 fuel env]
    generalize evalMicroC fuel env s1 = r
    cases r with
    | none => rfl
    | some p => cases p with | mk o e =>
      cases o with
      | normal => exact ih2 hcf.2 fuel e
      | _ => rfl
  | ite c t e iht ihe =>
    simp only [hasCallStmt, Bool.or_eq_false_iff] at hcf
    intro fuel env
    simp only [evalMicroC_withCalls, evalMicroC]
    generalize evalMicroCExpr env c = r
    cases r with
    | none => rfl
    | some v => cases v with
      | int _ => rfl
      | bool b => cases b with
        | true => exact iht hcf.1 fuel env
        | false => exact ihe hcf.2 fuel env
  | while_ c body ih =>
    simp only [hasCallStmt] at hcf
    exact fun fuel env => callFree_while fenv c body (ih hcf) fuel env

/-! ## Fuel Monotonicity -/

/-- Helper: sequence fuel monotonicity for withCalls. -/
private theorem fuel_mono_seq_wc
    (fenv : MicroCFuncEnv) {fuel fuel' : Nat} {env env' : MicroCEnv}
    {s1 s2 : MicroCStmt} {oc : Outcome}
    (ih1 : ∀ {fuel fuel' : Nat} {env env' : MicroCEnv} {oc : Outcome},
      evalMicroC_withCalls fenv fuel env s1 = some (oc, env') →
      fuel ≤ fuel' → oc ≠ .outOfFuel →
      evalMicroC_withCalls fenv fuel' env s1 = some (oc, env'))
    (ih2 : ∀ {fuel fuel' : Nat} {env env' : MicroCEnv} {oc : Outcome},
      evalMicroC_withCalls fenv fuel env s2 = some (oc, env') →
      fuel ≤ fuel' → oc ≠ .outOfFuel →
      evalMicroC_withCalls fenv fuel' env s2 = some (oc, env'))
    (h : evalMicroC_withCalls fenv fuel env (.seq s1 s2) = some (oc, env'))
    (hle : fuel ≤ fuel') (hoc : oc ≠ .outOfFuel) :
    evalMicroC_withCalls fenv fuel' env (.seq s1 s2) = some (oc, env') := by
  simp only [evalMicroC_withCalls_seq] at h ⊢
  generalize hm : evalMicroC_withCalls fenv fuel env s1 = r at h
  cases r with
  | none => simp at h
  | some p =>
    cases p with
    | mk o e_mid =>
      cases o with
      | normal => simp only [ih1 hm hle (by intro h; cases h)]; exact ih2 h hle hoc
      | break_ => simp only [ih1 hm hle (by intro h; cases h)]; exact h
      | continue_ => simp only [ih1 hm hle (by intro h; cases h)]; exact h
      | return_ rv => simp only [ih1 hm hle (by intro h; cases h)]; exact h
      | outOfFuel =>
        simp only [] at h
        have : oc = .outOfFuel := by
          have := Option.some.inj h; exact (congrArg Prod.fst this).symm
        exact absurd this hoc

/-- Helper: while loop fuel monotonicity for withCalls. -/
private theorem fuel_mono_while_wc
    (fenv : MicroCFuncEnv) {cond : MicroCExpr} {body : MicroCStmt}
    (ihBody : ∀ {fuel fuel' : Nat} {env env' : MicroCEnv} {oc : Outcome},
      evalMicroC_withCalls fenv fuel env body = some (oc, env') →
      fuel ≤ fuel' → oc ≠ .outOfFuel →
      evalMicroC_withCalls fenv fuel' env body = some (oc, env'))
    {fuel : Nat} :
    ∀ {fuel' : Nat} {env env' : MicroCEnv} {oc : Outcome},
    evalMicroC_withCalls fenv fuel env (.while_ cond body) = some (oc, env') →
    fuel ≤ fuel' → oc ≠ .outOfFuel →
    evalMicroC_withCalls fenv fuel' env (.while_ cond body) = some (oc, env') := by
  induction fuel with
  | zero =>
    intro fuel' env env' oc h _ hoc
    simp only [evalMicroC_withCalls_while_zero] at h
    have : oc = .outOfFuel := by
      have := Option.some.inj h; exact (congrArg Prod.fst this).symm
    exact absurd this hoc
  | succ n ih_fuel =>
    intro fuel' env env' oc h hle hoc
    obtain ⟨m, rfl⟩ : ∃ m, fuel' = m + 1 := ⟨fuel' - 1, by omega⟩
    have hnm : n ≤ m := by omega
    simp only [evalMicroC_withCalls_while_succ] at h ⊢
    generalize hc : evalMicroCExpr env cond = c at h ⊢
    cases c with
    | none => simp at h
    | some v => cases v with
      | int _ => simp at h
      | bool b => cases b with
        | false => exact h
        | true =>
          generalize hb : evalMicroC_withCalls fenv n env body = rb at h
          cases rb with
          | none => simp at h
          | some p => cases p with | mk ob e_mid =>
            cases ob with
            | normal =>
              simp only [ihBody hb hnm (by decide)]; exact ih_fuel h hnm hoc
            | continue_ =>
              simp only [ihBody hb hnm (by decide)]; exact ih_fuel h hnm hoc
            | break_ =>
              simp only [ihBody hb hnm (by simp_all)]; exact h
            | return_ rv =>
              simp only [ihBody hb hnm (by simp_all)]; exact h
            | outOfFuel =>
              simp only [] at h
              have : oc = .outOfFuel := by
                have := Option.some.inj h; exact (congrArg Prod.fst this).symm
              exact absurd this hoc

/-- Fuel monotonicity for evalMicroC_withCalls, generalized to all outcomes. -/
private theorem evalMicroC_withCalls_fuel_mono_gen (fenv : MicroCFuncEnv) (stmt : MicroCStmt) :
    ∀ {fuel fuel' : Nat} {env env' : MicroCEnv} {oc : Outcome},
    evalMicroC_withCalls fenv fuel env stmt = some (oc, env') →
    fuel ≤ fuel' → oc ≠ .outOfFuel →
    evalMicroC_withCalls fenv fuel' env stmt = some (oc, env') := by
  induction stmt with
  | skip | break_ | continue_ => intros; simp_all
  | return_ re =>
    intro fuel fuel' env env' oc h _ _
    cases re <;> (simp at h ⊢; exact h)
  | assign _ _ => intros; simp_all
  | store _ _ _ =>
    intro fuel fuel' env env' oc h _ _; simp [evalMicroC_withCalls] at h ⊢; exact h
  | load _ _ _ =>
    intro fuel fuel' env env' oc h _ _; simp [evalMicroC_withCalls] at h ⊢; exact h
  | call result fname args =>
    intro fuel fuel' env env' oc h hle hoc
    simp only [evalMicroC_withCalls_call] at h ⊢
    match hf : fenv fname with
    | none => simp [hf] at h
    | some fdef =>
      simp only [hf] at h ⊢
      match ha : evalArgs env args with
      | none => simp [ha] at h
      | some vals =>
        simp only [ha] at h ⊢
        match hbody : evalMicroC fuel (buildCallEnv fdef.params vals) fdef.body with
        | some (.return_ (some v), benv) =>
          simp [hbody] at h
          have hbody' := evalMicroC_fuel_mono_full hbody hle (by intro h; cases h)
          simp [hbody']; exact h
        | some (.return_ none, benv) =>
          simp [hbody] at h
          have hbody' := evalMicroC_fuel_mono_full hbody hle (by intro h; cases h)
          simp [hbody']; exact h
        | some (.normal, benv) =>
          simp [hbody] at h
          have hbody' := evalMicroC_fuel_mono_full hbody hle (by intro h; cases h)
          simp [hbody']; exact h
        | some (.outOfFuel, benv) =>
          simp [hbody] at h; exact absurd h.1.symm hoc
        | some (.break_, benv) =>
          simp [hbody] at h
        | some (.continue_, benv) =>
          simp [hbody] at h
        | none =>
          simp [hbody] at h
  | seq s1 s2 ih1 ih2 =>
    exact fun h hle hoc => fuel_mono_seq_wc fenv ih1 ih2 h hle hoc
  | ite c t e iht ihe =>
    intro fuel fuel' env env' oc h hle hoc
    match hcond : evalMicroCExpr env c with
    | some (.bool true) =>
      simp only [evalMicroC_withCalls, hcond] at h ⊢; exact iht h hle hoc
    | some (.bool false) =>
      simp only [evalMicroC_withCalls, hcond] at h ⊢; exact ihe h hle hoc
    | some (.int _) =>
      simp [evalMicroC_withCalls, hcond] at h
    | none =>
      simp [evalMicroC_withCalls, hcond] at h
  | while_ c body ih =>
    exact fun h hle hoc => fuel_mono_while_wc fenv ih h hle hoc

/-! ## Public API -/

/-- Fuel monotonicity: if evalMicroC_withCalls succeeds with `oc ≠ outOfFuel` at fuel f,
    it produces the same result at any fuel f' ≥ f. -/
theorem evalMicroC_withCalls_fuel_mono_full (fenv : MicroCFuncEnv)
    {fuel fuel' : Nat} {env env' : MicroCEnv} {stmt : MicroCStmt} {oc : Outcome}
    (h : evalMicroC_withCalls fenv fuel env stmt = some (oc, env'))
    (hle : fuel ≤ fuel') (hoc : oc ≠ .outOfFuel) :
    evalMicroC_withCalls fenv fuel' env stmt = some (oc, env') :=
  evalMicroC_withCalls_fuel_mono_gen fenv stmt h hle hoc

/-- Fuel monotonicity specialized to normal outcomes. -/
theorem evalMicroC_withCalls_fuel_mono (fenv : MicroCFuncEnv)
    {fuel fuel' : Nat} {env : MicroCEnv} {stmt : MicroCStmt}
    {env' : MicroCEnv}
    (h : evalMicroC_withCalls fenv fuel env stmt = some (.normal, env'))
    (hle : fuel ≤ fuel') :
    evalMicroC_withCalls fenv fuel' env stmt = some (.normal, env') :=
  evalMicroC_withCalls_fuel_mono_full fenv h hle (by decide)

/-! ## Smoke Tests -/

-- Smoke test: simple function call. inc(x) = return x + 1; result = inc(5).
#eval do
  let fdef : MicroCFuncDef := ⟨["x"], .return_ (some (.binOp .add (.varRef "x") (.litInt 1)))⟩
  let fenv := MicroCFuncEnv.default.update "inc" fdef
  let stmt := MicroCStmt.call "result" "inc" [.litInt 5]
  let r ← evalMicroC_withCalls fenv 10 MicroCEnv.default stmt
  pure (r.1, r.2 "result")

-- Smoke test: multi-arg function. add(a, b) = return a + b; r = add(3, 4).
#eval do
  let fdef : MicroCFuncDef := ⟨["a", "b"],
    .return_ (some (.binOp .add (.varRef "a") (.varRef "b")))⟩
  let fenv := MicroCFuncEnv.default.update "add" fdef
  let stmt := MicroCStmt.call "r" "add" [.litInt 3, .litInt 4]
  let r ← evalMicroC_withCalls fenv 10 MicroCEnv.default stmt
  pure (r.1, r.2 "r")

-- Smoke test: call-free program produces same result as evalMicroC.
#eval do
  let fenv := MicroCFuncEnv.default
  let stmt := MicroCStmt.assign "x" (.binOp .add (.litInt 3) (.litInt 4))
  let r1 ← evalMicroC_withCalls fenv 10 MicroCEnv.default stmt
  let r2 ← evalMicroC 10 MicroCEnv.default stmt
  pure (r1.2 "x", r2.2 "x")

-- Smoke test: undefined function returns none.
#eval
  let fenv := MicroCFuncEnv.default
  let stmt := MicroCStmt.call "r" "nonexistent" []
  (evalMicroC_withCalls fenv 10 MicroCEnv.default stmt).isSome

/-! ## Non-Vacuity -/

/-- Non-vacuity: function call evaluates correctly.
    inc(5) produces result = 6. -/
example :
    let fdef : MicroCFuncDef := ⟨["x"], .return_ (some (.binOp .add (.varRef "x") (.litInt 1)))⟩
    let fenv := MicroCFuncEnv.default.update "inc" fdef
    let stmt := MicroCStmt.call "result" "inc" [.litInt 5]
    (do let (_, e) ← evalMicroC_withCalls fenv 10 MicroCEnv.default stmt; pure (e "result")) =
    some (.int 6) := by native_decide

/-- Non-vacuity: call-free program agrees with evalMicroC.
    x = 3 + 4 produces x = 7 in both evaluators. -/
example :
    let fenv := MicroCFuncEnv.default
    let stmt := MicroCStmt.assign "x" (.binOp .add (.litInt 3) (.litInt 4))
    (do let (_, e) ← evalMicroC_withCalls fenv 10 MicroCEnv.default stmt; pure (e "x")) =
    some (.int 7) ∧
    (do let (_, e) ← evalMicroC 10 MicroCEnv.default stmt; pure (e "x")) =
    some (.int 7) := by
  constructor <;> native_decide

/-- Non-vacuity: multi-arg function call. add(3, 4) = 7. -/
example :
    let fdef : MicroCFuncDef := ⟨["a", "b"],
      .return_ (some (.binOp .add (.varRef "a") (.varRef "b")))⟩
    let fenv := MicroCFuncEnv.default.update "add" fdef
    let stmt := MicroCStmt.call "r" "add" [.litInt 3, .litInt 4]
    (do let (_, e) ← evalMicroC_withCalls fenv 10 MicroCEnv.default stmt; pure (e "r")) =
    some (.int 7) := by native_decide

/-- Non-vacuity: program with loop + call. -/
example :
    let incDef : MicroCFuncDef := ⟨["x"],
      .return_ (some (.binOp .add (.varRef "x") (.litInt 1)))⟩
    let fenv := MicroCFuncEnv.default.update "inc" incDef
    let prog := MicroCStmt.seq
      (MicroCStmt.assign "x" (.litInt 0))
      (MicroCStmt.seq
        (MicroCStmt.call "x" "inc" [.varRef "x"])
        (MicroCStmt.call "x" "inc" [.varRef "x"]))
    (do let (_, e) ← evalMicroC_withCalls fenv 10 MicroCEnv.default prog; pure (e "x")) =
    some (.int 2) := by native_decide

end TrustLean
