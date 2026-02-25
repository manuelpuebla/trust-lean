/-
  Trust-Lean — Verified Code Generation Framework
  Core/FuelMono.lean: Fuel monotonicity theorem (GATE for Fase 1)

  N1.5: CRITICO GATE — proves that if evaluation succeeds with fuel f,
  it succeeds with any fuel f' ≥ f producing the same result.

  Proof strategy (adapted from LeanScribe/Correctness.lean:310-372):
  1. Generalized version: holds for ALL non-outOfFuel outcomes (not just normal)
  2. While helper: separated out with nested fuel induction + body IH parameter
  3. Main proof: structural induction on Stmt, delegates while to helper
  4. for_ case: constructs seq IH from body+step IHs, then uses while helper
  5. Public theorem: specializes gen to Outcome.normal

  Complexity budget: < 200 lines (BENCHMARKS.md rubric)
-/

import TrustLean.Core.Foundation

set_option autoImplicit false

namespace TrustLean

/-! ## Helper: Seq fuel monotonicity from sub-term IHs -/

/-- Build fuel monotonicity for (seq s1 s2) given IHs for s1 and s2.
    Extracted as a helper because it's used by both the seq and for_ cases. -/
private theorem fuel_mono_seq
    {s1 s2 : Stmt}
    (ih1 : ∀ {fuel fuel' : Nat} {env env' : LowLevelEnv} {oc : Outcome},
      evalStmt fuel env s1 = some (oc, env') → fuel ≤ fuel' → oc ≠ .outOfFuel →
      evalStmt fuel' env s1 = some (oc, env'))
    (ih2 : ∀ {fuel fuel' : Nat} {env env' : LowLevelEnv} {oc : Outcome},
      evalStmt fuel env s2 = some (oc, env') → fuel ≤ fuel' → oc ≠ .outOfFuel →
      evalStmt fuel' env s2 = some (oc, env'))
    {fuel fuel' : Nat} {env env' : LowLevelEnv} {oc : Outcome}
    (h : evalStmt fuel env (.seq s1 s2) = some (oc, env'))
    (hle : fuel ≤ fuel')
    (hoc : oc ≠ .outOfFuel) :
    evalStmt fuel' env (.seq s1 s2) = some (oc, env') := by
  simp only [evalStmt_seq] at h ⊢
  generalize hm : evalStmt fuel env s1 = r at h
  cases r with
  | none => simp at h
  | some p =>
    cases p with
    | mk o e_mid =>
      cases o with
      | normal => simp only [ih1 hm hle (by simp)]; exact ih2 h hle hoc
      | break_ => simp only [ih1 hm hle (by simp)]; exact h
      | continue_ => simp only [ih1 hm hle (by simp)]; exact h
      | return_ rv => simp only [ih1 hm hle (by simp)]; exact h
      | outOfFuel =>
        simp only [] at h
        have : oc = .outOfFuel := by
          have := Option.some.inj h; exact (congrArg Prod.fst this).symm
        exact absurd this hoc

/-! ## While Helper -/

/-- Fuel monotonicity for while loops, with nested induction on fuel.
    Parameterized by body's fuel mono IH for composability with for_. -/
private theorem fuel_mono_while
    (cond : LowLevelExpr) (body : Stmt)
    (ih_body : ∀ {fuel fuel' : Nat} {env env' : LowLevelEnv} {oc : Outcome},
      evalStmt fuel env body = some (oc, env') → fuel ≤ fuel' → oc ≠ .outOfFuel →
      evalStmt fuel' env body = some (oc, env'))
    {fuel : Nat} :
    ∀ {fuel' : Nat} {env env' : LowLevelEnv} {oc : Outcome},
    evalStmt fuel env (.while cond body) = some (oc, env') →
    fuel ≤ fuel' →
    oc ≠ .outOfFuel →
    evalStmt fuel' env (.while cond body) = some (oc, env') := by
  induction fuel with
  | zero =>
    intro fuel' env env' oc h _ hoc
    simp only [evalStmt_while_zero] at h
    have : oc = .outOfFuel := by
      have := Option.some.inj h; exact (congrArg Prod.fst this).symm
    exact absurd this hoc
  | succ n ih_fuel =>
    intro fuel' env env' oc h hle hoc
    obtain ⟨m, rfl⟩ : ∃ m, fuel' = m + 1 := ⟨fuel' - 1, by omega⟩
    have hnm : n ≤ m := by omega
    simp only [evalStmt_while_succ] at h ⊢
    -- Case split on condition
    generalize hc : evalExpr env cond = c at h ⊢
    cases c with
    | none => simp at h
    | some v =>
      cases v with
      | int _ => simp at h
      | bool b =>
        cases b with
        | false => exact h
        | true =>
          -- Case split on body result
          generalize hb : evalStmt n env body = rb at h
          cases rb with
          | none => simp at h
          | some p =>
            cases p with
            | mk ob e_mid =>
              cases ob with
              | normal =>
                simp only [ih_body hb hnm (by simp)]; exact ih_fuel h hnm hoc
              | continue_ =>
                simp only [ih_body hb hnm (by simp)]; exact ih_fuel h hnm hoc
              | break_ =>
                simp only [ih_body hb hnm (by simp)]; exact h
              | return_ rv =>
                simp only [ih_body hb hnm (by simp)]; exact h
              | outOfFuel =>
                simp only [] at h
                have : oc = .outOfFuel := by
                  have := Option.some.inj h; exact (congrArg Prod.fst this).symm
                exact absurd this hoc

/-! ## Main Theorem: Generalized Fuel Monotonicity -/

private theorem evalStmt_fuel_mono_gen (stmt : Stmt) :
    ∀ {fuel fuel' : Nat} {env env' : LowLevelEnv} {oc : Outcome},
    evalStmt fuel env stmt = some (oc, env') →
    fuel ≤ fuel' →
    oc ≠ .outOfFuel →
    evalStmt fuel' env stmt = some (oc, env') := by
  induction stmt with
  | skip => intro _ _ _ _ _ h _ _; simp_all
  | break_ => intro _ _ _ _ _ h _ _; simp_all
  | continue_ => intro _ _ _ _ _ h _ _; simp_all
  | return_ _ => intro fuel fuel' _ _ _ h _ _; rw [evalStmt_return_fuel_indep fuel fuel'] at h; exact h
  | assign _ _ => intro fuel fuel' _ _ _ h _ _; rw [evalStmt_assign_fuel_indep fuel fuel'] at h; exact h
  | store _ _ _ => intro fuel fuel' _ _ _ h _ _; rw [evalStmt_store_fuel_indep fuel fuel'] at h; exact h
  | load _ _ _ => intro fuel fuel' _ _ _ h _ _; rw [evalStmt_load_fuel_indep fuel fuel'] at h; exact h
  | call _ _ _ => intro fuel fuel' _ _ _ h _ _; rw [evalStmt_call_fuel_indep fuel fuel'] at h; exact h
  | ite cond thenB elseB ih_then ih_else =>
    intro fuel fuel' env env' oc h hle hoc
    simp only [evalStmt_ite] at h ⊢
    generalize hc : evalExpr env cond = c at h ⊢
    cases c with
    | none => simp at h
    | some v =>
      cases v with
      | int _ => simp at h
      | bool b =>
        cases b with
        | true => exact ih_then h hle hoc
        | false => exact ih_else h hle hoc
  | seq s1 s2 ih1 ih2 => exact fuel_mono_seq ih1 ih2
  | «while» cond body ih_body => exact fuel_mono_while cond body ih_body
  | for_ init cond step body ih_init ih_step ih_body =>
    intro fuel fuel' env env' oc h hle hoc
    cases fuel with
    | zero =>
      simp only [evalStmt_for_zero] at h
      have : oc = .outOfFuel := by
        have := Option.some.inj h; exact (congrArg Prod.fst this).symm
      exact absurd this hoc
    | succ n =>
      cases fuel' with
      | zero => omega
      | succ m =>
        have hnm : n ≤ m := by omega
        simp only [evalStmt_for_succ] at h ⊢
        -- Build fuel mono for (.seq body step) from sub-term IHs
        have ih_seq := @fuel_mono_seq body step ih_body ih_step
        -- Case split on init result
        generalize hm : evalStmt n env init = r at h
        cases r with
        | none => simp at h
        | some p =>
          cases p with
          | mk oi e_mid =>
            cases oi with
            | normal =>
              simp only [ih_init hm hnm (by simp)]
              exact fuel_mono_while cond (.seq body step) ih_seq h hnm hoc
            | break_ => simp only [ih_init hm hnm (by simp)]; exact h
            | continue_ => simp only [ih_init hm hnm (by simp)]; exact h
            | return_ rv => simp only [ih_init hm hnm (by simp)]; exact h
            | outOfFuel =>
              simp only [] at h
              have : oc = .outOfFuel := by
                have := Option.some.inj h; exact (congrArg Prod.fst this).symm
              exact absurd this hoc

/-! ## Public API -/

/-- Fuel monotonicity: if evaluation succeeds with outcome `oc ≠ outOfFuel` at fuel f,
    it produces the same result at any fuel f' ≥ f.
    This is the GATE theorem for Fase 1 — all downstream proofs depend on it. -/
theorem evalStmt_fuel_mono_full {fuel fuel' : Nat} {env : LowLevelEnv} {stmt : Stmt}
    {env' : LowLevelEnv} {oc : Outcome}
    (h : evalStmt fuel env stmt = some (oc, env'))
    (hle : fuel ≤ fuel')
    (hoc : oc ≠ .outOfFuel) :
    evalStmt fuel' env stmt = some (oc, env') :=
  evalStmt_fuel_mono_gen stmt h hle hoc

/-- Fuel monotonicity specialized to normal outcomes.
    The most commonly used form in frontend correctness proofs. -/
theorem evalStmt_fuel_mono {fuel fuel' : Nat} {env : LowLevelEnv} {stmt : Stmt}
    {env' : LowLevelEnv}
    (h : evalStmt fuel env stmt = some (.normal, env'))
    (hle : fuel ≤ fuel') :
    evalStmt fuel' env stmt = some (.normal, env') :=
  evalStmt_fuel_mono_full h hle (by simp)

end TrustLean
