/-
  Trust-Lean — Verified Code Generation Framework
  MicroC/FuelMono.lean: Fuel monotonicity theorem for MicroC evaluator

  N10.3 (v2.0.0): CRITICO GATE — proves that if evalMicroC succeeds with
  fuel f producing outcome ≠ outOfFuel, it succeeds with any fuel f' ≥ f
  producing the same result.

  Proof strategy (mirroring Core/FuelMono.lean):
  1. fuel_mono_seq_mc: builds seq case from sub-term IHs
  2. fuel_mono_while_mc: nested fuel induction + body IH parameter
  3. evalMicroC_fuel_mono_gen: structural induction on MicroCStmt
  4. Public API: evalMicroC_fuel_mono_full + evalMicroC_fuel_mono

  Simpler than Core version — no for_ case (MicroC desugars for to seq+while).
-/

import TrustLean.MicroC.Eval

set_option autoImplicit false

namespace TrustLean

/-! ## Helper: Seq fuel monotonicity from sub-term IHs -/

/-- Build fuel monotonicity for (seq s1 s2) given IHs for s1 and s2. -/
private theorem fuel_mono_seq_mc
    {s1 s2 : MicroCStmt}
    (ih1 : ∀ {fuel fuel' : Nat} {env env' : MicroCEnv} {oc : Outcome},
      evalMicroC fuel env s1 = some (oc, env') → fuel ≤ fuel' → oc ≠ .outOfFuel →
      evalMicroC fuel' env s1 = some (oc, env'))
    (ih2 : ∀ {fuel fuel' : Nat} {env env' : MicroCEnv} {oc : Outcome},
      evalMicroC fuel env s2 = some (oc, env') → fuel ≤ fuel' → oc ≠ .outOfFuel →
      evalMicroC fuel' env s2 = some (oc, env'))
    {fuel fuel' : Nat} {env env' : MicroCEnv} {oc : Outcome}
    (h : evalMicroC fuel env (.seq s1 s2) = some (oc, env'))
    (hle : fuel ≤ fuel')
    (hoc : oc ≠ .outOfFuel) :
    evalMicroC fuel' env (.seq s1 s2) = some (oc, env') := by
  simp only [evalMicroC_seq] at h ⊢
  generalize hm : evalMicroC fuel env s1 = r at h
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

/-- Fuel monotonicity for MicroC while loops, with nested induction on fuel. -/
private theorem fuel_mono_while_mc
    (cond : MicroCExpr) (body : MicroCStmt)
    (ih_body : ∀ {fuel fuel' : Nat} {env env' : MicroCEnv} {oc : Outcome},
      evalMicroC fuel env body = some (oc, env') → fuel ≤ fuel' → oc ≠ .outOfFuel →
      evalMicroC fuel' env body = some (oc, env'))
    {fuel : Nat} :
    ∀ {fuel' : Nat} {env env' : MicroCEnv} {oc : Outcome},
    evalMicroC fuel env (.while_ cond body) = some (oc, env') →
    fuel ≤ fuel' →
    oc ≠ .outOfFuel →
    evalMicroC fuel' env (.while_ cond body) = some (oc, env') := by
  induction fuel with
  | zero =>
    intro fuel' env env' oc h _ hoc
    simp only [evalMicroC_while_zero] at h
    have : oc = .outOfFuel := by
      have := Option.some.inj h; exact (congrArg Prod.fst this).symm
    exact absurd this hoc
  | succ n ih_fuel =>
    intro fuel' env env' oc h hle hoc
    obtain ⟨m, rfl⟩ : ∃ m, fuel' = m + 1 := ⟨fuel' - 1, by omega⟩
    have hnm : n ≤ m := by omega
    simp only [evalMicroC_while_succ] at h ⊢
    generalize hc : evalMicroCExpr env cond = c at h ⊢
    cases c with
    | none => simp at h
    | some v =>
      cases v with
      | int _ => simp at h
      | bool b =>
        cases b with
        | false => exact h
        | true =>
          generalize hb : evalMicroC n env body = rb at h
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

/-- Fuel monotonicity for all MicroC statements, generalized to all outcomes. -/
private theorem evalMicroC_fuel_mono_gen (stmt : MicroCStmt) :
    ∀ {fuel fuel' : Nat} {env env' : MicroCEnv} {oc : Outcome},
    evalMicroC fuel env stmt = some (oc, env') →
    fuel ≤ fuel' →
    oc ≠ .outOfFuel →
    evalMicroC fuel' env stmt = some (oc, env') := by
  induction stmt with
  | skip => intro _ _ _ _ _ h _ _; simp_all
  | break_ => intro _ _ _ _ _ h _ _; simp_all
  | continue_ => intro _ _ _ _ _ h _ _; simp_all
  | return_ re =>
    intro fuel fuel' env env' oc h _ _
    cases re with
    | none => simp at h ⊢; exact h
    | some e => simp only [evalMicroC_return_some] at h ⊢; exact h
  | assign name expr =>
    intro fuel fuel' env env' oc h _ _
    simp only [evalMicroC_assign] at h ⊢; exact h
  | store base idx val =>
    intro fuel fuel' env env' oc h _ _
    simp [evalMicroC] at h ⊢; exact h
  | load var base idx =>
    intro fuel fuel' env env' oc h _ _
    simp [evalMicroC] at h ⊢; exact h
  | call f r args =>
    intro fuel fuel' env env' oc h _ _
    simp [evalMicroC] at h
  | ite cond thenB elseB ih_then ih_else =>
    intro fuel fuel' env env' oc h hle hoc
    simp only [evalMicroC_ite] at h ⊢
    generalize hc : evalMicroCExpr env cond = c at h ⊢
    cases c with
    | none => simp at h
    | some v =>
      cases v with
      | int _ => simp at h
      | bool b =>
        cases b with
        | true => exact ih_then h hle hoc
        | false => exact ih_else h hle hoc
  | seq s1 s2 ih1 ih2 => exact fuel_mono_seq_mc ih1 ih2
  | while_ cond body ih_body => exact fuel_mono_while_mc cond body ih_body

/-! ## Public API -/

/-- Fuel monotonicity: if evalMicroC succeeds with outcome `oc ≠ outOfFuel` at fuel f,
    it produces the same result at any fuel f' ≥ f.
    GATE theorem for MicroC — all downstream simulation proofs depend on it. -/
theorem evalMicroC_fuel_mono_full {fuel fuel' : Nat} {env : MicroCEnv} {stmt : MicroCStmt}
    {env' : MicroCEnv} {oc : Outcome}
    (h : evalMicroC fuel env stmt = some (oc, env'))
    (hle : fuel ≤ fuel')
    (hoc : oc ≠ .outOfFuel) :
    evalMicroC fuel' env stmt = some (oc, env') :=
  evalMicroC_fuel_mono_gen stmt h hle hoc

/-- Fuel monotonicity specialized to normal outcomes.
    Most commonly used form in simulation proofs. -/
theorem evalMicroC_fuel_mono {fuel fuel' : Nat} {env : MicroCEnv} {stmt : MicroCStmt}
    {env' : MicroCEnv}
    (h : evalMicroC fuel env stmt = some (.normal, env'))
    (hle : fuel ≤ fuel') :
    evalMicroC fuel' env stmt = some (.normal, env') :=
  evalMicroC_fuel_mono_full h hle (by simp)

end TrustLean
