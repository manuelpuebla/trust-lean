/-
  Trust-Lean v3.1 — Unsigned Fuel Monotonicity
  H1 fix: Proves evalMicroC_uint32/64_fuel_mono_full.

  Structure mirrors FuelMono.lean exactly (L-625).
  Uses `simp [evalMicroC_uint32]` to unfold the evaluator directly
  rather than relying on separate equation lemmas.
-/
import TrustLean.MicroC.UnsignedEval

set_option autoImplicit false

namespace TrustLean

/-! ## UInt32 equation lemmas for fuel-independent cases -/

private theorem evalMicroC_uint32_eq_return (fuel : Nat) (env : MicroCEnv) (re : Option MicroCExpr) :
    evalMicroC_uint32 fuel env (.return_ re) =
    (match re with
    | some e => match evalMicroCExpr_uint32 env e with
      | some v => some (.return_ (some v), env)
      | none => none
    | none => some (.return_ none, env)) := by
  unfold evalMicroC_uint32; rfl

private theorem evalMicroC_uint32_eq_assign (fuel : Nat) (env : MicroCEnv) (name : String) (expr : MicroCExpr) :
    evalMicroC_uint32 fuel env (.assign name expr) =
    (match evalMicroCExpr_uint32 env expr with
    | some v => some (.normal, env.update name v)
    | none => none) := by
  unfold evalMicroC_uint32; rfl

private theorem evalMicroC_uint32_eq_store (fuel : Nat) (env : MicroCEnv) (base idx val : MicroCExpr) :
    evalMicroC_uint32 fuel env (.store base idx val) =
    (match getMicroCArrayName' base, evalMicroCExpr_uint32 env idx, evalMicroCExpr_uint32 env val with
    | some name, some (.int i), some v =>
      some (.normal, env.update (name ++ "[" ++ toString i ++ "]") v)
    | _, _, _ => none) := by
  unfold evalMicroC_uint32; rfl

private theorem evalMicroC_uint32_eq_load (fuel : Nat) (env : MicroCEnv) (var : String) (base idx : MicroCExpr) :
    evalMicroC_uint32 fuel env (.load var base idx) =
    (match getMicroCArrayName' base, evalMicroCExpr_uint32 env idx with
    | some name, some (.int i) =>
      some (.normal, env.update var (env (name ++ "[" ++ toString i ++ "]")))
    | _, _ => none) := by
  unfold evalMicroC_uint32; rfl

private theorem evalMicroC_uint32_eq_call (fuel : Nat) (env : MicroCEnv) (r f : String) (args : List MicroCExpr) :
    evalMicroC_uint32 fuel env (.call r f args) = none := by
  unfold evalMicroC_uint32; rfl

/-! ## UInt32 Fuel Monotonicity -/

private theorem fuel_mono_seq_uint32
    {s1 s2 : MicroCStmt}
    (ih1 : ∀ {fuel fuel' : Nat} {env env' : MicroCEnv} {oc : Outcome},
      evalMicroC_uint32 fuel env s1 = some (oc, env') → fuel ≤ fuel' → oc ≠ .outOfFuel →
      evalMicroC_uint32 fuel' env s1 = some (oc, env'))
    (ih2 : ∀ {fuel fuel' : Nat} {env env' : MicroCEnv} {oc : Outcome},
      evalMicroC_uint32 fuel env s2 = some (oc, env') → fuel ≤ fuel' → oc ≠ .outOfFuel →
      evalMicroC_uint32 fuel' env s2 = some (oc, env'))
    {fuel fuel' : Nat} {env env' : MicroCEnv} {oc : Outcome}
    (h : evalMicroC_uint32 fuel env (.seq s1 s2) = some (oc, env'))
    (hle : fuel ≤ fuel')
    (hoc : oc ≠ .outOfFuel) :
    evalMicroC_uint32 fuel' env (.seq s1 s2) = some (oc, env') := by
  simp only [evalMicroC_uint32] at h ⊢
  generalize hm : evalMicroC_uint32 fuel env s1 = r at h
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

private theorem fuel_mono_while_uint32
    (cond : MicroCExpr) (body : MicroCStmt)
    (ih_body : ∀ {fuel fuel' : Nat} {env env' : MicroCEnv} {oc : Outcome},
      evalMicroC_uint32 fuel env body = some (oc, env') → fuel ≤ fuel' → oc ≠ .outOfFuel →
      evalMicroC_uint32 fuel' env body = some (oc, env'))
    {fuel : Nat} :
    ∀ {fuel' : Nat} {env env' : MicroCEnv} {oc : Outcome},
    evalMicroC_uint32 fuel env (.while_ cond body) = some (oc, env') →
    fuel ≤ fuel' →
    oc ≠ .outOfFuel →
    evalMicroC_uint32 fuel' env (.while_ cond body) = some (oc, env') := by
  induction fuel with
  | zero =>
    intro fuel' env env' oc h _ hoc
    simp only [evalMicroC_uint32] at h
    have : oc = .outOfFuel := by
      have := Option.some.inj h; exact (congrArg Prod.fst this).symm
    exact absurd this hoc
  | succ n ih_fuel =>
    intro fuel' env env' oc h hle hoc
    obtain ⟨m, rfl⟩ : ∃ m, fuel' = m + 1 := ⟨fuel' - 1, by omega⟩
    have hnm : n ≤ m := by omega
    simp only [evalMicroC_uint32] at h ⊢
    generalize hc : evalMicroCExpr_uint32 env cond = c at h ⊢
    cases c with
    | none => simp at h
    | some v =>
      cases v with
      | int _ => simp at h
      | bool b =>
        cases b with
        | false => exact h
        | true =>
          generalize hb : evalMicroC_uint32 n env body = rb at h
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

private theorem evalMicroC_uint32_fuel_mono_gen (stmt : MicroCStmt) :
    ∀ {fuel fuel' : Nat} {env env' : MicroCEnv} {oc : Outcome},
    evalMicroC_uint32 fuel env stmt = some (oc, env') →
    fuel ≤ fuel' →
    oc ≠ .outOfFuel →
    evalMicroC_uint32 fuel' env stmt = some (oc, env') := by
  induction stmt with
  | skip => intro _ _ _ _ _ h _ _; simp_all
  | break_ => intro _ _ _ _ _ h _ _; simp_all [evalMicroC_uint32]
  | continue_ => intro _ _ _ _ _ h _ _; simp_all [evalMicroC_uint32]
  | return_ re =>
    intro fuel fuel' env env' oc h _ _
    simp only [evalMicroC_uint32_eq_return] at h ⊢; exact h
  | assign name expr =>
    intro fuel fuel' env env' oc h _ _
    simp only [evalMicroC_uint32_eq_assign] at h ⊢; exact h
  | store base idx val =>
    intro fuel fuel' env env' oc h _ _
    simp only [evalMicroC_uint32_eq_store] at h ⊢; exact h
  | load var base idx =>
    intro fuel fuel' env env' oc h _ _
    simp only [evalMicroC_uint32_eq_load] at h ⊢; exact h
  | call f r args =>
    intro fuel fuel' env env' oc h _ _
    simp only [evalMicroC_uint32_eq_call] at h; cases h
  | ite cond thenB elseB ih_then ih_else =>
    intro fuel fuel' env env' oc h hle hoc
    simp only [evalMicroC_uint32] at h ⊢
    generalize hc : evalMicroCExpr_uint32 env cond = c at h ⊢
    cases c with
    | none => simp at h
    | some v =>
      cases v with
      | int _ => simp at h
      | bool b =>
        cases b with
        | true => exact ih_then h hle hoc
        | false => exact ih_else h hle hoc
  | seq s1 s2 ih1 ih2 => exact fuel_mono_seq_uint32 ih1 ih2
  | while_ cond body ih_body => exact fuel_mono_while_uint32 cond body ih_body

/-! ## UInt32 Public API -/

/-- Fuel monotonicity for UInt32: if evalMicroC_uint32 succeeds with outcome oc ≠ outOfFuel
    at fuel f, it produces the same result at any fuel f' ≥ f. -/
theorem evalMicroC_uint32_fuel_mono_full {fuel fuel' : Nat} {env : MicroCEnv} {stmt : MicroCStmt}
    {env' : MicroCEnv} {oc : Outcome}
    (h : evalMicroC_uint32 fuel env stmt = some (oc, env'))
    (hle : fuel ≤ fuel')
    (hoc : oc ≠ .outOfFuel) :
    evalMicroC_uint32 fuel' env stmt = some (oc, env') :=
  evalMicroC_uint32_fuel_mono_gen stmt h hle hoc

/-- Fuel monotonicity specialized to normal outcomes (UInt32). -/
theorem evalMicroC_uint32_fuel_mono {fuel fuel' : Nat} {env : MicroCEnv} {stmt : MicroCStmt}
    {env' : MicroCEnv}
    (h : evalMicroC_uint32 fuel env stmt = some (.normal, env'))
    (hle : fuel ≤ fuel') :
    evalMicroC_uint32 fuel' env stmt = some (.normal, env') :=
  evalMicroC_uint32_fuel_mono_full h hle (by simp)

/-! ## UInt64 equation lemmas -/

private theorem evalMicroC_uint64_eq_return (fuel : Nat) (env : MicroCEnv) (re : Option MicroCExpr) :
    evalMicroC_uint64 fuel env (.return_ re) =
    (match re with
    | some e => match evalMicroCExpr_uint64 env e with
      | some v => some (.return_ (some v), env)
      | none => none
    | none => some (.return_ none, env)) := by
  unfold evalMicroC_uint64; rfl

private theorem evalMicroC_uint64_eq_assign (fuel : Nat) (env : MicroCEnv) (name : String) (expr : MicroCExpr) :
    evalMicroC_uint64 fuel env (.assign name expr) =
    (match evalMicroCExpr_uint64 env expr with
    | some v => some (.normal, env.update name v)
    | none => none) := by
  unfold evalMicroC_uint64; rfl

private theorem evalMicroC_uint64_eq_store (fuel : Nat) (env : MicroCEnv) (base idx val : MicroCExpr) :
    evalMicroC_uint64 fuel env (.store base idx val) =
    (match getMicroCArrayName' base, evalMicroCExpr_uint64 env idx, evalMicroCExpr_uint64 env val with
    | some name, some (.int i), some v =>
      some (.normal, env.update (name ++ "[" ++ toString i ++ "]") v)
    | _, _, _ => none) := by
  unfold evalMicroC_uint64; rfl

private theorem evalMicroC_uint64_eq_load (fuel : Nat) (env : MicroCEnv) (var : String) (base idx : MicroCExpr) :
    evalMicroC_uint64 fuel env (.load var base idx) =
    (match getMicroCArrayName' base, evalMicroCExpr_uint64 env idx with
    | some name, some (.int i) =>
      some (.normal, env.update var (env (name ++ "[" ++ toString i ++ "]")))
    | _, _ => none) := by
  unfold evalMicroC_uint64; rfl

private theorem evalMicroC_uint64_eq_call (fuel : Nat) (env : MicroCEnv) (r f : String) (args : List MicroCExpr) :
    evalMicroC_uint64 fuel env (.call r f args) = none := by
  unfold evalMicroC_uint64; rfl

/-! ## UInt64 Fuel Monotonicity -/

private theorem fuel_mono_seq_uint64
    {s1 s2 : MicroCStmt}
    (ih1 : ∀ {fuel fuel' : Nat} {env env' : MicroCEnv} {oc : Outcome},
      evalMicroC_uint64 fuel env s1 = some (oc, env') → fuel ≤ fuel' → oc ≠ .outOfFuel →
      evalMicroC_uint64 fuel' env s1 = some (oc, env'))
    (ih2 : ∀ {fuel fuel' : Nat} {env env' : MicroCEnv} {oc : Outcome},
      evalMicroC_uint64 fuel env s2 = some (oc, env') → fuel ≤ fuel' → oc ≠ .outOfFuel →
      evalMicroC_uint64 fuel' env s2 = some (oc, env'))
    {fuel fuel' : Nat} {env env' : MicroCEnv} {oc : Outcome}
    (h : evalMicroC_uint64 fuel env (.seq s1 s2) = some (oc, env'))
    (hle : fuel ≤ fuel')
    (hoc : oc ≠ .outOfFuel) :
    evalMicroC_uint64 fuel' env (.seq s1 s2) = some (oc, env') := by
  simp only [evalMicroC_uint64] at h ⊢
  generalize hm : evalMicroC_uint64 fuel env s1 = r at h
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

private theorem fuel_mono_while_uint64
    (cond : MicroCExpr) (body : MicroCStmt)
    (ih_body : ∀ {fuel fuel' : Nat} {env env' : MicroCEnv} {oc : Outcome},
      evalMicroC_uint64 fuel env body = some (oc, env') → fuel ≤ fuel' → oc ≠ .outOfFuel →
      evalMicroC_uint64 fuel' env body = some (oc, env'))
    {fuel : Nat} :
    ∀ {fuel' : Nat} {env env' : MicroCEnv} {oc : Outcome},
    evalMicroC_uint64 fuel env (.while_ cond body) = some (oc, env') →
    fuel ≤ fuel' →
    oc ≠ .outOfFuel →
    evalMicroC_uint64 fuel' env (.while_ cond body) = some (oc, env') := by
  induction fuel with
  | zero =>
    intro fuel' env env' oc h _ hoc
    simp only [evalMicroC_uint64] at h
    have : oc = .outOfFuel := by
      have := Option.some.inj h; exact (congrArg Prod.fst this).symm
    exact absurd this hoc
  | succ n ih_fuel =>
    intro fuel' env env' oc h hle hoc
    obtain ⟨m, rfl⟩ : ∃ m, fuel' = m + 1 := ⟨fuel' - 1, by omega⟩
    have hnm : n ≤ m := by omega
    simp only [evalMicroC_uint64] at h ⊢
    generalize hc : evalMicroCExpr_uint64 env cond = c at h ⊢
    cases c with
    | none => simp at h
    | some v =>
      cases v with
      | int _ => simp at h
      | bool b =>
        cases b with
        | false => exact h
        | true =>
          generalize hb : evalMicroC_uint64 n env body = rb at h
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

private theorem evalMicroC_uint64_fuel_mono_gen (stmt : MicroCStmt) :
    ∀ {fuel fuel' : Nat} {env env' : MicroCEnv} {oc : Outcome},
    evalMicroC_uint64 fuel env stmt = some (oc, env') →
    fuel ≤ fuel' →
    oc ≠ .outOfFuel →
    evalMicroC_uint64 fuel' env stmt = some (oc, env') := by
  induction stmt with
  | skip => intro _ _ _ _ _ h _ _; simp_all
  | break_ => intro _ _ _ _ _ h _ _; simp_all [evalMicroC_uint64]
  | continue_ => intro _ _ _ _ _ h _ _; simp_all [evalMicroC_uint64]
  | return_ re =>
    intro fuel fuel' env env' oc h _ _
    simp only [evalMicroC_uint64_eq_return] at h ⊢; exact h
  | assign name expr =>
    intro fuel fuel' env env' oc h _ _
    simp only [evalMicroC_uint64_eq_assign] at h ⊢; exact h
  | store base idx val =>
    intro fuel fuel' env env' oc h _ _
    simp only [evalMicroC_uint64_eq_store] at h ⊢; exact h
  | load var base idx =>
    intro fuel fuel' env env' oc h _ _
    simp only [evalMicroC_uint64_eq_load] at h ⊢; exact h
  | call f r args =>
    intro fuel fuel' env env' oc h _ _
    simp only [evalMicroC_uint64_eq_call] at h; cases h
  | ite cond thenB elseB ih_then ih_else =>
    intro fuel fuel' env env' oc h hle hoc
    simp only [evalMicroC_uint64] at h ⊢
    generalize hc : evalMicroCExpr_uint64 env cond = c at h ⊢
    cases c with
    | none => simp at h
    | some v =>
      cases v with
      | int _ => simp at h
      | bool b =>
        cases b with
        | true => exact ih_then h hle hoc
        | false => exact ih_else h hle hoc
  | seq s1 s2 ih1 ih2 => exact fuel_mono_seq_uint64 ih1 ih2
  | while_ cond body ih_body => exact fuel_mono_while_uint64 cond body ih_body

/-! ## UInt64 Public API -/

/-- Fuel monotonicity for UInt64: if evalMicroC_uint64 succeeds with outcome oc ≠ outOfFuel
    at fuel f, it produces the same result at any fuel f' ≥ f. -/
theorem evalMicroC_uint64_fuel_mono_full {fuel fuel' : Nat} {env : MicroCEnv} {stmt : MicroCStmt}
    {env' : MicroCEnv} {oc : Outcome}
    (h : evalMicroC_uint64 fuel env stmt = some (oc, env'))
    (hle : fuel ≤ fuel')
    (hoc : oc ≠ .outOfFuel) :
    evalMicroC_uint64 fuel' env stmt = some (oc, env') :=
  evalMicroC_uint64_fuel_mono_gen stmt h hle hoc

/-- Fuel monotonicity specialized to normal outcomes (UInt64). -/
theorem evalMicroC_uint64_fuel_mono {fuel fuel' : Nat} {env : MicroCEnv} {stmt : MicroCStmt}
    {env' : MicroCEnv}
    (h : evalMicroC_uint64 fuel env stmt = some (.normal, env'))
    (hle : fuel ≤ fuel') :
    evalMicroC_uint64 fuel' env stmt = some (.normal, env') :=
  evalMicroC_uint64_fuel_mono_full h hle (by simp)

end TrustLean
