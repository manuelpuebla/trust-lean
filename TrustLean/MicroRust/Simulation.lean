/-
  Trust-Lean — Verified Code Generation Framework
  MicroRust/Simulation.lean: Per-case simulation lemmas + master simulation theorem

  N24.3 (v4.0.0): CRITICO GATE — proves stmtToMicroRust_correct:
  if evalStmt fuel env stmt = some (oc, env') with microRustBridge env mcEnv,
  then evalMicroC fuel mcEnv (stmtToMicroRust stmt) = some (oc, mcEnv')
  and microRustBridge env' mcEnv'.

  Proof strategy:
  1. WellFormedArrayBasesRust + WellFormedBaseRust predicates
  2. sim_while_helper_rust: fuel induction with parameterized body IH
  3. stmtToMicroRust_correct: structural induction on Stmt
     - Simple cases inline (skip, break, continue, return, assign, call)
     - store/load: need WellFormedBaseRust for sanitizeIdentifierRust bridge
     - seq/ite: use sub-IHs
     - while: delegate to sim_while_helper_rust
     - for_: fuel split, init IH + compound seq IH + sim_while_helper_rust + fuel_mono

  Key hypotheses:
  - microRustBridge env mcEnv (environments agree via varNameToRust)
  - varNameToRust injective (well-formed program, no identifier collisions)
  - WellFormedArrayBasesRust stmt (store/load bases are .user vars with clean names)
-/

import TrustLean.MicroRust.Bridge
import TrustLean.MicroC.FuelMono
import TrustLean.Core.Eval
import TrustLean.Core.FuelMono

set_option autoImplicit false

namespace TrustLean

/-! ## Well-formedness conditions -/

/-- Well-formedness: varNameToRust is injective on the program's variable names. -/
abbrev VarNameInjectiveRust := Function.Injective varNameToRust

/-- A store/load base expression is well-formed if it's a user variable
    whose name is a valid Rust identifier (sanitizeIdentifierRust is identity on it). -/
def WellFormedBaseRust : LowLevelExpr → Prop
  | .varRef (.user name) => sanitizeIdentifierRust name = name
  | _ => False

/-- All store/load operations in a statement use well-formed bases. -/
def WellFormedArrayBasesRust : Stmt → Prop
  | .skip => True
  | .break_ => True
  | .continue_ => True
  | .return_ _ => True
  | .assign _ _ => True
  | .store base _ _ => WellFormedBaseRust base
  | .load _ base _ => WellFormedBaseRust base
  | .call _ _ _ => True
  | .seq s1 s2 => WellFormedArrayBasesRust s1 ∧ WellFormedArrayBasesRust s2
  | .ite _ thenB elseB => WellFormedArrayBasesRust thenB ∧ WellFormedArrayBasesRust elseB
  | .while _ body => WellFormedArrayBasesRust body
  | .for_ init _ step body =>
      WellFormedArrayBasesRust init ∧ WellFormedArrayBasesRust body ∧ WellFormedArrayBasesRust step

/-! ## Array bridge helper -/

/-- If getArrayName succeeds and the base is well-formed, then the base is a user
    variable and sanitizeIdentifierRust is identity on the name. -/
private theorem wf_base_is_user_rust (base : LowLevelExpr) (name : String)
    (hgn : getArrayName base = some name)
    (hwf : WellFormedBaseRust base) :
    base = .varRef (.user name) ∧ sanitizeIdentifierRust name = name := by
  cases base with
  | varRef v =>
    cases v with
    | user s =>
      simp [getArrayName] at hgn
      subst hgn
      exact ⟨rfl, hwf⟩
    | array _ _ => exact absurd hwf id
    | temp _ => simp [getArrayName] at hgn
  | litInt _ => simp [getArrayName] at hgn
  | litBool _ => simp [getArrayName] at hgn
  | binOp _ _ _ => exact absurd hwf id
  | unaryOp _ _ => exact absurd hwf id
  | powCall _ _ => exact absurd hwf id
  | addrOf _ => exact absurd hwf id

/-- Bridge preservation for array updates: updating .array name i in Core
    corresponds to updating (name ++ "[" ++ toString i ++ "]") in MicroRust. -/
private theorem microRustBridge_array_update {env : LowLevelEnv} {mcEnv : MicroRustEnv}
    (hb : microRustBridge env mcEnv) (hinj : VarNameInjectiveRust)
    (name : String) (i : Int) (v : Value) :
    microRustBridge (env.update (.array name i) v)
      (mcEnv.update (name ++ "[" ++ toString i ++ "]") v) := by
  intro w
  simp only [LowLevelEnv.update, MicroCEnv.update]
  by_cases hw : w = .array name i
  · subst hw
    have hk : varNameToRust (VarName.array name i) = name ++ "[" ++ toString i ++ "]" := rfl
    simp [hk]
  · have hne : varNameToRust w ≠ name ++ "[" ++ toString i ++ "]" := by
      intro heq
      apply hw
      have : varNameToRust w = varNameToRust (.array name i) := by
        show varNameToRust w = name ++ "[" ++ toString i ++ "]"
        exact heq
      exact hinj this
    simp [hw, hne, hb w]

/-! ## While simulation helper -/

/-- Simulation for while loops by fuel induction.
    Takes body simulation as parameter (from structural IH of master theorem). -/
private theorem sim_while_helper_rust
    (cond : LowLevelExpr) (body : Stmt)
    (body_sim : ∀ {fuel : Nat} {env env' : LowLevelEnv} {mcEnv : MicroRustEnv} {oc : Outcome},
      evalStmt fuel env body = some (oc, env') →
      microRustBridge env mcEnv → VarNameInjectiveRust → oc ≠ .outOfFuel →
      WellFormedArrayBasesRust body →
      ∃ mcEnv', evalMicroC fuel mcEnv (stmtToMicroRust body) = some (oc, mcEnv')
        ∧ microRustBridge env' mcEnv')
    {fuel : Nat} :
    ∀ {env env' : LowLevelEnv} {mcEnv : MicroRustEnv} {oc : Outcome},
    evalStmt fuel env (.while cond body) = some (oc, env') →
    microRustBridge env mcEnv → VarNameInjectiveRust → oc ≠ .outOfFuel →
    WellFormedArrayBasesRust body →
    ∃ mcEnv', evalMicroC fuel mcEnv (.while_ (exprToMicroRust cond) (stmtToMicroRust body))
      = some (oc, mcEnv') ∧ microRustBridge env' mcEnv' := by
  induction fuel with
  | zero =>
    intro env env' mcEnv oc h _ _ hoc _
    simp only [evalStmt_while_zero] at h
    have : oc = .outOfFuel := by
      have := Option.some.inj h; exact (congrArg Prod.fst this).symm
    exact absurd this hoc
  | succ n ih_fuel =>
    intro env env' mcEnv oc h hb hinj hoc hwf
    simp only [evalStmt_while_succ] at h
    simp only [evalMicroC_while_succ]
    -- Bridge the condition: rewrite MicroRust condition to Core condition
    have hcb := exprToMicroRust_bridge env mcEnv cond hb
    rw [← hcb]
    -- Now both h and goal match on evalExpr env cond
    generalize hec : evalExpr env cond = ec at h ⊢
    cases ec with
    | none => simp at h
    | some v =>
      cases v with
      | int _ => simp at h
      | bool b =>
        cases b with
        | false =>
          -- While exits: both return (.normal, env)
          have := Option.some.inj h
          have hoc_eq : oc = .normal := (congrArg Prod.fst this).symm
          have henv_eq : env' = env := by
            have := congrArg Prod.snd this; simp at this; exact this.symm
          subst hoc_eq; subst henv_eq
          exact ⟨mcEnv, rfl, hb⟩
        | true =>
          -- Evaluate body
          generalize hbody : evalStmt n env body = rb at h
          cases rb with
          | none => simp at h
          | some p =>
            obtain ⟨ob, e_mid⟩ := p
            cases ob with
            | normal =>
              -- Body normal → get MicroRust body result, then recurse
              obtain ⟨mcMid, hmcBody, hbMid⟩ := body_sim hbody hb hinj (by simp) hwf
              rw [hmcBody]
              exact ih_fuel h hbMid hinj hoc hwf
            | continue_ =>
              -- Body continue → same as normal for while
              obtain ⟨mcMid, hmcBody, hbMid⟩ := body_sim hbody hb hinj (by simp) hwf
              rw [hmcBody]
              exact ih_fuel h hbMid hinj hoc hwf
            | break_ =>
              -- Body break → while exits with normal
              obtain ⟨mcMid, hmcBody, hbMid⟩ := body_sim hbody hb hinj (by simp) hwf
              rw [hmcBody]
              have := Option.some.inj h
              have hoc_eq : oc = .normal := (congrArg Prod.fst this).symm
              have henv_eq : env' = e_mid := by
                have := congrArg Prod.snd this; simp at this; exact this.symm
              subst hoc_eq; subst henv_eq
              exact ⟨mcMid, rfl, hbMid⟩
            | return_ rv =>
              -- Body return → while propagates
              obtain ⟨mcMid, hmcBody, hbMid⟩ := body_sim hbody hb hinj (by simp) hwf
              rw [hmcBody]
              have := Option.some.inj h
              have hoc_eq : oc = .return_ rv := (congrArg Prod.fst this).symm
              have henv_eq : env' = e_mid := by
                have := congrArg Prod.snd this; simp at this; exact this.symm
              subst hoc_eq; subst henv_eq
              exact ⟨mcMid, rfl, hbMid⟩
            | outOfFuel =>
              -- Body outOfFuel → contradiction
              simp only [] at h
              have : oc = .outOfFuel := by
                have := Option.some.inj h; exact (congrArg Prod.fst this).symm
              exact absurd this hoc

/-! ## Master Simulation Theorem (combined B5+B6) -/

/-- Master simulation: stmtToMicroRust preserves evalStmt semantics.
    For any non-outOfFuel, non-None result of evalStmt, the translated
    MicroRust program produces the same result under the bridged environment.

    This is THE gate theorem for MicroRust. -/
theorem stmtToMicroRust_correct
    {fuel : Nat} {env env' : LowLevelEnv} {mcEnv : MicroRustEnv}
    {stmt : Stmt} {oc : Outcome}
    (heval : evalStmt fuel env stmt = some (oc, env'))
    (hb : microRustBridge env mcEnv)
    (hinj : VarNameInjectiveRust)
    (hoc : oc ≠ .outOfFuel)
    (hwf : WellFormedArrayBasesRust stmt) :
    ∃ mcEnv', evalMicroC fuel mcEnv (stmtToMicroRust stmt) = some (oc, mcEnv')
      ∧ microRustBridge env' mcEnv' := by
  induction stmt generalizing fuel env env' mcEnv oc with
  | skip =>
    simp only [evalStmt_skip] at heval
    have := Option.some.inj heval
    have hoc_eq : oc = .normal := (congrArg Prod.fst this).symm
    have henv_eq : env' = env := by have := congrArg Prod.snd this; simp at this; exact this.symm
    subst hoc_eq; subst henv_eq
    exact ⟨mcEnv, by simp, hb⟩
  | break_ =>
    simp only [evalStmt_break] at heval
    have := Option.some.inj heval
    have hoc_eq : oc = .break_ := (congrArg Prod.fst this).symm
    have henv_eq : env' = env := by have := congrArg Prod.snd this; simp at this; exact this.symm
    subst hoc_eq; subst henv_eq
    exact ⟨mcEnv, by simp, hb⟩
  | continue_ =>
    simp only [evalStmt_continue] at heval
    have := Option.some.inj heval
    have hoc_eq : oc = .continue_ := (congrArg Prod.fst this).symm
    have henv_eq : env' = env := by have := congrArg Prod.snd this; simp at this; exact this.symm
    subst hoc_eq; subst henv_eq
    exact ⟨mcEnv, by simp, hb⟩
  | return_ re =>
    cases re with
    | none =>
      simp only [evalStmt_return_none] at heval
      have := Option.some.inj heval
      have hoc_eq : oc = .return_ none := (congrArg Prod.fst this).symm
      have henv_eq : env' = env := by have := congrArg Prod.snd this; simp at this; exact this.symm
      subst hoc_eq; subst henv_eq
      exact ⟨mcEnv, by simp, hb⟩
    | some e =>
      simp only [evalStmt_return_some] at heval
      simp only [stmtToMicroRust_return, Option.map, evalMicroC_return_some]
      have hcb := exprToMicroRust_bridge env mcEnv e hb
      rw [← hcb]
      generalize hev : evalExpr env e = ev at heval ⊢
      cases ev with
      | none => simp at heval
      | some v =>
        simp only [] at heval
        have := Option.some.inj heval
        have hoc_eq : oc = .return_ (some v) := (congrArg Prod.fst this).symm
        have henv_eq : env' = env := by have := congrArg Prod.snd this; simp at this; exact this.symm
        subst hoc_eq; subst henv_eq
        exact ⟨mcEnv, rfl, hb⟩
  | assign name expr =>
    simp only [evalStmt_assign] at heval
    simp only [stmtToMicroRust_assign, evalMicroC_assign]
    have hcb := exprToMicroRust_bridge env mcEnv expr hb
    rw [← hcb]
    generalize hev : evalExpr env expr = ev at heval ⊢
    cases ev with
    | none => simp at heval
    | some v =>
      simp only [] at heval
      have := Option.some.inj heval
      have hoc_eq : oc = .normal := (congrArg Prod.fst this).symm
      have henv_eq : env' = env.update name v := by
        have := congrArg Prod.snd this; simp at this; exact this.symm
      subst hoc_eq; subst henv_eq
      exact ⟨mcEnv.update (varNameToRust name) v, rfl,
        microRustBridge_update hb name v (fun w h => hinj h)⟩
  | store base idx val =>
    simp only [evalStmt_store] at heval
    -- Extract getArrayName result from heval
    generalize hgn : getArrayName base = gn at heval
    cases gn with
    | none => simp at heval
    | some name =>
      -- WellFormedBaseRust gives us: base = .varRef (.user name) ∧ sanitizeIdentifierRust name = name
      obtain ⟨hbase_eq, hsn⟩ := wf_base_is_user_rust base name hgn hwf
      subst hbase_eq
      -- Bridge idx and val expressions
      have hidx := exprToMicroRust_bridge env mcEnv idx hb
      have hval := exprToMicroRust_bridge env mcEnv val hb
      -- Simplify MicroRust side
      simp only [stmtToMicroRust_store, exprToMicroRust_varRef]
      simp only [evalMicroC, getMicroCArrayName, varNameToRust, hsn]
      rw [← hidx, ← hval]
      generalize hei : evalExpr env idx = ei at heval ⊢
      cases ei with
      | none => simp at heval
      | some vi =>
        generalize hev : evalExpr env val = ev at heval ⊢
        cases vi with
        | bool _ => simp at heval
        | int i =>
          cases ev with
          | none => simp at heval
          | some vv =>
            simp only [] at heval
            have := Option.some.inj heval
            have hoc_eq : oc = .normal := (congrArg Prod.fst this).symm
            have henv_eq : env' = env.update (.array name i) vv := by
              have := congrArg Prod.snd this; simp at this; exact this.symm
            subst hoc_eq; subst henv_eq
            exact ⟨mcEnv.update (name ++ "[" ++ toString i ++ "]") vv, rfl,
              microRustBridge_array_update hb hinj name i vv⟩
  | load var base idx =>
    simp only [evalStmt_load] at heval
    generalize hgn : getArrayName base = gn at heval
    cases gn with
    | none => simp at heval
    | some name =>
      obtain ⟨hbase_eq, hsn⟩ := wf_base_is_user_rust base name hgn hwf
      subst hbase_eq
      have hidx := exprToMicroRust_bridge env mcEnv idx hb
      simp only [stmtToMicroRust_load, exprToMicroRust_varRef]
      simp only [evalMicroC, getMicroCArrayName, varNameToRust, hsn]
      rw [← hidx]
      generalize hei : evalExpr env idx = ei at heval ⊢
      cases ei with
      | none => simp at heval
      | some vi =>
        cases vi with
        | bool _ => simp at heval
        | int i =>
          simp only [] at heval
          have := Option.some.inj heval
          have hoc_eq : oc = .normal := (congrArg Prod.fst this).symm
          have henv_eq : env' = env.update var (env (.array name i)) := by
            have := congrArg Prod.snd this; simp at this; exact this.symm
          subst hoc_eq; subst henv_eq
          -- MicroRust loads mcEnv (name ++ "[" ++ toString i ++ "]") into varNameToRust var
          -- Core loads env (.array name i) into var
          -- Bridge: env (.array name i) = mcEnv (varNameToRust (.array name i))
          --       = mcEnv (name ++ "[" ++ toString i ++ "]")
          have hval_bridge : env (.array name i) = mcEnv (name ++ "[" ++ toString i ++ "]") := by
            have := hb (.array name i)
            show env (.array name i) = mcEnv (name ++ "[" ++ toString i ++ "]")
            exact this
          refine ⟨mcEnv.update (varNameToRust var) (mcEnv (name ++ "[" ++ toString i ++ "]")), rfl, ?_⟩
          rw [← hval_bridge]
          exact microRustBridge_update hb var (env (.array name i)) (fun w h => hinj h)
  | call result fname args =>
    simp only [evalStmt_call] at heval
    exact absurd heval (by simp)
  | seq s1 s2 ih1 ih2 =>
    simp only [evalStmt_seq] at heval
    simp only [stmtToMicroRust_seq, evalMicroC_seq]
    obtain ⟨hwf1, hwf2⟩ := hwf
    generalize hs1 : evalStmt fuel env s1 = r1 at heval
    cases r1 with
    | none => simp at heval
    | some p =>
      obtain ⟨o1, e_mid⟩ := p
      cases o1 with
      | normal =>
        obtain ⟨mcMid, hmcS1, hbMid⟩ := ih1 hs1 hb (by simp) hwf1
        rw [hmcS1]
        exact ih2 heval hbMid hoc hwf2
      | break_ =>
        obtain ⟨mcMid, hmcS1, hbMid⟩ := ih1 hs1 hb (by simp) hwf1
        rw [hmcS1]
        have := Option.some.inj heval
        have hoc_eq : oc = .break_ := (congrArg Prod.fst this).symm
        have henv_eq : env' = e_mid := by
          have := congrArg Prod.snd this; simp at this; exact this.symm
        subst hoc_eq; subst henv_eq
        exact ⟨mcMid, rfl, hbMid⟩
      | continue_ =>
        obtain ⟨mcMid, hmcS1, hbMid⟩ := ih1 hs1 hb (by simp) hwf1
        rw [hmcS1]
        have := Option.some.inj heval
        have hoc_eq : oc = .continue_ := (congrArg Prod.fst this).symm
        have henv_eq : env' = e_mid := by
          have := congrArg Prod.snd this; simp at this; exact this.symm
        subst hoc_eq; subst henv_eq
        exact ⟨mcMid, rfl, hbMid⟩
      | return_ rv =>
        obtain ⟨mcMid, hmcS1, hbMid⟩ := ih1 hs1 hb (by simp) hwf1
        rw [hmcS1]
        have := Option.some.inj heval
        have hoc_eq : oc = .return_ rv := (congrArg Prod.fst this).symm
        have henv_eq : env' = e_mid := by
          have := congrArg Prod.snd this; simp at this; exact this.symm
        subst hoc_eq; subst henv_eq
        exact ⟨mcMid, rfl, hbMid⟩
      | outOfFuel =>
        -- seq propagates outOfFuel from s1 → oc = outOfFuel, contradicting hoc
        simp only [] at heval
        have : oc = .outOfFuel := by
          have := Option.some.inj heval; exact (congrArg Prod.fst this).symm
        exact absurd this hoc
  | ite cond thenB elseB ih_then ih_else =>
    simp only [evalStmt_ite] at heval
    simp only [stmtToMicroRust_ite, evalMicroC_ite]
    obtain ⟨hwf_then, hwf_else⟩ := hwf
    have hcb := exprToMicroRust_bridge env mcEnv cond hb
    rw [← hcb]
    generalize hec : evalExpr env cond = ec at heval ⊢
    cases ec with
    | none => simp at heval
    | some v =>
      cases v with
      | int _ => simp at heval
      | bool b =>
        cases b with
        | true => exact ih_then heval hb hoc hwf_then
        | false => exact ih_else heval hb hoc hwf_else
  | «while» cond body ih_body =>
    exact sim_while_helper_rust cond body
      (fun {f} {e} {e'} {me} {o} he hbe _hinj hoe hwe =>
        ih_body he hbe hoe hwe)
      heval hb hinj hoc hwf
  | for_ init cond step body ih_init ih_step ih_body =>
    obtain ⟨hwf_init, hwf_body, hwf_step⟩ := hwf
    cases fuel with
    | zero =>
      simp only [evalStmt_for_zero] at heval
      have : oc = .outOfFuel := by
        have := Option.some.inj heval; exact (congrArg Prod.fst this).symm
      exact absurd this hoc
    | succ n =>
      simp only [evalStmt_for_succ] at heval
      simp only [stmtToMicroRust_for, evalMicroC_seq]
      -- Core: evalStmt n env init, then evalStmt n env' (.while cond (.seq body step))
      -- MicroRust: evalMicroC (n+1) mcEnv (stmtToMicroRust init), then while
      generalize hinit_eval : evalStmt n env init = r_init at heval
      cases r_init with
      | none => simp at heval
      | some p =>
        obtain ⟨o_init, e_init⟩ := p
        cases o_init with
        | normal =>
          -- Init succeeded normally
          -- IH for init at fuel n → evalMicroC n mcEnv (stmtToMicroRust init) = some (.normal, mcEnvInit)
          obtain ⟨mcInit, hmcInit, hbInit⟩ := ih_init hinit_eval hb (by simp) hwf_init
          -- Boost to fuel n+1 via fuel_mono
          have hmcInit' := evalMicroC_fuel_mono hmcInit (Nat.le_succ n)
          rw [hmcInit']
          -- Now need: evalMicroC (n+1) mcInit (while_ condMC (seq bodyMC stepMC)) = some (oc, mcEnv')
          -- Core has: evalStmt n e_init (.while cond (.seq body step)) = some (oc, env')
          -- Build compound body IH for (.seq body step)
          have seq_sim : ∀ {f : Nat} {e e' : LowLevelEnv} {me : MicroRustEnv} {o : Outcome},
              evalStmt f e (.seq body step) = some (o, e') →
              microRustBridge e me → VarNameInjectiveRust → o ≠ .outOfFuel →
              WellFormedArrayBasesRust (.seq body step) →
              ∃ me', evalMicroC f me (stmtToMicroRust (.seq body step)) = some (o, me')
                ∧ microRustBridge e' me' := by
            intro f e e' me o he hbe _h hoe hwe
            obtain ⟨hwb, hws⟩ := hwe
            -- This IS the seq case of the master theorem applied to body and step
            simp only [evalStmt_seq] at he
            simp only [stmtToMicroRust_seq, evalMicroC_seq]
            generalize hbs : evalStmt f e body = rb at he
            cases rb with
            | none => simp at he
            | some pb =>
              obtain ⟨ob, eb⟩ := pb
              cases ob with
              | normal =>
                obtain ⟨mcB, hmcB, hbB⟩ := ih_body hbs hbe (by simp) hwb
                rw [hmcB]
                exact ih_step he hbB hoe hws
              | break_ =>
                obtain ⟨mcB, hmcB, hbB⟩ := ih_body hbs hbe (by simp) hwb
                rw [hmcB]
                have := Option.some.inj he
                have hoc_eq : o = .break_ := (congrArg Prod.fst this).symm
                have henv_eq : e' = eb := by
                  have := congrArg Prod.snd this; simp at this; exact this.symm
                subst hoc_eq; subst henv_eq
                exact ⟨mcB, rfl, hbB⟩
              | continue_ =>
                obtain ⟨mcB, hmcB, hbB⟩ := ih_body hbs hbe (by simp) hwb
                rw [hmcB]
                have := Option.some.inj he
                have hoc_eq : o = .continue_ := (congrArg Prod.fst this).symm
                have henv_eq : e' = eb := by
                  have := congrArg Prod.snd this; simp at this; exact this.symm
                subst hoc_eq; subst henv_eq
                exact ⟨mcB, rfl, hbB⟩
              | return_ rv =>
                obtain ⟨mcB, hmcB, hbB⟩ := ih_body hbs hbe (by simp) hwb
                rw [hmcB]
                have := Option.some.inj he
                have hoc_eq : o = .return_ rv := (congrArg Prod.fst this).symm
                have henv_eq : e' = eb := by
                  have := congrArg Prod.snd this; simp at this; exact this.symm
                subst hoc_eq; subst henv_eq
                exact ⟨mcB, rfl, hbB⟩
              | outOfFuel =>
                simp only [] at he
                have : o = .outOfFuel := by
                  have := Option.some.inj he; exact (congrArg Prod.fst this).symm
                exact absurd this hoe
          -- Use sim_while_helper_rust at fuel n with compound seq IH
          have while_at_n := sim_while_helper_rust cond (.seq body step) seq_sim
            heval hbInit hinj hoc ⟨hwf_body, hwf_step⟩
          -- Get MicroRust result at fuel n
          obtain ⟨mcFinal, hmcWhile_n, hbFinal⟩ := while_at_n
          -- Boost while from fuel n to n+1 via fuel_mono
          have hmcWhile := evalMicroC_fuel_mono_full hmcWhile_n (Nat.le_succ n) hoc
          exact ⟨mcFinal, hmcWhile, hbFinal⟩
        | break_ | continue_ | return_ _ =>
          -- Init returned non-normal → for_ propagates directly
          simp only [] at heval
          have := Option.some.inj heval
          have hoc_eq := (congrArg Prod.fst this).symm
          have henv_eq : env' = e_init := by
            have := congrArg Prod.snd this; simp at this; exact this.symm
          subst henv_eq
          obtain ⟨mcInit, hmcInit, hbInit⟩ := ih_init hinit_eval hb
            (by subst hoc_eq; exact hoc) hwf_init
          have hmcInit' := evalMicroC_fuel_mono_full hmcInit (Nat.le_succ n)
            (by subst hoc_eq; exact hoc)
          rw [hmcInit']
          subst hoc_eq
          exact ⟨mcInit, rfl, hbInit⟩
        | outOfFuel =>
          simp only [] at heval
          have : oc = .outOfFuel := by
            have := Option.some.inj heval; exact (congrArg Prod.fst this).symm
          exact absurd this hoc

/-! ## WellFormedArrayBasesRust: key fact -/

/-- "mem" is already a valid Rust identifier (sanitizeIdentifierRust is identity). -/
theorem sanitizeIdentifierRust_mem : sanitizeIdentifierRust "mem" = "mem" := by native_decide

end TrustLean
