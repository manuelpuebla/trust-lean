/-
  Trust-Lean — Verified Code Generation Framework
  Bridge/Correctness.lean: Capstone correctness theorem

  N8.1: CRIT — proves the full simulation diagram:
  for any ExpandedSigma `sigma` and initial environment satisfying `fullBridge`,
  there exists sufficient fuel such that evaluating the compiled Stmt produces
  a result satisfying fullBridge with the denotational semantics.

  The proof is by structural induction on ExpandedSigma.
  v1.1.0: .par has sequential semantics (identical to .seq).
  v1.1.0a: wellFormed precondition ensures loop vars are not reused.
-/

import TrustLean.Bridge.Compile
import TrustLean.Core.FuelMono

set_option autoImplicit false

namespace TrustLean.Bridge

/-! ## Well-Formedness -/

/-- A loop variable does not appear as a loop binder in the given ExpandedSigma.
    Required: the compiled while loop assumes the body doesn't modify the
    outer loop counter. Always satisfied by amo-lean output. -/
def loopVarFresh (lv : LoopVar) : ExpandedSigma → Prop
  | .scalar _ _ _ => True
  | .loop _ lv' body => lv ≠ lv' ∧ loopVarFresh lv body
  | .seq s1 s2 => loopVarFresh lv s1 ∧ loopVarFresh lv s2
  | .par s1 s2 => loopVarFresh lv s1 ∧ loopVarFresh lv s2
  | .temp _ body => loopVarFresh lv body
  | .nop => True

/-- An ExpandedSigma is well-formed: no loop variable is reused at different
    nesting levels. Always satisfied by amo-lean's compiler output. -/
def wellFormed : ExpandedSigma → Prop
  | .scalar _ _ _ => True
  | .loop _ lv body => loopVarFresh lv body ∧ wellFormed body
  | .seq s1 s2 => wellFormed s1 ∧ wellFormed s2
  | .par s1 s2 => wellFormed s1 ∧ wellFormed s2
  | .temp _ body => wellFormed body
  | .nop => True

/-! ## Bridge Update Helpers -/

/-- After loading a value into a scalar var, the scalar bridge holds for the
    updated env with a point-update to the accumulator. -/
theorem scalarBridge_load_update
    (acc : ScalarVar → Int) (llEnv : LowLevelEnv)
    (v : ScalarVar) (val : Int) (hAcc : scalarBridge acc llEnv) :
    scalarBridge (fun var => if var = v then val else acc var)
      (llEnv.update (scalarVarToVarName v) (.int val)) := by
  intro var
  by_cases hv : var = v
  · subst hv; simp [LowLevelEnv.update_same]
  · simp only [hv, ite_false]
    exact scalarBridge_update_other acc llEnv var v (.int val) (Ne.symm hv) (hAcc var)

/-- After storing a value in memory, the memory bridge holds for the
    updated env with a point-update to the memory function. -/
theorem memBridge_store_update
    (mem : Nat → Int) (llEnv : LowLevelEnv)
    (addr : Nat) (val : Int) (hMem : memBridge mem llEnv) :
    memBridge (fun idx => if idx = addr then val else mem idx)
      (llEnv.update (.array memArrayName (Int.ofNat addr)) (.int val)) := by
  intro i
  by_cases hi : i = addr
  · subst hi; simp [LowLevelEnv.update_same]
  · simp only [hi, ite_false]
    have hne : (.array memArrayName (Int.ofNat i) : VarName) ≠
               .array memArrayName (Int.ofNat addr) := by
      intro heq; cases heq; exact hi (Int.ofNat.inj rfl)
    rw [LowLevelEnv.update_other _ _ _ _ hne]
    exact hMem i

/-! ## Gather/Scatter Unfold Lemmas -/

theorem gatherToStmt_unfold (inputVars : List ScalarVar) (g : Gather) :
    gatherToStmt inputVars g = gatherToStmt.go g inputVars 0 := rfl

theorem scatterToStmt_unfold (outputVars : List ScalarVar) (s : Scatter) :
    scatterToStmt outputVars s = scatterToStmt.go s outputVars 0 := rfl

/-! ## Gather Correctness -/

/-- gatherToStmt.go correctly loads values from memory into scalar variables,
    preserving all three bridge components. By induction on the variable list. -/
theorem gatherToStmt_go_correct
    (g : Gather) (vars : List ScalarVar) (i : Nat)
    (env : SigmaEnv) (acc : ScalarVar → Int) (llEnv : LowLevelEnv)
    (hAcc : scalarBridge acc llEnv)
    (hLoop : loopBridge env.loopEnv llEnv)
    (hMem : memBridge env.mem llEnv) (fuel : Nat) :
    ∃ llEnv',
      evalStmt fuel llEnv (gatherToStmt.go g vars i) = some (.normal, llEnv') ∧
      scalarBridge (applyGather_go g env vars i acc) llEnv' ∧
      loopBridge env.loopEnv llEnv' ∧
      memBridge env.mem llEnv' := by
  induction vars generalizing i acc llEnv with
  | nil =>
    exact ⟨llEnv, by simp [gatherToStmt.go, evalStmt_skip], hAcc, hLoop, hMem⟩
  | cons v rest ih =>
    simp only [gatherToStmt.go, evalStmt_seq]
    rw [load_mem_correct v env.loopEnv env.mem llEnv g.baseAddr g.stride i hLoop hMem fuel]
    simp only []
    exact ih (i + 1)
      (fun var => if var = v
        then env.mem (evalIdxExpr env.loopEnv g.baseAddr + g.stride * i)
        else acc var)
      (llEnv.update (scalarVarToVarName v)
        (.int (env.mem (evalIdxExpr env.loopEnv g.baseAddr + g.stride * i))))
      (scalarBridge_load_update acc llEnv v _ hAcc)
      (loopBridge_update_scalar env.loopEnv llEnv v _ hLoop)
      (memBridge_update_scalar env.mem llEnv v _ hMem)

/-! ## Scatter Correctness -/

/-- scatterToStmt.go correctly stores scalar values to memory,
    preserving scalar and loop bridges and updating the memory bridge. -/
theorem scatterToStmt_go_correct
    (s : Scatter) (vars : List ScalarVar) (i : Nat)
    (sEnv : ScalarVar → Int) (lEnv : LoopVar → Nat) (curMem : Nat → Int)
    (llEnv : LowLevelEnv)
    (hScalar : scalarBridge sEnv llEnv)
    (hLoop : loopBridge lEnv llEnv)
    (hMem : memBridge curMem llEnv) (fuel : Nat) :
    ∃ llEnv',
      evalStmt fuel llEnv (scatterToStmt.go s vars i) = some (.normal, llEnv') ∧
      scalarBridge sEnv llEnv' ∧
      loopBridge lEnv llEnv' ∧
      memBridge (applyScatter_go s sEnv lEnv vars i curMem) llEnv' := by
  induction vars generalizing i curMem llEnv with
  | nil =>
    exact ⟨llEnv, by simp [scatterToStmt.go, evalStmt_skip], hScalar, hLoop, hMem⟩
  | cons v rest ih =>
    simp only [scatterToStmt.go, evalStmt_seq]
    rw [store_mem_correct v sEnv lEnv llEnv s.baseAddr s.stride i hScalar hLoop fuel]
    simp only []
    exact ih (i + 1)
      (fun idx => if idx = evalIdxExpr lEnv s.baseAddr + s.stride * i
        then sEnv v else curMem idx)
      (llEnv.update (.array memArrayName
        (Int.ofNat (evalIdxExpr lEnv s.baseAddr + s.stride * i))) (.int (sEnv v)))
      (scalarBridge_update_mem sEnv llEnv _ _ hScalar)
      (loopBridge_update_mem lEnv llEnv _ _ hLoop)
      (memBridge_store_update curMem llEnv _ (sEnv v) hMem)

/-! ## InitTemps Correctness -/

/-- initTempsToStmt correctly initializes temp scalar variables to 0. -/
theorem initTempsToStmt_correct
    (size start : Nat) (sEnv : ScalarVar → Int) (lEnv : LoopVar → Nat)
    (mem : Nat → Int) (llEnv : LowLevelEnv)
    (hScalar : scalarBridge sEnv llEnv)
    (hLoop : loopBridge lEnv llEnv)
    (hMem : memBridge mem llEnv) (fuel : Nat) :
    ∃ llEnv',
      evalStmt fuel llEnv (initTempsToStmt size start) = some (.normal, llEnv') ∧
      scalarBridge (initTempScalars size start sEnv) llEnv' ∧
      loopBridge lEnv llEnv' ∧
      memBridge mem llEnv' := by
  induction size generalizing start sEnv llEnv with
  | zero =>
    exact ⟨llEnv, by simp [initTempsToStmt, evalStmt_skip], hScalar, hLoop, hMem⟩
  | succ n ih =>
    simp only [initTempsToStmt, evalStmt_seq, evalStmt_assign, evalExpr_litInt]
    exact ih (start + 1)
      (fun var => if var = ⟨.temp, start⟩ then 0 else sEnv var)
      (llEnv.update (scalarVarToVarName ⟨.temp, start⟩) (.int 0))
      (scalarBridge_load_update sEnv llEnv ⟨.temp, start⟩ 0 hScalar)
      (loopBridge_update_scalar lEnv llEnv ⟨.temp, start⟩ _ hLoop)
      (memBridge_update_scalar mem llEnv ⟨.temp, start⟩ _ hMem)

/-! ## Scalar Case Correctness -/

/-- The .scalar case: gather → kernel body → scatter. Fuel-independent. -/
theorem scalar_case_correct
    (k : ExpandedKernel) (g : Gather) (s : Scatter)
    (state : SigmaEnv) (llEnv : LowLevelEnv)
    (hBridge : fullBridge state llEnv) (fuel : Nat) :
    ∃ llEnv',
      evalStmt fuel llEnv (expandedSigmaToStmt (.scalar k g s)) = some (.normal, llEnv') ∧
      fullBridge (evalExpandedSigma (.scalar k g s) state) llEnv' := by
  simp only [expandedSigmaToStmt_scalar, evalStmt_seq]
  -- Step 1: Gather — unfold gatherToStmt to gatherToStmt.go
  rw [gatherToStmt_unfold]
  obtain ⟨llEnv1, hEval1, hScalar1, hLoop1, hMem1⟩ :=
    gatherToStmt_go_correct g k.inputVars 0 state state.scalarEnv llEnv
      hBridge.1 hBridge.2.1 hBridge.2.2 fuel
  rw [hEval1]; simp only []
  -- Step 2: Scalar block
  obtain ⟨llEnv2, hEval2, hScalar2, hLoop2, hMem2⟩ :=
    scalarBlockToStmt_correct k.body (applyGather k.inputVars g state) llEnv1
      state.loopEnv state.mem hScalar1 hLoop1 hMem1 fuel
  rw [hEval2]; simp only []
  -- Step 3: Scatter — unfold scatterToStmt to scatterToStmt.go
  rw [scatterToStmt_unfold]
  obtain ⟨llEnv3, hEval3, hScalar3, hLoop3, hMem3⟩ :=
    scatterToStmt_go_correct s k.outputVars 0
      (evalScalarBlock k.body (applyGather k.inputVars g state))
      state.loopEnv state.mem llEnv2 hScalar2 hLoop2 hMem2 fuel
  rw [hEval3]
  exact ⟨llEnv3, rfl, ⟨hScalar3, hLoop3, hMem3⟩⟩

/-! ## Loop Case Correctness -/

/-- Helper: the condition `loopVar < n` evaluates correctly. -/
private theorem loopCond_eval (lv : LoopVar) (n i : Nat) (llEnv : LowLevelEnv)
    (hCounter : llEnv (loopVarToVarName lv) = .int (Int.ofNat i)) :
    evalExpr llEnv (loopCondExpr lv n) =
      some (.bool (decide (Int.ofNat i < Int.ofNat n))) := by
  simp [loopCondExpr, loopCounterVar, hCounter]

/-- Helper: the step `loopVar := loopVar + 1` evaluates correctly. -/
private theorem loopStep_eval (lv : LoopVar) (i : Nat) (llEnv : LowLevelEnv) (fuel : Nat)
    (hCounter : llEnv (loopVarToVarName lv) = .int (Int.ofNat i)) :
    evalStmt fuel llEnv (loopStepStmt lv) =
      some (.normal, llEnv.update (loopVarToVarName lv) (.int (Int.ofNat (i + 1)))) := by
  simp only [loopStepStmt, loopCounterVar, evalStmt_assign, evalExpr_binOp,
    evalExpr_varRef, hCounter, evalExpr_litInt, evalBinOp_add]
  constructor

/-- loopGo preserves a fresh loop variable, given that the body evaluation does. -/
private theorem loopGo_preserves_loopVar
    (bodyEval : SigmaEnv → SigmaEnv) (lv lv' : LoopVar) (hne : lv ≠ lv')
    (hBody : ∀ s, (bodyEval s).loopEnv lv = s.loopEnv lv)
    (n i : Nat) (state : SigmaEnv) :
    (loopGo bodyEval lv' n i state).loopEnv lv = state.loopEnv lv := by
  induction n generalizing i state with
  | zero => simp [loopGo]
  | succ n ih =>
    simp only [loopGo]; rw [ih (i + 1)]; rw [hBody]; simp [hne]

/-- evalExpandedSigma preserves a fresh loop variable. -/
theorem evalExpandedSigma_preserves_fresh_loopVar
    (lv : LoopVar) (sigma : ExpandedSigma) (hFresh : loopVarFresh lv sigma)
    (state : SigmaEnv) :
    (evalExpandedSigma sigma state).loopEnv lv = state.loopEnv lv := by
  induction sigma generalizing state with
  | scalar _ _ _ => simp [evalExpandedSigma]
  | nop => simp [evalExpandedSigma]
  | seq s1 s2 ih1 ih2 =>
    simp only [evalExpandedSigma]; rw [ih2 hFresh.2, ih1 hFresh.1]
  | par s1 s2 ih1 ih2 =>
    simp only [evalExpandedSigma]; rw [ih2 hFresh.2, ih1 hFresh.1]
  | temp _ body ih =>
    simp only [evalExpandedSigma]; exact ih hFresh _
  | loop n lv' body ih =>
    simp only [evalExpandedSigma]; simp only [hFresh.1, ite_false]
    exact loopGo_preserves_loopVar (evalExpandedSigma body) lv lv' hFresh.1
      (fun s => ih hFresh.2 s) n 0 state

/-- Two SigmaEnvs that agree on scalarEnv, mem, and loopEnv at v ≠ lv
    produce equal loopGo results when rem ≥ 1 (the first step normalizes loopEnv[lv]). -/
private theorem loopGo_succ_eq_of_agree
    (bodyEval : SigmaEnv → SigmaEnv) (lv : LoopVar)
    (k i : Nat) (s1 s2 : SigmaEnv)
    (hS : s1.scalarEnv = s2.scalarEnv) (hM : s1.mem = s2.mem)
    (hL : ∀ v, v ≠ lv → s1.loopEnv v = s2.loopEnv v) :
    loopGo bodyEval lv (k + 1) i s1 = loopGo bodyEval lv (k + 1) i s2 := by
  simp only [loopGo]
  congr 1
  -- Show the arguments to bodyEval are equal
  show bodyEval { s1 with loopEnv := fun v => if v = lv then i else s1.loopEnv v } =
       bodyEval { s2 with loopEnv := fun v => if v = lv then i else s2.loopEnv v }
  congr 1
  cases s1; cases s2; simp only [SigmaEnv.mk.injEq] at hS hM ⊢
  refine ⟨hS, funext fun v => ?_, hM⟩
  by_cases hv : v = lv
  · simp [hv]
  · simp only [hv, ite_false]; exact hL v hv

/-- The while-loop part. Fixed context: n, lv, body, hFresh, hWFBody, ihBody.
    Induction on rem with generalizing i, state, llEnv. -/
private theorem while_loop_correct
    (n : Nat) (lv : LoopVar) (body : ExpandedSigma)
    (hFresh : loopVarFresh lv body) (_hWFBody : wellFormed body)
    (ihBody : ∀ state' llEnv', fullBridge state' llEnv' →
      ∃ fuel llEnv'', evalStmt fuel llEnv' (expandedSigmaToStmt body) =
        some (.normal, llEnv'') ∧
        fullBridge (evalExpandedSigma body state') llEnv'')
    (rem : Nat) (i : Nat) (hi : i + rem = n)
    (state : SigmaEnv) (llEnv : LowLevelEnv)
    (hBridge : fullBridge state llEnv)
    (hLoopVal : state.loopEnv lv = i) :
    ∃ fuel llEnv',
      evalStmt fuel llEnv (.while (loopCondExpr lv n)
        (.seq (expandedSigmaToStmt body) (loopStepStmt lv))) =
        some (.normal, llEnv') ∧
      fullBridge
        { (loopGo (evalExpandedSigma body) lv rem i state) with
          loopEnv := fun v => if v = lv then n
            else (loopGo (evalExpandedSigma body) lv rem i state).loopEnv v }
        llEnv' := by
  induction rem generalizing i state llEnv with
  | zero =>
    subst hi
    have hCounter := hBridge.2.1 lv; rw [hLoopVal] at hCounter
    have hCond := loopCond_eval lv i i llEnv hCounter
    simp [Int.lt_irrefl] at hCond
    refine ⟨1, llEnv, while_false 0 llEnv _ _ hCond, ?_⟩
    simp only [loopGo]
    refine ⟨hBridge.1, fun lv' => ?_, hBridge.2.2⟩
    by_cases hlv : lv' = lv
    · subst hlv; simp only [ite_true]; exact hCounter
    · simp only [hlv, ite_false]; exact hBridge.2.1 lv'
  | succ rem' ih =>
    have hi_lt : i < n := by omega
    have hCounter := hBridge.2.1 lv; rw [hLoopVal] at hCounter
    have hCond := loopCond_eval lv n i llEnv hCounter
    simp [Int.ofNat_lt.mpr hi_lt] at hCond
    -- Body correctness
    obtain ⟨fuelBody, llEnvBody, hEvalBody, hBridgeBody⟩ := ihBody state llEnv hBridge
    let state' := evalExpandedSigma body state
    -- Counter preserved by freshness
    have hPreserve : state'.loopEnv lv = i := by
      exact (evalExpandedSigma_preserves_fresh_loopVar lv body hFresh state).trans hLoopVal
    have hCounterBody : llEnvBody (loopVarToVarName lv) = .int (Int.ofNat i) := by
      have := hBridgeBody.2.1 lv; rw [hPreserve] at this; exact this
    -- Step: counter++
    have hEvalStep := loopStep_eval lv i llEnvBody fuelBody hCounterBody
    let llEnvStep := llEnvBody.update (loopVarToVarName lv) (.int (Int.ofNat (i + 1)))
    have hBodyStep : evalStmt fuelBody llEnv
        (.seq (expandedSigmaToStmt body) (loopStepStmt lv)) =
        some (.normal, llEnvStep) := by
      simp only [evalStmt_seq, hEvalBody]; exact hEvalStep
    -- Next iteration state
    let stateNext : SigmaEnv :=
      { state' with loopEnv := fun v => if v = lv then i + 1 else state'.loopEnv v }
    have hBridgeNext : fullBridge stateNext llEnvStep :=
      ⟨scalarBridge_update_loop state'.scalarEnv llEnvBody lv _ hBridgeBody.1,
       loopBridge_update_loop state'.loopEnv llEnvBody lv (i + 1) hBridgeBody.2.1,
       memBridge_update_loop state'.mem llEnvBody lv _ hBridgeBody.2.2⟩
    -- Apply IH
    obtain ⟨fuelRem, llEnvFinal, hEvalRem, hBridgeFinal⟩ :=
      ih (i + 1) (by omega) stateNext llEnvStep hBridgeNext (by simp [stateNext])
    -- Compose fuels
    let totalFuel := Nat.max fuelBody fuelRem + 1
    have hBodyStep' := evalStmt_fuel_mono hBodyStep
      (Nat.le_succ_of_le (Nat.le_max_left fuelBody fuelRem))
    have hEvalRem' := evalStmt_fuel_mono hEvalRem
      (Nat.le_succ_of_le (Nat.le_max_right fuelBody fuelRem))
    refine ⟨totalFuel + 1, llEnvFinal,
      (while_true_body_normal totalFuel llEnv llEnvStep _ _ hCond hBodyStep').trans hEvalRem',
      ?_⟩
    -- Bridge: connect loopGo (rem'+1) i state with loopGo rem' (i+1) stateNext
    -- The loopEnv update {state with loopEnv[lv]=i} is identity by hLoopVal
    have hStateEq :
        ({ state with loopEnv := fun v => if v = lv then i else state.loopEnv v } : SigmaEnv) =
        state := by
      cases state; simp only [SigmaEnv.mk.injEq]
      refine ⟨trivial, funext fun v => ?_, trivial⟩
      by_cases hv : v = lv
      · subst hv; simp only [ite_true]; exact hLoopVal.symm
      · simp [hv]
    -- Unfold one step: loopGo (rem'+1) i state → loopGo rem' (i+1) (body state)
    simp only [loopGo_succ, hStateEq]
    -- Goal now has: loopGo rem' (i+1) (evalExpandedSigma body state)
    cases rem' with
    | zero =>
      -- loopGo 0 = identity; evalExpandedSigma body state and stateNext agree after post-update
      simp only [loopGo]
      -- Decompose fullBridge to handle the loopEnv difference
      simp only [loopGo] at hBridgeFinal
      obtain ⟨hSF, hLF, hMF⟩ := hBridgeFinal
      refine ⟨hSF, fun lv' => ?_, hMF⟩
      have h := hLF lv'
      by_cases hlv : lv' = lv
      · subst hlv; simpa only [ite_true] using h
      · simp only [hlv, ite_false] at h ⊢
        simp only [stateNext, hlv, ite_false] at h
        exact h
    | succ k =>
      -- For rem' ≥ 1: full equality via loopGo_succ_eq_of_agree
      have hEq := loopGo_succ_eq_of_agree (evalExpandedSigma body) lv k (i + 1)
        (evalExpandedSigma body state) stateNext rfl rfl
        (fun v hv => by simp [stateNext, state', hv])
      simp only [hEq]; exact hBridgeFinal

/-- The .loop case: init counter → while → post-update. -/
theorem loop_case_correct
    (n : Nat) (lv : LoopVar) (body : ExpandedSigma)
    (state : SigmaEnv) (llEnv : LowLevelEnv)
    (hBridge : fullBridge state llEnv)
    (hWF : wellFormed (.loop n lv body))
    (ihBody : ∀ state' llEnv', wellFormed body → fullBridge state' llEnv' →
      ∃ fuel llEnv'', evalStmt fuel llEnv' (expandedSigmaToStmt body) =
        some (.normal, llEnv'') ∧
        fullBridge (evalExpandedSigma body state') llEnv'') :
    ∃ fuel llEnv',
      evalStmt fuel llEnv (expandedSigmaToStmt (.loop n lv body)) =
        some (.normal, llEnv') ∧
      fullBridge (evalExpandedSigma (.loop n lv body) state) llEnv' := by
  -- Init: assign counter = 0
  let state0 : SigmaEnv :=
    { state with loopEnv := fun v => if v = lv then 0 else state.loopEnv v }
  let llEnvInit := llEnv.update (loopVarToVarName lv) (.int 0)
  have hBridgeInit : fullBridge state0 llEnvInit :=
    ⟨scalarBridge_update_loop state.scalarEnv llEnv lv _ hBridge.1,
     loopBridge_update_loop state.loopEnv llEnv lv 0 hBridge.2.1,
     memBridge_update_loop state.mem llEnv lv _ hBridge.2.2⟩
  -- Apply while_loop_correct with state0
  obtain ⟨fuelWhile, llEnvFinal, hEvalWhile, hBridgeFinal⟩ :=
    while_loop_correct n lv body hWF.1 hWF.2
      (fun s' e' hb => ihBody s' e' hWF.2 hb)
      n 0 (by omega) state0 llEnvInit hBridgeInit (by simp [state0])
  refine ⟨fuelWhile, llEnvFinal, ?_, ?_⟩
  · simp only [expandedSigmaToStmt_loop, evalStmt_seq, evalStmt_assign, evalExpr_litInt]
    exact hEvalWhile
  · -- Connect loopGo ... state (semantic) with loopGo ... state0 (from while helper)
    simp only [evalExpandedSigma]
    -- Goal: fullBridge { (loopGo n 0 state) with loopEnv[lv]=n } llEnvFinal
    -- hBridgeFinal: fullBridge { (loopGo n 0 state0) with loopEnv[lv]=n } llEnvFinal
    cases n with
    | zero =>
      -- loopGo 0 = identity; post-update normalizes
      simp only [loopGo]
      have hEq : (⟨state.scalarEnv,
          fun v => if v = lv then 0 else state.loopEnv v,
          state.mem⟩ : SigmaEnv) =
        ⟨state0.scalarEnv,
          fun v => if v = lv then 0 else state0.loopEnv v,
          state0.mem⟩ := by
        simp only [state0, SigmaEnv.mk.injEq]
        refine ⟨trivial, funext fun v => ?_, trivial⟩
        by_cases hv : v = lv <;> simp [hv]
      rw [hEq]; exact hBridgeFinal
    | succ k =>
      -- For n ≥ 1: first step normalizes, so loopGo gives same result
      have hEq := loopGo_succ_eq_of_agree (evalExpandedSigma body) lv k 0
        state state0 rfl rfl (fun v hv => by simp [state0, hv])
      simp only [hEq]; exact hBridgeFinal

/-! ## Main Correctness Theorem -/

/-- **Capstone correctness theorem** for expandedSigmaToStmt.
    For any well-formed ExpandedSigma program and initial environment satisfying
    the full bridge, there exists sufficient fuel such that the compiled Stmt
    evaluates to a normal result whose environment satisfies the full bridge
    with the denotational semantics of the source program.

    Proof: structural induction on ExpandedSigma, using per-case helpers. -/
theorem expandedSigmaToStmt_correct (sigma : ExpandedSigma)
    (hWF : wellFormed sigma)
    (state : SigmaEnv) (llEnv : LowLevelEnv)
    (hBridge : fullBridge state llEnv) :
    ∃ fuel llEnv',
      evalStmt fuel llEnv (expandedSigmaToStmt sigma) = some (.normal, llEnv') ∧
      fullBridge (evalExpandedSigma sigma state) llEnv' := by
  induction sigma generalizing state llEnv with
  | nop =>
    exact ⟨0, llEnv, by simp [expandedSigmaToStmt, evalStmt_skip], hBridge⟩
  | scalar k g s =>
    exact ⟨0, scalar_case_correct k g s state llEnv hBridge 0⟩
  | seq s1 s2 ih1 ih2 =>
    obtain ⟨fuel1, llEnv1, hEval1, hBridge1⟩ := ih1 hWF.1 state llEnv hBridge
    obtain ⟨fuel2, llEnv2, hEval2, hBridge2⟩ := ih2 hWF.2
      (evalExpandedSigma s1 state) llEnv1 hBridge1
    refine ⟨Nat.max fuel1 fuel2, llEnv2, ?_, hBridge2⟩
    simp only [expandedSigmaToStmt_seq, evalStmt_seq]
    rw [evalStmt_fuel_mono hEval1 (Nat.le_max_left fuel1 fuel2)]
    exact evalStmt_fuel_mono hEval2 (Nat.le_max_right fuel1 fuel2)
  | par s1 s2 ih1 ih2 =>
    obtain ⟨fuel1, llEnv1, hEval1, hBridge1⟩ := ih1 hWF.1 state llEnv hBridge
    obtain ⟨fuel2, llEnv2, hEval2, hBridge2⟩ := ih2 hWF.2
      (evalExpandedSigma s1 state) llEnv1 hBridge1
    refine ⟨Nat.max fuel1 fuel2, llEnv2, ?_, hBridge2⟩
    simp only [expandedSigmaToStmt_par, evalStmt_seq]
    rw [evalStmt_fuel_mono hEval1 (Nat.le_max_left fuel1 fuel2)]
    exact evalStmt_fuel_mono hEval2 (Nat.le_max_right fuel1 fuel2)
  | temp size body ih =>
    -- Get intermediate state from initTemps (using fuel=0)
    obtain ⟨llEnv1, hEval1_0, hScalar1, hLoop1, hMem1⟩ :=
      initTempsToStmt_correct size 0 state.scalarEnv state.loopEnv state.mem llEnv
        hBridge.1 hBridge.2.1 hBridge.2.2 0
    -- Get body correctness
    obtain ⟨fuelBody, llEnv2, hEval2, hBridge2⟩ :=
      ih hWF { state with scalarEnv := initTempScalars size 0 state.scalarEnv } llEnv1
        ⟨hScalar1, hLoop1, hMem1⟩
    -- Compose: use fuelBody for the whole thing
    refine ⟨fuelBody, llEnv2, ?_, hBridge2⟩
    simp only [expandedSigmaToStmt_temp, evalStmt_seq]
    rw [evalStmt_fuel_mono hEval1_0 (Nat.zero_le fuelBody)]
    exact hEval2
  | loop n lv body ih =>
    exact loop_case_correct n lv body state llEnv hBridge hWF
      (fun state' llEnv' hwf hb => ih hwf state' llEnv' hb)

end TrustLean.Bridge
