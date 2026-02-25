/-
  Trust-Lean — Verified Code Generation Framework
  Bridge/Semantics.lean: Denotational semantics for amo-lean types

  N6.1: FUND — defines evaluation functions for ScalarExpr, IdxExpr,
  ScalarBlock, and ExpandedSigma. These serve as the reference semantics
  for the correctness theorem in N8.1.

  v1.1.0: `.par` has sequential semantics identical to `.seq`.
-/

import TrustLean.Bridge.Types

set_option autoImplicit false

namespace TrustLean.Bridge

/-! ## Scalar Expression Evaluation -/

/-- Evaluate a scalar expression in a scalar variable environment.
    Total function: no division, no partial operations.
    Mirrors amo-lean's `ScalarExpr.eval`. -/
def evalScalarExpr (env : ScalarVar → Int) : ScalarExpr → Int
  | .var v     => env v
  | .const n   => n
  | .neg e     => -(evalScalarExpr env e)
  | .add e1 e2 => evalScalarExpr env e1 + evalScalarExpr env e2
  | .sub e1 e2 => evalScalarExpr env e1 - evalScalarExpr env e2
  | .mul e1 e2 => evalScalarExpr env e1 * evalScalarExpr env e2

/-! ## evalScalarExpr @[simp] Lemmas -/

@[simp] theorem evalScalarExpr_var (env : ScalarVar → Int) (v : ScalarVar) :
    evalScalarExpr env (.var v) = env v := rfl

@[simp] theorem evalScalarExpr_const (env : ScalarVar → Int) (n : Int) :
    evalScalarExpr env (.const n) = n := rfl

@[simp] theorem evalScalarExpr_neg (env : ScalarVar → Int) (e : ScalarExpr) :
    evalScalarExpr env (.neg e) = -(evalScalarExpr env e) := rfl

@[simp] theorem evalScalarExpr_add (env : ScalarVar → Int) (e1 e2 : ScalarExpr) :
    evalScalarExpr env (.add e1 e2) = evalScalarExpr env e1 + evalScalarExpr env e2 := rfl

@[simp] theorem evalScalarExpr_sub (env : ScalarVar → Int) (e1 e2 : ScalarExpr) :
    evalScalarExpr env (.sub e1 e2) = evalScalarExpr env e1 - evalScalarExpr env e2 := rfl

@[simp] theorem evalScalarExpr_mul (env : ScalarVar → Int) (e1 e2 : ScalarExpr) :
    evalScalarExpr env (.mul e1 e2) = evalScalarExpr env e1 * evalScalarExpr env e2 := rfl

/-- evalScalarExpr(.const n) is independent of the environment. -/
theorem evalScalarExpr_const_env_indep (n : Int) (env1 env2 : ScalarVar → Int) :
    evalScalarExpr env1 (.const n) = evalScalarExpr env2 (.const n) := rfl

/-! ## Index Expression Evaluation -/

/-- Evaluate an index expression in a loop variable environment.
    Returns Nat (unsigned index for memory addressing).
    Mirrors amo-lean's `IdxExpr.eval`. -/
def evalIdxExpr (env : LoopVar → Nat) : IdxExpr → Nat
  | .const n          => n
  | .var v            => env v
  | .affine base s v  => base + s * env v
  | .add e1 e2        => evalIdxExpr env e1 + evalIdxExpr env e2
  | .mul c e          => c * evalIdxExpr env e

/-! ## evalIdxExpr @[simp] Lemmas -/

@[simp] theorem evalIdxExpr_const (env : LoopVar → Nat) (n : Nat) :
    evalIdxExpr env (.const n) = n := rfl

@[simp] theorem evalIdxExpr_var (env : LoopVar → Nat) (v : LoopVar) :
    evalIdxExpr env (.var v) = env v := rfl

@[simp] theorem evalIdxExpr_affine (env : LoopVar → Nat) (base s : Nat) (v : LoopVar) :
    evalIdxExpr env (.affine base s v) = base + s * env v := rfl

@[simp] theorem evalIdxExpr_add (env : LoopVar → Nat) (e1 e2 : IdxExpr) :
    evalIdxExpr env (.add e1 e2) = evalIdxExpr env e1 + evalIdxExpr env e2 := rfl

@[simp] theorem evalIdxExpr_mul (env : LoopVar → Nat) (c : Nat) (e : IdxExpr) :
    evalIdxExpr env (.mul c e) = c * evalIdxExpr env e := rfl

/-! ## Scalar Assignment and Block Evaluation -/

/-- Execute a single scalar assignment: update the target variable
    with the evaluated expression value. -/
def evalScalarAssign (a : ScalarAssign) (env : ScalarVar → Int) : ScalarVar → Int :=
  fun v => if v = a.target then evalScalarExpr env a.value else env v

/-- Execute a block of scalar assignments sequentially.
    Each assignment sees the effects of all previous assignments. -/
def evalScalarBlock : ScalarBlock → (ScalarVar → Int) → (ScalarVar → Int)
  | [], env => env
  | a :: rest, env => evalScalarBlock rest (evalScalarAssign a env)

/-! ## evalScalarAssign/Block @[simp] Lemmas -/

@[simp] theorem evalScalarAssign_target (a : ScalarAssign) (env : ScalarVar → Int) :
    evalScalarAssign a env a.target = evalScalarExpr env a.value := by
  simp [evalScalarAssign]

@[simp] theorem evalScalarAssign_other (a : ScalarAssign) (env : ScalarVar → Int)
    (v : ScalarVar) (h : v ≠ a.target) :
    evalScalarAssign a env v = env v := by
  simp [evalScalarAssign, h]

@[simp] theorem evalScalarBlock_nil (env : ScalarVar → Int) :
    evalScalarBlock [] env = env := rfl

@[simp] theorem evalScalarBlock_cons (a : ScalarAssign) (rest : ScalarBlock)
    (env : ScalarVar → Int) :
    evalScalarBlock (a :: rest) env = evalScalarBlock rest (evalScalarAssign a env) := rfl

/-! ## Gather/Scatter Helpers -/

/-- Recursive gather helper: load elements from memory into scalar vars.
    Processes `vars` starting at index `i`, accumulating into `acc`.
    Uses explicit recursion (not foldl) for clean induction in N8.1. -/
def applyGather_go (g : Gather) (env : SigmaEnv) :
    List ScalarVar → Nat → (ScalarVar → Int) → ScalarVar → Int
  | [], _, acc => acc
  | v :: rest, i, acc =>
    applyGather_go g env rest (i + 1)
      (fun var => if var = v then env.mem (evalIdxExpr env.loopEnv g.baseAddr + g.stride * i)
                  else acc var)

/-- Apply gather: load elements from memory into kernel input variables.
    For i in 0..count-1: inputVars[i] := mem[baseAddr + stride * i]. -/
def applyGather (inputVars : List ScalarVar) (g : Gather)
    (env : SigmaEnv) : ScalarVar → Int :=
  applyGather_go g env inputVars 0 env.scalarEnv

/-- Recursive scatter helper: write scalar values to memory.
    Processes `vars` starting at index `i`, accumulating into `curMem`.
    Uses explicit recursion (not foldl) for clean induction in N8.1. -/
def applyScatter_go (s : Scatter) (scalarEnv : ScalarVar → Int)
    (loopEnv : LoopVar → Nat) :
    List ScalarVar → Nat → (Nat → Int) → Nat → Int
  | [], _, curMem => curMem
  | v :: rest, i, curMem =>
    applyScatter_go s scalarEnv loopEnv rest (i + 1)
      (fun idx => if idx = evalIdxExpr loopEnv s.baseAddr + s.stride * i
                  then scalarEnv v else curMem idx)

/-- Apply scatter: write kernel output variable values to memory.
    For i in 0..count-1: mem[baseAddr + stride * i] := outputVars[i]. -/
def applyScatter (outputVars : List ScalarVar) (s : Scatter)
    (scalarEnv : ScalarVar → Int) (loopEnv : LoopVar → Nat) (mem : Nat → Int) : Nat → Int :=
  applyScatter_go s scalarEnv loopEnv outputVars 0 mem

@[simp] theorem applyGather_go_nil (g : Gather) (env : SigmaEnv)
    (i : Nat) (acc : ScalarVar → Int) :
    applyGather_go g env [] i acc = acc := rfl

@[simp] theorem applyGather_go_cons (g : Gather) (env : SigmaEnv)
    (v : ScalarVar) (rest : List ScalarVar) (i : Nat) (acc : ScalarVar → Int) :
    applyGather_go g env (v :: rest) i acc =
    applyGather_go g env rest (i + 1)
      (fun var => if var = v then env.mem (evalIdxExpr env.loopEnv g.baseAddr + g.stride * i)
                  else acc var) := rfl

@[simp] theorem applyScatter_go_nil (s : Scatter) (scalarEnv : ScalarVar → Int)
    (loopEnv : LoopVar → Nat) (i : Nat) (curMem : Nat → Int) :
    applyScatter_go s scalarEnv loopEnv [] i curMem = curMem := rfl

@[simp] theorem applyScatter_go_cons (s : Scatter) (scalarEnv : ScalarVar → Int)
    (loopEnv : LoopVar → Nat) (v : ScalarVar) (rest : List ScalarVar)
    (i : Nat) (curMem : Nat → Int) :
    applyScatter_go s scalarEnv loopEnv (v :: rest) i curMem =
    applyScatter_go s scalarEnv loopEnv rest (i + 1)
      (fun idx => if idx = evalIdxExpr loopEnv s.baseAddr + s.stride * i
                  then scalarEnv v else curMem idx) := rfl

/-! ## Loop and Temp Helpers -/

/-- Iterate body evaluation n times with loop variable counting from `start`.
    Uses explicit recursion (not foldl) for clean induction in N8.1. -/
def loopGo (bodyEval : SigmaEnv → SigmaEnv) (lv : LoopVar) :
    Nat → Nat → SigmaEnv → SigmaEnv
  | 0, _, env => env
  | n + 1, i, env =>
    loopGo bodyEval lv n (i + 1)
      (bodyEval { env with loopEnv := fun v => if v = lv then i else env.loopEnv v })

/-- Initialize temp scalar variables to 0, from index `start` for `n` variables. -/
def initTempScalars : Nat → Nat → (ScalarVar → Int) → ScalarVar → Int
  | 0, _, acc => acc
  | n + 1, start, acc =>
    initTempScalars n (start + 1)
      (fun var => if var = ⟨.temp, start⟩ then 0 else acc var)

@[simp] theorem loopGo_zero (bodyEval : SigmaEnv → SigmaEnv) (lv : LoopVar)
    (i : Nat) (env : SigmaEnv) :
    loopGo bodyEval lv 0 i env = env := rfl

@[simp] theorem loopGo_succ (bodyEval : SigmaEnv → SigmaEnv) (lv : LoopVar)
    (n i : Nat) (env : SigmaEnv) :
    loopGo bodyEval lv (n + 1) i env =
    loopGo bodyEval lv n (i + 1)
      (bodyEval { env with loopEnv := fun v => if v = lv then i else env.loopEnv v }) := rfl

@[simp] theorem initTempScalars_zero (start : Nat) (acc : ScalarVar → Int) :
    initTempScalars 0 start acc = acc := rfl

@[simp] theorem initTempScalars_succ (n start : Nat) (acc : ScalarVar → Int) :
    initTempScalars (n + 1) start acc =
    initTempScalars n (start + 1)
      (fun var => if var = ⟨.temp, start⟩ then 0 else acc var) := rfl

/-! ## ExpandedSigma Denotational Semantics -/

/-- Big-step denotational semantics for ExpandedSigma.

    - `.scalar k g s`: gather → kernel body → scatter
    - `.loop n lv body`: iterate body n times with loopVar = 0..n-1
    - `.seq s1 s2`: execute s1, then s2
    - `.par s1 s2`: sequential interpretation (v1.1.0), identical to `.seq`
    - `.temp size body`: initialize temp vars to 0, execute body
    - `.nop`: identity

    v1.1.0a: loop/temp use explicit recursion (loopGo/initTempScalars) for
    clean inductive proofs. Gather/scatter use applyGather_go/applyScatter_go.
    v1.1.0b: loop post-updates loopEnv[lv] := n to match compiled counter value,
    enabling fullBridge composability. Loop vars are "don't care" after their loop. -/
def evalExpandedSigma : ExpandedSigma → SigmaEnv → SigmaEnv
  | .scalar k g s, env =>
    let gatheredScalars := applyGather k.inputVars g env
    let computedScalars := evalScalarBlock k.body gatheredScalars
    let newMem := applyScatter k.outputVars s computedScalars env.loopEnv env.mem
    { env with scalarEnv := computedScalars, mem := newMem }
  | .loop n lv body, env =>
    let result := loopGo (evalExpandedSigma body) lv n 0 env
    { result with loopEnv := fun v => if v = lv then n else result.loopEnv v }
  | .seq s1 s2, env =>
    evalExpandedSigma s2 (evalExpandedSigma s1 env)
  | .par s1 s2, env =>
    evalExpandedSigma s2 (evalExpandedSigma s1 env)
  | .temp size body, env =>
    evalExpandedSigma body { env with scalarEnv := initTempScalars size 0 env.scalarEnv }
  | .nop, env => env

/-! ## evalExpandedSigma @[simp] Lemmas -/

@[simp] theorem evalExpandedSigma_nop (env : SigmaEnv) :
    evalExpandedSigma .nop env = env := rfl

@[simp] theorem evalExpandedSigma_seq (s1 s2 : ExpandedSigma) (env : SigmaEnv) :
    evalExpandedSigma (.seq s1 s2) env =
    evalExpandedSigma s2 (evalExpandedSigma s1 env) := rfl

/-- Core v1.1.0 property: `.par` has sequential semantics identical to `.seq`. -/
@[simp] theorem evalExpandedSigma_par (s1 s2 : ExpandedSigma) (env : SigmaEnv) :
    evalExpandedSigma (.par s1 s2) env =
    evalExpandedSigma s2 (evalExpandedSigma s1 env) := rfl

/-- `.par` = `.seq` equivalence (direct statement for ARCHITECTURE.md P0 property). -/
theorem par_eq_seq (s1 s2 : ExpandedSigma) (env : SigmaEnv) :
    evalExpandedSigma (.par s1 s2) env =
    evalExpandedSigma (.seq s1 s2) env := rfl

@[simp] theorem evalExpandedSigma_loop_zero (lv : LoopVar) (body : ExpandedSigma)
    (env : SigmaEnv) :
    evalExpandedSigma (.loop 0 lv body) env =
    { env with loopEnv := fun v => if v = lv then 0 else env.loopEnv v } := rfl

end TrustLean.Bridge
