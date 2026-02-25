/-
  Trust-Lean — Verified Code Generation Framework
  Bridge/Types.lean: Wrapper types for amo-lean constructs

  N6.1: FUND — defines wrapper types mirroring amo-lean's ExpandedSigma
  type hierarchy, VarName mapping with constructor-based partitioning,
  and the bridge predicates (scalarBridge + loopBridge + memBridge).

  Design: wrapper types (not direct lake dependency) enable independent
  compilation. VarName injectivity is FREE from VarName constructor
  disjointness + VarName.array.injEq + Int.ofNat injectivity.

  VarName partitioning:
  - ScalarVar → VarName.array (kindTag kind) (Int.ofNat idx)
  - LoopVar   → VarName.user s!"loop_{lv}"
  - Memory    → VarName.array memArrayName (Int.ofNat addr)
  - Temps     → VarName.temp n  (from CodeGenState, disjoint by constructor)
-/

import TrustLean.Core.Value

set_option autoImplicit false

namespace TrustLean.Bridge

/-! ## Scalar Variable Kind -/

/-- Classification of scalar variables. Mirrors amo-lean's ScalarVar naming
    conventions: input ("x"), output ("y"), temp ("t"). Using an enum instead
    of String enables trivial injectivity proofs. -/
inductive ScalarVarKind where
  | input | output | temp
  deriving Repr, BEq, DecidableEq, Inhabited

/-! ## Scalar Variables -/

/-- Scalar variable identifier. Uses (kind, idx) instead of amo-lean's (name, idx)
    for provable injectivity of the VarName mapping. -/
structure ScalarVar where
  kind : ScalarVarKind
  idx  : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-! ## Loop Variables -/

/-- Loop variable identifier. amo-lean uses `abbrev LoopVar := Nat`. -/
abbrev LoopVar := Nat

/-! ## Scalar Expressions -/

/-- Scalar arithmetic expression. Mirrors amo-lean's ScalarExpr (6 constructors). -/
inductive ScalarExpr where
  | var   : ScalarVar → ScalarExpr
  | const : Int → ScalarExpr
  | neg   : ScalarExpr → ScalarExpr
  | add   : ScalarExpr → ScalarExpr → ScalarExpr
  | sub   : ScalarExpr → ScalarExpr → ScalarExpr
  | mul   : ScalarExpr → ScalarExpr → ScalarExpr
  deriving Repr, BEq, Inhabited

/-! ## Index Expressions -/

/-- Index expression for memory addressing. Mirrors amo-lean's IdxExpr (5 constructors).
    Evaluates to Nat (unsigned indices for gather/scatter). -/
inductive IdxExpr where
  | const  : Nat → IdxExpr
  | var    : LoopVar → IdxExpr
  | affine : (base : Nat) → (stride : Nat) → LoopVar → IdxExpr
  | add    : IdxExpr → IdxExpr → IdxExpr
  | mul    : Nat → IdxExpr → IdxExpr
  deriving Repr, BEq, Inhabited

/-! ## Scalar Assignments and Blocks -/

/-- A single scalar assignment: target := value. -/
structure ScalarAssign where
  target : ScalarVar
  value  : ScalarExpr
  deriving Repr, BEq, Inhabited

/-- A block of scalar assignments (straight-line code). -/
abbrev ScalarBlock := List ScalarAssign

/-! ## Expanded Kernel -/

/-- Expanded kernel: scalar operations replacing a symbolic kernel.
    Mirrors amo-lean's ExpandedKernel (input vars + output vars + body). -/
structure ExpandedKernel where
  inputVars  : List ScalarVar
  outputVars : List ScalarVar
  body       : ScalarBlock
  deriving Repr, Inhabited

/-! ## Gather and Scatter -/

/-- Gather: read elements from memory with stride pattern.
    count elements starting at baseAddr with given stride. -/
structure Gather where
  count    : Nat
  baseAddr : IdxExpr
  stride   : Nat
  deriving Repr, Inhabited

/-- Scatter: write elements to memory with stride pattern.
    count elements starting at baseAddr with given stride. -/
structure Scatter where
  count    : Nat
  baseAddr : IdxExpr
  stride   : Nat
  deriving Repr, Inhabited

/-! ## ExpandedSigma -/

/-- SigmaExpr with kernels expanded to scalar operations.
    Mirrors amo-lean's ExpandedSigma (6 constructors).

    v1.1.0 note: `.par` is given sequential semantics identical to `.seq`.
    True parallelism deferred to v2.0. -/
inductive ExpandedSigma where
  | scalar : ExpandedKernel → Gather → Scatter → ExpandedSigma
  | loop   : (n : Nat) → (loopVar : LoopVar) → ExpandedSigma → ExpandedSigma
  | seq    : ExpandedSigma → ExpandedSigma → ExpandedSigma
  | par    : ExpandedSigma → ExpandedSigma → ExpandedSigma
  | temp   : (size : Nat) → ExpandedSigma → ExpandedSigma
  | nop    : ExpandedSigma
  deriving Repr, Inhabited

/-! ## VarName Mapping -/

/-- Tag string for each scalar variable kind. Used in VarName.array encoding.
    Reserved names: "I", "O", "T" — must not be used as memory array names. -/
private def kindTag : ScalarVarKind → String
  | .input  => "I"
  | .output => "O"
  | .temp   => "T"

/-- Map a scalar variable to a Trust-Lean VarName.
    Uses `VarName.array (kindTag kind) (Int.ofNat idx)`.
    Injectivity is trivial: VarName.array.injEq + kindTag injectivity + Int.ofNat injectivity. -/
def scalarVarToVarName (v : ScalarVar) : VarName :=
  .array (kindTag v.kind) (Int.ofNat v.idx)

/-- Map a loop variable to a Trust-Lean VarName.
    Uses `VarName.array "loop"` for provable injectivity.
    Disjoint from ScalarVar (kindTag ≠ "loop") and memory ("loop" ≠ "mem"). -/
def loopVarToVarName (lv : LoopVar) : VarName :=
  .array "loop" (Int.ofNat lv)

/-- Canonical array name for Gather/Scatter memory operations.
    Must not collide with kindTag values ("I", "O", "T"). -/
def memArrayName : String := "mem"

/-! ## VarName Mapping Injectivity -/

private theorem kindTag_injective : Function.Injective kindTag := by
  intro k1 k2 h
  cases k1 <;> cases k2 <;> simp_all [kindTag]

/-- scalarVarToVarName is injective: different ScalarVars map to different VarNames.
    Proof: VarName.array.injEq gives tag + Int equality;
    kindTag_injective gives kind equality; omega gives idx equality. -/
theorem scalarVarToVarName_injective (v1 v2 : ScalarVar)
    (h : scalarVarToVarName v1 = scalarVarToVarName v2) : v1 = v2 := by
  obtain ⟨k1, i1⟩ := v1
  obtain ⟨k2, i2⟩ := v2
  simp [scalarVarToVarName] at h
  obtain ⟨hk, hi⟩ := h
  have hk' := kindTag_injective hk
  have hi' : i1 = i2 := by omega
  subst hk' hi'
  rfl

/-- loopVarToVarName is injective: different LoopVars map to different VarNames. -/
theorem loopVarToVarName_injective (lv1 lv2 : LoopVar)
    (h : loopVarToVarName lv1 = loopVarToVarName lv2) : lv1 = lv2 := by
  simp only [loopVarToVarName] at h
  rw [VarName.array.injEq] at h
  exact Int.ofNat.inj h.2

/-- ScalarVar and LoopVar VarName ranges are disjoint:
    kindTag ∈ {"in_","out_","tmp_"} ≠ "loop". -/
theorem scalarVar_loopVar_disjoint (sv : ScalarVar) (lv : LoopVar) :
    scalarVarToVarName sv ≠ loopVarToVarName lv := by
  obtain ⟨k, i⟩ := sv
  intro h
  simp only [scalarVarToVarName, loopVarToVarName, VarName.array.injEq] at h
  obtain ⟨hk, _⟩ := h
  cases k <;> unfold kindTag at hk <;> exact absurd hk (by decide)

/-- ScalarVar VarNames are disjoint from temp VarNames (from CodeGenState):
    VarName.array ≠ VarName.temp by constructor disjointness. -/
theorem scalarVar_temp_disjoint (sv : ScalarVar) (n : Nat) :
    scalarVarToVarName sv ≠ .temp n := by
  simp [scalarVarToVarName]

/-- LoopVar VarNames are disjoint from temp VarNames:
    VarName.array ≠ VarName.temp by constructor disjointness. -/
theorem loopVar_temp_disjoint (lv : LoopVar) (n : Nat) :
    loopVarToVarName lv ≠ .temp n := by
  simp [loopVarToVarName]

/-- Memory array name does not collide with scalar variable tags. -/
theorem memArrayName_ne_kindTag (k : ScalarVarKind) :
    memArrayName ≠ kindTag k := by
  cases k <;> simp [memArrayName, kindTag]

/-- Loop array name "loop" does not collide with memory array name "mem". -/
theorem loopArrayName_ne_memArrayName : ("loop" : String) ≠ memArrayName := by
  simp [memArrayName]

/-- Memory array name does not collide with loop array name. -/
theorem memArrayName_ne_loopArrayName : memArrayName ≠ ("loop" : String) := by
  simp [memArrayName]

/-! ## Source Environment -/

/-- Environment for ExpandedSigma denotational semantics.
    Tracks scalar variables, loop variables, and flat memory. -/
structure SigmaEnv where
  scalarEnv : ScalarVar → Int
  loopEnv   : LoopVar → Nat
  mem       : Nat → Int
  deriving Inhabited

/-! ## Bridge Predicates -/

/-- Scalar bridge: amo-lean scalar environment agrees with Trust-Lean low-level env
    on all scalar variables, via the VarName mapping. -/
def scalarBridge (sEnv : ScalarVar → Int) (llEnv : LowLevelEnv) : Prop :=
  ∀ (v : ScalarVar), llEnv (scalarVarToVarName v) = .int (sEnv v)

/-- Loop bridge: amo-lean loop environment agrees with Trust-Lean low-level env
    on all loop variables, via the VarName mapping. -/
def loopBridge (lEnv : LoopVar → Nat) (llEnv : LowLevelEnv) : Prop :=
  ∀ (lv : LoopVar), llEnv (loopVarToVarName lv) = .int (lEnv lv)

/-- Memory bridge: amo-lean flat memory agrees with Trust-Lean low-level env
    array entries under the canonical memory array name. -/
def memBridge (mem : Nat → Int) (llEnv : LowLevelEnv) : Prop :=
  ∀ (i : Nat), llEnv (.array memArrayName (Int.ofNat i)) = .int (mem i)

/-- Full bridge: scalar, loop, and memory environments all agree. -/
def fullBridge (state : SigmaEnv) (llEnv : LowLevelEnv) : Prop :=
  scalarBridge state.scalarEnv llEnv ∧
  loopBridge state.loopEnv llEnv ∧
  memBridge state.mem llEnv

/-! ## Bridge Predicate Lemmas -/

@[simp] theorem scalarBridge_lookup (sEnv : ScalarVar → Int) (llEnv : LowLevelEnv)
    (v : ScalarVar) (h : scalarBridge sEnv llEnv) :
    llEnv (scalarVarToVarName v) = .int (sEnv v) := h v

@[simp] theorem loopBridge_lookup (lEnv : LoopVar → Nat) (llEnv : LowLevelEnv)
    (lv : LoopVar) (h : loopBridge lEnv llEnv) :
    llEnv (loopVarToVarName lv) = .int (lEnv lv) := h lv

@[simp] theorem memBridge_lookup (mem : Nat → Int) (llEnv : LowLevelEnv)
    (i : Nat) (h : memBridge mem llEnv) :
    llEnv (.array memArrayName (Int.ofNat i)) = .int (mem i) := h i

theorem fullBridge_scalar (state : SigmaEnv) (llEnv : LowLevelEnv)
    (h : fullBridge state llEnv) : scalarBridge state.scalarEnv llEnv := h.1

theorem fullBridge_loop (state : SigmaEnv) (llEnv : LowLevelEnv)
    (h : fullBridge state llEnv) : loopBridge state.loopEnv llEnv := h.2.1

theorem fullBridge_mem (state : SigmaEnv) (llEnv : LowLevelEnv)
    (h : fullBridge state llEnv) : memBridge state.mem llEnv := h.2.2

/-- Updating a scalar var in the LowLevelEnv preserves the loop bridge,
    because ScalarVar VarNames (kindTag) ≠ LoopVar VarNames ("loop"). -/
theorem loopBridge_update_scalar (lEnv : LoopVar → Nat) (llEnv : LowLevelEnv)
    (sv : ScalarVar) (val : Value) (h : loopBridge lEnv llEnv) :
    loopBridge lEnv (llEnv.update (scalarVarToVarName sv) val) := by
  intro lv
  rw [LowLevelEnv.update_other _ _ _ _ (Ne.symm (scalarVar_loopVar_disjoint sv lv))]
  exact h lv

/-- Updating a scalar var preserves the memory bridge,
    because kindTag ≠ memArrayName. -/
theorem memBridge_update_scalar (mem : Nat → Int) (llEnv : LowLevelEnv)
    (sv : ScalarVar) (val : Value) (h : memBridge mem llEnv) :
    memBridge mem (llEnv.update (scalarVarToVarName sv) val) := by
  intro i
  simp only [LowLevelEnv.update]
  split
  · next heq =>
    simp [scalarVarToVarName] at heq
    exact absurd heq.1 (memArrayName_ne_kindTag sv.kind)
  · exact h i

/-- Updating a different scalar var preserves the scalar bridge for the original var. -/
theorem scalarBridge_update_other (sEnv : ScalarVar → Int) (llEnv : LowLevelEnv)
    (sv sv' : ScalarVar) (val : Value) (hne : sv' ≠ sv)
    (h : llEnv (scalarVarToVarName sv) = .int (sEnv sv)) :
    (llEnv.update (scalarVarToVarName sv') val) (scalarVarToVarName sv) = .int (sEnv sv) := by
  simp [LowLevelEnv.update]
  split
  · next heq =>
    exact absurd (scalarVarToVarName_injective sv sv' heq) (Ne.symm hne)
  · exact h

/-- Updating a memory entry preserves the scalar bridge,
    because memArrayName ≠ kindTag. -/
theorem scalarBridge_update_mem (sEnv : ScalarVar → Int) (llEnv : LowLevelEnv)
    (addr : Nat) (val : Value) (h : scalarBridge sEnv llEnv) :
    scalarBridge sEnv (llEnv.update (.array memArrayName (Int.ofNat addr)) val) := by
  intro v
  simp only [LowLevelEnv.update]
  split
  · next heq =>
    simp [scalarVarToVarName] at heq
    exact absurd heq.1.symm (memArrayName_ne_kindTag v.kind)
  · exact h v

/-- Updating a memory entry preserves the loop bridge,
    because memArrayName ≠ "loop". -/
theorem loopBridge_update_mem (lEnv : LoopVar → Nat) (llEnv : LowLevelEnv)
    (addr : Nat) (val : Value) (h : loopBridge lEnv llEnv) :
    loopBridge lEnv (llEnv.update (.array memArrayName (Int.ofNat addr)) val) := by
  intro lv
  simp only [LowLevelEnv.update]
  split
  · next heq =>
    simp [loopVarToVarName, memArrayName] at heq
  · exact h lv

/-- Updating a loop var preserves the scalar bridge,
    because "loop" ≠ kindTag. -/
theorem scalarBridge_update_loop (sEnv : ScalarVar → Int) (llEnv : LowLevelEnv)
    (lv : LoopVar) (val : Value) (h : scalarBridge sEnv llEnv) :
    scalarBridge sEnv (llEnv.update (loopVarToVarName lv) val) := by
  intro v
  simp only [LowLevelEnv.update]
  split
  · next heq =>
    exact absurd heq (scalarVar_loopVar_disjoint v lv)
  · exact h v

/-- Updating a loop var preserves the memory bridge,
    because "loop" ≠ memArrayName. -/
theorem memBridge_update_loop (mem : Nat → Int) (llEnv : LowLevelEnv)
    (lv : LoopVar) (val : Value) (h : memBridge mem llEnv) :
    memBridge mem (llEnv.update (loopVarToVarName lv) val) := by
  intro i
  simp only [LowLevelEnv.update]
  split
  · next heq =>
    simp [loopVarToVarName, memArrayName] at heq
  · exact h i

/-- After updating a loop variable, the loop bridge holds for the point-updated
    loop environment. -/
theorem loopBridge_update_loop (lEnv : LoopVar → Nat) (llEnv : LowLevelEnv)
    (lv : LoopVar) (val : Nat) (h : loopBridge lEnv llEnv) :
    loopBridge (fun v => if v = lv then val else lEnv v)
      (llEnv.update (loopVarToVarName lv) (.int (Int.ofNat val))) := by
  intro lv'
  by_cases hlv : lv' = lv
  · subst hlv; simp [LowLevelEnv.update_same]
  · simp only [hlv, ite_false]
    have hne : loopVarToVarName lv' ≠ loopVarToVarName lv := by
      intro heq; exact hlv (loopVarToVarName_injective lv' lv heq)
    rw [LowLevelEnv.update_other _ _ _ _ hne]
    exact h lv'

end TrustLean.Bridge
