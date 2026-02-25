/-
  Trust-Lean — Test Suite
  Tests/Properties/BridgeExpandedSigma.lean

  N3.1: Property tests for Bridge ExpandedSigma translation.
  Covers: scalarExprToLLExpr, idxExprToLLExpr, VarName mapping injectivity,
  structural homomorphism, and fullBridge frame property.
-/

import TrustLean.Bridge.Types
import TrustLean.Bridge.Semantics
import TrustLean.Bridge.ExprTranslation
import TrustLean.Core.Eval

set_option autoImplicit false

open TrustLean
open TrustLean.Bridge

/-! ## P1: P0 SOUNDNESS — ScalarExpr translation correctness

  The evaluation of a translated ScalarExpr in a bridged environment
  equals the evaluation of the original ScalarExpr in the source environment.

  We verify with concrete decidable examples since SigmaEnv uses
  function types (ScalarVar -> Int) which lack SampleableExt.
-/

-- P0, INVARIANT: scalarExprToLLExpr preserves semantics under bridge

/-- Build a concrete LowLevelEnv that satisfies scalarBridge for a given sEnv. -/
private def mkBridgedEnv (sEnv : ScalarVar → Int) (lEnv : LoopVar → Nat) (mem : Nat → Int) : LowLevelEnv :=
  fun v =>
    match v with
    | .array tag idx =>
      if tag = "I" then .int (sEnv ⟨.input, idx.toNat⟩)
      else if tag = "O" then .int (sEnv ⟨.output, idx.toNat⟩)
      else if tag = "T" then .int (sEnv ⟨.temp, idx.toNat⟩)
      else if tag = "loop" then .int (lEnv idx.toNat)
      else if tag = "mem" then .int (mem idx.toNat)
      else .int 0
    | _ => .int 0

-- P1 concrete example 1: var + const
#eval do
  let sv_in0 : ScalarVar := ScalarVar.mk .input 0
  let sEnv : ScalarVar → Int := fun v =>
    if v == sv_in0 then 10 else 0
  let llEnv := mkBridgedEnv sEnv (fun _ => 0) (fun _ => 0)
  let expr := ScalarExpr.add (.var sv_in0) (.const 42)
  let result := evalExpr llEnv (scalarExprToLLExpr expr)
  let expected := some (Value.int (evalScalarExpr sEnv expr))
  if result == expected then IO.println "P1-a [PASS] ScalarExpr var+const translation correct"
  else IO.println s!"P1-a [FAIL] Expected {repr expected}, got {repr result}"

-- P1 concrete example 2: nested mul(sub, add)
#eval do
  let sv_in0 : ScalarVar := ScalarVar.mk .input 0
  let sv_in1 : ScalarVar := ScalarVar.mk .input 1
  let sEnv : ScalarVar → Int := fun v =>
    if v == sv_in0 then 10
    else if v == sv_in1 then 3
    else 0
  let llEnv := mkBridgedEnv sEnv (fun _ => 0) (fun _ => 0)
  let expr := ScalarExpr.mul (.sub (.var sv_in0) (.const 5)) (.add (.var sv_in1) (.const 2))
  let result := evalExpr llEnv (scalarExprToLLExpr expr)
  let expected := some (Value.int (evalScalarExpr sEnv expr))
  if result == expected then IO.println "P1-b [PASS] ScalarExpr nested mul(sub,add) translation correct"
  else IO.println s!"P1-b [FAIL] Expected {repr expected}, got {repr result}"

-- P1 concrete example 3: negation
#eval do
  let sv_out2 : ScalarVar := ScalarVar.mk .output 2
  let sEnv : ScalarVar → Int := fun v =>
    if v == sv_out2 then 7 else 0
  let llEnv := mkBridgedEnv sEnv (fun _ => 0) (fun _ => 0)
  let expr := ScalarExpr.neg (.var sv_out2)
  let result := evalExpr llEnv (scalarExprToLLExpr expr)
  let expected := some (Value.int (evalScalarExpr sEnv expr))
  if result == expected then IO.println "P1-c [PASS] ScalarExpr negation translation correct"
  else IO.println s!"P1-c [FAIL] Expected {repr expected}, got {repr result}"

-- P1 verified: The formal proof already exists in ExprTranslation.lean
-- (scalarExprToLLExpr_correct). We verify it type-checks:
#check @scalarExprToLLExpr_correct

/-! ## P2: P0 SOUNDNESS — IdxExpr translation correctness

  The evaluation of a translated IdxExpr in a bridged environment
  equals the evaluation of the original IdxExpr in the source environment.
-/

-- P0, INVARIANT: idxExprToLLExpr preserves semantics under bridge

-- P2 concrete example 1: var + const
#eval do
  let lEnv : LoopVar → Nat := fun lv =>
    if lv == 3 then 7 else 0
  let llEnv := mkBridgedEnv (fun _ => 0) lEnv (fun _ => 0)
  let expr := IdxExpr.add (.var 3) (.const 5)
  let result := evalExpr llEnv (idxExprToLLExpr expr)
  let expected := some (Value.int (Int.ofNat (evalIdxExpr lEnv expr)))
  if result == expected then IO.println "P2-a [PASS] IdxExpr var+const translation correct"
  else IO.println s!"P2-a [FAIL] Expected {repr expected}, got {repr result}"

-- P2 concrete example 2: affine expression
#eval do
  let lEnv : LoopVar → Nat := fun lv =>
    if lv == 0 then 4 else 0
  let llEnv := mkBridgedEnv (fun _ => 0) lEnv (fun _ => 0)
  let expr := IdxExpr.affine 10 3 0  -- 10 + 3 * lv0 = 10 + 12 = 22
  let result := evalExpr llEnv (idxExprToLLExpr expr)
  let expected := some (Value.int (Int.ofNat (evalIdxExpr lEnv expr)))
  if result == expected then IO.println "P2-b [PASS] IdxExpr affine translation correct"
  else IO.println s!"P2-b [FAIL] Expected {repr expected}, got {repr result}"

-- P2 concrete example 3: mul
#eval do
  let lEnv : LoopVar → Nat := fun lv =>
    if lv == 2 then 5 else 0
  let llEnv := mkBridgedEnv (fun _ => 0) lEnv (fun _ => 0)
  let expr := IdxExpr.mul 3 (.var 2)  -- 3 * 5 = 15
  let result := evalExpr llEnv (idxExprToLLExpr expr)
  let expected := some (Value.int (Int.ofNat (evalIdxExpr lEnv expr)))
  if result == expected then IO.println "P2-c [PASS] IdxExpr mul translation correct"
  else IO.println s!"P2-c [FAIL] Expected {repr expected}, got {repr result}"

-- P2 verified: The formal proof already exists
#check @idxExprToLLExpr_correct

/-! ## P3: P0 INVARIANT — VarName mapping injectivity and disjointness

  The name-mangling scheme for variables is injective and produces
  disjoint name sets for different variable types.
-/

-- P0, INVARIANT: scalarVarToVarName is injective

-- P3-a: Different ScalarVars map to different VarNames
example : scalarVarToVarName ⟨.input, 0⟩ ≠ scalarVarToVarName ⟨.input, 1⟩ := by decide
example : scalarVarToVarName ⟨.input, 0⟩ ≠ scalarVarToVarName ⟨.output, 0⟩ := by decide
example : scalarVarToVarName ⟨.input, 5⟩ ≠ scalarVarToVarName ⟨.temp, 5⟩ := by decide

-- P3-b: ScalarVar and LoopVar produce disjoint VarNames
example : scalarVarToVarName ⟨.input, 0⟩ ≠ loopVarToVarName 0 := by decide
example : scalarVarToVarName ⟨.output, 3⟩ ≠ loopVarToVarName 3 := by decide
example : scalarVarToVarName ⟨.temp, 7⟩ ≠ loopVarToVarName 7 := by decide

-- P3-c: ScalarVar and memArrayName are disjoint
example : scalarVarToVarName ⟨.input, 0⟩ ≠ .array memArrayName 0 := by decide
example : scalarVarToVarName ⟨.output, 0⟩ ≠ .array memArrayName 0 := by decide
example : scalarVarToVarName ⟨.temp, 0⟩ ≠ .array memArrayName 0 := by decide

-- P3-d: LoopVar and memArrayName are disjoint
example : loopVarToVarName 0 ≠ .array memArrayName 0 := by decide
example : loopVarToVarName 5 ≠ .array memArrayName 5 := by decide

-- P3 verified: The formal proofs already exist
#check @scalarVarToVarName_injective
#check @loopVarToVarName_injective
#check @scalarVar_loopVar_disjoint

/-! ## P4: P1 PRESERVATION — scalarExprToLLExpr is a structural homomorphism

  The translation preserves the algebraic structure of add, sub, mul.
-/

-- P1, PRESERVATION: structural homomorphism for arithmetic operations

-- P4 decidable examples for add
example (a b : ScalarExpr) :
    scalarExprToLLExpr (.add a b) = .binOp .add (scalarExprToLLExpr a) (scalarExprToLLExpr b) := by rfl

-- P4 decidable examples for sub
example (a b : ScalarExpr) :
    scalarExprToLLExpr (.sub a b) = .binOp .sub (scalarExprToLLExpr a) (scalarExprToLLExpr b) := by rfl

-- P4 decidable examples for mul
example (a b : ScalarExpr) :
    scalarExprToLLExpr (.mul a b) = .binOp .mul (scalarExprToLLExpr a) (scalarExprToLLExpr b) := by rfl

-- P4 decidable examples for neg
example (e : ScalarExpr) :
    scalarExprToLLExpr (.neg e) = .unaryOp .neg (scalarExprToLLExpr e) := by rfl

-- P4 verified: The formal proofs already exist
#check @scalarExprToLLExpr_add_homo
#check @scalarExprToLLExpr_sub_homo
#check @scalarExprToLLExpr_mul_homo
#check @scalarExprToLLExpr_neg_homo

/-! ## P5: P1 PRESERVATION — fullBridge frame property

  Updating a scalar variable in SigmaEnv only affects the corresponding
  value in the bridged environment. Loop variables remain unchanged.
-/

-- P1, PRESERVATION: frame property for scalar updates

-- The formal proof exists (loopBridge_update_scalar, memBridge_update_scalar,
-- scalarBridge_update_other etc.), verifying type-checking:
#check @loopBridge_update_scalar
#check @memBridge_update_scalar
#check @scalarBridge_update_other

-- P5 concrete verification: updating a scalar does not change loop bridge lookup
#eval do
  let sv := ScalarVar.mk .input 0
  let svName := scalarVarToVarName sv
  let lvName := loopVarToVarName 3
  -- These names must be different (frame property requires this)
  if svName != lvName
  then IO.println "P5-a [PASS] scalarVar and loopVar names are distinct"
  else IO.println "P5-a [FAIL] scalarVar and loopVar names collided!"

-- P5 concrete verification: updating a scalar does not change mem bridge lookup
#eval do
  let sv := ScalarVar.mk .output 2
  let svName := scalarVarToVarName sv
  let memName := VarName.array memArrayName 0
  if svName != memName
  then IO.println "P5-b [PASS] scalarVar and memArray names are distinct"
  else IO.println "P5-b [FAIL] scalarVar and memArray names collided!"
