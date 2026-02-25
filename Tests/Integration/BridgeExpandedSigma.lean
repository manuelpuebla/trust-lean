/-
  Trust-Lean — Test Suite
  Tests/Integration/BridgeExpandedSigma.lean

  N3.1: Integration tests for Bridge ExpandedSigma translation.
  Tests: expression translation end-to-end, fullBridge mapping,
  name generation correctness.
-/

import TrustLean.Bridge.Types
import TrustLean.Bridge.Semantics
import TrustLean.Bridge.ExprTranslation
import TrustLean.Core.Eval

set_option autoImplicit false

open TrustLean
open TrustLean.Bridge

/-- Build a concrete LowLevelEnv that satisfies bridge conditions. -/
private def mkBridgedEnv (sEnv : ScalarVar → Int) (lEnv : LoopVar → Nat) (mem : Nat → Int) : LowLevelEnv :=
  fun v =>
    match v with
    | .array tag idx =>
      if tag = "I" then .int (sEnv (ScalarVar.mk .input idx.toNat))
      else if tag = "O" then .int (sEnv (ScalarVar.mk .output idx.toNat))
      else if tag = "T" then .int (sEnv (ScalarVar.mk .temp idx.toNat))
      else if tag = "loop" then .int (lEnv idx.toNat)
      else if tag = "mem" then .int (mem idx.toNat)
      else .int 0
    | _ => .int 0

/-! ## T1: Translate and evaluate a simple ScalarExpr (var + lit) -/

def T1_simple_scalar_expr : IO Bool := do
  let sv_in := ScalarVar.mk .input 0
  let expr := ScalarExpr.add (.var sv_in) (.const 42)
  let sEnv : ScalarVar → Int := fun v => if v == sv_in then 10 else 0
  let llEnv := mkBridgedEnv sEnv (fun _ => 0) (fun _ => 0)
  let result := evalExpr llEnv (scalarExprToLLExpr expr)
  let expected := some (Value.int 52)
  if result == expected then
    IO.println "[PASS] T1 simple ScalarExpr var+lit evaluates to 52"
    return true
  else
    IO.println s!"[FAIL] T1 Expected {repr expected}, got {repr result}"
    return false

/-! ## T2: Translate and evaluate a nested ScalarExpr -/

def T2_nested_scalar_expr : IO Bool := do
  let sv_in0 := ScalarVar.mk .input 0
  let sv_in1 := ScalarVar.mk .input 1
  let expr := ScalarExpr.mul (.sub (.var sv_in0) (.const 5)) (.add (.var sv_in1) (.const 2))
  -- (10 - 5) * (3 + 2) = 5 * 5 = 25
  let sEnv : ScalarVar → Int := fun v =>
    if v == sv_in0 then 10
    else if v == sv_in1 then 3
    else 0
  let llEnv := mkBridgedEnv sEnv (fun _ => 0) (fun _ => 0)
  let result := evalExpr llEnv (scalarExprToLLExpr expr)
  let expected := some (Value.int 25)
  if result == expected then
    IO.println "[PASS] T2 nested ScalarExpr mul(sub,add) evaluates to 25"
    return true
  else
    IO.println s!"[FAIL] T2 Expected {repr expected}, got {repr result}"
    return false

/-! ## T3: Translate and evaluate a simple IdxExpr (loop var) -/

def T3_simple_idx_expr : IO Bool := do
  let lv0 : LoopVar := 0
  let expr := IdxExpr.add (.var lv0) (.const 5)
  -- lv0 = 3, so 3 + 5 = 8
  let lEnv : LoopVar → Nat := fun v => if v == lv0 then 3 else 0
  let llEnv := mkBridgedEnv (fun _ => 0) lEnv (fun _ => 0)
  let result := evalExpr llEnv (idxExprToLLExpr expr)
  let expected := some (Value.int 8)
  if result == expected then
    IO.println "[PASS] T3 simple IdxExpr var+const evaluates to 8"
    return true
  else
    IO.println s!"[FAIL] T3 Expected {repr expected}, got {repr result}"
    return false

/-! ## T4: Translate and evaluate a constant-only ScalarExpr -/

def T4_constant_scalar_expr : IO Bool := do
  let expr := ScalarExpr.add (.const 100) (.const 200)
  let sEnv : ScalarVar → Int := fun _ => 0
  let llEnv := mkBridgedEnv sEnv (fun _ => 0) (fun _ => 0)
  let result := evalExpr llEnv (scalarExprToLLExpr expr)
  let expected := some (Value.int 300)
  if result == expected then
    IO.println "[PASS] T4 constant ScalarExpr 100+200 evaluates to 300"
    return true
  else
    IO.println s!"[FAIL] T4 Expected {repr expected}, got {repr result}"
    return false

/-! ## T5: fullBridge on empty SigmaEnv -/

def T5_empty_bridge : IO Bool := do
  -- Default SigmaEnv: all scalars 0, all loops 0, mem all 0
  let _env : SigmaEnv := default
  -- In the empty environment, everything resolves via the bridge.
  -- The bridge is a Prop (relation), not a concrete function — so we
  -- verify the properties of the naming scheme instead.
  -- scalarVarToVarName, loopVarToVarName should produce distinct names from memArrayName
  let anyName := VarName.user "any_var"
  let memName := VarName.array memArrayName 0
  -- A user-provided VarName "any_var" is NOT in the bridge domain
  -- (bridge only maps .array names)
  let scalarName := scalarVarToVarName (ScalarVar.mk .input 0)
  -- Verify memArrayName is "mem"
  let memIsCorrect := memArrayName == "mem"
  -- Verify that "any_var" as a user name is distinct from all bridge names
  let anyDistinctFromScalar := anyName != scalarName
  let anyDistinctFromMem := anyName != memName
  if memIsCorrect && anyDistinctFromScalar && anyDistinctFromMem then
    IO.println "[PASS] T5 empty SigmaEnv: memArrayName=mem, user vars distinct from bridge"
    return true
  else
    IO.println "[FAIL] T5 empty SigmaEnv bridge verification failed"
    return false

/-! ## T6: fullBridge correctly maps all components of populated SigmaEnv -/

def T6_populated_bridge : IO Bool := do
  let sv_in0 := ScalarVar.mk .input 0
  let lv0 : LoopVar := 0
  -- Build environments
  let sEnv : ScalarVar → Int := fun v => if v == sv_in0 then 100 else 0
  let lEnv : LoopVar → Nat := fun v => if v == lv0 then 5 else 0
  let mem : Nat → Int := fun i => if i == 0 then 1 else if i == 1 then 2 else if i == 2 then 3 else 0
  let llEnv := mkBridgedEnv sEnv lEnv mem
  -- Check scalar variable mapping
  let scalarOk := llEnv (scalarVarToVarName sv_in0) == Value.int 100
  -- Check loop variable mapping
  let loopOk := llEnv (loopVarToVarName lv0) == Value.int 5
  -- Check memory mapping
  let memOk := llEnv (VarName.array memArrayName 0) == Value.int 1
  let memOk2 := llEnv (VarName.array memArrayName 1) == Value.int 2
  let memOk3 := llEnv (VarName.array memArrayName 2) == Value.int 3
  if scalarOk && loopOk && memOk && memOk2 && memOk3 then
    IO.println "[PASS] T6 populated SigmaEnv: all components correctly bridged"
    return true
  else
    IO.println s!"[FAIL] T6 bridged env verification failed: scalar={scalarOk} loop={loopOk} mem={memOk},{memOk2},{memOk3}"
    return false

/-! ## T7: Name generation for different variable kinds -/

def T7_name_generation : IO Bool := do
  let v_in := ScalarVar.mk .input 5
  let v_out := ScalarVar.mk .output 5
  let v_tmp := ScalarVar.mk .temp 5
  let lv : LoopVar := 3
  -- Get the generated VarNames
  let n_in := scalarVarToVarName v_in
  let n_out := scalarVarToVarName v_out
  let n_tmp := scalarVarToVarName v_tmp
  let n_loop := loopVarToVarName lv
  let n_mem := VarName.array memArrayName 0
  -- Check expected VarName structure:
  -- ScalarVar uses VarName.array with kindTag
  let inOk := n_in == VarName.array "I" 5
  let outOk := n_out == VarName.array "O" 5
  let tmpOk := n_tmp == VarName.array "T" 5
  let loopOk := n_loop == VarName.array "loop" 3
  -- All names distinct from each other
  let allDistinct :=
    n_in != n_out && n_in != n_tmp && n_in != n_loop && n_in != n_mem &&
    n_out != n_tmp && n_out != n_loop && n_out != n_mem &&
    n_tmp != n_loop && n_tmp != n_mem &&
    n_loop != n_mem
  if inOk && outOk && tmpOk && loopOk && allDistinct then
    IO.println "[PASS] T7 name generation: all kinds correct and distinct"
    return true
  else
    IO.println s!"[FAIL] T7 name generation: in={inOk} out={outOk} tmp={tmpOk} loop={loopOk} distinct={allDistinct}"
    return false

/-! ## Main -/

def main : IO UInt32 := do
  let mut allPass := true
  let results ← [T1_simple_scalar_expr, T2_nested_scalar_expr, T3_simple_idx_expr,
                  T4_constant_scalar_expr, T5_empty_bridge, T6_populated_bridge,
                  T7_name_generation].mapM id
  for r in results do
    if !r then allPass := false
  if allPass then
    IO.println "\n=== All N3.1 integration tests PASSED ==="
    return 0
  else
    IO.println "\n=== Some N3.1 integration tests FAILED ==="
    return 1
