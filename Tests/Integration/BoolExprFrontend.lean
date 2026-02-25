/-
  Trust-Lean — Tests/Integration/BoolExprFrontend.lean
  Integration tests for N2.2: BoolExpr Frontend

  Each test prints [PASS] or [FAIL].
  main returns 0 if all pass, 1 otherwise.
-/

import TrustLean.Frontend.BoolExpr.Syntax
import TrustLean.Frontend.BoolExpr.Compile
import TrustLean.Frontend.BoolExpr.Correctness
import TrustLean.Core.Eval

open TrustLean

/-! ## Test Helpers -/

def runTest (name : String) (check : Bool) : IO Bool := do
  if check then
    IO.println s!"[PASS] {name}"
    return true
  else
    IO.println s!"[FAIL] {name}"
    return false

/-! ## T1: BASIC — simple eval for each logical operator -/
def T1_basic_operators : IO Bool := do
  -- env: var 0 = true, var 1 = false
  let env : VarId → Bool := fun v => if v == 0 then true else false
  let e_and := BoolExpr.and_ (.var 0) (.var 1)
  let e_or := BoolExpr.or_ (.var 0) (.var 1)
  let e_not := BoolExpr.not_ (.var 1)
  let r1 := BoolExpr.eval env e_and  -- true && false = false
  let r2 := BoolExpr.eval env e_or   -- true || false = true
  let r3 := BoolExpr.eval env e_not  -- !false = true
  runTest "T1_basic_operators" (r1 == false && r2 == true && r3 == true)

/-! ## T2: EDGE_CASE — short-circuit behavior for and/or -/
def T2_short_circuit : IO Bool := do
  -- BoolExpr.eval is a Lean pure function, so it evaluates both sides
  -- But the key test: and_ with false on left should give false
  -- regardless of right operand
  let env : VarId → Bool := fun _ => false
  let e_and := BoolExpr.and_ (.lit false) (.var 99)
  let e_or := BoolExpr.or_ (.lit true) (.var 99)
  let r1 := BoolExpr.eval env e_and  -- false && _ = false
  let r2 := BoolExpr.eval env e_or   -- true || _ = true
  runTest "T2_short_circuit" (r1 == false && r2 == true)

/-! ## T3: EDGE_CASE — unbound variable defaults to env default -/
def T3_unbound_var : IO Bool := do
  -- All vars default to false
  let env : VarId → Bool := fun _ => false
  let e := BoolExpr.or_ (.var 999) (.lit false)
  let r := BoolExpr.eval env e  -- false || false = false
  runTest "T3_unbound_var" (r == false)

/-! ## T4: BASIC — complex mixed expression -/
def T4_complex_mixed : IO Bool := do
  -- env: var 0 = true, var 1 = false, var 2 = true
  let env : VarId → Bool := fun v =>
    if v == 0 then true
    else if v == 2 then true
    else false
  -- (var 0 && var 2) || var 1 = (true && true) || false = true
  let e := BoolExpr.or_ (.and_ (.var 0) (.var 2)) (.var 1)
  let r := BoolExpr.eval env e
  runTest "T4_complex_mixed" (r == true)

/-! ## T5: BASIC — literals only, no variables -/
def T5_literals_only : IO Bool := do
  let env : VarId → Bool := fun _ => false
  -- and_ (lit true) (not_ (lit false)) = true && true = true
  let e := BoolExpr.and_ (.lit true) (.not_ (.lit false))
  let r := BoolExpr.eval env e
  runTest "T5_literals_only" (r == true)

/-! ## T6: STRESS — deeply nested not (1000 levels) -/
def T6_deep_nested_not : IO Bool := do
  -- Build not (not (not ... (lit true) ...)) with 1000 nots
  -- Even number of nots => true
  let mut expr : BoolExpr := .lit true
  for _ in [:1000] do
    expr := .not_ expr
  let env : VarId → Bool := fun _ => false
  let result := BoolExpr.eval env expr
  -- 1000 nots (even) => true
  runTest "T6_deep_nested_not" (result == true)

/-! ## Main -/

def main : IO UInt32 := do
  let mut allPass := true
  let results ← (
    [T1_basic_operators, T2_short_circuit, T3_unbound_var,
     T4_complex_mixed, T5_literals_only, T6_deep_nested_not]
  ).mapM id
  for r in results do
    if !r then allPass := false
  if allPass then
    IO.println "All integration tests passed."
    return 0
  else
    IO.println "Some integration tests FAILED."
    return 1
