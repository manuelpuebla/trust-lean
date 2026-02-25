/-
  Trust-Lean — Tests/Integration/ArithExprFrontend.lean
  Integration tests for N2.1: ArithExpr Frontend

  Each test prints [PASS] or [FAIL].
  main returns 0 if all pass, 1 otherwise.
-/

import TrustLean.Frontend.ArithExpr.Syntax
import TrustLean.Frontend.ArithExpr.Compile
import TrustLean.Frontend.ArithExpr.Correctness
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

/-! ## T1: BASIC — addition of constant and variable -/
def T1_add_const_var : IO Bool := do
  let env : VarId → Int := fun v => if v == 0 then 5 else 0
  let expr := ArithExpr.add (.lit 10) (.var 0)
  let result := ArithExpr.eval env expr
  runTest "T1_add_const_var" (result == 15)

/-! ## T2: BASIC — nested multiplication and subtraction -/
def T2_nested_mul_sub : IO Bool := do
  -- ArithExpr only has add and mul, no sub.
  -- We test: mul (lit 5) (add (var 0) (lit (-2))) with var 0 = 10
  -- => 5 * (10 + (-2)) = 5 * 8 = 40
  let env : VarId → Int := fun v => if v == 0 then 10 else 0
  let expr := ArithExpr.mul (.lit 5) (.add (.var 0) (.lit (-2)))
  let result := ArithExpr.eval env expr
  runTest "T2_nested_mul_sub" (result == 40)

/-! ## T3: EDGE_CASE — multiplication by zero -/
def T3_mul_by_zero : IO Bool := do
  let env : VarId → Int := fun v => if v == 0 then 12345 else 0
  let expr := ArithExpr.mul (.add (.var 0) (.lit 100)) (.lit 0)
  let result := ArithExpr.eval env expr
  runTest "T3_mul_by_zero" (result == 0)

/-! ## T4: EDGE_CASE — negative numbers -/
def T4_negative_numbers : IO Bool := do
  -- (-5) * 3 + (-10) = -15 + (-10) = -25
  let env : VarId → Int := fun v => if v == 0 then 3 else 0
  let expr := ArithExpr.add (.mul (.lit (-5)) (.var 0)) (.lit (-10))
  let result := ArithExpr.eval env expr
  runTest "T4_negative_numbers" (result == -25)

/-! ## T5: EDGE_CASE — unbound variable defaults to env default -/
def T5_unbound_var : IO Bool := do
  -- env maps var 0 to 10, var 99 defaults to 0
  let env : VarId → Int := fun v => if v == 0 then 10 else 0
  let expr := ArithExpr.add (.var 0) (.var 99)
  let result := ArithExpr.eval env expr
  runTest "T5_unbound_var" (result == 10)

/-! ## T6: EDGE_CASE — single variable -/
def T6_single_var : IO Bool := do
  let env : VarId → Int := fun v => if v == 0 then 99 else 0
  let expr := ArithExpr.var 0
  let result := ArithExpr.eval env expr
  runTest "T6_single_var" (result == 99)

/-! ## T7: STRESS — deeply nested expression (depth 500) -/
def T7_deep_nested : IO Bool := do
  -- Build add (lit 1) (add (lit 1) ... (lit 1)) with depth 500
  let mut expr : ArithExpr := .lit 1
  for _ in [:499] do
    expr := .add (.lit 1) expr
  let env : VarId → Int := fun _ => 0
  let result := ArithExpr.eval env expr
  runTest "T7_deep_nested" (result == 500)

/-! ## T8: STRESS — wide expression with many variables -/
def T8_wide_expression : IO Bool := do
  -- Sum of 100 variables, each mapped to 1
  let env : VarId → Int := fun v => if v < 100 then 1 else 0
  let mut expr : ArithExpr := .var 0
  for i in [1:100] do
    expr := .add (.var i) expr
  let result := ArithExpr.eval env expr
  runTest "T8_wide_expression" (result == 100)

/-! ## Main -/

def main : IO UInt32 := do
  let mut allPass := true
  let results ← (
    [T1_add_const_var, T2_nested_mul_sub, T3_mul_by_zero, T4_negative_numbers,
     T5_unbound_var, T6_single_var, T7_deep_nested, T8_wide_expression]
  ).mapM id
  for r in results do
    if !r then allPass := false
  if allPass then
    IO.println "All integration tests passed."
    return 0
  else
    IO.println "Some integration tests FAILED."
    return 1
