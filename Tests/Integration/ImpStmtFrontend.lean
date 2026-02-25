/-
  Trust-Lean — Tests/Integration/ImpStmtFrontend.lean
  Integration tests for N2.3: ImpStmt Frontend

  Each test prints [PASS] or [FAIL].
  main returns 0 if all pass, 1 otherwise.
-/

import TrustLean.Frontend.ImpStmt.Syntax
import TrustLean.Frontend.ImpStmt.Compile
import TrustLean.Frontend.ImpStmt.Correctness
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

/-- Default empty ImpEnv: all variables map to 0. -/
def emptyEnv : ImpEnv := fun _ => 0

/-- Lookup helper to extract the value at a given VarId from an optional env. -/
def lookupEnv (result : Option ImpEnv) (v : VarId) : Option Int :=
  result.map (fun env => env v)

/-! ## T1: BASIC — sequential assignment -/
def T1_sequential_assign : IO Bool := do
  -- x := 10; y := x + 5
  let s := ImpStmt.seq
    (.assign 0 (.lit 10))
    (.assign 1 (.add (.var 0) (.lit 5)))
  let result := ImpStmt.eval 100 emptyEnv s
  let xVal := lookupEnv result 0
  let yVal := lookupEnv result 1
  runTest "T1_sequential_assign" (xVal == some 10 && yVal == some 15)

/-! ## T2: BASIC — if with true condition -/
def T2_if_true : IO Bool := do
  -- if 5 < 10 then x := 1 else x := 0
  let s := ImpStmt.ite
    (.lt_ (.lit 5) (.lit 10))
    (.assign 0 (.lit 1))
    (.assign 0 (.lit 0))
  let result := ImpStmt.eval 100 emptyEnv s
  let xVal := lookupEnv result 0
  runTest "T2_if_true" (xVal == some 1)

/-! ## T3: BASIC — if with false condition -/
def T3_if_false : IO Bool := do
  -- if 10 < 5 then x := 1 else x := 0
  let s := ImpStmt.ite
    (.lt_ (.lit 10) (.lit 5))
    (.assign 0 (.lit 1))
    (.assign 0 (.lit 0))
  let result := ImpStmt.eval 100 emptyEnv s
  let xVal := lookupEnv result 0
  runTest "T3_if_false" (xVal == some 0)

/-! ## T4: BASIC — while loop (sum 3+2+1) -/
def T4_while_sum : IO Bool := do
  -- x := 3; total := 0; while not(x == 0) do (total := total + x; x := x + (-1))
  -- Using var 0 = x, var 1 = total
  let s := ImpStmt.seq
    (.assign 0 (.lit 3))
    (.seq
      (.assign 1 (.lit 0))
      (.while
        (.not_ (.eq_ (.var 0) (.lit 0)))
        (.seq
          (.assign 1 (.add (.var 1) (.var 0)))
          (.assign 0 (.add (.var 0) (.lit (-1)))))))
  let result := ImpStmt.eval 100 emptyEnv s
  let xVal := lookupEnv result 0
  let totalVal := lookupEnv result 1
  runTest "T4_while_sum" (xVal == some 0 && totalVal == some 6)

/-! ## T5: EDGE_CASE — while with initially false condition -/
def T5_while_false : IO Bool := do
  -- while false do x := 1
  let s := ImpStmt.while (.lit false) (.assign 0 (.lit 1))
  let result := ImpStmt.eval 100 emptyEnv s
  let xVal := lookupEnv result 0
  runTest "T5_while_false" (xVal == some 0)  -- x never assigned, stays 0

/-! ## T6: EDGE_CASE — uninitialized variable defaults to 0 -/
def T6_uninitialized_var : IO Bool := do
  -- x := y + 5  (y is uninitialized, defaults to 0)
  let s := ImpStmt.assign 0 (.add (.var 1) (.lit 5))
  let result := ImpStmt.eval 100 emptyEnv s
  let xVal := lookupEnv result 0
  runTest "T6_uninitialized_var" (xVal == some 5)

/-! ## T7: EDGE_CASE — overwriting an existing variable -/
def T7_overwrite_var : IO Bool := do
  -- x := 10; x := x + 1
  let s := ImpStmt.seq
    (.assign 0 (.lit 10))
    (.assign 0 (.add (.var 0) (.lit 1)))
  let result := ImpStmt.eval 100 emptyEnv s
  let xVal := lookupEnv result 0
  runTest "T7_overwrite_var" (xVal == some 11)

/-! ## T8: EDGE_CASE — skip preserves state -/
def T8_skip_preserves : IO Bool := do
  let env : ImpEnv := fun v => if v == 0 then 42 else 0
  let s := ImpStmt.skip
  let result := ImpStmt.eval 100 env s
  let xVal := lookupEnv result 0
  runTest "T8_skip_preserves" (xVal == some 42)

/-! ## T9: STRESS — deeply nested if statements -/
def T9_deep_nested_if : IO Bool := do
  -- Build 100 nested if true then (if true then ... (x := 1) ... else skip) else skip
  let mut s : ImpStmt := .assign 0 (.lit 1)
  for _ in [:100] do
    s := .ite (.lit true) s .skip
  let result := ImpStmt.eval 100 emptyEnv s
  let xVal := lookupEnv result 0
  runTest "T9_deep_nested_if" (xVal == some 1)

/-! ## T10: STRESS — while loop with many iterations (sum 1..100) -/
def T10_while_many_iterations : IO Bool := do
  -- x := 100; total := 0; while not(x == 0) do (total := total + x; x := x - 1)
  let s := ImpStmt.seq
    (.assign 0 (.lit 100))
    (.seq
      (.assign 1 (.lit 0))
      (.while
        (.not_ (.eq_ (.var 0) (.lit 0)))
        (.seq
          (.assign 1 (.add (.var 1) (.var 0)))
          (.assign 0 (.add (.var 0) (.lit (-1)))))))
  let result := ImpStmt.eval 200 emptyEnv s
  let totalVal := lookupEnv result 1
  -- Sum 1..100 = 5050
  runTest "T10_while_many_iterations" (totalVal == some 5050)

/-! ## T11: REGRESSION — compile preserves semantics on concrete while loop -/
def T11_compile_correctness : IO Bool := do
  -- The same program from T4 evaluated both directly and through compilation
  -- x := 3; total := 0; while not(x == 0) do (total := total + x; x := x - 1)
  let s := ImpStmt.seq
    (.assign 0 (.lit 3))
    (.seq
      (.assign 1 (.lit 0))
      (.while
        (.not_ (.eq_ (.var 0) (.lit 0)))
        (.seq
          (.assign 1 (.add (.var 1) (.var 0)))
          (.assign 0 (.add (.var 0) (.lit (-1)))))))
  -- Evaluate directly
  let directResult := ImpStmt.eval 100 emptyEnv s
  -- Compile and evaluate via Core
  let compiled := ImpStmt.compile impVarNames s
  let llEnv : LowLevelEnv := fun _ => .int 0
  let coreResult := evalStmt 100 llEnv compiled
  -- Both should succeed and give same values
  let directTotal := lookupEnv directResult 1
  let coreTotal := coreResult.bind fun (_, env') => some (env' (.user "i1"))
  runTest "T11_compile_correctness"
    (directTotal == some 6 && coreTotal == some (.int 6))

/-! ## Main -/

def main : IO UInt32 := do
  let mut allPass := true
  let results ← (
    [T1_sequential_assign, T2_if_true, T3_if_false, T4_while_sum,
     T5_while_false, T6_uninitialized_var, T7_overwrite_var,
     T8_skip_preserves, T9_deep_nested_if, T10_while_many_iterations,
     T11_compile_correctness]
  ).mapM id
  for r in results do
    if !r then allPass := false
  if allPass then
    IO.println "All integration tests passed."
    return 0
  else
    IO.println "Some integration tests FAILED."
    return 1
