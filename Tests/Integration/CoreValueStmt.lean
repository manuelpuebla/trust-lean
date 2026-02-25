/-
  Trust-Lean Test Suite — Integration Tests for N1.1 (Core Value + Stmt)
  Tests adapted from TESTS_OUTSOURCE.md specifications.
-/

import TrustLean.Core.Value
import TrustLean.Core.Stmt

open TrustLean

/-- Helper: print test result -/
def reportTest (name : String) (passed : Bool) : IO Bool := do
  if passed then
    IO.println s!"[PASS] {name}"
    return true
  else
    IO.println s!"[FAIL] {name}"
    return false

/-- T1 BASIC: evalBinOp add and mul on integers -/
def T1_evalBinOp_int_arith : IO Bool := do
  let r1 := evalBinOp .add (.int 5) (.int 3)
  let r2 := evalBinOp .mul (.int 4) (.int 2)
  reportTest "T1_evalBinOp_int_arith" (r1 == some (.int 8) && r2 == some (.int 8))

/-- T2 EDGE_CASE: evalBinOp division by zero — no div/mod in this IR,
    so we test that eqOp and ltOp work correctly as the comparison ops. -/
def T2_evalBinOp_comparison_ops : IO Bool := do
  -- No div/mod in the IR, test comparison edge cases instead
  let r1 := evalBinOp .eqOp (.int 0) (.int 0)
  let r2 := evalBinOp .ltOp (.int 0) (.int 0)
  reportTest "T2_evalBinOp_comparison_ops" (r1 == some (.bool true) && r2 == some (.bool false))

/-- T3 BASIC: evalBinOp logical ops on booleans -/
def T3_evalBinOp_bool_logic : IO Bool := do
  let r1 := evalBinOp .land (.bool true) (.bool false)
  let r2 := evalBinOp .lor (.bool true) (.bool false)
  reportTest "T3_evalBinOp_bool_logic" (r1 == some (.bool false) && r2 == some (.bool true))

/-- T4 EDGE_CASE: evalBinOp returns none on type mismatch -/
def T4_evalBinOp_type_mismatch : IO Bool := do
  let r := evalBinOp .add (.int 5) (.bool true)
  reportTest "T4_evalBinOp_type_mismatch" (r == none)

/-- T5 BASIC: evalUnaryOp neg and lnot -/
def T5_evalUnaryOp : IO Bool := do
  let r1 := evalUnaryOp .neg (.int 10)
  let r2 := evalUnaryOp .lnot (.bool false)
  reportTest "T5_evalUnaryOp" (r1 == some (.int (-10)) && r2 == some (.bool true))

/-- T6 BASIC: LowLevelEnv update and lookup -/
def T6_env_update_lookup : IO Bool := do
  let vx := VarName.user "x"
  let vy := VarName.user "y"
  let vz := VarName.user "z"
  let env0 := LowLevelEnv.default
  let env1 := env0.update vx (.int 42)
  let env2 := env1.update vy (.bool false)
  let checkX := env2 vx == .int 42
  let checkY := env2 vy == .bool false
  let checkZ := env2 vz == .int 0  -- default value
  reportTest "T6_env_update_lookup" (checkX && checkY && checkZ)

/-- T7 BASIC: Stmt.desugarFor produces correct structure -/
def T7_desugarFor_structure : IO Bool := do
  let varI := VarName.user "i"
  let init := Stmt.assign varI (.litInt 0)
  let cond := LowLevelExpr.binOp .ltOp (.varRef varI) (.litInt 3)
  let body := Stmt.assign varI (.binOp .add (.varRef varI) (.litInt 1))
  let step := Stmt.skip
  let result := Stmt.desugarFor init cond step body
  let expected := Stmt.seq init (Stmt.while cond (Stmt.seq body step))
  -- We check structural equality by repr comparison
  reportTest "T7_desugarFor_structure" (toString (repr result) == toString (repr expected))

/-- T8 EDGE_CASE: desugarFor for zero-iteration loop -/
def T8_desugarFor_zero_iter : IO Bool := do
  let varI := VarName.user "i"
  let init := Stmt.assign varI (.litInt 5)
  let cond := LowLevelExpr.binOp .ltOp (.varRef varI) (.litInt 5)
  let body := Stmt.skip
  let step := Stmt.skip
  let result := Stmt.desugarFor init cond step body
  -- Should be: seq(assign i=5, while(i < 5, seq(skip, skip)))
  -- The while condition will be false immediately since 5 < 5 is false
  let expected := Stmt.seq init (Stmt.while cond (Stmt.seq body step))
  reportTest "T8_desugarFor_zero_iter" (toString (repr result) == toString (repr expected))

/-- T9 EDGE_CASE: assignmentsToStmt on empty list -/
def T9_assignmentsToStmt_empty : IO Bool := do
  let result := assignmentsToStmt []
  reportTest "T9_assignmentsToStmt_empty" (toString (repr result) == toString (repr Stmt.skip))

/-- T10 BASIC: assignmentsToStmt on multi-element list -/
def T10_assignmentsToStmt_multi : IO Bool := do
  let a1 : Assignment := { varName := .user "x", value := .litInt 1 }
  let a2 : Assignment := { varName := .user "y", value := .litInt 2 }
  let result := assignmentsToStmt [a1, a2]
  let expected := Stmt.seq (.assign a1.varName a1.value) (.assign a2.varName a2.value)
  reportTest "T10_assignmentsToStmt_multi" (toString (repr result) == toString (repr expected))

def main : IO UInt32 := do
  let mut allPassed := true
  let tests := [
    T1_evalBinOp_int_arith,
    T2_evalBinOp_comparison_ops,
    T3_evalBinOp_bool_logic,
    T4_evalBinOp_type_mismatch,
    T5_evalUnaryOp,
    T6_env_update_lookup,
    T7_desugarFor_structure,
    T8_desugarFor_zero_iter,
    T9_assignmentsToStmt_empty,
    T10_assignmentsToStmt_multi
  ]
  for test in tests do
    let passed ← test
    if !passed then allPassed := false
  return if allPassed then 0 else 1
