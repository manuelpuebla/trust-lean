/-
  Trust-Lean — Tests/Integration/IntegrationRegression.lean
  N9.4: Integration + regression tests for CBackend industrial.
  Each test prints [PASS] or [FAIL].
-/

import TrustLean.Pipeline
import TrustLean.Frontend.ArithExpr
import TrustLean.Frontend.BoolExpr
import TrustLean.Backend.CBackend
import TrustLean.Backend.CBackendProperties
import TrustLean.Backend.RustBackend
import TrustLean.Bridge

set_option autoImplicit false

open TrustLean TrustLean.Bridge

/-- Check if `haystack` contains `needle` as a substring. -/
def containsSub (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

-- T1: Simple arithmetic and variable assignment (structural)
def T1_arithmetic : IO Bool := do
  let body := Stmt.seq
    (Stmt.assign (.user "x") (.litInt 10))
    (Stmt.seq
      (Stmt.assign (.user "y") (.litInt 20))
      (Stmt.assign (.user "z") (.binOp .add (.varRef (.user "x")) (.varRef (.user "y")))))
  let cfg := CConfig.mk true true
  let func := generateCFunction cfg "sum_test" [] body (.varRef (.user "z"))
  let ok := containsSub func "z = (x + y);" && containsSub func "return z;"
  IO.println (if ok then "[PASS] T1_arithmetic"
    else s!"[FAIL] T1_arithmetic: got '{func}'")
  return ok

-- T2: Conditional if-then-else logic
def T2_conditional : IO Bool := do
  let body := Stmt.ite (.varRef (.user "flag"))
    (Stmt.assign (.user "result") (.litInt 1))
    (Stmt.assign (.user "result") (.litInt 0))
  let code := stmtToC 0 body
  let hasIf := containsSub code "if (flag)"
  let hasThen := containsSub code "result = 1;"
  let hasElse := containsSub code "result = 0;"
  let ok := hasIf && hasThen && hasElse
  IO.println (if ok then "[PASS] T2_conditional"
    else s!"[FAIL] T2_conditional: if={hasIf} then={hasThen} else={hasElse}")
  return ok

-- T3: While loop functionality
def T3_while_loop : IO Bool := do
  let body := Stmt.seq
    (Stmt.assign (.user "counter") (.litInt 0))
    (Stmt.while
      (.binOp .ltOp (.varRef (.user "counter")) (.litInt 5))
      (Stmt.assign (.user "counter")
        (.binOp .add (.varRef (.user "counter")) (.litInt 1))))
  let code := stmtToC 0 body
  let hasInit := containsSub code "counter = 0;"
  let hasWhile := containsSub code "while ("
  let hasIncrement := containsSub code "counter = (counter + 1);"
  let ok := hasInit && hasWhile && hasIncrement
  IO.println (if ok then "[PASS] T3_while_loop"
    else s!"[FAIL] T3_while_loop: init={hasInit} while={hasWhile} incr={hasIncrement}")
  return ok

-- T4: Array store and load
def T4_array_store_load : IO Bool := do
  let body := Stmt.seq
    (Stmt.store (.varRef (.user "arr")) (.litInt 3) (.litInt 42))
    (Stmt.load (.user "x") (.varRef (.user "arr")) (.litInt 3))
  let code := stmtToC 0 body
  let hasStore := containsSub code "arr[3] = 42;"
  let hasLoad := containsSub code "x = arr[3];"
  let ok := hasStore && hasLoad
  IO.println (if ok then "[PASS] T4_array_store_load"
    else s!"[FAIL] T4_array_store_load: store={hasStore} load={hasLoad}")
  return ok

-- T5: Empty program generates valid C
def T5_empty_program : IO Bool := do
  let cfg := CConfig.mk true true
  let func := generateCFunction cfg "empty_main" [] .skip (.litInt 0)
  let header := generateCHeader cfg
  let full := header ++ "\n\n" ++ func
  let hasIncludes := containsSub full "#include <stdint.h>"
  let hasReturn := containsSub full "return 0;"
  let opens := countChar '{' full
  let closes := countChar '}' full
  let balanced := opens == closes
  let ok := hasIncludes && hasReturn && balanced
  IO.println (if ok then "[PASS] T5_empty_program"
    else s!"[FAIL] T5_empty_program: includes={hasIncludes} return={hasReturn} balanced={balanced}")
  return ok

-- T6: Loop with zero iterations (while false)
def T6_zero_iterations : IO Bool := do
  let body := Stmt.while (.litBool false)
    (Stmt.assign (.user "x") (.litInt 999))
  let code := stmtToC 0 body
  let hasWhile := containsSub code "while (0)"
  let ok := hasWhile
  IO.println (if ok then "[PASS] T6_zero_iterations"
    else s!"[FAIL] T6_zero_iterations: got '{code}'")
  return ok

-- T7: Deeply nested control flow
def T7_deep_nesting : IO Bool := do
  -- for { if { while { assign } skip } }
  let innerAssign := Stmt.assign (.user "val") (.litInt 1)
  let innerWhile := Stmt.while (.litBool false) innerAssign
  let innerIf := Stmt.ite (.varRef (.user "flag")) innerWhile .skip
  let forInit := Stmt.assign (.user "i") (.litInt 0)
  let forCond := LowLevelExpr.binOp .ltOp (.varRef (.user "i")) (.litInt 10)
  let forStep := Stmt.assign (.user "i") (.binOp .add (.varRef (.user "i")) (.litInt 1))
  let outerFor := Stmt.for_ forInit forCond forStep innerIf
  let code := stmtToC 0 outerFor
  let opens := countChar '{' code
  let closes := countChar '}' code
  let balanced := opens == closes
  let hasControl := containsSub code "while (" && containsSub code "if ("
  let ok := balanced && hasControl && opens >= 3
  IO.println (if ok then s!"[PASS] T7_deep_nesting (braces: {opens}/{closes})"
    else s!"[FAIL] T7_deep_nesting: balanced={balanced} control={hasControl} opens={opens}")
  return ok

-- T8: Operator precedence (full parenthesization)
def T8_precedence : IO Bool := do
  -- (a + b) * c vs a + (b * c)
  let expr1 := LowLevelExpr.binOp .mul
    (.binOp .add (.varRef (.user "a")) (.varRef (.user "b")))
    (.varRef (.user "c"))
  let expr2 := LowLevelExpr.binOp .add
    (.varRef (.user "a"))
    (.binOp .mul (.varRef (.user "b")) (.varRef (.user "c")))
  let r1 := exprToC expr1
  let r2 := exprToC expr2
  let ok := r1 == "((a + b) * c)" && r2 == "(a + (b * c))"
  IO.println (if ok then "[PASS] T8_precedence"
    else s!"[FAIL] T8_precedence: r1='{r1}' r2='{r2}'")
  return ok

-- T9: Array access with complex index expression
def T9_complex_index : IO Bool := do
  -- arr[(a + b) * 2]
  let idx := LowLevelExpr.binOp .mul
    (.binOp .add (.varRef (.user "a")) (.varRef (.user "b")))
    (.litInt 2)
  let loadStmt := Stmt.load (.user "val") (.varRef (.user "arr")) idx
  let code := stmtToC 0 loadStmt
  -- Expected: val = arr[((a + b) * 2)];
  let ok := containsSub code "arr[((a + b) * 2)]"
  IO.println (if ok then "[PASS] T9_complex_index"
    else s!"[FAIL] T9_complex_index: got '{code}'")
  return ok

-- T10: Identifier sanitization (keywords become tl_ prefixed)
def T10_identifier_sanitization : IO Bool := do
  -- Variable named "int" should become "tl_int"
  let stmt1 := Stmt.assign (.user "int") (.litInt 5)
  let stmt2 := Stmt.assign (.user "for") (.litInt 10)
  let code := stmtToC 0 (Stmt.seq stmt1 stmt2)
  let ok := containsSub code "tl_int" && containsSub code "tl_for"
  IO.println (if ok then "[PASS] T10_identifier_sanitization"
    else s!"[FAIL] T10_identifier_sanitization: got '{code}'")
  return ok

-- T11: Large number of sequential statements (stress)
def T11_stress_sequential : IO Bool := do
  -- Build 100 sequential assignments (500 would be slow to compile)
  let mut stmt := Stmt.skip
  for i in List.range 100 do
    stmt := Stmt.seq stmt (Stmt.assign (.user s!"x{i}") (.litInt i))
  let code := stmtToC 0 stmt
  let opens := countChar '{' code
  let closes := countChar '}' code
  let balanced := opens == closes
  let hasFirst := containsSub code "x0 = 0;"
  let hasLast := containsSub code "x99 = 99;"
  let ok := balanced && hasFirst && hasLast && code.length > 500
  IO.println (if ok then s!"[PASS] T11_stress_sequential ({code.length} chars)"
    else s!"[FAIL] T11_stress_sequential: balanced={balanced} first={hasFirst} last={hasLast} len={code.length}")
  return ok

-- T12: Signed integer division semantics (structural)
-- The IR uses evalBinOp which doesn't have div. We test negative literal emission.
def T12_negative_literals : IO Bool := do
  let expr := LowLevelExpr.litInt (-10)
  let code := exprToC expr
  -- Negative literal should be parenthesized
  let ok := code == "(-10)"
  IO.println (if ok then "[PASS] T12_negative_literals"
    else s!"[FAIL] T12_negative_literals: got '{code}'")
  return ok

-- T13: Boolean expression with short-circuit operators
def T13_boolean_shortcircuit : IO Bool := do
  -- if (x != 0 && y / x > 1) → uses land (&&) in C
  let cond := LowLevelExpr.binOp .land
    (.unaryOp .lnot (.binOp .eqOp (.varRef (.user "x")) (.litInt 0)))
    (.binOp .ltOp (.litInt 1) (.varRef (.user "y")))
  let stmt := Stmt.ite cond (Stmt.assign (.user "r") (.litInt 1)) .skip
  let code := stmtToC 0 stmt
  let hasAnd := containsSub code "&&"
  let ok := hasAnd
  IO.println (if ok then "[PASS] T13_boolean_shortcircuit"
    else s!"[FAIL] T13_boolean_shortcircuit: got '{code}'")
  return ok

-- T14: All Stmt constructors handled (comprehensive)
def T14_all_constructors : IO Bool := do
  let allStmts : List (String × Stmt) := [
    ("assign", .assign (.user "x") (.litInt 1)),
    ("store", .store (.varRef (.user "arr")) (.litInt 0) (.litInt 1)),
    ("load", .load (.user "x") (.varRef (.user "arr")) (.litInt 0)),
    ("seq", .seq (.assign (.user "a") (.litInt 1)) (.assign (.user "b") (.litInt 2))),
    ("ite", .ite (.litBool true) (.assign (.user "x") (.litInt 1)) .skip),
    ("while", .while (.litBool false) .skip),
    ("for_", .for_ (.assign (.user "i") (.litInt 0)) (.litBool true)
                    (.assign (.user "i") (.litInt 1)) .skip),
    ("call", .call (.user "r") "func" [.litInt 1, .litInt 2]),
    ("skip", .skip),
    ("break_", .break_),
    ("continue_", .continue_),
    ("return_", .return_ (some (.litInt 0)))
  ]
  let mut allOk := true
  let mut failedNames := #[]
  for (name, stmt) in allStmts do
    let code := stmtToC 0 stmt
    -- Only skip should produce empty string
    if name != "skip" && code.isEmpty then
      allOk := false
      failedNames := failedNames.push name
  IO.println (if allOk then "[PASS] T14_all_constructors (12/12)"
    else s!"[FAIL] T14_all_constructors: failed={failedNames}")
  return allOk

-- T15: stdint.h inclusion
def T15_stdint_inclusion : IO Bool := do
  let header := generateCHeader (CConfig.mk true true)
  let ok := containsSub header "#include <stdint.h>"
  IO.println (if ok then "[PASS] T15_stdint_inclusion"
    else s!"[FAIL] T15_stdint_inclusion")
  return ok

-- T16: stdbool.h inclusion
def T16_stdbool_inclusion : IO Bool := do
  let header := generateCHeader (CConfig.mk true true)
  let ok := containsSub header "#include <stdbool.h>"
  IO.println (if ok then "[PASS] T16_stdbool_inclusion"
    else s!"[FAIL] T16_stdbool_inclusion")
  return ok

/-! ## Regression Tests -/

-- REG-1: Pipeline.sound for ArithExpr still type-checks
example : ∀ (a : ArithExpr) (env : VarId → Value) (llEnv : LowLevelEnv),
    CodeGenSound.wellTyped a env →
    (∀ v, llEnv (.user (CodeGenerable.varNames (α := ArithExpr) v)) = env v) →
    ∃ (fuel : Nat) (resultEnv : LowLevelEnv),
      evalStmt fuel llEnv (Pipeline.lower a).stmt = some (.normal, resultEnv) ∧
      evalExpr resultEnv (Pipeline.lower a).resultVar = some (CodeGenerable.denote a env) ∧
      ∀ v, resultEnv (.user (CodeGenerable.varNames (α := ArithExpr) v)) = env v :=
  fun a env llEnv hwt hb => Pipeline.sound a env llEnv hwt hb

-- REG-2: Pipeline.sound for BoolExpr still type-checks
example : ∀ (a : BoolExpr) (env : VarId → Value) (llEnv : LowLevelEnv),
    CodeGenSound.wellTyped a env →
    (∀ v, llEnv (.user (CodeGenerable.varNames (α := BoolExpr) v)) = env v) →
    ∃ (fuel : Nat) (resultEnv : LowLevelEnv),
      evalStmt fuel llEnv (Pipeline.lower a).stmt = some (.normal, resultEnv) ∧
      evalExpr resultEnv (Pipeline.lower a).resultVar = some (CodeGenerable.denote a env) ∧
      ∀ v, resultEnv (.user (CodeGenerable.varNames (α := BoolExpr) v)) = env v :=
  fun a env llEnv hwt hb => Pipeline.sound a env llEnv hwt hb

-- REG-3: expandedSigmaToStmt_correct still type-checks
example := @expandedSigmaToStmt_correct

-- REG-4: BackendEmitter CConfig instance resolves
example : BackendEmitter CConfig := inferInstance

-- REG-5: BackendEmitter RustConfig instance resolves
example : BackendEmitter RustConfig := inferInstance

def main : IO UInt32 := do
  let results := #[
    (← T1_arithmetic),
    (← T2_conditional),
    (← T3_while_loop),
    (← T4_array_store_load),
    (← T5_empty_program),
    (← T6_zero_iterations),
    (← T7_deep_nesting),
    (← T8_precedence),
    (← T9_complex_index),
    (← T10_identifier_sanitization),
    (← T11_stress_sequential),
    (← T12_negative_literals),
    (← T13_boolean_shortcircuit),
    (← T14_all_constructors),
    (← T15_stdint_inclusion),
    (← T16_stdbool_inclusion)
  ]
  let passed := results.filter (· == true) |>.size
  let total := results.size
  IO.println s!"\nN9.4 Integration: {passed}/{total} passed"
  IO.println "Regression tests: 5 type-checking examples verified at compile time"
  return if passed == total then 0 else 1

-- #eval calls for test runner (lake env lean captures this output)
#eval T1_arithmetic
#eval T2_conditional
#eval T3_while_loop
#eval T4_array_store_load
#eval T5_empty_program
#eval T6_zero_iterations
#eval T7_deep_nesting
#eval T8_precedence
#eval T9_complex_index
#eval T10_identifier_sanitization
#eval T11_stress_sequential
#eval T12_negative_literals
#eval T13_boolean_shortcircuit
#eval T14_all_constructors
#eval T15_stdint_inclusion
#eval T16_stdbool_inclusion
