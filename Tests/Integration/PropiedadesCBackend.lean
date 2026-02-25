/-
  Trust-Lean — Tests/Integration/PropiedadesCBackend.lean
  N9.3: Integration tests for CBackendProperties formal guarantees.
  Each test prints [PASS] or [FAIL].
-/

import TrustLean.Backend.CBackend
import TrustLean.Backend.CBackendProperties

set_option autoImplicit false

open TrustLean

/-- Check if `haystack` contains `needle` as a substring. -/
def containsSub (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

-- T1: sanitizeIdentifier handles valid names, keywords, invalid chars
def T1_sanitize_cases : IO Bool := do
  let r1 := sanitizeIdentifier "my_var"
  let r2 := sanitizeIdentifier "while"
  -- "var-name" → strip '-' → "varname"
  let r3 := sanitizeIdentifier "var-name"

  let ok1 := r1 == "my_var"
  let ok2 := r2 == "tl_while"
  let ok3 := r3 == "varname"

  let ok := ok1 && ok2 && ok3
  IO.println (if ok then "[PASS] T1_sanitize_cases"
    else s!"[FAIL] T1_sanitize_cases: '{r1}' '{r2}' '{r3}'")
  return ok

-- T2: generateCHeader includes required standard C headers
def T2_header_includes : IO Bool := do
  let cfg := CConfig.mk true false  -- no power helper for simpler output
  let header := generateCHeader cfg
  let hasStdint := containsSub header "stdint.h"
  let hasStdbool := containsSub header "stdbool.h"
  let ok := hasStdint && hasStdbool
  IO.println (if ok then "[PASS] T2_header_includes"
    else s!"[FAIL] T2_header_includes: stdint={hasStdint} stdbool={hasStdbool}")
  return ok

-- T3: All 12 Stmt constructors produce valid C code snippets
def T3_all_constructors : IO Bool := do
  let stmts : List (String × Stmt) := [
    ("skip", .skip),
    ("assign", .assign (.user "x") (.litInt 42)),
    ("store", .store (.varRef (.user "arr")) (.litInt 0) (.litInt 1)),
    ("load", .load (.user "x") (.varRef (.user "arr")) (.litInt 0)),
    ("seq", .seq (.assign (.user "x") (.litInt 1)) (.assign (.user "y") (.litInt 2))),
    ("ite", .ite (.litBool true) (.assign (.user "x") (.litInt 1)) .skip),
    ("while", .while (.litBool false) .skip),
    ("for_", .for_ (.assign (.user "i") (.litInt 0)) (.litBool true)
                    (.assign (.user "i") (.litInt 1)) .skip),
    ("call", .call (.user "r") "func" [.litInt 1, .litInt 2]),
    ("break_", .break_),
    ("continue_", .continue_),
    ("return_", .return_ (some (.litInt 0)))
  ]
  let mut allOk := true
  for (name, stmt) in stmts do
    let code := stmtToC 0 stmt
    -- skip produces empty string, which is valid
    if name != "skip" && code.isEmpty then
      IO.println s!"[FAIL] T3_all_constructors: {name} produced empty output"
      allOk := false
  IO.println (if allOk then "[PASS] T3_all_constructors"
    else "[FAIL] T3_all_constructors: some constructors failed")
  return allOk

-- T4: Stmt.ite without else (using skip) still generates else block (mandatory braces)
def T4_ite_with_skip_else : IO Bool := do
  let cond := LowLevelExpr.litBool true
  let thenB := Stmt.assign (.user "x") (.litInt 1)
  let iteStmt := Stmt.ite cond thenB .skip
  let result := stmtToC 0 iteStmt
  -- CBackend always emits "} else {" (mandatory braces)
  let hasIf := containsSub result "if ("
  let hasElse := containsSub result "} else {"
  let ok := hasIf && hasElse
  IO.println (if ok then "[PASS] T4_ite_with_skip_else"
    else s!"[FAIL] T4_ite_with_skip_else: if={hasIf} else={hasElse}\n  got: '{result}'")
  return ok

-- T5: Store/load with complex base address correctly parenthesized
def T5_complex_store : IO Bool := do
  -- store (arr + offset)[0] = 100
  let base := LowLevelExpr.binOp .add (.varRef (.user "arr")) (.varRef (.user "offset"))
  let idx := LowLevelExpr.litInt 0
  let storeStmt := Stmt.store base idx (.litInt 100)
  let result := stmtToC 0 storeStmt
  -- Expected: (arr + offset)[0] = 100;
  let ok := containsSub result "(arr + offset)[0] = 100;"
  IO.println (if ok then "[PASS] T5_complex_store"
    else s!"[FAIL] T5_complex_store: got '{result}'")
  return ok

-- T6: Empty main function compiles to valid minimal C
def T6_empty_main : IO Bool := do
  let cfg := CConfig.mk true true
  let func := generateCFunction cfg "main_func" [] .skip (.litInt 0)
  let hasReturn := containsSub func "return 0;"
  let hasBraces := containsSub func "{" && containsSub func "}"
  let opens := countChar '{' func
  let closes := countChar '}' func
  let balanced := opens == closes
  let ok := hasReturn && hasBraces && balanced
  IO.println (if ok then "[PASS] T6_empty_main"
    else s!"[FAIL] T6_empty_main: return={hasReturn} balanced={balanced}\n  got: '{func}'")
  return ok

-- T7: Deeply nested control flow maintains correct brace structure
def T7_deep_nesting : IO Bool := do
  -- for { while { if { assign } skip } }
  let innerAssign := Stmt.assign (.user "x") (.litInt 1)
  let innerIf := Stmt.ite (.litBool true) innerAssign .skip
  let innerWhile := Stmt.while (.litBool false) innerIf
  let forInit := Stmt.assign (.user "i") (.litInt 0)
  let forCond := LowLevelExpr.binOp .ltOp (.varRef (.user "i")) (.litInt 5)
  let forStep := Stmt.assign (.user "i") (.binOp .add (.varRef (.user "i")) (.litInt 1))
  let outerFor := Stmt.for_ forInit forCond forStep innerWhile
  let result := stmtToC 0 outerFor
  let opens := countChar '{' result
  let closes := countChar '}' result
  let balanced := opens == closes
  let ok := balanced && opens > 0
  IO.println (if ok then s!"[PASS] T7_deep_nesting (braces: {opens}/{closes})"
    else s!"[FAIL] T7_deep_nesting: balanced={balanced} opens={opens} closes={closes}")
  return ok

-- T8: All binary and unary operators translated to C equivalents
def T8_all_operators : IO Bool := do
  let binTests : List (BinOp × String) :=
    [(.add, "+"), (.sub, "-"), (.mul, "*"), (.eqOp, "=="), (.ltOp, "<"),
     (.land, "&&"), (.lor, "||")]
  let mut ok := true
  for (op, cOp) in binTests do
    let result := exprToC (.binOp op (.varRef (.user "x")) (.varRef (.user "y")))
    if !containsSub result cOp then
      IO.println s!"[FAIL] T8_all_operators: binOp '{cOp}' not in '{result}'"
      ok := false

  let unaryTests : List (UnaryOp × String) :=
    [(.neg, "-"), (.lnot, "!")]
  for (op, cOp) in unaryTests do
    let result := exprToC (.unaryOp op (.varRef (.user "x")))
    if !containsSub result cOp then
      IO.println s!"[FAIL] T8_all_operators: unaryOp '{cOp}' not in '{result}'"
      ok := false

  if ok then IO.println "[PASS] T8_all_operators"
  return ok

def main : IO UInt32 := do
  let results := #[
    (← T1_sanitize_cases),
    (← T2_header_includes),
    (← T3_all_constructors),
    (← T4_ite_with_skip_else),
    (← T5_complex_store),
    (← T6_empty_main),
    (← T7_deep_nesting),
    (← T8_all_operators)
  ]
  let passed := results.filter (· == true) |>.size
  let total := results.size
  IO.println s!"\nN9.3 Integration: {passed}/{total} passed"
  return if passed == total then 0 else 1

-- #eval calls for test runner (lake env lean captures this output)
#eval T1_sanitize_cases
#eval T2_header_includes
#eval T3_all_constructors
#eval T4_ite_with_skip_else
#eval T5_complex_store
#eval T6_empty_main
#eval T7_deep_nesting
#eval T8_all_operators
