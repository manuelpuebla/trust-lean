/-
  Trust-Lean — Tests/Integration/CBackendRefactor.lean
  N9.2: Integration tests for CBackend refactored emission.
  Each test prints [PASS] or [FAIL].
-/

import TrustLean.Backend.CBackend
import TrustLean.Backend.CBackendProperties

set_option autoImplicit false

open TrustLean

/-- Check if `haystack` contains `needle` as a substring. -/
def containsSub (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

-- T1: Simple assignment statement generation
def T1_assignment : IO Bool := do
  let stmt := Stmt.assign (.user "x") (.binOp .add (.varRef (.user "y")) (.litInt 1))
  let result := stmtToC 0 stmt
  let expected := "x = (y + 1);"
  let ok := result == expected
  IO.println (if ok then "[PASS] T1_assignment"
    else s!"[FAIL] T1_assignment: expected '{expected}', got '{result}'")
  return ok

-- T2: If-Then-Else statement generation
def T2_ite : IO Bool := do
  let cond := LowLevelExpr.varRef (.user "flag")
  let thenB := Stmt.assign (.user "x") (.litInt 1)
  let elseB := Stmt.assign (.user "x") (.litInt 0)
  let stmt := Stmt.ite cond thenB elseB
  let result := stmtToC 0 stmt
  let hasIf := containsSub result "if ("
  let hasElse := containsSub result "} else {"
  let ok := hasIf && hasElse
  IO.println (if ok then "[PASS] T2_ite"
    else s!"[FAIL] T2_ite: if={hasIf} else={hasElse}\n  got: '{result}'")
  return ok

-- T3: For loop generation (desugared to while)
def T3_for_loop : IO Bool := do
  let init := Stmt.assign (.user "i") (.litInt 0)
  let cond := LowLevelExpr.binOp .ltOp (.varRef (.user "i")) (.litInt 10)
  let step := Stmt.assign (.user "i") (.binOp .add (.varRef (.user "i")) (.litInt 1))
  let body := Stmt.skip
  let stmt := Stmt.for_ init cond step body
  let result := stmtToC 0 stmt
  let hasAssign := containsSub result "i = 0;"
  let hasWhile := containsSub result "while ("
  let ok := hasAssign && hasWhile
  IO.println (if ok then "[PASS] T3_for_loop"
    else s!"[FAIL] T3_for_loop: assign={hasAssign} while={hasWhile}\n  got: '{result}'")
  return ok

-- T4: All BinOp and UnaryOp variants translated correctly
def T4_operators : IO Bool := do
  let binOps : List (BinOp × String) :=
    [(.add, "+"), (.sub, "-"), (.mul, "*"), (.eqOp, "=="), (.ltOp, "<"),
     (.land, "&&"), (.lor, "||")]
  let mut binOk := true
  for (op, expected) in binOps do
    let result := exprToC (.binOp op (.varRef (.user "a")) (.varRef (.user "b")))
    if !containsSub result expected then
      IO.println s!"[FAIL] T4_operators: binOp {expected} not found in '{result}'"
      binOk := false

  let unaryOps : List (UnaryOp × String) :=
    [(.neg, "-"), (.lnot, "!")]
  let mut unaryOk := true
  for (op, expected) in unaryOps do
    let result := exprToC (.unaryOp op (.varRef (.user "a")))
    if !containsSub result expected then
      IO.println s!"[FAIL] T4_operators: unaryOp {expected} not found in '{result}'"
      unaryOk := false

  let ok := binOk && unaryOk
  if ok then IO.println "[PASS] T4_operators"
  return ok

-- T5: Store and Load expressions with array access
def T5_store_load : IO Bool := do
  let storeStmt := Stmt.store (.varRef (.user "arr")) (.litInt 3) (.litInt 42)
  let storeResult := stmtToC 0 storeStmt
  let storeOk := containsSub storeResult "arr[3] = 42;"

  let loadStmt := Stmt.load (.user "x") (.varRef (.user "arr")) (.litInt 3)
  let loadResult := stmtToC 0 loadStmt
  let loadOk := containsSub loadResult "x = arr[3];"

  let ok := storeOk && loadOk
  IO.println (if ok then "[PASS] T5_store_load"
    else s!"[FAIL] T5_store_load: store={storeOk} load={loadOk}\n  store: '{storeResult}'\n  load: '{loadResult}'")
  return ok

-- T6: Variable names that are C keywords are sanitized
def T6_keyword_sanitization : IO Bool := do
  let stmt := Stmt.assign (.user "int") (.litInt 5)
  let result := stmtToC 0 stmt
  let ok := containsSub result "tl_int"
  IO.println (if ok then "[PASS] T6_keyword_sanitization"
    else s!"[FAIL] T6_keyword_sanitization: got '{result}'")
  return ok

-- T7: Variable names with invalid C characters are sanitized
def T7_invalid_char_sanitization : IO Bool := do
  let result := varNameToC (.user "a-b")
  let ok := result == "ab"
  IO.println (if ok then "[PASS] T7_invalid_char_sanitization"
    else s!"[FAIL] T7_invalid_char_sanitization: got '{result}'")
  return ok

-- T8: Control flow with empty bodies
def T8_empty_bodies : IO Bool := do
  let iteStmt := Stmt.ite (.litBool true) .skip .skip
  let iteResult := stmtToC 0 iteStmt
  let iteOk := containsSub iteResult "if (" && containsSub iteResult "} else {"

  let forStmt := Stmt.for_ .skip (.litBool false) .skip .skip
  let forResult := stmtToC 0 forStmt
  let forOk := containsSub forResult "while ("

  let ok := iteOk && forOk
  IO.println (if ok then "[PASS] T8_empty_bodies"
    else s!"[FAIL] T8_empty_bodies: ite={iteOk} for={forOk}")
  return ok

-- T9: Function with no arguments and empty body
def T9_empty_function : IO Bool := do
  let cfg := CConfig.mk true true
  let result := generateCFunction cfg "my_func" [] .skip (.litInt 0)
  let hasName := containsSub result "my_func"
  let hasReturn := containsSub result "return 0;"
  let hasBraces := containsSub result "{" && containsSub result "}"
  let ok := hasName && hasReturn && hasBraces
  IO.println (if ok then "[PASS] T9_empty_function"
    else s!"[FAIL] T9_empty_function: name={hasName} return={hasReturn} braces={hasBraces}\n  got: '{result}'")
  return ok

-- T10: Full function and header generation
def T10_full_function_and_header : IO Bool := do
  let cfg := CConfig.mk true true
  let body := Stmt.assign (.user "z") (.binOp .add (.varRef (.user "x")) (.varRef (.user "y")))
  let func := generateCFunction cfg "compute" [("x", "int64_t"), ("y", "int64_t")] body (.varRef (.user "z"))
  let header := generateCHeader cfg

  let funcOk := containsSub func "int64_t compute(" && containsSub func "return z;"
  let headerOk := containsSub header "stdint.h" && containsSub header "stdbool.h"

  let ok := funcOk && headerOk
  IO.println (if ok then "[PASS] T10_full_function_and_header"
    else s!"[FAIL] T10_full_function_and_header: func={funcOk} header={headerOk}")
  return ok

-- T11: GCC compilation structural check
-- (Cannot run gcc from Lean in this test setup; verify structural soundness instead)
def T11_gcc_compilation_structural : IO Bool := do
  let cfg := CConfig.mk true true
  let body := Stmt.seq
    (Stmt.assign (.user "z") (.binOp .add (.varRef (.user "x")) (.varRef (.user "y"))))
    (Stmt.ite (.binOp .ltOp (.varRef (.user "z")) (.litInt 0))
      (Stmt.assign (.user "z") (.binOp .mul (.varRef (.user "z")) (.litInt (-1))))
      .skip)
  let header := generateCHeader cfg
  let func := generateCFunction cfg "abs_sum" [("x", "int64_t"), ("y", "int64_t")] body (.varRef (.user "z"))
  let full := header ++ "\n\n" ++ func

  let hasIncludes := containsSub full "#include <stdint.h>" && containsSub full "#include <stdbool.h>"
  let hasReturnType := containsSub full "int64_t abs_sum("
  let hasReturn := containsSub full "return z;"
  let opens := countChar '{' full
  let closes := countChar '}' full
  let balanced := opens == closes

  let ok := hasIncludes && hasReturnType && hasReturn && balanced
  IO.println (if ok then "[PASS] T11_gcc_structural"
    else s!"[FAIL] T11_gcc_structural: includes={hasIncludes} type={hasReturnType} return={hasReturn} balanced={balanced}")
  return ok

-- T12: Operator precedence — binary ops are fully parenthesized
def T12_precedence : IO Bool := do
  let expr := LowLevelExpr.binOp .add
    (.varRef (.user "a"))
    (.binOp .mul (.varRef (.user "b")) (.varRef (.user "c")))
  let result := exprToC expr
  let ok := result == "(a + (b * c))"
  IO.println (if ok then "[PASS] T12_precedence"
    else s!"[FAIL] T12_precedence: got '{result}'")
  return ok

def main : IO UInt32 := do
  let results := #[
    (← T1_assignment),
    (← T2_ite),
    (← T3_for_loop),
    (← T4_operators),
    (← T5_store_load),
    (← T6_keyword_sanitization),
    (← T7_invalid_char_sanitization),
    (← T8_empty_bodies),
    (← T9_empty_function),
    (← T10_full_function_and_header),
    (← T11_gcc_compilation_structural),
    (← T12_precedence)
  ]
  let passed := results.filter (· == true) |>.size
  let total := results.size
  IO.println s!"\nN9.2 Integration: {passed}/{total} passed"
  return if passed == total then 0 else 1

-- #eval calls for test runner (lake env lean captures this output)
#eval T1_assignment
#eval T2_ite
#eval T3_for_loop
#eval T4_operators
#eval T5_store_load
#eval T6_keyword_sanitization
#eval T7_invalid_char_sanitization
#eval T8_empty_bodies
#eval T9_empty_function
#eval T10_full_function_and_header
#eval T11_gcc_compilation_structural
#eval T12_precedence
