/-
  Trust-Lean Test Suite — Integration Tests for N1.3 (Typeclasses)
  Tests adapted from TESTS_OUTSOURCE.md specifications.
-/

import TrustLean.Typeclass.CodeGenerable
import TrustLean.Typeclass.CodeGenSound
import TrustLean.Typeclass.BackendEmitter
import TrustLean.Backend.CBackend
import TrustLean.Backend.Common
import TrustLean.Backend.CBackendProperties

open TrustLean

/-- Helper: print test result -/
def reportTest (name : String) (passed : Bool) : IO Bool := do
  if passed then
    IO.println s!"[PASS] {name}"
    return true
  else
    IO.println s!"[FAIL] {name}"
    return false

/-- Helper: check if a string contains a substring -/
def String.containsSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-- Helper: count character occurrences in a string -/
def charCount (c : Char) (s : String) : Nat :=
  s.toList.filter (· == c) |>.length

/-- T1 BASIC: End-to-end code generation for assignments.
    x := 10; y := x + 5;
    Check: output contains assignment syntax. -/
def T1_codegen_assignments : IO Bool := do
  let cfg : CConfig := {}
  let s := Stmt.seq
    (.assign (.user "x") (.litInt 10))
    (.assign (.user "y") (.binOp .add (.varRef (.user "x")) (.litInt 5)))
  let code := BackendEmitter.emitStmt cfg 0 s
  -- Check code contains expected patterns
  let hasX := code.containsSubstr "x = 10"
  let hasY := code.containsSubstr "y = (x + 5)"
  reportTest "T1_codegen_assignments" (hasX && hasY)

/-- T2 EDGE_CASE: Code generation for skip (no-op). -/
def T2_codegen_skip : IO Bool := do
  let cfg : CConfig := {}
  let code := BackendEmitter.emitStmt cfg 0 Stmt.skip
  -- skip emits empty string
  reportTest "T2_codegen_skip" (code == "")

/-- T3 BASIC: Nested control flow (while containing if). -/
def T3_codegen_nested_control : IO Bool := do
  let cfg : CConfig := {}
  let s := Stmt.while (.litBool true)
    (Stmt.ite (.varRef (.user "x")) (.assign (.user "y") (.litInt 1)) .skip)
  let code := BackendEmitter.emitStmt cfg 0 s
  -- Check balanced braces
  let openBraces := charCount '{' code
  let closeBraces := charCount '}' code
  let hasWhile := code.containsSubstr "while"
  let hasIf := code.containsSubstr "if"
  reportTest "T3_codegen_nested_control" (openBraces == closeBraces && hasWhile && hasIf)

/-- T4 EDGE_CASE: Identifier sanitization for C keywords. -/
def T4_sanitize_keywords : IO Bool := do
  let cfg : CConfig := {}
  -- Assign to variables named "for", "continue", "my-variable"
  let s := Stmt.seq
    (.assign (.user "for") (.litInt 1))
    (Stmt.seq
      (.assign (.user "continue") (.litInt 2))
      (.assign (.user "my-variable") (.litInt 3)))
  let code := BackendEmitter.emitStmt cfg 0 s
  -- Should use sanitized names: tl_for, tl_continue, myvariable (hyphen removed)
  let hasTlFor := code.containsSubstr "tl_for"
  let hasTlContinue := code.containsSubstr "tl_continue"
  -- "my-variable" -> characters filtered, hyphen removed -> "myvariable"
  let hasSanitizedMyVar := code.containsSubstr "myvariable"
  reportTest "T4_sanitize_keywords" (hasTlFor && hasTlContinue && hasSanitizedMyVar)

/-- T5 BASIC: Coverage of Stmt constructors.
    Check that emitting each constructor does not fail. -/
def T5_stmt_coverage : IO Bool := do
  let cfg : CConfig := {}
  let stmts : List Stmt := [
    .assign (.user "x") (.litInt 1),
    .store (.varRef (.user "arr")) (.litInt 0) (.litInt 42),
    .load (.user "x") (.varRef (.user "arr")) (.litInt 0),
    .seq (.assign (.user "a") (.litInt 1)) (.assign (.user "b") (.litInt 2)),
    .ite (.litBool true) .skip .skip,
    .while (.litBool false) .skip,
    .for_ .skip (.litBool false) .skip .skip,
    .call (.user "r") "my_func" [.litInt 1, .litInt 2],
    .skip,
    .break_,
    .continue_,
    .return_ (some (.litInt 0)),
    .return_ none
  ]
  let mut allNonEmpty := true
  for s in stmts do
    let code := BackendEmitter.emitStmt cfg 0 s
    -- skip emits "", which is fine for that constructor
    if code.isEmpty && !(match s with | Stmt.skip => true | _ => false) then
      allNonEmpty := false
  -- All non-skip constructors should produce non-empty code
  -- skip produces "" which is semantically correct
  reportTest "T5_stmt_coverage" allNonEmpty

/-- T6 EDGE_CASE: Code generation for memory operations (load/store). -/
def T6_codegen_memory : IO Bool := do
  let cfg : CConfig := {}
  -- store(base, 0, 42); x := load(base, 1);
  let base := LowLevelExpr.varRef (.user "base")
  let s := Stmt.seq
    (.store base (.litInt 0) (.litInt 42))
    (.load (.user "x") base (.litInt 1))
  let code := BackendEmitter.emitStmt cfg 0 s
  -- Check for array access syntax: base[0] and base[1]
  let hasStore := code.containsSubstr "base[0]"
  let hasLoad := code.containsSubstr "base[1]"
  let hasValue := code.containsSubstr "42"
  reportTest "T6_codegen_memory" (hasStore && hasLoad && hasValue)

def main : IO UInt32 := do
  let mut allPassed := true
  let tests := [
    T1_codegen_assignments,
    T2_codegen_skip,
    T3_codegen_nested_control,
    T4_sanitize_keywords,
    T5_stmt_coverage,
    T6_codegen_memory
  ]
  for test in tests do
    let passed ← test
    if !passed then allPassed := false
  return if allPassed then 0 else 1
