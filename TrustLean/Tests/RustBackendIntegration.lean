/-
  Trust-Lean — Verified Code Generation Framework
  Tests/RustBackendIntegration.lean: Integration tests for Rust backend

  N23.1 (v3.2.0): Smoke tests for all 12 Stmt constructors,
  non-vacuity witnesses, and regression verification.
-/

import TrustLean.Backend.RustBackend
import TrustLean.Backend.RustBackendProperties
import TrustLean.Backend.Common

set_option autoImplicit false

namespace TrustLean

/-! ## Smoke Tests: All 12 Stmt Constructors Produce Expected Rust -/

-- skip: empty string
#eval do
  let r := stmtToRust 0 .skip
  assert! r == ""

-- assign: variable assignment
#eval do
  let r := stmtToRust 0 (.assign (.user "x") (.litInt 42))
  assert! r == "x = 42;"

-- store: array store with "as usize"
#eval do
  let r := stmtToRust 0 (.store (.varRef (.user "arr")) (.litInt 0) (.litInt 99))
  assert! r.containsSubstr "as usize"

-- load: array load with "as usize"
#eval do
  let r := stmtToRust 0 (.load (.user "x") (.varRef (.user "arr")) (.litInt 0))
  assert! r.containsSubstr "as usize"

-- seq: two statements joined
#eval do
  let r := stmtToRust 0 (.seq (.assign (.user "x") (.litInt 1)) (.assign (.user "y") (.litInt 2)))
  assert! r.containsSubstr "x = 1;"
  assert! r.containsSubstr "y = 2;"

-- ite: if-else with no parens around condition
#eval do
  let r := stmtToRust 0 (.ite (.litBool true) (.assign (.user "x") (.litInt 1)) .skip)
  assert! r.containsSubstr "if true"
  assert! r.containsSubstr "} else {"
  assert! !r.containsSubstr "if (true)"  -- NO C-style parens

-- while: while loop with no parens
#eval do
  let r := stmtToRust 0 (.while (.litBool false) .skip)
  assert! r.containsSubstr "while false"
  assert! !r.containsSubstr "while (false)"  -- NO C-style parens

-- for_: desugared to init + while
#eval do
  let r := stmtToRust 0 (.for_ (.assign (.user "i") (.litInt 0))
    (.binOp .ltOp (.varRef (.user "i")) (.litInt 10))
    (.assign (.user "i") (.binOp .add (.varRef (.user "i")) (.litInt 1)))
    .skip)
  assert! r.containsSubstr "i = 0;"
  assert! r.containsSubstr "while"

-- call: function call
#eval do
  let r := stmtToRust 0 (.call (.user "result") "foo" [.litInt 1, .litInt 2])
  assert! r == "result = foo(1, 2);"

-- break_: break statement
#eval do
  let r := stmtToRust 0 .break_
  assert! r == "break;"

-- continue_: continue statement
#eval do
  let r := stmtToRust 0 .continue_
  assert! r == "continue;"

-- return_: return with and without value
#eval do
  let r1 := stmtToRust 0 (.return_ (some (.litInt 42)))
  assert! r1 == "return 42;"
  let r2 := stmtToRust 0 (.return_ none)
  assert! r2 == "return;"

/-! ## Boolean Literal Verification: true/false (not 1/0) -/

#eval do
  assert! exprToRust (.litBool true) == "true"
  assert! exprToRust (.litBool false) == "false"
  -- Verify NOT C encoding:
  assert! exprToRust (.litBool true) != "1"
  assert! exprToRust (.litBool false) != "0"

/-! ## Operator Coverage: All 12 BinOps + 4 UnaryOps -/

#eval do
  assert! binOpToRust .add == "+"
  assert! binOpToRust .sub == "-"
  assert! binOpToRust .mul == "*"
  assert! binOpToRust .eqOp == "=="
  assert! binOpToRust .ltOp == "<"
  assert! binOpToRust .land == "&&"
  assert! binOpToRust .lor == "||"
  assert! binOpToRust .band == "&"
  assert! binOpToRust .bor == "|"
  assert! binOpToRust .bxor == "^"
  assert! binOpToRust .bshl == "<<"
  assert! binOpToRust .bshr == ">>"

#eval do
  assert! unaryOpToRust .neg == "-"
  assert! unaryOpToRust .lnot == "!"
  assert! unaryOpToRust .widen32to64 == "(as i64)"
  assert! unaryOpToRust .trunc64to32 == "(as i32)"

/-! ## Header Generation -/

#eval do
  let h1 := generateRustHeader { includePowerHelper := true }
  assert! h1.containsSubstr "fn power"
  assert! h1.containsSubstr "result"
  let h2 := generateRustHeader { includePowerHelper := false }
  assert! h2 == ""

/-! ## Function Generation -/

#eval do
  let f := generateRustFunction {} "add" [("x", "i64"), ("y", "i64")]
    (.assign (.user "result") (.binOp .add (.varRef (.user "x")) (.varRef (.user "y"))))
    (.varRef (.user "result"))
  assert! f.containsSubstr "fn add(x: i64, y: i64) -> i64"
  assert! f.containsSubstr "result = (x + y);"

/-! ## Sanitization Smoke Tests -/

#eval do
  -- Rust keywords are sanitized
  assert! sanitizeIdentifierRust "fn" == "tl_fn"
  assert! sanitizeIdentifierRust "let" == "tl_let"
  assert! sanitizeIdentifierRust "mut" == "tl_mut"
  assert! sanitizeIdentifierRust "self" == "tl_self"
  assert! sanitizeIdentifierRust "async" == "tl_async"
  assert! sanitizeIdentifierRust "await" == "tl_await"
  -- Non-keywords pass through
  assert! sanitizeIdentifierRust "x" == "x"
  assert! sanitizeIdentifierRust "counter" == "counter"
  -- Idempotent
  assert! sanitizeIdentifierRust (sanitizeIdentifierRust "fn") == sanitizeIdentifierRust "fn"

/-! ## Non-Vacuity: End-to-End with Nested Control Flow -/

/-- Non-vacuity witness: a complex nested program generates non-empty Rust code
    with balanced braces and correct structure. -/
example : let prog := Stmt.while (.litBool true)
    (.seq (.ite (.binOp .ltOp (.varRef (.user "x")) (.litInt 10))
      (.assign (.user "x") (.binOp .add (.varRef (.user "x")) (.litInt 1)))
      (.seq (.assign (.user "y") (.litInt 0)) .break_))
    (.assign (.user "z") (.varRef (.user "x"))))
  let code := stmtToRust 0 prog
  countChar '{' code = countChar '}' code := by decide

end TrustLean
