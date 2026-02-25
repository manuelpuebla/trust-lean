/-
  Trust-Lean — Tests/Properties/SanitizacionHelpers.lean
  N9.1: Property tests for sanitizeIdentifier and helper functions.

  SlimCheck/Plausible tactic not available in this build.
  Using decidable examples and #eval-based exhaustive checks instead.
-/

import TrustLean.Backend.Common

set_option autoImplicit false

namespace TrustLean.Tests.Properties.SanitizacionHelpers

/-! ## P1 — P0 IDEMPOTENCY: sanitizeIdentifier is idempotent -/
-- NOT_YET_RUNNABLE for universal quantifier (no SampleableExt for String)
-- Testing with representative examples instead

-- Concrete idempotency checks (decide works on String equality)
example : sanitizeIdentifier (sanitizeIdentifier "hello") = sanitizeIdentifier "hello" := by decide
example : sanitizeIdentifier (sanitizeIdentifier "while") = sanitizeIdentifier "while" := by decide
example : sanitizeIdentifier (sanitizeIdentifier "2bad") = sanitizeIdentifier "2bad" := by decide
example : sanitizeIdentifier (sanitizeIdentifier "") = sanitizeIdentifier "" := by decide
example : sanitizeIdentifier (sanitizeIdentifier "tl_x") = sanitizeIdentifier "tl_x" := by decide
example : sanitizeIdentifier (sanitizeIdentifier "a-b") = sanitizeIdentifier "a-b" := by decide
example : sanitizeIdentifier (sanitizeIdentifier "int") = sanitizeIdentifier "int" := by decide
example : sanitizeIdentifier (sanitizeIdentifier "for") = sanitizeIdentifier "for" := by decide
example : sanitizeIdentifier (sanitizeIdentifier "main") = sanitizeIdentifier "main" := by decide
example : sanitizeIdentifier (sanitizeIdentifier "_x") = sanitizeIdentifier "_x" := by decide

-- P0, INVARIANT: idempotency on wider set via #eval
#eval do
  let inputs := ["hello", "while", "for", "int", "2bad", "", "a-b", "tl_x", "_x",
                  "main", "void", "!@#$%^", "v*o*i*d", "my_variable_name",
                  "abort", "NULL", "printf", "uint64_t", "bool", "true", "false"]
  let mut failures := #[]
  for s in inputs do
    let once := sanitizeIdentifier s
    let twice := sanitizeIdentifier once
    if twice != once then
      failures := failures.push s
  if failures.isEmpty then
    IO.println "P1 IDEMPOTENCY: PASS (all 21 samples)"
  else
    IO.println s!"P1 IDEMPOTENCY: FAIL on {failures}"

/-! ## P2 — P1 PRESERVATION: Valid non-keyword identifiers are unchanged -/

-- Concrete preservation checks
example : sanitizeIdentifier "hello" = "hello" := by decide
example : sanitizeIdentifier "my_var" = "my_var" := by decide
example : sanitizeIdentifier "_x" = "_x" := by decide
example : sanitizeIdentifier "foo42" = "foo42" := by decide
example : sanitizeIdentifier "a" = "a" := by decide
example : sanitizeIdentifier "z" = "z" := by decide

#eval do
  let validNonKeywords := ["hello", "my_var", "_x", "foo42", "a", "z",
                           "myFunc", "counter", "result_1", "data"]
  let mut failures := #[]
  for s in validNonKeywords do
    let result := sanitizeIdentifier s
    if result != s then
      failures := failures.push (s, result)
  if failures.isEmpty then
    IO.println "P2 PRESERVATION: PASS (all 10 samples)"
  else
    IO.println s!"P2 PRESERVATION: FAIL on {failures}"

/-! ## P3 — P1 INVARIANT: Keywords and invalid idents get tl_ prefix -/

-- Concrete prefix checks via equality (decide works on String eq)
example : sanitizeIdentifier "while" = "tl_while" := by decide
example : sanitizeIdentifier "for" = "tl_for" := by decide
example : sanitizeIdentifier "int" = "tl_int" := by decide
example : sanitizeIdentifier "void" = "tl_void" := by decide
example : sanitizeIdentifier "2bad" = "tl_2bad" := by decide
example : sanitizeIdentifier "" = "tl_empty" := by decide

#eval do
  let keywords := c99Keywords ++ cReservedExtra
  let mut failures := #[]
  for kw in keywords do
    let result := sanitizeIdentifier kw
    if !(result.startsWith "tl_") then
      failures := failures.push (kw, result)
  if failures.isEmpty then
    IO.println s!"P3 INVARIANT (keywords→tl_ prefix): PASS (all {keywords.length} keywords)"
  else
    IO.println s!"P3 INVARIANT: FAIL on {failures}"

#eval do
  let invalidIdents := ["", "2x", "3abc", "!@#", "0"]
  let mut failures := #[]
  for s in invalidIdents do
    let result := sanitizeIdentifier s
    if !(result.startsWith "tl_") then
      failures := failures.push (s, result)
  if failures.isEmpty then
    IO.println s!"P3 INVARIANT (invalid→tl_ prefix): PASS (all {invalidIdents.length} samples)"
  else
    IO.println s!"P3 INVARIANT: FAIL on {failures}"

/-! ## P4 — P2 SOUNDNESS: joinCode correctness -/
-- Note: joinCode in Common.lean takes 2 args (c1 c2 : String), not a list

-- joinCode basic properties
example : joinCode "" "b" = "b" := by decide
example : joinCode "a" "" = "a" := by decide
example : joinCode "" "" = "" := by decide
example : joinCode "a" "b" = "a\nb" := by decide
example : joinCode "hello" "world" = "hello\nworld" := by decide

#eval do
  -- Check joinCode skips empty strings correctly
  let tests := [("", "b", "b"), ("a", "", "a"), ("", "", ""),
                ("a", "b", "a\nb"), ("x", "y", "x\ny")]
  let mut failures := #[]
  for (c1, c2, expected) in tests do
    let result := joinCode c1 c2
    if result != expected then
      failures := failures.push (c1, c2, expected, result)
  if failures.isEmpty then
    IO.println s!"P4 SOUNDNESS (joinCode): PASS (all {tests.length} cases)"
  else
    IO.println s!"P4 SOUNDNESS (joinCode): FAIL on {failures}"

/-! ## Bonus: sanitizeIdentifier_valid is formally proved in Common.lean -/
-- Re-check: sanitizeIdentifier output is always a valid C identifier
example : isValidCIdent (sanitizeIdentifier "while") = true := by decide
example : isValidCIdent (sanitizeIdentifier "") = true := by decide
example : isValidCIdent (sanitizeIdentifier "2x") = true := by decide
example : isValidCIdent (sanitizeIdentifier "a-b") = true := by decide
example : isValidCIdent (sanitizeIdentifier "hello") = true := by decide

-- Re-check: sanitizeIdentifier output is never a C99 keyword
-- (This is formally proved as sanitizeIdentifier_not_keyword)
example : sanitizeIdentifier "while" ∉ c99Keywords := by decide
example : sanitizeIdentifier "int" ∉ c99Keywords := by decide
example : sanitizeIdentifier "for" ∉ c99Keywords := by decide

end TrustLean.Tests.Properties.SanitizacionHelpers
