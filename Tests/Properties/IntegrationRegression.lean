/-
  Trust-Lean — Tests/Properties/IntegrationRegression.lean
  N9.4: Property tests for Integration + Regression.

  SlimCheck/Plausible tactic not available in this build.
  Using decidable examples and #eval-based exhaustive checks instead.
-/

import TrustLean.Backend.CBackend
import TrustLean.Backend.CBackendProperties

set_option autoImplicit false

namespace TrustLean.Tests.Properties.IntegrationRegression

/-! ## P1 — P0 IDEMPOTENCY: sanitizeIdentifier is idempotent -/

example : sanitizeIdentifier (sanitizeIdentifier "hello") = sanitizeIdentifier "hello" := by decide
example : sanitizeIdentifier (sanitizeIdentifier "while") = sanitizeIdentifier "while" := by decide
example : sanitizeIdentifier (sanitizeIdentifier "") = sanitizeIdentifier "" := by decide
example : sanitizeIdentifier (sanitizeIdentifier "2x") = sanitizeIdentifier "2x" := by decide
example : sanitizeIdentifier (sanitizeIdentifier "int") = sanitizeIdentifier "int" := by decide
example : sanitizeIdentifier (sanitizeIdentifier "a-b") = sanitizeIdentifier "a-b" := by decide
example : sanitizeIdentifier (sanitizeIdentifier "tl_x") = sanitizeIdentifier "tl_x" := by decide
example : sanitizeIdentifier (sanitizeIdentifier "main") = sanitizeIdentifier "main" := by decide
example : sanitizeIdentifier (sanitizeIdentifier "bool") = sanitizeIdentifier "bool" := by decide
example : sanitizeIdentifier (sanitizeIdentifier "true") = sanitizeIdentifier "true" := by decide

#eval do
  let allInputs := c99Keywords ++ cReservedExtra ++
    ["", "2x", "3abc", "!@#", "0", "a-b", "hello", "tl_x", "_x", "v*o*i*d",
     "my_func", "counter_1", "data", "result", "tl_empty"]
  let mut failures := #[]
  for s in allInputs do
    let once := sanitizeIdentifier s
    let twice := sanitizeIdentifier once
    if twice != once then
      failures := failures.push s
  if failures.isEmpty then
    IO.println s!"P1 IDEMPOTENCY: PASS (all {allInputs.length} samples)"
  else
    IO.println s!"P1 IDEMPOTENCY: FAIL on {failures}"

/-! ## P2 — P0 INVARIANT: sanitizeIdentifier output is always valid C identifier -/

-- Formally proved: sanitizeIdentifier_valid
example : isValidCIdent (sanitizeIdentifier "hello") = true := by decide
example : isValidCIdent (sanitizeIdentifier "while") = true := by decide
example : isValidCIdent (sanitizeIdentifier "") = true := by decide
example : isValidCIdent (sanitizeIdentifier "2x") = true := by decide
example : isValidCIdent (sanitizeIdentifier "!@#") = true := by decide
example : isValidCIdent (sanitizeIdentifier "main") = true := by decide
example : isValidCIdent (sanitizeIdentifier "tl_x") = true := by decide

#eval do
  let allInputs := c99Keywords ++ cReservedExtra ++
    ["", "2x", "3abc", "!@#", "0", "a-b", "hello", "tl_x", "_x", "v*o*i*d"]
  let mut failures := #[]
  for s in allInputs do
    let result := sanitizeIdentifier s
    if !isValidCIdent result then
      failures := failures.push (s, result)
  if failures.isEmpty then
    IO.println s!"P2 INVARIANT (valid C ident): PASS (all {allInputs.length} samples)"
  else
    IO.println s!"P2 INVARIANT: FAIL on {failures}"

/-! ## P3 — P0 INVARIANT: sanitizeIdentifier output is never a C keyword -/

-- Formally proved: sanitizeIdentifier_not_keyword
example : sanitizeIdentifier "while" ∉ c99Keywords := by decide
example : sanitizeIdentifier "for" ∉ c99Keywords := by decide
example : sanitizeIdentifier "int" ∉ c99Keywords := by decide
example : sanitizeIdentifier "void" ∉ c99Keywords := by decide
example : sanitizeIdentifier "main" ∉ c99Keywords := by decide

#eval do
  let allInputs := c99Keywords ++ cReservedExtra ++
    ["", "2x", "3abc", "!@#", "0", "a-b", "hello", "tl_x"]
  let keywords := c99Keywords ++ cReservedExtra
  let mut failures := #[]
  for s in allInputs do
    let result := sanitizeIdentifier s
    if keywords.contains result then
      failures := failures.push (s, result)
  if failures.isEmpty then
    IO.println s!"P3 INVARIANT (not keyword): PASS (all {allInputs.length} samples)"
  else
    IO.println s!"P3 INVARIANT: FAIL on {failures}"

/-! ## P4 — P1 SOUNDNESS: stmtToC balanced braces -/

-- Concrete decidable proofs
example : countChar '{' (stmtToC 0 .skip) = countChar '}' (stmtToC 0 .skip) := by decide
example : countChar '{' (stmtToC 0 .break_) = countChar '}' (stmtToC 0 .break_) := by decide
example : countChar '{' (stmtToC 0 (.ite (.litBool true) .skip .skip))
    = countChar '}' (stmtToC 0 (.ite (.litBool true) .skip .skip)) := by decide
example : countChar '{' (stmtToC 0 (.while (.litBool true) .skip))
    = countChar '}' (stmtToC 0 (.while (.litBool true) .skip)) := by decide
example : countChar '{' (stmtToC 0 (.for_ .skip (.litBool true) .skip .skip))
    = countChar '}' (stmtToC 0 (.for_ .skip (.litBool true) .skip .skip)) := by decide

-- Broad coverage via #eval
#eval do
  let stmts : List Stmt := [
    .skip, .break_, .continue_,
    .return_ none, .return_ (some (.litInt 42)),
    .assign (.user "x") (.litInt 1),
    .store (.varRef (.user "arr")) (.litInt 0) (.litInt 1),
    .load (.user "x") (.varRef (.user "arr")) (.litInt 0),
    .call (.user "r") "func" [.litInt 1],
    .ite (.litBool true) .skip .skip,
    .ite (.litBool true) (.assign (.user "x") (.litInt 1)) .skip,
    .while (.litBool false) .skip,
    .while (.litBool true) .break_,
    .for_ .skip (.litBool true) .skip .skip,
    .seq .skip .skip,
    .seq (.ite (.litBool true) .skip .skip) (.while (.litBool false) .skip),
    -- Deep nesting
    .while (.litBool true) (.ite (.litBool false)
      (.while (.litBool true) .break_) .skip),
    -- For with body
    .for_ (.assign (.user "i") (.litInt 0)) (.litBool true)
          (.assign (.user "i") (.litInt 1))
          (.ite (.litBool false) .break_ .continue_),
    -- Triple nesting
    .ite (.litBool true) (.while (.litBool true)
      (.ite (.litBool false) .break_ .continue_)) .skip
  ]
  let mut failures := #[]
  for s in stmts do
    let code := stmtToC 0 s
    let opens := countChar '{' code
    let closes := countChar '}' code
    if opens != closes then
      failures := failures.push (opens, closes)
  if failures.isEmpty then
    IO.println s!"P4 SOUNDNESS (balanced braces): PASS (all {stmts.length} stmts)"
  else
    IO.println s!"P4 SOUNDNESS: FAIL ({failures.size} failures)"

/-! ## P5 — P2 EQUIVALENCE: stmtToC is deterministic -/

-- Trivially true: stmtToC is a pure function, so f(x) = f(x) by rfl.
example : stmtToC 0 .skip = stmtToC 0 .skip := rfl
example : stmtToC 0 (.assign (.user "x") (.litInt 1)) = stmtToC 0 (.assign (.user "x") (.litInt 1)) := rfl
example : stmtToC 0 (.ite (.litBool true) .skip .skip)
    = stmtToC 0 (.ite (.litBool true) .skip .skip) := rfl
example : stmtToC 0 (.while (.litBool false) .skip)
    = stmtToC 0 (.while (.litBool false) .skip) := rfl

-- Also check exprToC determinism
example : exprToC (.litInt 42) = exprToC (.litInt 42) := rfl
example : exprToC (.binOp .add (.varRef (.user "x")) (.litInt 1))
    = exprToC (.binOp .add (.varRef (.user "x")) (.litInt 1)) := rfl

#eval do
  let stmts : List Stmt := [
    .skip, .break_, .continue_,
    .assign (.user "x") (.litInt 1),
    .ite (.litBool true) .skip .skip,
    .while (.litBool false) .skip,
    .for_ .skip (.litBool true) .skip .skip
  ]
  let mut ok := true
  for s in stmts do
    let r1 := stmtToC 0 s
    let r2 := stmtToC 0 s
    if r1 != r2 then ok := false
  if ok then
    IO.println s!"P5 EQUIVALENCE (deterministic): PASS (all {stmts.length} stmts)"
  else
    IO.println "P5 EQUIVALENCE: FAIL (non-determinism detected)"

end TrustLean.Tests.Properties.IntegrationRegression
