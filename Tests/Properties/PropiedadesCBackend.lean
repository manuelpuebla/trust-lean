/-
  Trust-Lean — Tests/Properties/PropiedadesCBackend.lean
  N9.3: Property tests for CBackendProperties formal guarantees.

  SlimCheck/Plausible tactic not available in this build.
  Using decidable examples and #eval-based exhaustive checks instead.
-/

import TrustLean.Backend.CBackend
import TrustLean.Backend.CBackendProperties

set_option autoImplicit false

namespace TrustLean.Tests.Properties.PropiedadesCBackend

/-! ## P1 — P0 INVARIANT: stmtToC balanced braces for all constructors -/

-- Concrete balanced brace proofs
example : countChar '{' (stmtToC 0 .skip) = countChar '}' (stmtToC 0 .skip) := by decide
example : countChar '{' (stmtToC 0 .break_) = countChar '}' (stmtToC 0 .break_) := by decide
example : countChar '{' (stmtToC 0 .continue_) = countChar '}' (stmtToC 0 .continue_) := by decide
example : countChar '{' (stmtToC 0 (.return_ none)) = countChar '}' (stmtToC 0 (.return_ none)) := by decide
example : countChar '{' (stmtToC 0 (.return_ (some (.litInt 0))))
    = countChar '}' (stmtToC 0 (.return_ (some (.litInt 0)))) := by decide
example : countChar '{' (stmtToC 0 (.assign (.user "x") (.litInt 1)))
    = countChar '}' (stmtToC 0 (.assign (.user "x") (.litInt 1))) := by decide
example : countChar '{' (stmtToC 0 (.ite (.litBool true) .skip .skip))
    = countChar '}' (stmtToC 0 (.ite (.litBool true) .skip .skip)) := by decide
example : countChar '{' (stmtToC 0 (.while (.litBool true) .skip))
    = countChar '}' (stmtToC 0 (.while (.litBool true) .skip)) := by decide
example : countChar '{' (stmtToC 0 (.for_ .skip (.litBool true) .skip .skip))
    = countChar '}' (stmtToC 0 (.for_ .skip (.litBool true) .skip .skip)) := by decide
-- Nested
example : countChar '{' (stmtToC 0 (.while (.litBool true) (.ite (.litBool false) .break_ .continue_)))
    = countChar '}' (stmtToC 0 (.while (.litBool true) (.ite (.litBool false) .break_ .continue_))) := by decide
-- Seq of control flow
example : countChar '{' (stmtToC 0 (.seq (.ite (.litBool true) .skip .skip)
    (.while (.litBool false) (.assign (.user "x") (.litInt 0)))))
    = countChar '}' (stmtToC 0 (.seq (.ite (.litBool true) .skip .skip)
    (.while (.litBool false) (.assign (.user "x") (.litInt 0))))) := by decide

-- #eval wide coverage
#eval do
  let stmts : List Stmt := [
    .skip,
    .break_,
    .continue_,
    .return_ none,
    .return_ (some (.litInt 42)),
    .assign (.user "x") (.litInt 1),
    .store (.varRef (.user "arr")) (.litInt 0) (.litInt 42),
    .load (.user "x") (.varRef (.user "arr")) (.litInt 0),
    .call (.user "r") "func" [.litInt 1],
    .ite (.litBool true) .skip .skip,
    .ite (.varRef (.user "x")) (.assign (.user "y") (.litInt 1)) (.assign (.user "y") (.litInt 2)),
    .while (.litBool false) .skip,
    .while (.litBool true) .break_,
    .for_ .skip (.litBool true) .skip .skip,
    .for_ (.assign (.user "i") (.litInt 0)) (.binOp .ltOp (.varRef (.user "i")) (.litInt 5))
          (.assign (.user "i") (.binOp .add (.varRef (.user "i")) (.litInt 1))) .skip,
    .seq .skip .skip,
    .seq (.ite (.litBool true) .skip .skip) (.while (.litBool false) .skip),
    -- 3-level nesting
    .while (.litBool true) (.ite (.litBool false) (.while (.litBool true) .break_) .skip),
    -- for with body containing ite
    .for_ (.assign (.user "i") (.litInt 0)) (.litBool true) (.assign (.user "i") (.litInt 1))
          (.ite (.litBool false) .break_ .continue_)
  ]
  let mut failures := #[]
  for s in stmts do
    let code := stmtToC 0 s
    let opens := countChar '{' code
    let closes := countChar '}' code
    if opens != closes then
      failures := failures.push (opens, closes)
  if failures.isEmpty then
    IO.println s!"P1 INVARIANT (balanced braces): PASS (all {stmts.length} stmts)"
  else
    IO.println s!"P1 INVARIANT: FAIL ({failures.size} failures)"

/-! ## P2 — P0 INVARIANT: sanitizeIdentifier produces valid C identifier -/

-- Formally proved as sanitizeIdentifier_valid in Common.lean.
-- Concrete re-checks:
example : isValidCIdent (sanitizeIdentifier "while") = true := by decide
example : isValidCIdent (sanitizeIdentifier "") = true := by decide
example : isValidCIdent (sanitizeIdentifier "2x") = true := by decide
example : isValidCIdent (sanitizeIdentifier "a-b") = true := by decide
example : isValidCIdent (sanitizeIdentifier "tl_x") = true := by decide

#eval do
  let inputs := c99Keywords ++ cReservedExtra ++
    ["", "2x", "3abc", "!@#", "0", "a-b", "hello", "tl_x", "_x", "v*o*i*d"]
  let mut failures := #[]
  for s in inputs do
    let result := sanitizeIdentifier s
    if !isValidCIdent result then
      failures := failures.push (s, result)
  if failures.isEmpty then
    IO.println s!"P2 INVARIANT (valid C ident): PASS (all {inputs.length} samples)"
  else
    IO.println s!"P2 INVARIANT: FAIL on {failures}"

/-! ## P3 — P0 INVARIANT: sanitizeIdentifier never produces a C keyword -/

-- Formally proved as sanitizeIdentifier_not_keyword in Common.lean.
example : sanitizeIdentifier "while" ∉ c99Keywords := by decide
example : sanitizeIdentifier "int" ∉ c99Keywords := by decide
example : sanitizeIdentifier "void" ∉ c99Keywords := by decide

#eval do
  let inputs := c99Keywords ++ cReservedExtra ++
    ["", "2x", "3abc", "!@#", "0", "a-b", "hello", "tl_x"]
  let keywords := c99Keywords ++ cReservedExtra
  let mut failures := #[]
  for s in inputs do
    let result := sanitizeIdentifier s
    if keywords.contains result then
      failures := failures.push (s, result)
  if failures.isEmpty then
    IO.println s!"P3 INVARIANT (not keyword): PASS (all {inputs.length} samples)"
  else
    IO.println s!"P3 INVARIANT: FAIL on {failures}"

/-! ## P4 — P1 IDEMPOTENCY: sanitizeIdentifier is idempotent -/

example : sanitizeIdentifier (sanitizeIdentifier "while") = sanitizeIdentifier "while" := by decide
example : sanitizeIdentifier (sanitizeIdentifier "") = sanitizeIdentifier "" := by decide
example : sanitizeIdentifier (sanitizeIdentifier "2x") = sanitizeIdentifier "2x" := by decide
example : sanitizeIdentifier (sanitizeIdentifier "a-b") = sanitizeIdentifier "a-b" := by decide

#eval do
  let inputs := c99Keywords ++ cReservedExtra ++
    ["", "2x", "3abc", "!@#", "0", "a-b", "hello", "tl_x", "_x", "v*o*i*d"]
  let mut failures := #[]
  for s in inputs do
    let once := sanitizeIdentifier s
    let twice := sanitizeIdentifier once
    if twice != once then
      failures := failures.push s
  if failures.isEmpty then
    IO.println s!"P4 IDEMPOTENCY: PASS (all {inputs.length} samples)"
  else
    IO.println s!"P4 IDEMPOTENCY: FAIL on {failures}"

/-! ## P5 — P1 SOUNDNESS: stmtToC/exprToC are deterministic (pure functions) -/

-- Formally proved as stmtToC_deterministic and exprToC_deterministic.
-- Trivially true by rfl in a pure functional language.
-- Re-check with concrete examples:

example : stmtToC 0 .skip = stmtToC 0 .skip := rfl
example : stmtToC 0 (.ite (.litBool true) .skip .skip) = stmtToC 0 (.ite (.litBool true) .skip .skip) := rfl
example : exprToC (.litInt 42) = exprToC (.litInt 42) := rfl
example : exprToC (.binOp .add (.varRef (.user "x")) (.litInt 1))
    = exprToC (.binOp .add (.varRef (.user "x")) (.litInt 1)) := rfl

#eval do
  -- Check determinism by running twice
  let stmts : List Stmt := [
    .skip, .break_, .continue_, .return_ none,
    .assign (.user "x") (.litInt 1),
    .ite (.litBool true) .skip .skip,
    .while (.litBool false) .skip
  ]
  let mut ok := true
  for s in stmts do
    let r1 := stmtToC 0 s
    let r2 := stmtToC 0 s
    if r1 != r2 then ok := false
  if ok then
    IO.println s!"P5 SOUNDNESS (deterministic): PASS (all {stmts.length} stmts)"
  else
    IO.println "P5 SOUNDNESS: FAIL (non-determinism detected)"

/-! ## P6 — P2 INVARIANT: exprToC balanced parentheses -/

#eval do
  let exprs : List LowLevelExpr := [
    .litInt 0,
    .litInt 42,
    .litInt (-5),
    .litBool true,
    .litBool false,
    .varRef (.user "x"),
    .varRef (.temp 3),
    .binOp .add (.varRef (.user "x")) (.litInt 1),
    .binOp .mul (.binOp .add (.varRef (.user "a")) (.varRef (.user "b"))) (.varRef (.user "c")),
    .unaryOp .neg (.varRef (.user "x")),
    .unaryOp .lnot (.varRef (.user "flag")),
    .unaryOp .neg (.binOp .add (.litInt 1) (.litInt 2)),
    .powCall (.varRef (.user "x")) 3,
    .binOp .eqOp (.binOp .add (.varRef (.user "a")) (.varRef (.user "b")))
                  (.binOp .mul (.varRef (.user "c")) (.varRef (.user "d")))
  ]
  let mut failures := #[]
  for e in exprs do
    let code := exprToC e
    let opens := countChar '(' code
    let closes := countChar ')' code
    if opens != closes then
      failures := failures.push (opens, closes)
  if failures.isEmpty then
    IO.println s!"P6 INVARIANT (balanced parens): PASS (all {exprs.length} exprs)"
  else
    IO.println s!"P6 INVARIANT: FAIL ({failures.size} failures)"

end TrustLean.Tests.Properties.PropiedadesCBackend
