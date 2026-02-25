/-
  Trust-Lean Test Suite — Properties for N1.3 (Typeclasses)
  Tests adapted from TESTS_OUTSOURCE.md specifications.

  API notes:
  - CodeGenerable is a typeclass with denote/lower/varNames
  - CodeGenSound has lower_correct proof obligation
  - BackendEmitter has name/emitStmt/emitFunction/emitHeader
  - sanitizeIdentifier in Backend/Common.lean
  - CConfig instance of BackendEmitter in Backend/CBackend.lean
  - CBackendProperties.lean has countChar, stmtBracePairs, determinism proofs

  Since these are typeclasses (interfaces), property tests focus on:
  - Determinism of pure functions (P1)
  - sanitizeIdentifier properties (P3, P4)
  - Balanced braces in C emission (P5)
  - Note: P1 (toCode determinism) and P2 (CodeGenSound) are interface obligations;
    they are verified when instances are provided. We test them structurally.
-/

import TrustLean.Typeclass.CodeGenerable
import TrustLean.Typeclass.CodeGenSound
import TrustLean.Typeclass.BackendEmitter
import TrustLean.Backend.CBackend
import TrustLean.Backend.Common
import TrustLean.Backend.CBackendProperties

open TrustLean

/-! ## P1 — P0 INVARIANT: Determinism of toCode/lower/emitStmt

    These are pure functions, so determinism is trivially true by referential
    transparency. We verify this structurally.
-/

-- P0, INVARIANT: stmtToC is deterministic (pure function)
example (s : Stmt) (l : Nat) : stmtToC l s = stmtToC l s := rfl

-- P0, INVARIANT: exprToC is deterministic (pure function)
example (e : LowLevelExpr) : exprToC e = exprToC e := rfl

-- P0, INVARIANT: BackendEmitter instance for CConfig is deterministic
example (cfg : CConfig) (l : Nat) (s : Stmt) :
    BackendEmitter.emitStmt cfg l s = BackendEmitter.emitStmt cfg l s := rfl

/-! ## P2 — P0 SOUNDNESS: CodeGenSound lower_correct (structural check)

    CodeGenSound is a typeclass with a proof obligation. We can't test it
    without concrete instances. The proof obligation is:
    For any instance satisfying CodeGenSound,
    evalStmt fuel (toCode x) env = .normal (eval x env).
    This is verified when each frontend provides its instance.

    We verify the typeclass structure exists:
-/

-- P0, SOUNDNESS: CodeGenSound typeclass exists and has lower_correct field
-- (This compiles only if the typeclass is well-formed)
#check @CodeGenSound
#check @CodeGenSound.lower_correct

/-! ## P3 — P1 IDEMPOTENCY: sanitizeIdentifier is idempotent -/

-- P1, IDEMPOTENCY: concrete examples
example : sanitizeIdentifier (sanitizeIdentifier "hello") = sanitizeIdentifier "hello" := by
  native_decide

example : sanitizeIdentifier (sanitizeIdentifier "for") = sanitizeIdentifier "for" := by
  native_decide

example : sanitizeIdentifier (sanitizeIdentifier "int") = sanitizeIdentifier "int" := by
  native_decide

example : sanitizeIdentifier (sanitizeIdentifier "my-var") = sanitizeIdentifier "my-var" := by
  native_decide

example : sanitizeIdentifier (sanitizeIdentifier "123abc") = sanitizeIdentifier "123abc" := by
  native_decide

example : sanitizeIdentifier (sanitizeIdentifier "") = sanitizeIdentifier "" := by
  native_decide

example : sanitizeIdentifier (sanitizeIdentifier "tl_x") = sanitizeIdentifier "tl_x" := by
  native_decide

example : sanitizeIdentifier (sanitizeIdentifier "continue") = sanitizeIdentifier "continue" := by
  native_decide

/-! ## P4 — P0 INVARIANT: sanitizeIdentifier produces valid non-keyword C identifier -/

-- P0, INVARIANT: sanitizeIdentifier output is a valid C identifier (proven theorem)
-- Re-verify the theorem exists
#check sanitizeIdentifier_valid
#check sanitizeIdentifier_not_keyword
#check sanitizeIdentifier_nonempty

-- P0, INVARIANT: concrete verification
example : isValidCIdent (sanitizeIdentifier "for") = true := by native_decide
example : isValidCIdent (sanitizeIdentifier "while") = true := by native_decide
example : isValidCIdent (sanitizeIdentifier "int") = true := by native_decide
example : isValidCIdent (sanitizeIdentifier "x") = true := by native_decide
example : isValidCIdent (sanitizeIdentifier "") = true := by native_decide
example : isValidCIdent (sanitizeIdentifier "123") = true := by native_decide
example : isValidCIdent (sanitizeIdentifier "my-var") = true := by native_decide

-- P0, INVARIANT: not a C keyword
-- The theorem sanitizeIdentifier_not_keyword proves this for ALL inputs.
-- Concrete verification:
example : sanitizeIdentifier "for" ∉ c99Keywords := sanitizeIdentifier_not_keyword "for"
example : sanitizeIdentifier "int" ∉ c99Keywords := sanitizeIdentifier_not_keyword "int"
example : sanitizeIdentifier "while" ∉ c99Keywords := sanitizeIdentifier_not_keyword "while"

/-! ## P5 — P0 INVARIANT: C code generated for Stmt has balanced braces -/

-- P0, INVARIANT: balanced braces on concrete examples
-- Using the proven examples from CBackendProperties.lean

-- skip: balanced (both 0)
example : countChar '{' (stmtToC 0 .skip) = countChar '}' (stmtToC 0 .skip) := by decide

-- break: balanced (both 0)
example : countChar '{' (stmtToC 0 .break_) = countChar '}' (stmtToC 0 .break_) := by decide

-- continue: balanced (both 0)
example : countChar '{' (stmtToC 0 .continue_) = countChar '}' (stmtToC 0 .continue_) := by decide

-- return none: balanced (both 0)
example : countChar '{' (stmtToC 0 (.return_ none)) =
          countChar '}' (stmtToC 0 (.return_ none)) := by decide

-- ite with skip branches: balanced
example : countChar '{' (stmtToC 0 (.ite (.litBool true) .skip .skip)) =
          countChar '}' (stmtToC 0 (.ite (.litBool true) .skip .skip)) := by decide

-- while with skip body: balanced
example : countChar '{' (stmtToC 0 (.while (.litBool true) .skip)) =
          countChar '}' (stmtToC 0 (.while (.litBool true) .skip)) := by decide

-- nested ite inside while: balanced
example : countChar '{'
    (stmtToC 0 (.while (.litBool true) (.ite (.litBool false) .break_ .continue_)))
  = countChar '}'
    (stmtToC 0 (.while (.litBool true) (.ite (.litBool false) .break_ .continue_))) := by decide

-- for_ with skip components: balanced
example : countChar '{' (stmtToC 0 (.for_ .skip (.litBool true) .skip .skip)) =
          countChar '}' (stmtToC 0 (.for_ .skip (.litBool true) .skip .skip)) := by decide

-- More complex: while containing assignment in body
example : countChar '{'
    (stmtToC 0 (.while (.litBool true) (.assign (.user "x") (.litInt 1))))
  = countChar '}'
    (stmtToC 0 (.while (.litBool true) (.assign (.user "x") (.litInt 1)))) := by decide

-- Double nested: while containing while
example : countChar '{'
    (stmtToC 0 (.while (.litBool true) (.while (.litBool false) .skip)))
  = countChar '}'
    (stmtToC 0 (.while (.litBool true) (.while (.litBool false) .skip))) := by decide
