/-
  Trust-Lean — Verified Code Generation Framework
  Typeclass/BackendEmitter.lean: Backend emission typeclass

  N4.1: PAR — defines the uniform interface for target language backends.
  Backend emitters are outside the TCB (trusted pretty-printers).
-/

import TrustLean.Core.Stmt

set_option autoImplicit false

namespace TrustLean

/-- Typeclass for backend code emitters.
    Each backend provides emission functions for statements, functions, and preambles.
    Backend emitters are outside the TCB — they are trusted pretty-printers.
    A verified emitter would require formalized target language semantics. -/
class BackendEmitter (β : Type) where
  /-- Target language name (e.g., "C", "Rust"). -/
  name : String
  /-- Emit a statement in the target language at the given indentation level. -/
  emitStmt : β → Nat → Stmt → String
  /-- Emit a complete function: config, name, typed params, body, return expr. -/
  emitFunction : β → String → List (String × String) → Stmt → LowLevelExpr → String
  /-- Emit preamble (includes, imports, type definitions). -/
  emitHeader : β → String

end TrustLean
