/-
  Trust-Lean — Verified Code Generation Framework
  Typeclass/CodeGenerable.lean: Operational compilation typeclass

  N2.1: CRITICO — defines the uniform interface that all DSL frontends
  must implement to compile to the Core IR.
-/

import TrustLean.Core.Stmt

set_option autoImplicit false

namespace TrustLean

/-! ## Source Variable Identifiers -/

/-- Source-level variable identifiers, represented as natural numbers.
    Each frontend maps these to low-level VarNames via `varNames`. -/
abbrev VarId := Nat

/-! ## CodeGenerable Typeclass -/

/-- Typeclass for DSL types that can be compiled to the Core IR.

    Each frontend must provide:
    - `denote`: denotational semantics in terms of source-level values
    - `lower`: compilation to Core IR (Stmt + result location)
    - `varNames`: mapping from source variable IDs to low-level names

    The companion typeclass `CodeGenSound` provides the proof that
    `lower` preserves the semantics defined by `denote`. -/
class CodeGenerable (α : Type) where
  /-- Denotational semantics of the source language.
      Maps a DSL term and a source-level environment to a Value. -/
  denote : α → (VarId → Value) → Value
  /-- Compile a DSL term to Core IR.
      Takes a CodeGenState for fresh variable generation.
      Returns the compiled Stmt and the expression holding the result. -/
  lower : α → CodeGenState → StmtResult
  /-- Variable naming scheme: maps source variable IDs to low-level names.
      Must be injective to ensure no aliasing between distinct source variables. -/
  varNames : VarId → String

end TrustLean
