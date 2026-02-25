/-
  Trust-Lean — Verified Code Generation Framework
  Typeclass/CodeGenSound.lean: Verification obligation typeclass

  N2.1: CRITICO — defines the uniform proof obligation that each
  DSL frontend must satisfy to guarantee correct compilation.

  The three-part contract (from DESIGN_SPEC.md, adapted from LeanScribe):
  1. There exists sufficient fuel for normal termination
  2. The result expression evaluates to the correct value
  3. User variables are preserved (only temps are written)
-/

import TrustLean.Typeclass.CodeGenerable
import TrustLean.Core.Eval

set_option autoImplicit false

namespace TrustLean

/-! ## CodeGenSound Typeclass -/

/-- Verification typeclass: compilation preserves semantics.

    Any DSL that implements both `CodeGenerable` and `CodeGenSound`
    has a machine-checked proof that its compilation is correct.

    The proof obligation is a three-part existential:
    given a well-typed source environment `env` and a compatible low-level
    environment `llEnv`, there exists fuel and a result environment such that:
    1. `evalStmt` terminates normally with that fuel
    2. The result expression evaluates to `denote a env`
    3. All user variables are preserved (compilation only writes temps)

    The `wellTyped` predicate defaults to `True`, so DSLs that accept
    any Value environment (e.g., ImpStmt) need not specify it. -/
class CodeGenSound (α : Type) [inst : CodeGenerable α] where
  /-- Well-typedness predicate on the source environment.
      Defaults to `True` (all environments accepted). -/
  wellTyped : α → (VarId → Value) → Prop := fun _ _ => True
  /-- Central correctness theorem: compilation preserves semantics. -/
  lower_correct :
    ∀ (a : α) (env : VarId → Value) (llEnv : LowLevelEnv),
      wellTyped a env →
      (∀ (v : VarId), llEnv (.user (inst.varNames v)) = env v) →
      ∃ (fuel : Nat) (resultEnv : LowLevelEnv),
        evalStmt fuel llEnv (inst.lower a default).stmt =
          some (.normal, resultEnv) ∧
        evalExpr resultEnv (inst.lower a default).resultVar =
          some (inst.denote a env) ∧
        ∀ (v : VarId), resultEnv (.user (inst.varNames v)) = env v

end TrustLean
