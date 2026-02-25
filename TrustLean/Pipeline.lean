/-
  Trust-Lean — Verified Code Generation Framework
  Pipeline.lean: End-to-end compilation pipeline

  N5.1: HOJA — wires CodeGenerable (frontend) to BackendEmitter (backend).
  Provides generic compilation functions and a soundness theorem that
  delegates to CodeGenSound.lower_correct.
-/

import TrustLean.Typeclass.CodeGenerable
import TrustLean.Typeclass.CodeGenSound
import TrustLean.Typeclass.BackendEmitter
import TrustLean.Core.Eval

set_option autoImplicit false

namespace TrustLean

/-! ## Pipeline: Frontend → Core IR → Backend -/

/-- Compile a DSL term to Core IR (Stmt + result expression).
    Uses default CodeGenState (fresh counter starts at 0). -/
def Pipeline.lower {α : Type} [CodeGenerable α] (a : α) : StmtResult :=
  CodeGenerable.lower a default

/-- Generate target language code for a DSL term.
    Compiles to Core IR via CodeGenerable, then emits via BackendEmitter.
    Returns a complete function with the given name and parameters. -/
def Pipeline.emit {α : Type} {β : Type} [CodeGenerable α] [BackendEmitter β]
    (a : α) (cfg : β) (funcName : String)
    (params : List (String × String)) : String :=
  let sr := Pipeline.lower a
  let header := BackendEmitter.emitHeader cfg
  let body := BackendEmitter.emitFunction cfg funcName params sr.stmt sr.resultVar
  if header.isEmpty then body
  else header ++ "\n\n" ++ body

/-- Generate only the statement body (no function wrapper).
    Useful for inspecting the emitted IR without function scaffolding. -/
def Pipeline.emitBody {α : Type} {β : Type} [CodeGenerable α] [BackendEmitter β]
    (a : α) (cfg : β) (level : Nat := 0) : String :=
  let sr := Pipeline.lower a
  BackendEmitter.emitStmt cfg level sr.stmt

/-! ## Soundness -/

/-- End-to-end soundness: if a DSL type implements both CodeGenerable and CodeGenSound,
    then for any well-typed environment, the compiled Core IR evaluates to the
    denotational semantics of the source term.

    This theorem delegates entirely to CodeGenSound.lower_correct.
    Backend emission is outside the TCB (trusted pretty-printing). -/
theorem Pipeline.sound {α : Type} [inst : CodeGenerable α] [CodeGenSound α]
    (a : α) (env : VarId → Value) (llEnv : LowLevelEnv)
    (hwt : CodeGenSound.wellTyped a env)
    (hbridge : ∀ (v : VarId), llEnv (.user (inst.varNames v)) = env v) :
    ∃ (fuel : Nat) (resultEnv : LowLevelEnv),
      evalStmt fuel llEnv (Pipeline.lower a).stmt =
        some (.normal, resultEnv) ∧
      evalExpr resultEnv (Pipeline.lower a).resultVar =
        some (inst.denote a env) ∧
      ∀ (v : VarId), resultEnv (.user (inst.varNames v)) = env v :=
  CodeGenSound.lower_correct a env llEnv hwt hbridge

end TrustLean
