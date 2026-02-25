/-
  Trust-Lean — Verified Code Generation Framework
  Core/Stmt.lean: Statement IR, Outcome type, and StmtResult

  N1.2: FUNDACIONAL — the 12-constructor Stmt IR is the core intermediate
  representation through which all frontends compile and all backends emit.

  Key design decisions (from DESIGN_SPEC.md):
  - 12 Stmt constructors covering: assignment, memory (store/load), control flow
    (seq/ite/while/for_/break_/continue_/return_), function calls, and skip
  - for_ is syntactic sugar: `seq init (while cond (seq body step))` per Clight
  - Outcome has 5 variants: normal + 3 control flow signals + outOfFuel
  - return_ carries Option Value (functions may return void)
  - Fuel only decreases in while/for_ — other constructors do NOT consume fuel
-/

import TrustLean.Core.Value

set_option autoImplicit false

namespace TrustLean

/-! ## Statement IR -/

/-- Core IR statement type: 12 constructors.
    All frontends compile to Stmt via CodeGenerable.
    All backends emit from Stmt via BackendEmitter.

    Constructor classification:
    - Data flow: assign, store, load
    - Sequential: seq, skip
    - Conditional: ite
    - Loops: while, for_ (for_ desugars to while)
    - Control flow: break_, continue_, return_
    - External: call -/
inductive Stmt where
  | assign    : VarName → LowLevelExpr → Stmt
  /-- `store base index value` — writes `value` into `base[index]`.
      base, index, value are all expressions (base evaluates to array ref). -/
  | store     : (base : LowLevelExpr) → (index : LowLevelExpr) → (value : LowLevelExpr) → Stmt
  /-- `load var base index` — reads `base[index]` into variable `var`. -/
  | load      : (var : VarName) → (base : LowLevelExpr) → (index : LowLevelExpr) → Stmt
  | seq       : Stmt → Stmt → Stmt
  | ite       : LowLevelExpr → Stmt → Stmt → Stmt
  | while     : LowLevelExpr → Stmt → Stmt
  | for_      : Stmt → LowLevelExpr → Stmt → Stmt → Stmt
  | call      : VarName → String → List LowLevelExpr → Stmt
  | skip      : Stmt
  | break_    : Stmt
  | continue_ : Stmt
  | return_   : Option LowLevelExpr → Stmt
  deriving Repr, Inhabited

/-- `for_` desugaring to while.
    `for_ init cond step body` ≡ `seq init (while cond (seq body step))`
    Following Clight's decomposition (DESIGN_SPEC.md).
    This is a definitional convenience — proofs only need to handle while. -/
def Stmt.desugarFor (init : Stmt) (cond : LowLevelExpr) (step body : Stmt) : Stmt :=
  .seq init (.while cond (.seq body step))

/-! ## Outcome Type -/

/-- Execution outcome for fuel-based statement evaluation.
    - normal: statement completed, continue execution
    - break_: exit innermost loop
    - continue_: skip to next loop iteration
    - return_: exit function, optionally with a value
    - outOfFuel: fuel exhausted (depth bound reached) -/
inductive Outcome where
  | normal    : Outcome
  | break_    : Outcome
  | continue_ : Outcome
  | return_   : Option Value → Outcome
  | outOfFuel : Outcome
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Is this a normal completion? -/
def Outcome.isNormal : Outcome → Bool
  | .normal => true
  | _ => false

/-- Is this a loop-exit signal (break or continue)? -/
def Outcome.isLoopSignal : Outcome → Bool
  | .break_ => true
  | .continue_ => true
  | _ => false

/-- Is this a non-fuel termination (normal, break, continue, return)? -/
def Outcome.isTerminating : Outcome → Bool
  | .outOfFuel => false
  | _ => true

@[simp] theorem Outcome.isNormal_normal : Outcome.normal.isNormal = true := rfl
@[simp] theorem Outcome.isNormal_break : Outcome.break_.isNormal = false := rfl
@[simp] theorem Outcome.isNormal_continue : Outcome.continue_.isNormal = false := rfl
@[simp] theorem Outcome.isNormal_return (v : Option Value) :
    (Outcome.return_ v).isNormal = false := rfl
@[simp] theorem Outcome.isNormal_outOfFuel : Outcome.outOfFuel.isNormal = false := rfl

@[simp] theorem Outcome.isTerminating_normal : Outcome.normal.isTerminating = true := rfl
@[simp] theorem Outcome.isTerminating_break : Outcome.break_.isTerminating = true := rfl
@[simp] theorem Outcome.isTerminating_continue : Outcome.continue_.isTerminating = true := rfl
@[simp] theorem Outcome.isTerminating_return (v : Option Value) :
    (Outcome.return_ v).isTerminating = true := rfl
@[simp] theorem Outcome.isTerminating_outOfFuel : Outcome.outOfFuel.isTerminating = false := rfl

/-- Normal and outOfFuel are distinct. -/
theorem Outcome.normal_ne_outOfFuel : Outcome.normal ≠ Outcome.outOfFuel := by
  intro h; cases h

/-- return_ is injective. -/
theorem Outcome.return_injective : Function.Injective Outcome.return_ := fun _ _ h => by
  cases h; rfl

/-! ## StmtResult -/

/-- Result of lowering a DSL expression to statements:
    the statement to execute and the expression that holds the final value.
    Used by CodeGenerable.lower to return both the compiled code and
    where the result is stored. -/
structure StmtResult where
  stmt      : Stmt
  resultVar : LowLevelExpr
  deriving Repr

/-! ## CodeGenState (extended with assignments) -/

/-- Assignment of a value to a named temporary variable.
    Used during code generation to accumulate three-address-code style assignments. -/
structure Assignment where
  varName : VarName
  value   : LowLevelExpr
  deriving Repr

/-- Extended code generation state with accumulated assignments.
    Inherits freshVar counter from Value.lean's CodeGenState. -/
structure ExtCodeGenState where
  nextVar     : Nat := 0
  assignments : List Assignment := []
  deriving Repr, Inhabited

/-- Generate a fresh temporary and advance the counter. -/
def ExtCodeGenState.freshVar (s : ExtCodeGenState) : VarName × ExtCodeGenState :=
  (.temp s.nextVar, { s with nextVar := s.nextVar + 1 })

/-- Append an assignment to the accumulated list. -/
def ExtCodeGenState.addAssignment (s : ExtCodeGenState) (a : Assignment) : ExtCodeGenState :=
  { s with assignments := s.assignments ++ [a] }

/-- Convert a list of assignments to a sequential Stmt chain.
    Each assignment becomes a Stmt.assign, chained via Stmt.seq.
    Empty list yields Stmt.skip. -/
def assignmentsToStmt : List Assignment → Stmt
  | [] => .skip
  | [a] => .assign a.varName a.value
  | a :: as => .seq (.assign a.varName a.value) (assignmentsToStmt as)

end TrustLean
