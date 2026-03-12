/-
  Trust-Lean — Verified Code Generation Framework
  MicroC/CallTypes.lean: Call Types + Function Environment (v3.0.0)

  N15.1: Foundation types for MicroC function call semantics.
  Non-recursive calls only (no call constructors in function bodies).

  Key definitions:
  - MicroCFuncDef: function definition (params + body)
  - MicroCFuncEnv: function name → Optional function definition
  - hasCallStmt: decidable predicate for call presence in statements
  - NonRecursive: property asserting no calls in function body
  - buildCallEnv: create fresh callee environment from params + arg values
-/

import TrustLean.MicroC.AST

set_option autoImplicit false

namespace TrustLean

/-! ## Function Definition -/

/-- A MicroC function definition: parameter names and a body statement.
    No return type annotation (MicroC is dynamically typed). -/
structure MicroCFuncDef where
  params : List String
  body   : MicroCStmt
  deriving Repr, Inhabited, BEq, DecidableEq

/-! ## Function Environment -/

/-- Function environment: maps function names to definitions.
    Returns `none` for undefined functions. -/
abbrev MicroCFuncEnv := String → Option MicroCFuncDef

/-- Default function environment: no functions defined. -/
def MicroCFuncEnv.default : MicroCFuncEnv := fun _ => none

/-- Update the function environment with a new function definition. -/
def MicroCFuncEnv.update (fenv : MicroCFuncEnv) (name : String) (fdef : MicroCFuncDef) :
    MicroCFuncEnv :=
  fun n => if n = name then some fdef else fenv n

/-! ## HasCall Predicate -/

/-- Does a MicroCStmt contain a `.call` constructor? Decidable (computable). -/
def hasCallStmt : MicroCStmt → Bool
  | .call _ _ _ => true
  | .seq s1 s2 => hasCallStmt s1 || hasCallStmt s2
  | .ite _ s1 s2 => hasCallStmt s1 || hasCallStmt s2
  | .while_ _ s => hasCallStmt s
  | _ => false

/-! ## NonRecursive Predicate -/

/-- A function definition is non-recursive if its body contains no call constructors.
    This rules out ALL recursion: direct, mutual, and transitive. -/
def NonRecursive (fdef : MicroCFuncDef) : Prop := hasCallStmt fdef.body = false

/-- NonRecursive is decidable (hasCallStmt is computable). -/
instance (fdef : MicroCFuncDef) : Decidable (NonRecursive fdef) :=
  inferInstanceAs (Decidable (hasCallStmt fdef.body = false))

/-- A function environment is fully non-recursive if every defined function is non-recursive. -/
def AllNonRecursive (fenv : MicroCFuncEnv) : Prop :=
  ∀ name fdef, fenv name = some fdef → NonRecursive fdef

/-! ## Build Callee Environment -/

/-- Build a fresh environment for callee from parameter names and argument values.
    Parameters are bound left-to-right; unmatched params get default (int 0),
    extra args are ignored. -/
def buildCallEnv (params : List String) (args : List Value) : MicroCEnv :=
  (params.zip args).foldl (fun env (name, val) => env.update name val) MicroCEnv.default

/-! ## @[simp] Equation Lemmas -/

@[simp] theorem hasCallStmt_call (r f : String) (args : List MicroCExpr) :
    hasCallStmt (.call r f args) = true := rfl

@[simp] theorem hasCallStmt_seq (s1 s2 : MicroCStmt) :
    hasCallStmt (.seq s1 s2) = (hasCallStmt s1 || hasCallStmt s2) := rfl

@[simp] theorem hasCallStmt_ite (c : MicroCExpr) (s1 s2 : MicroCStmt) :
    hasCallStmt (.ite c s1 s2) = (hasCallStmt s1 || hasCallStmt s2) := rfl

@[simp] theorem hasCallStmt_while (c : MicroCExpr) (s : MicroCStmt) :
    hasCallStmt (.while_ c s) = hasCallStmt s := rfl

@[simp] theorem hasCallStmt_skip : hasCallStmt .skip = false := rfl
@[simp] theorem hasCallStmt_break : hasCallStmt .break_ = false := rfl
@[simp] theorem hasCallStmt_continue : hasCallStmt .continue_ = false := rfl

@[simp] theorem hasCallStmt_assign (n : String) (e : MicroCExpr) :
    hasCallStmt (.assign n e) = false := rfl

@[simp] theorem hasCallStmt_store (b i v : MicroCExpr) :
    hasCallStmt (.store b i v) = false := rfl

@[simp] theorem hasCallStmt_load (n : String) (b i : MicroCExpr) :
    hasCallStmt (.load n b i) = false := rfl

@[simp] theorem hasCallStmt_return (e : Option MicroCExpr) :
    hasCallStmt (.return_ e) = false := by cases e <;> rfl

@[simp] theorem MicroCFuncEnv_default_none (name : String) :
    MicroCFuncEnv.default name = none := rfl

@[simp] theorem MicroCFuncEnv_update_same (fenv : MicroCFuncEnv) (name : String)
    (fdef : MicroCFuncDef) :
    (fenv.update name fdef) name = some fdef := by
  simp [MicroCFuncEnv.update]

@[simp] theorem MicroCFuncEnv_update_other (fenv : MicroCFuncEnv) (name name' : String)
    (fdef : MicroCFuncDef) (h : name' ≠ name) :
    (fenv.update name fdef) name' = fenv name' := by
  simp [MicroCFuncEnv.update, h]

@[simp] theorem buildCallEnv_nil :
    buildCallEnv [] [] = MicroCEnv.default := rfl

/-! ## Key Properties -/

/-- NonRecursive is preserved through well-formed function construction:
    if the body has no calls, the function is non-recursive. -/
theorem nonRecursive_of_body (params : List String) (body : MicroCStmt)
    (h : hasCallStmt body = false) :
    NonRecursive ⟨params, body⟩ := h

/-- The negation: a function with a call in its body is NOT non-recursive. -/
theorem not_nonRecursive_of_hasCall (params : List String) (body : MicroCStmt)
    (h : hasCallStmt body = true) :
    ¬ NonRecursive ⟨params, body⟩ := by
  simp [NonRecursive, h]

/-- Default function environment is trivially all non-recursive (no functions defined). -/
theorem allNonRecursive_default : AllNonRecursive MicroCFuncEnv.default := by
  intro name fdef h
  simp [MicroCFuncEnv.default] at h

/-- Updating with a non-recursive function preserves AllNonRecursive. -/
theorem allNonRecursive_update (fenv : MicroCFuncEnv) (name : String) (fdef : MicroCFuncDef)
    (hall : AllNonRecursive fenv) (hnr : NonRecursive fdef) :
    AllNonRecursive (fenv.update name fdef) := by
  intro name' fdef' h
  simp [MicroCFuncEnv.update] at h
  split at h
  · cases h; exact hnr
  · exact hall name' fdef' h

/-! ## Non-Vacuity -/

/-- Non-vacuity: a simple non-recursive function exists.
    `add_one(x) { return x + 1; }` -/
example : NonRecursive ⟨["x"], .return_ (some (.binOp .add (.varRef "x") (.litInt 1)))⟩ := by
  native_decide

/-- Non-vacuity: a function WITH a call is not non-recursive.
    `bad(x) { call result "other" [x]; }` -/
example : ¬ NonRecursive ⟨["x"], .call "result" "other" [.varRef "x"]⟩ := by
  native_decide

/-- Non-vacuity: buildCallEnv correctly binds parameters. -/
example : buildCallEnv ["x", "y"] [.int 10, .int 20] "x" = .int 10 := by native_decide
example : buildCallEnv ["x", "y"] [.int 10, .int 20] "y" = .int 20 := by native_decide

/-- Non-vacuity: unbound variable in callee env returns default (.int 0). -/
example : buildCallEnv ["x"] [.int 42] "z" = .int 0 := by native_decide

/-- Non-vacuity: default function environment has no functions. -/
example : MicroCFuncEnv.default "myFunc" = none := by native_decide

/-- Non-vacuity: updated environment has the function. -/
example :
    let fdef : MicroCFuncDef := ⟨["x"], .return_ (some (.varRef "x"))⟩
    (MicroCFuncEnv.default.update "identity" fdef) "identity" = some fdef := by
  native_decide

/-- Non-vacuity: AllNonRecursive holds for a simple function environment. -/
example :
    let fdef : MicroCFuncDef := ⟨["x"], .return_ (some (.binOp .add (.varRef "x") (.litInt 1)))⟩
    AllNonRecursive (MicroCFuncEnv.default.update "inc" fdef) :=
  allNonRecursive_update _ _ _ allNonRecursive_default (by native_decide)

end TrustLean
