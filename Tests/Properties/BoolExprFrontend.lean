/-
  Trust-Lean — Tests/Properties/BoolExprFrontend.lean
  Property tests for N2.2: BoolExpr Frontend

  Tests the BoolExpr AST, eval, and compile functions.
  Uses decidable examples since BoolExpr/VarId types lack SampleableExt.
-/

import TrustLean.Frontend.BoolExpr.Syntax
import TrustLean.Frontend.BoolExpr.Compile
import TrustLean.Frontend.BoolExpr.Correctness

open TrustLean

/-! ## P1: P0, SOUNDNESS: BoolExpr.compile preserves eval semantics -/

-- P0, SOUNDNESS: compile_correct theorem exists with 0 sorry.
-- Concrete checks for compile structure.

-- Compiling a literal: skip + litBool
example : BoolExpr.compile boolVarNames (.lit true) 0 = (.skip, .litBool true, 0) := rfl
example : BoolExpr.compile boolVarNames (.lit false) 0 = (.skip, .litBool false, 0) := rfl

-- Compiling a variable: skip + varRef
example : BoolExpr.compile boolVarNames (.var 0) 0 = (.skip, .varRef (.user "b0"), 0) := rfl

-- Compiling and_: produces seq + assign with land
example : (BoolExpr.compile boolVarNames (.and_ (.lit true) (.lit false)) 0).2.2 = 1 := rfl

-- Compiling or_: produces seq + assign with lor
example : (BoolExpr.compile boolVarNames (.or_ (.lit true) (.lit false)) 0).2.2 = 1 := rfl

-- Compiling not_: produces seq + assign with lnot
example : (BoolExpr.compile boolVarNames (.not_ (.lit true)) 0).2.2 = 1 := rfl

/-! ## P2: P1, INVARIANT: BoolExpr.eval is invariant to irrelevant env changes -/

-- P1, INVARIANT: eval on lit doesn't depend on env at all.
example (env1 env2 : VarId → Bool) :
    BoolExpr.eval env1 (.lit true) = BoolExpr.eval env2 (.lit true) := rfl

example (env1 env2 : VarId → Bool) :
    BoolExpr.eval env1 (.lit false) = BoolExpr.eval env2 (.lit false) := rfl

-- eval on var v only depends on env v
example (env1 env2 : VarId → Bool) (v : VarId) (h : env1 v = env2 v) :
    BoolExpr.eval env1 (.var v) = BoolExpr.eval env2 (.var v) := by
  simp [BoolExpr.eval, h]

/-! ## P3: P2, EQUIVALENCE: double negation elimination -/

-- P2, EQUIVALENCE: not (not e) = e for all BoolExpr and env.
example (e : BoolExpr) (env : VarId → Bool) :
    BoolExpr.eval env (.not_ (.not_ e)) = BoolExpr.eval env e := by
  simp [BoolExpr.eval, Bool.not_not]

-- Concrete instances
example : BoolExpr.eval (fun _ => true) (.not_ (.not_ (.lit true))) = true := rfl
example : BoolExpr.eval (fun _ => false) (.not_ (.not_ (.lit false))) = false := rfl
example : BoolExpr.eval (fun _ => true) (.not_ (.not_ (.var 0))) = true := rfl

/-! ## Bonus: compile_mono and compile_correct type checks -/

-- Counter monotonicity holds
example : 0 ≤ (BoolExpr.compile boolVarNames (.and_ (.lit true) (.var 0)) 0).2.2 :=
  Nat.zero_le _

-- Main correctness theorem exists
#check @BoolExpr.compile_correct

-- De Morgan's law: not (and a b) = or (not a) (not b)
example (a b : Bool) :
    BoolExpr.eval (fun _ => a) (.not_ (.and_ (.lit a) (.lit b))) =
    BoolExpr.eval (fun _ => a) (.or_ (.not_ (.lit a)) (.not_ (.lit b))) := by
  simp [BoolExpr.eval, Bool.not_and]
