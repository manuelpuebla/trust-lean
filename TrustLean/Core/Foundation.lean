/-
  Trust-Lean — Verified Code Generation Framework
  Core/Foundation.lean: Foundation lemmas for store/load, seq, and control flow

  N1.4: CRITICO — provides the building blocks for frontend correctness proofs
  and the amo-lean integration bridge.

  Key properties:
  - store_load_same / store_load_other: memory model soundness via functional env
  - seq_skip_left/right: seq identity lemmas
  - break/continue/return propagation: control flow composition for ImpStmt
  - Fuel independence: non-loop constructs produce same result regardless of fuel
  - All key lemmas tagged @[simp] for automated downstream proofs
-/

import TrustLean.Core.Eval

set_option autoImplicit false

namespace TrustLean

/-! ## VarName Constructor Disjointness

    These @[simp] lemmas let the simplifier resolve VarName equalities/inequalities
    arising in store/load proofs. Cross-constructor pairs and same-constructor
    injectivity for the `array` constructor. -/

@[simp] theorem VarName.array_ne_of_index_ne {name : String} {i j : Int} (h : i ≠ j) :
    VarName.array name i ≠ VarName.array name j := by
  intro heq; cases heq; exact h rfl

@[simp] theorem VarName.array_ne_of_name_ne {name1 name2 : String} {i j : Int}
    (h : name1 ≠ name2) :
    VarName.array name1 i ≠ VarName.array name2 j := by
  intro heq; cases heq; exact h rfl

@[simp] theorem VarName.user_ne_array {s : String} {name : String} {i : Int} :
    VarName.user s ≠ VarName.array name i := by
  intro h; cases h

@[simp] theorem VarName.array_ne_user {name : String} {i : Int} {s : String} :
    VarName.array name i ≠ VarName.user s := by
  intro h; cases h

@[simp] theorem VarName.temp_ne_array {n : Nat} {name : String} {i : Int} :
    VarName.temp n ≠ VarName.array name i := by
  intro h; cases h

@[simp] theorem VarName.array_ne_temp {name : String} {i : Int} {n : Nat} :
    VarName.array name i ≠ VarName.temp n := by
  intro h; cases h

@[simp] theorem VarName.user_ne_temp {s : String} {n : Nat} :
    VarName.user s ≠ VarName.temp n := by
  intro h; cases h

@[simp] theorem VarName.temp_ne_user {n : Nat} {s : String} :
    VarName.temp n ≠ VarName.user s := by
  intro h; cases h

/-! ## Store/Load Lemmas (Environment Level)

    These formalize the memory model soundness for Trust-Lean's functional environment.
    Store = `env.update (.array name idx) val`, Load = `env (.array name idx)`.
    No aliasing by construction (functional env, per DESIGN_SPEC.md). -/

/-- Store then load at the same (base, index) returns the stored value. -/
@[simp] theorem store_load_same (env : LowLevelEnv) (base : String)
    (idx : Int) (val : Value) :
    (env.update (.array base idx) val) (.array base idx) = val :=
  LowLevelEnv.update_same env (.array base idx) val

/-- Store at index i, load at index j ≠ i: original value preserved. -/
@[simp] theorem store_load_other_index (env : LowLevelEnv) (base : String)
    (idx1 idx2 : Int) (val : Value) (h : idx1 ≠ idx2) :
    (env.update (.array base idx1) val) (.array base idx2) = env (.array base idx2) := by
  apply LowLevelEnv.update_other
  exact VarName.array_ne_of_index_ne (Ne.symm h)

/-- Store in array base1, load from array base2 ≠ base1: original value preserved. -/
@[simp] theorem store_load_other_name (env : LowLevelEnv) (base1 base2 : String)
    (idx1 idx2 : Int) (val : Value) (h : base1 ≠ base2) :
    (env.update (.array base1 idx1) val) (.array base2 idx2) = env (.array base2 idx2) := by
  apply LowLevelEnv.update_other
  exact VarName.array_ne_of_name_ne (Ne.symm h)

/-- Store in array does not affect user variables. -/
@[simp] theorem store_preserves_user (env : LowLevelEnv) (base : String)
    (idx : Int) (val : Value) (s : String) :
    (env.update (.array base idx) val) (.user s) = env (.user s) := by
  exact LowLevelEnv.update_other env (.array base idx) (.user s) val VarName.user_ne_array

/-- Store in array does not affect temp variables. -/
@[simp] theorem store_preserves_temp (env : LowLevelEnv) (base : String)
    (idx : Int) (val : Value) (n : Nat) :
    (env.update (.array base idx) val) (.temp n) = env (.temp n) := by
  exact LowLevelEnv.update_other env (.array base idx) (.temp n) val VarName.temp_ne_array

/-! ## Seq Foundation Lemmas -/

/-- Skip is a left identity for seq. -/
@[simp] theorem seq_skip_left (fuel : Nat) (env : LowLevelEnv) (s : Stmt) :
    evalStmt fuel env (.seq .skip s) = evalStmt fuel env s := by
  simp [evalStmt_seq, evalStmt_skip]

/-- Skip is a right identity for seq (when s returns normal). -/
theorem seq_skip_right (fuel : Nat) (env env' : LowLevelEnv) (s : Stmt)
    (h : evalStmt fuel env s = some (.normal, env')) :
    evalStmt fuel env (.seq s .skip) = some (.normal, env') := by
  simp [evalStmt_seq, h, evalStmt_skip]

/-! ## Outcome Propagation Through Seq

    When the first statement in a seq produces a non-normal outcome,
    the second statement is never executed. -/

/-- Break propagates through seq (left position). -/
theorem break_propagates_seq (fuel : Nat) (env env' : LowLevelEnv) (s1 s2 : Stmt)
    (h : evalStmt fuel env s1 = some (.break_, env')) :
    evalStmt fuel env (.seq s1 s2) = some (.break_, env') := by
  simp [evalStmt_seq, h]

/-- Continue propagates through seq (left position). -/
theorem continue_propagates_seq (fuel : Nat) (env env' : LowLevelEnv) (s1 s2 : Stmt)
    (h : evalStmt fuel env s1 = some (.continue_, env')) :
    evalStmt fuel env (.seq s1 s2) = some (.continue_, env') := by
  simp [evalStmt_seq, h]

/-- Return propagates through seq (left position). -/
theorem return_propagates_seq (fuel : Nat) (env env' : LowLevelEnv) (s1 s2 : Stmt)
    (rv : Option Value)
    (h : evalStmt fuel env s1 = some (.return_ rv, env')) :
    evalStmt fuel env (.seq s1 s2) = some (.return_ rv, env') := by
  simp [evalStmt_seq, h]

/-- outOfFuel propagates through seq (left position). -/
theorem outOfFuel_propagates_seq (fuel : Nat) (env env' : LowLevelEnv) (s1 s2 : Stmt)
    (h : evalStmt fuel env s1 = some (.outOfFuel, env')) :
    evalStmt fuel env (.seq s1 s2) = some (.outOfFuel, env') := by
  simp [evalStmt_seq, h]

/-! ## While Loop Control Flow Composition

    These lemmas compose the raw evalStmt_while_succ equation lemma into
    higher-level patterns for each Outcome variant. Following the Clight
    3-rule pattern from DESIGN_SPEC.md. -/

/-- While with false condition exits normally (requires fuel > 0). -/
@[simp] theorem while_false (fuel : Nat) (env : LowLevelEnv)
    (cond : LowLevelExpr) (body : Stmt)
    (hcond : evalExpr env cond = some (.bool false)) :
    evalStmt (fuel + 1) env (.while cond body) = some (.normal, env) := by
  simp [evalStmt_while_succ, hcond]

/-- While with true condition and normal body: re-enter the loop. -/
theorem while_true_body_normal (fuel : Nat) (env env' : LowLevelEnv)
    (cond : LowLevelExpr) (body : Stmt)
    (hcond : evalExpr env cond = some (.bool true))
    (hbody : evalStmt fuel env body = some (.normal, env')) :
    evalStmt (fuel + 1) env (.while cond body) =
      evalStmt fuel env' (.while cond body) := by
  simp [evalStmt_while_succ, hcond, hbody]

/-- Break exits the innermost while loop with normal outcome. -/
theorem break_exits_while (fuel : Nat) (env env' : LowLevelEnv)
    (cond : LowLevelExpr) (body : Stmt)
    (hcond : evalExpr env cond = some (.bool true))
    (hbody : evalStmt fuel env body = some (.break_, env')) :
    evalStmt (fuel + 1) env (.while cond body) = some (.normal, env') := by
  simp [evalStmt_while_succ, hcond, hbody]

/-- Continue re-enters the while loop with the body's final environment. -/
theorem continue_reenter_while (fuel : Nat) (env env' : LowLevelEnv)
    (cond : LowLevelExpr) (body : Stmt)
    (hcond : evalExpr env cond = some (.bool true))
    (hbody : evalStmt fuel env body = some (.continue_, env')) :
    evalStmt (fuel + 1) env (.while cond body) =
      evalStmt fuel env' (.while cond body) := by
  simp [evalStmt_while_succ, hcond, hbody]

/-- Return propagates out of while loop. -/
theorem return_propagates_while (fuel : Nat) (env env' : LowLevelEnv)
    (cond : LowLevelExpr) (body : Stmt) (rv : Option Value)
    (hcond : evalExpr env cond = some (.bool true))
    (hbody : evalStmt fuel env body = some (.return_ rv, env')) :
    evalStmt (fuel + 1) env (.while cond body) = some (.return_ rv, env') := by
  simp [evalStmt_while_succ, hcond, hbody]

/-- outOfFuel in body propagates out of while loop. -/
theorem outOfFuel_propagates_while (fuel : Nat) (env env' : LowLevelEnv)
    (cond : LowLevelExpr) (body : Stmt)
    (hcond : evalExpr env cond = some (.bool true))
    (hbody : evalStmt fuel env body = some (.outOfFuel, env')) :
    evalStmt (fuel + 1) env (.while cond body) = some (.outOfFuel, env') := by
  simp [evalStmt_while_succ, hcond, hbody]

/-! ## Fuel Independence for Non-Loop Constructs

    These lemmas show that non-loop statements produce the same result
    regardless of fuel. Useful for FuelMono (N1.5) base cases. -/

@[simp] theorem evalStmt_skip_fuel_indep (f1 f2 : Nat) (env : LowLevelEnv) :
    evalStmt f1 env .skip = evalStmt f2 env .skip := by simp

@[simp] theorem evalStmt_break_fuel_indep (f1 f2 : Nat) (env : LowLevelEnv) :
    evalStmt f1 env .break_ = evalStmt f2 env .break_ := by simp

@[simp] theorem evalStmt_continue_fuel_indep (f1 f2 : Nat) (env : LowLevelEnv) :
    evalStmt f1 env .continue_ = evalStmt f2 env .continue_ := by simp

@[simp] theorem evalStmt_return_fuel_indep (f1 f2 : Nat) (env : LowLevelEnv)
    (re : Option LowLevelExpr) :
    evalStmt f1 env (.return_ re) = evalStmt f2 env (.return_ re) := by
  cases re with
  | none => simp
  | some e => simp [evalStmt_return_some]

@[simp] theorem evalStmt_assign_fuel_indep (f1 f2 : Nat) (env : LowLevelEnv)
    (name : VarName) (e : LowLevelExpr) :
    evalStmt f1 env (.assign name e) = evalStmt f2 env (.assign name e) := by simp

@[simp] theorem evalStmt_store_fuel_indep (f1 f2 : Nat) (env : LowLevelEnv)
    (base idx val : LowLevelExpr) :
    evalStmt f1 env (.store base idx val) = evalStmt f2 env (.store base idx val) := by simp

@[simp] theorem evalStmt_load_fuel_indep (f1 f2 : Nat) (env : LowLevelEnv)
    (var : VarName) (base idx : LowLevelExpr) :
    evalStmt f1 env (.load var base idx) = evalStmt f2 env (.load var base idx) := by simp

@[simp] theorem evalStmt_call_fuel_indep (f1 f2 : Nat) (env : LowLevelEnv)
    (var : VarName) (fname : String) (args : List LowLevelExpr) :
    evalStmt f1 env (.call var fname args) = evalStmt f2 env (.call var fname args) := by simp

end TrustLean
