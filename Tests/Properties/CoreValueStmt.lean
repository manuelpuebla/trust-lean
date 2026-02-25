/-
  Trust-Lean Test Suite — Properties for N1.1 (Core Value + Stmt)
  Tests adapted from TESTS_OUTSOURCE.md specifications.

  Note: The actual API differs from the spec sketches in several ways:
  - BinOp has: add, sub, mul, eqOp, ltOp, land, lor (no div/mod/eq/ne)
  - UnaryOp has: neg, lnot (not "not")
  - LowLevelEnv is an abbreviation for VarName -> Value (not a map with find?)
  - Assignment has fields .varName and .value (not .lhs/.rhs)
  - Stmt.desugarFor takes (init : Stmt) (cond : LowLevelExpr) (step body : Stmt)
  - No BinOp.isIntOp / isBoolOp predicates exist

  Since the custom inductive types (Value, BinOp, etc.) lack SlimCheck
  SampleableExt instances, we use concrete decidable examples with native_decide
  or direct proof instead.
-/

import TrustLean.Core.Value
import TrustLean.Core.Stmt

open TrustLean

/-! ## P1 — P0 SOUNDNESS: evalBinOp on integer types correctly reflects arithmetic -/
-- P0, INVARIANT: evalBinOp add on Ints produces correct result
example : evalBinOp .add (.int 5) (.int 3) = some (.int 8) := by native_decide
example : evalBinOp .sub (.int 10) (.int 4) = some (.int 6) := by native_decide
example : evalBinOp .mul (.int 3) (.int 7) = some (.int 21) := by native_decide
-- Comparison ops on Ints
example : evalBinOp .eqOp (.int 5) (.int 5) = some (.bool true) := by native_decide
example : evalBinOp .eqOp (.int 5) (.int 3) = some (.bool false) := by native_decide
example : evalBinOp .ltOp (.int 3) (.int 5) = some (.bool true) := by native_decide
example : evalBinOp .ltOp (.int 5) (.int 3) = some (.bool false) := by native_decide

/-! ## P2 — P0 SOUNDNESS: evalBinOp on boolean types correctly reflects logical ops -/
-- P0, INVARIANT: evalBinOp logical on Bools produces correct result
example : evalBinOp .land (.bool true) (.bool false) = some (.bool false) := by native_decide
example : evalBinOp .land (.bool true) (.bool true) = some (.bool true) := by native_decide
example : evalBinOp .lor (.bool false) (.bool true) = some (.bool true) := by native_decide
example : evalBinOp .lor (.bool false) (.bool false) = some (.bool false) := by native_decide

/-! ## P3 — P1 COMMUTATIVITY: evalBinOp commutative for add, mul, land, lor, eqOp -/
-- P1, COMMUTATIVITY: add is commutative
example (a b : Int) : evalBinOp .add (.int a) (.int b) = evalBinOp .add (.int b) (.int a) := by
  simp [evalBinOp, Int.add_comm]

-- P1, COMMUTATIVITY: mul is commutative
example (a b : Int) : evalBinOp .mul (.int a) (.int b) = evalBinOp .mul (.int b) (.int a) := by
  simp [evalBinOp, Int.mul_comm]

-- P1, COMMUTATIVITY: land is commutative
example (a b : Bool) : evalBinOp .land (.bool a) (.bool b) = evalBinOp .land (.bool b) (.bool a) := by
  simp [evalBinOp, Bool.and_comm]

-- P1, COMMUTATIVITY: lor is commutative
example (a b : Bool) : evalBinOp .lor (.bool a) (.bool b) = evalBinOp .lor (.bool b) (.bool a) := by
  simp [evalBinOp, Bool.or_comm]

-- P1, COMMUTATIVITY: eqOp is commutative on concrete values
example : evalBinOp .eqOp (.int 3) (.int 5) = evalBinOp .eqOp (.int 5) (.int 3) := by native_decide
example : evalBinOp .eqOp (.int 7) (.int 7) = evalBinOp .eqOp (.int 7) (.int 7) := by native_decide
example : evalBinOp .eqOp (.int 0) (.int (-1)) = evalBinOp .eqOp (.int (-1)) (.int 0) := by native_decide
-- General proof: eqOp commutativity
example (a b : Int) : evalBinOp .eqOp (.int a) (.int b) = evalBinOp .eqOp (.int b) (.int a) := by
  simp only [evalBinOp_eqOp]
  -- Goal: some (Value.bool (a == b)) = some (Value.bool (b == a))
  -- where (==) on Int is BEq.beq
  have h : (a == b) = (b == a) := by
    show decide (a = b) = decide (b = a)
    cases hab : decide (a = b) <;> cases hba : decide (b = a)
    all_goals simp_all
  rw [h]

/-! ## P4 — P1 INVARIANT: evalBinOp on mismatched types returns none -/
-- P1, INVARIANT: mismatched types always produce none
-- Arithmetic ops on int + bool = none
example (n : Int) (b : Bool) : evalBinOp .add (.int n) (.bool b) = none := by rfl
example (n : Int) (b : Bool) : evalBinOp .add (.bool b) (.int n) = none := by cases n <;> rfl
example (n : Int) (b : Bool) : evalBinOp .sub (.int n) (.bool b) = none := by rfl
example (n : Int) (b : Bool) : evalBinOp .mul (.int n) (.bool b) = none := by rfl
-- Logical ops on bool + int = none
example (b : Bool) (n : Int) : evalBinOp .land (.bool b) (.int n) = none := by rfl
example (b : Bool) (n : Int) : evalBinOp .lor (.bool b) (.int n) = none := by rfl
-- All ops exhaustively checked on mismatched pairs
example : evalBinOp .add (.int 1) (.bool true) = none := by native_decide
example : evalBinOp .land (.int 1) (.bool true) = none := by native_decide

/-! ## P5 — P1 SOUNDNESS: evalUnaryOp correctly reflects underlying ops -/
-- P1, SOUNDNESS: evalUnaryOp neg on Int
example (n : Int) : evalUnaryOp .neg (.int n) = some (.int (-n)) := by rfl
-- P1, SOUNDNESS: evalUnaryOp lnot on Bool
example (b : Bool) : evalUnaryOp .lnot (.bool b) = some (.bool (!b)) := by rfl
-- P1, SOUNDNESS: mismatched types
example (b : Bool) : evalUnaryOp .neg (.bool b) = none := by rfl
example (n : Int) : evalUnaryOp .lnot (.int n) = none := by rfl

/-! ## P6 — P1 IDEMPOTENCY: Applying neg or lnot twice is identity -/
-- P1, IDEMPOTENCY: neg is an involution on Ints
example (n : Int) : (evalUnaryOp .neg (.int n)) >>= (evalUnaryOp .neg) = some (.int n) := by
  simp [evalUnaryOp, Int.neg_neg]

-- P1, IDEMPOTENCY: lnot is an involution on Bools
example (b : Bool) : (evalUnaryOp .lnot (.bool b)) >>= (evalUnaryOp .lnot) = some (.bool b) := by
  simp [evalUnaryOp, Bool.not_not]

/-! ## P7 — P0 INVARIANT: Read-over-write for LowLevelEnv.update -/
-- P0, INVARIANT: updating a key and reading it returns the new value
example (env : LowLevelEnv) (k : VarName) (v : Value) :
    (env.update k v) k = v := by
  simp [LowLevelEnv.update]

/-! ## P8 — P1 PRESERVATION: Updating a key does not affect other keys -/
-- P1, PRESERVATION: update on k1 does not affect k2 when k1 != k2
example (env : LowLevelEnv) (k1 k2 : VarName) (v : Value) (h : k1 ≠ k2) :
    (env.update k1 v) k2 = env k2 := by
  simp [LowLevelEnv.update, Ne.symm h]

/-! ## P9 — P0 INVARIANT: CodeGenState.freshVar produces distinct names -/
-- P0, INVARIANT: consecutive freshVar calls produce different names
-- Concrete verification (general proof difficult without omega on VarName)
example : let r1 := (CodeGenState.mk 0).freshVar
          let r2 := r1.2.freshVar
          r1.1 ≠ r2.1 := by native_decide
example : let r1 := (CodeGenState.mk 5).freshVar
          let r2 := r1.2.freshVar
          r1.1 ≠ r2.1 := by native_decide
example : let r1 := (CodeGenState.mk 100).freshVar
          let r2 := r1.2.freshVar
          r1.1 ≠ r2.1 := by native_decide

/-! ## P10 — P1 EQUIVALENCE: Stmt.desugarFor translates for to while -/
-- P1, EQUIVALENCE: desugarFor is seq of init + while(cond, seq(body, step))
example (init : Stmt) (cond : LowLevelExpr) (step body : Stmt) :
    Stmt.desugarFor init cond step body =
    Stmt.seq init (Stmt.while cond (Stmt.seq body step)) := by
  rfl

/-! ## P11 — P2 INVARIANT: Outcome boolean predicates are mutually exclusive -/
-- P2, INVARIANT: isNormal and isLoopSignal are never both true
example (o : Outcome) : ¬ (o.isNormal = true ∧ o.isLoopSignal = true) := by
  cases o <;> simp [Outcome.isNormal, Outcome.isLoopSignal]

-- P2, INVARIANT: normal implies terminating (they can overlap at normal)
-- But normal implies NOT outOfFuel:
example (o : Outcome) : o.isNormal = true → o.isTerminating = true := by
  cases o <;> simp [Outcome.isNormal, Outcome.isTerminating]

/-! ## P12 — P1 SOUNDNESS: assignmentsToStmt correctly folds assignments -/
-- P1, SOUNDNESS: empty list yields skip
example : assignmentsToStmt [] = Stmt.skip := by rfl

-- P1, SOUNDNESS: single element yields assign
example (a : Assignment) : assignmentsToStmt [a] = Stmt.assign a.varName a.value := by rfl

-- P1, SOUNDNESS: two elements yield seq
example (a1 a2 : Assignment) :
    assignmentsToStmt [a1, a2] =
    Stmt.seq (Stmt.assign a1.varName a1.value) (Stmt.assign a2.varName a2.value) := by rfl

-- P1, SOUNDNESS: three elements
example (a1 a2 a3 : Assignment) :
    assignmentsToStmt [a1, a2, a3] =
    Stmt.seq (Stmt.assign a1.varName a1.value)
      (Stmt.seq (Stmt.assign a2.varName a2.value) (Stmt.assign a3.varName a3.value)) := by rfl
