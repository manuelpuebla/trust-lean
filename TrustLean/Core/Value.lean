/-
  Trust-Lean — Verified Code Generation Framework
  Core/Value.lean: Value type, expressions, and binary operations

  N1.1: FUNDACIONAL — all downstream nodes depend on these types.

  Key design decisions (from DESIGN_SPEC.md):
  - Value as sum type (not phantom/GADT) — avoids proof explosion (L-248)
  - VarName tagged union — constructor disjointness from kernel
  - evalBinOp → Option Value — None for type mismatch (QA feedback)
  - 7 BinOps: 3 arithmetic (Int→Int→Int) + 2 comparison (Int→Int→Bool) + 2 logical (Bool→Bool→Bool)
  - 6 LowLevelExpr constructors including litBool for heterogeneous computation
-/

set_option autoImplicit false

namespace TrustLean

/-! ## Value Type -/

/-- Heterogeneous value type for the Core IR.
    Sum type avoids phantom type proof explosion while supporting Int and Bool. -/
inductive Value where
  | int  : Int → Value
  | bool : Bool → Value
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Extract Int from a Value, or None if Bool. -/
def Value.asInt : Value → Option Int
  | .int n => some n
  | .bool _ => none

/-- Extract Bool from a Value, or None if Int. -/
def Value.asBool : Value → Option Bool
  | .bool b => some b
  | .int _ => none

@[simp] theorem Value.asInt_int (n : Int) : (Value.int n).asInt = some n := rfl
@[simp] theorem Value.asInt_bool (b : Bool) : (Value.bool b).asInt = none := rfl
@[simp] theorem Value.asBool_bool (b : Bool) : (Value.bool b).asBool = some b := rfl
@[simp] theorem Value.asBool_int (n : Int) : (Value.int n).asBool = none := rfl

/-- Value.int is injective. -/
theorem Value.int_injective : Function.Injective Value.int := fun _ _ h => by
  cases h; rfl

/-- Value.bool is injective. -/
theorem Value.bool_injective : Function.Injective Value.bool := fun _ _ h => by
  cases h; rfl

/-- Int and Bool constructors are disjoint. -/
theorem Value.int_ne_bool (n : Int) (b : Bool) : Value.int n ≠ Value.bool b := by
  intro h; cases h

/-! ## Binary Operations -/

/-- Binary operations in the Core IR.
    3 arithmetic (Int→Int→Int) + 2 comparison (Int→Int→Bool) + 2 logical (Bool→Bool→Bool). -/
inductive BinOp where
  | add   -- Int → Int → Int
  | sub   -- Int → Int → Int
  | mul   -- Int → Int → Int
  | eqOp  -- Int → Int → Bool
  | ltOp  -- Int → Int → Bool
  | land  -- Bool → Bool → Bool
  | lor   -- Bool → Bool → Bool
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Evaluate a binary operation. Returns None on type mismatch.
    Arithmetic ops require two Ints; logical ops require two Bools.
    No div/mod in this IR — added at frontend level if needed. -/
def evalBinOp : BinOp → Value → Value → Option Value
  | .add, .int a, .int b => some (.int (a + b))
  | .sub, .int a, .int b => some (.int (a - b))
  | .mul, .int a, .int b => some (.int (a * b))
  | .eqOp, .int a, .int b => some (.bool (a == b))
  | .ltOp, .int a, .int b => some (.bool (decide (a < b)))
  | .land, .bool a, .bool b => some (.bool (a && b))
  | .lor, .bool a, .bool b => some (.bool (a || b))
  | _, _, _ => none

-- @[simp] lemmas for evalBinOp: arithmetic on matching types
@[simp] theorem evalBinOp_add (a b : Int) :
    evalBinOp .add (.int a) (.int b) = some (.int (a + b)) := rfl
@[simp] theorem evalBinOp_sub (a b : Int) :
    evalBinOp .sub (.int a) (.int b) = some (.int (a - b)) := rfl
@[simp] theorem evalBinOp_mul (a b : Int) :
    evalBinOp .mul (.int a) (.int b) = some (.int (a * b)) := rfl

-- @[simp] lemmas for evalBinOp: comparison
@[simp] theorem evalBinOp_eqOp (a b : Int) :
    evalBinOp .eqOp (.int a) (.int b) = some (.bool (a == b)) := rfl
@[simp] theorem evalBinOp_ltOp (a b : Int) :
    evalBinOp .ltOp (.int a) (.int b) = some (.bool (decide (a < b))) := rfl

-- @[simp] lemmas for evalBinOp: logical
@[simp] theorem evalBinOp_land (a b : Bool) :
    evalBinOp .land (.bool a) (.bool b) = some (.bool (a && b)) := rfl
@[simp] theorem evalBinOp_lor (a b : Bool) :
    evalBinOp .lor (.bool a) (.bool b) = some (.bool (a || b)) := rfl

-- @[simp] lemmas for evalBinOp: type mismatch cases
@[simp] theorem evalBinOp_add_bool_l (b : Bool) (v : Value) :
    evalBinOp .add (.bool b) v = none := by cases v <;> rfl
@[simp] theorem evalBinOp_add_bool_r (n : Int) (b : Bool) :
    evalBinOp .add (.int n) (.bool b) = none := rfl
@[simp] theorem evalBinOp_sub_bool_l (b : Bool) (v : Value) :
    evalBinOp .sub (.bool b) v = none := by cases v <;> rfl
@[simp] theorem evalBinOp_sub_bool_r (n : Int) (b : Bool) :
    evalBinOp .sub (.int n) (.bool b) = none := rfl
@[simp] theorem evalBinOp_mul_bool_l (b : Bool) (v : Value) :
    evalBinOp .mul (.bool b) v = none := by cases v <;> rfl
@[simp] theorem evalBinOp_mul_bool_r (n : Int) (b : Bool) :
    evalBinOp .mul (.int n) (.bool b) = none := rfl
@[simp] theorem evalBinOp_land_int_l (n : Int) (v : Value) :
    evalBinOp .land (.int n) v = none := by cases v <;> rfl
@[simp] theorem evalBinOp_land_int_r (b : Bool) (n : Int) :
    evalBinOp .land (.bool b) (.int n) = none := rfl
@[simp] theorem evalBinOp_lor_int_l (n : Int) (v : Value) :
    evalBinOp .lor (.int n) v = none := by cases v <;> rfl
@[simp] theorem evalBinOp_lor_int_r (b : Bool) (n : Int) :
    evalBinOp .lor (.bool b) (.int n) = none := rfl

/-- evalBinOp on matching Int operands always succeeds for arithmetic ops. -/
theorem evalBinOp_int_some (op : BinOp) (a b : Int)
    (h : op = .add ∨ op = .sub ∨ op = .mul ∨ op = .eqOp ∨ op = .ltOp) :
    (evalBinOp op (.int a) (.int b)).isSome = true := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [evalBinOp]

/-- evalBinOp on matching Bool operands always succeeds for logical ops. -/
theorem evalBinOp_bool_some (op : BinOp) (a b : Bool)
    (h : op = .land ∨ op = .lor) :
    (evalBinOp op (.bool a) (.bool b)).isSome = true := by
  rcases h with rfl | rfl <;> simp [evalBinOp]

/-! ## Unary Operations -/

/-- Unary operations: integer negation and boolean negation. -/
inductive UnaryOp where
  | neg   -- Int → Int
  | lnot  -- Bool → Bool
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Evaluate a unary operation. Returns None on type mismatch. -/
def evalUnaryOp : UnaryOp → Value → Option Value
  | .neg, .int n => some (.int (-n))
  | .lnot, .bool b => some (.bool (!b))
  | _, _ => none

@[simp] theorem evalUnaryOp_neg (n : Int) :
    evalUnaryOp .neg (.int n) = some (.int (-n)) := rfl
@[simp] theorem evalUnaryOp_lnot (b : Bool) :
    evalUnaryOp .lnot (.bool b) = some (.bool (!b)) := rfl
@[simp] theorem evalUnaryOp_neg_bool (b : Bool) :
    evalUnaryOp .neg (.bool b) = none := rfl
@[simp] theorem evalUnaryOp_lnot_int (n : Int) :
    evalUnaryOp .lnot (.int n) = none := rfl

/-! ## Variable Names -/

/-- Variable names: user-provided, compiler-generated temporaries, or array elements.
    Constructor disjointness (user ≠ temp ≠ array) is free from DecidableEq. -/
inductive VarName where
  | user  : String → VarName
  | temp  : Nat → VarName
  | array : String → Int → VarName
  deriving Repr, BEq, DecidableEq, Inhabited

/-! ## Low-Level Expressions -/

/-- Low-level expression IR, closer to three-address code / SSA.
    6 constructors supporting heterogeneous computation (Int and Bool). -/
inductive LowLevelExpr where
  | litInt   : Int → LowLevelExpr
  | litBool  : Bool → LowLevelExpr
  | varRef   : VarName → LowLevelExpr
  | binOp    : BinOp → LowLevelExpr → LowLevelExpr → LowLevelExpr
  | unaryOp  : UnaryOp → LowLevelExpr → LowLevelExpr
  | powCall  : LowLevelExpr → Nat → LowLevelExpr
  deriving Repr, Inhabited

/-! ## Environment -/

/-- Environment mapping variable names to values.
    Pure function (total): uninitialized variables map to a default.
    This is the LeanScribe-proven model; O(1) hash map is a future optimization. -/
abbrev LowLevelEnv := VarName → Value

/-- Default environment: all variables initialized to int 0. -/
def LowLevelEnv.default : LowLevelEnv := fun _ => .int 0

/-- Update a single variable in the environment. -/
def LowLevelEnv.update (env : LowLevelEnv) (name : VarName) (val : Value) : LowLevelEnv :=
  fun n => if n = name then val else env n

@[simp] theorem LowLevelEnv.update_same (env : LowLevelEnv) (name : VarName) (val : Value) :
    (env.update name val) name = val := by
  simp [LowLevelEnv.update]

@[simp] theorem LowLevelEnv.update_other (env : LowLevelEnv) (name name' : VarName) (val : Value)
    (h : name' ≠ name) :
    (env.update name val) name' = env name' := by
  simp [LowLevelEnv.update, h]

/-- Updating the same variable twice: last write wins. -/
theorem LowLevelEnv.update_update_same (env : LowLevelEnv) (name : VarName) (v1 v2 : Value) :
    (env.update name v1).update name v2 = env.update name v2 := by
  funext n
  simp only [LowLevelEnv.update]
  split <;> rfl

/-- Updating different variables commutes. -/
theorem LowLevelEnv.update_comm (env : LowLevelEnv) (n1 n2 : VarName) (v1 v2 : Value)
    (h : n1 ≠ n2) :
    (env.update n1 v1).update n2 v2 = (env.update n2 v2).update n1 v1 := by
  funext n
  simp only [LowLevelEnv.update]
  by_cases h1 : n = n2 <;> by_cases h2 : n = n1 <;> simp_all

/-! ## Code Generation State -/

/-- Code generation state: tracks fresh variable counter. -/
structure CodeGenState where
  nextVar : Nat := 0
  deriving Repr, Inhabited

/-- Generate a fresh temporary variable name, incrementing the counter. -/
def CodeGenState.freshVar (s : CodeGenState) : VarName × CodeGenState :=
  (.temp s.nextVar, { s with nextVar := s.nextVar + 1 })

end TrustLean
