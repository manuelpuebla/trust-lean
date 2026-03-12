/-
  Trust-Lean — Verified Code Generation Framework
  MicroC/AST.lean: MicroC AST — formal C99 subset types

  N10.1 (v2.0.0): FUNDACIONAL — MicroC AST definitions.
  MicroC is a formal C99 subset with ~20 AST nodes matching the output
  of Trust-Lean's stmtToC backend. String-based identifiers (C identifiers).

  Design decisions:
  - MicroCExpr: 7 constructors (litInt, litBool, varRef, binOp, unaryOp, powCall, arrayAccess)
  - MicroCStmt: 11 constructors (no for_ — desugared to seq+while during translation)
  - String identifiers: MicroC IS a C subset, so identifiers are C strings
  - Flat namespace: no shadowing, no nested scopes (v2.0.0 simplification)
  - MicroCEnv: String → Value (functional environment, no heap)
  - No short-circuit &&/||: pure expressions, so semantically equivalent
  - Int = Lean Int (unbounded): int64_t wrapping deferred to v3.0
-/

import TrustLean.Core.Value

set_option autoImplicit false

namespace TrustLean

/-! ## MicroC Binary Operators -/

/-- MicroC binary operators matching C infix operators.
    Same set as BinOp but in the MicroC namespace. -/
inductive MicroCBinOp where
  | add   -- +
  | sub   -- -
  | mul   -- *
  | eqOp  -- ==
  | ltOp  -- <
  | land  -- &&
  | lor   -- ||
  deriving Repr, BEq, DecidableEq, Inhabited

/-- MicroC unary operators. -/
inductive MicroCUnaryOp where
  | neg   -- - (integer negation)
  | lnot  -- ! (boolean negation)
  deriving Repr, BEq, DecidableEq, Inhabited

/-! ## MicroC Expressions -/

/-- MicroC expression AST. 7 constructors matching LowLevelExpr
    but with String identifiers (C-level names).
    All binary sub-expressions are parenthesized in the canonical form. -/
inductive MicroCExpr where
  | litInt    : Int → MicroCExpr
  | litBool   : Bool → MicroCExpr
  | varRef    : String → MicroCExpr
  | binOp     : MicroCBinOp → MicroCExpr → MicroCExpr → MicroCExpr
  | unaryOp   : MicroCUnaryOp → MicroCExpr → MicroCExpr
  | powCall   : MicroCExpr → Nat → MicroCExpr
  | arrayAccess : MicroCExpr → MicroCExpr → MicroCExpr
  deriving Repr, Inhabited, BEq, DecidableEq

/-! ## MicroC Statements -/

/-- MicroC statement AST. 11 constructors (no for_ — desugared during translation).
    Matches the output of stmtToC for all 12 Stmt constructors (for_ becomes seq+while). -/
inductive MicroCStmt where
  | assign    : String → MicroCExpr → MicroCStmt
  | store     : MicroCExpr → MicroCExpr → MicroCExpr → MicroCStmt
  | load      : String → MicroCExpr → MicroCExpr → MicroCStmt
  | seq       : MicroCStmt → MicroCStmt → MicroCStmt
  | ite       : MicroCExpr → MicroCStmt → MicroCStmt → MicroCStmt
  | while_    : MicroCExpr → MicroCStmt → MicroCStmt
  | call      : String → String → List MicroCExpr → MicroCStmt
  | skip      : MicroCStmt
  | break_    : MicroCStmt
  | continue_ : MicroCStmt
  | return_   : Option MicroCExpr → MicroCStmt
  deriving Repr, Inhabited, BEq, DecidableEq

/-! ## MicroC Environment -/

/-- MicroC environment: String-keyed (C identifiers) → Value.
    Functional model (no heap). -/
abbrev MicroCEnv := String → Value

/-- Default MicroC environment: all variables initialized to int 0. -/
def MicroCEnv.default : MicroCEnv := fun _ => .int 0

/-- Update a single variable in the MicroC environment. -/
def MicroCEnv.update (env : MicroCEnv) (name : String) (val : Value) : MicroCEnv :=
  fun n => if n = name then val else env n

@[simp] theorem MicroCEnv.update_same (env : MicroCEnv) (name : String) (val : Value) :
    (env.update name val) name = val := by
  simp [MicroCEnv.update]

@[simp] theorem MicroCEnv.update_other (env : MicroCEnv) (name name' : String) (val : Value)
    (h : name' ≠ name) :
    (env.update name val) name' = env name' := by
  simp [MicroCEnv.update, h]

/-- Updating the same variable twice: last write wins. -/
theorem MicroCEnv.update_update_same (env : MicroCEnv) (name : String) (v1 v2 : Value) :
    (env.update name v1).update name v2 = env.update name v2 := by
  funext n; simp only [MicroCEnv.update]; split <;> rfl

/-- Updating different variables commutes. -/
theorem MicroCEnv.update_comm (env : MicroCEnv) (n1 n2 : String) (v1 v2 : Value)
    (h : n1 ≠ n2) :
    (env.update n1 v1).update n2 v2 = (env.update n2 v2).update n1 v1 := by
  funext n; simp only [MicroCEnv.update]; by_cases h1 : n = n2 <;> by_cases h2 : n = n1 <;> simp_all

/-! ## Operator Conversion -/

/-- Convert Trust-Lean BinOp to MicroC BinOp. -/
def binOpToMicroC : BinOp → MicroCBinOp
  | .add => .add
  | .sub => .sub
  | .mul => .mul
  | .eqOp => .eqOp
  | .ltOp => .ltOp
  | .land => .land
  | .lor => .lor

/-- Convert Trust-Lean UnaryOp to MicroC UnaryOp. -/
def unaryOpToMicroC : UnaryOp → MicroCUnaryOp
  | .neg => .neg
  | .lnot => .lnot

/-- Convert MicroC BinOp back to Trust-Lean BinOp. -/
def microCBinOpToCore : MicroCBinOp → BinOp
  | .add => .add
  | .sub => .sub
  | .mul => .mul
  | .eqOp => .eqOp
  | .ltOp => .ltOp
  | .land => .land
  | .lor => .lor

/-- Convert MicroC UnaryOp back to Trust-Lean UnaryOp. -/
def microCUnaryOpToCore : MicroCUnaryOp → UnaryOp
  | .neg => .neg
  | .lnot => .lnot

/-! ## Operator Roundtrip Properties -/

@[simp] theorem microCBinOpToCore_binOpToMicroC (op : BinOp) :
    microCBinOpToCore (binOpToMicroC op) = op := by
  cases op <;> rfl

@[simp] theorem binOpToMicroC_microCBinOpToCore (op : MicroCBinOp) :
    binOpToMicroC (microCBinOpToCore op) = op := by
  cases op <;> rfl

@[simp] theorem microCUnaryOpToCore_unaryOpToMicroC (op : UnaryOp) :
    microCUnaryOpToCore (unaryOpToMicroC op) = op := by
  cases op <;> rfl

@[simp] theorem unaryOpToMicroC_microCUnaryOpToCore (op : MicroCUnaryOp) :
    unaryOpToMicroC (microCUnaryOpToCore op) = op := by
  cases op <;> rfl

/-! ## Evaluate MicroC Operators (reuse Core) -/

/-- Evaluate a MicroC binary operator via the Core evalBinOp. -/
def evalMicroCBinOp (op : MicroCBinOp) (v1 v2 : Value) : Option Value :=
  evalBinOp (microCBinOpToCore op) v1 v2

/-- Evaluate a MicroC unary operator via the Core evalUnaryOp. -/
def evalMicroCUnaryOp (op : MicroCUnaryOp) (v : Value) : Option Value :=
  evalUnaryOp (microCUnaryOpToCore op) v

/-! ## Size Functions -/

/-- Size of a MicroC expression (number of constructors). -/
def MicroCExpr.size : MicroCExpr → Nat
  | .litInt _ => 1
  | .litBool _ => 1
  | .varRef _ => 1
  | .binOp _ lhs rhs => 1 + lhs.size + rhs.size
  | .unaryOp _ e => 1 + e.size
  | .powCall base _ => 1 + base.size
  | .arrayAccess base idx => 1 + base.size + idx.size

/-- Size of a MicroC statement (number of constructors). -/
def MicroCStmt.size : MicroCStmt → Nat
  | .assign _ e => 1 + e.size
  | .store b i v => 1 + b.size + i.size + v.size
  | .load _ b i => 1 + b.size + i.size
  | .seq s1 s2 => 1 + s1.size + s2.size
  | .ite c t e => 1 + c.size + t.size + e.size
  | .while_ c body => 1 + c.size + body.size
  | .call _ _ args => 1 + args.foldl (fun acc a => acc + a.size) 0
  | .skip => 1
  | .break_ => 1
  | .continue_ => 1
  | .return_ none => 1
  | .return_ (some e) => 1 + e.size

/-! ## Structural Properties -/

/-- Size of any MicroC expression is positive. -/
theorem MicroCExpr.size_pos (e : MicroCExpr) : 0 < e.size := by
  cases e <;> simp [MicroCExpr.size] <;> omega

/-- Size of any MicroC statement is positive. -/
theorem MicroCStmt.size_pos (s : MicroCStmt) : 0 < s.size := by
  match s with
  | .assign _ e => simp [MicroCStmt.size]; omega
  | .store b i v => simp [MicroCStmt.size]; omega
  | .load _ b i => simp [MicroCStmt.size]; omega
  | .seq s1 s2 => simp [MicroCStmt.size]; omega
  | .ite c t e => simp [MicroCStmt.size]; omega
  | .while_ c body => simp [MicroCStmt.size]; omega
  | .call _ _ args => simp [MicroCStmt.size]; omega
  | .skip => decide
  | .break_ => decide
  | .continue_ => decide
  | .return_ none => decide
  | .return_ (some e) => simp [MicroCStmt.size]; omega

/-- MicroCStmt.skip is the identity for seq (left). -/
@[simp] theorem MicroCStmt.seq_skip_left_size (s : MicroCStmt) :
    (MicroCStmt.seq .skip s).size = 1 + 1 + s.size := by
  simp [MicroCStmt.size]

/-- binOpToMicroC is injective. -/
theorem binOpToMicroC_injective : Function.Injective binOpToMicroC := by
  intro a b h; cases a <;> cases b <;> first | rfl | simp [binOpToMicroC] at h

/-- unaryOpToMicroC is injective. -/
theorem unaryOpToMicroC_injective : Function.Injective unaryOpToMicroC := by
  intro a b h; cases a <;> cases b <;> first | rfl | simp [unaryOpToMicroC] at h

end TrustLean
