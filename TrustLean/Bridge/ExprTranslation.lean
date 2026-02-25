/-
  Trust-Lean — Verified Code Generation Framework
  Bridge/ExprTranslation.lean: Expression-level translation + correctness proofs

  N6.2: CRIT GATE — translates ScalarExpr → LowLevelExpr and IdxExpr → LowLevelExpr,
  with correctness theorems proving evalExpr ∘ translate = eval_source under bridge.
  This is the gate theorem: N7.1/N7.2 depend on these proofs.

  v1.1.0: Translation is purely structural (homomorphism).
-/

import TrustLean.Bridge.Types
import TrustLean.Bridge.Semantics
import TrustLean.Core.Eval

set_option autoImplicit false

namespace TrustLean.Bridge

/-! ## Scalar Expression Translation -/

/-- Translate a ScalarExpr to a LowLevelExpr.
    Structural homomorphism: each constructor maps to its LowLevelExpr analogue.
    - `.var v` → `.varRef (scalarVarToVarName v)`
    - `.const n` → `.litInt n`
    - `.neg e` → `.unaryOp .neg (translate e)`
    - `.add/sub/mul e1 e2` → `.binOp .add/.sub/.mul (translate e1) (translate e2)` -/
def scalarExprToLLExpr : ScalarExpr → LowLevelExpr
  | .var v     => .varRef (scalarVarToVarName v)
  | .const n   => .litInt n
  | .neg e     => .unaryOp .neg (scalarExprToLLExpr e)
  | .add e1 e2 => .binOp .add (scalarExprToLLExpr e1) (scalarExprToLLExpr e2)
  | .sub e1 e2 => .binOp .sub (scalarExprToLLExpr e1) (scalarExprToLLExpr e2)
  | .mul e1 e2 => .binOp .mul (scalarExprToLLExpr e1) (scalarExprToLLExpr e2)

/-! ## scalarExprToLLExpr @[simp] Lemmas -/

@[simp] theorem scalarExprToLLExpr_var (v : ScalarVar) :
    scalarExprToLLExpr (.var v) = .varRef (scalarVarToVarName v) := rfl

@[simp] theorem scalarExprToLLExpr_const (n : Int) :
    scalarExprToLLExpr (.const n) = .litInt n := rfl

@[simp] theorem scalarExprToLLExpr_neg (e : ScalarExpr) :
    scalarExprToLLExpr (.neg e) = .unaryOp .neg (scalarExprToLLExpr e) := rfl

@[simp] theorem scalarExprToLLExpr_add (e1 e2 : ScalarExpr) :
    scalarExprToLLExpr (.add e1 e2) =
    .binOp .add (scalarExprToLLExpr e1) (scalarExprToLLExpr e2) := rfl

@[simp] theorem scalarExprToLLExpr_sub (e1 e2 : ScalarExpr) :
    scalarExprToLLExpr (.sub e1 e2) =
    .binOp .sub (scalarExprToLLExpr e1) (scalarExprToLLExpr e2) := rfl

@[simp] theorem scalarExprToLLExpr_mul (e1 e2 : ScalarExpr) :
    scalarExprToLLExpr (.mul e1 e2) =
    .binOp .mul (scalarExprToLLExpr e1) (scalarExprToLLExpr e2) := rfl

/-! ## Scalar Expression Translation Correctness -/

/-- **Gate theorem**: scalarExprToLLExpr is correct under the scalar bridge.
    For any ScalarExpr e, evaluating the translated LowLevelExpr in the low-level
    environment produces `some (.int (evalScalarExpr sEnv e))`, provided the
    scalar bridge holds between sEnv and llEnv. -/
theorem scalarExprToLLExpr_correct
    (sEnv : ScalarVar → Int) (llEnv : LowLevelEnv)
    (hBridge : scalarBridge sEnv llEnv)
    (e : ScalarExpr) :
    evalExpr llEnv (scalarExprToLLExpr e) = some (.int (evalScalarExpr sEnv e)) := by
  induction e with
  | var v =>
    simp [scalarExprToLLExpr, evalScalarExpr, hBridge v]
  | const n =>
    simp [scalarExprToLLExpr, evalScalarExpr]
  | neg e ih =>
    simp [scalarExprToLLExpr, evalScalarExpr, ih, evalUnaryOp]
  | add e1 e2 ih1 ih2 =>
    simp [scalarExprToLLExpr, evalScalarExpr, ih1, ih2, evalBinOp]
  | sub e1 e2 ih1 ih2 =>
    simp [scalarExprToLLExpr, evalScalarExpr, ih1, ih2, evalBinOp]
  | mul e1 e2 ih1 ih2 =>
    simp [scalarExprToLLExpr, evalScalarExpr, ih1, ih2, evalBinOp]

/-! ## Index Expression Translation -/

/-- Translate an IdxExpr to a LowLevelExpr.
    IdxExpr evaluates to Nat, but LowLevelExpr works with Int.
    All Nat constants are wrapped with `Int.ofNat`.
    - `.const n` → `.litInt (Int.ofNat n)`
    - `.var v` → `.varRef (loopVarToVarName v)`
    - `.affine base s v` → `litInt base + litInt s * varRef v`
    - `.add e1 e2` → `.binOp .add (translate e1) (translate e2)`
    - `.mul c e` → `.binOp .mul (litInt c) (translate e)` -/
def idxExprToLLExpr : IdxExpr → LowLevelExpr
  | .const n         => .litInt (Int.ofNat n)
  | .var v           => .varRef (loopVarToVarName v)
  | .affine base s v =>
    .binOp .add (.litInt (Int.ofNat base))
      (.binOp .mul (.litInt (Int.ofNat s)) (.varRef (loopVarToVarName v)))
  | .add e1 e2       => .binOp .add (idxExprToLLExpr e1) (idxExprToLLExpr e2)
  | .mul c e         => .binOp .mul (.litInt (Int.ofNat c)) (idxExprToLLExpr e)

/-! ## idxExprToLLExpr @[simp] Lemmas -/

@[simp] theorem idxExprToLLExpr_const (n : Nat) :
    idxExprToLLExpr (.const n) = .litInt (Int.ofNat n) := rfl

@[simp] theorem idxExprToLLExpr_var (v : LoopVar) :
    idxExprToLLExpr (.var v) = .varRef (loopVarToVarName v) := rfl

@[simp] theorem idxExprToLLExpr_affine (base s : Nat) (v : LoopVar) :
    idxExprToLLExpr (.affine base s v) =
    .binOp .add (.litInt (Int.ofNat base))
      (.binOp .mul (.litInt (Int.ofNat s)) (.varRef (loopVarToVarName v))) := rfl

@[simp] theorem idxExprToLLExpr_add (e1 e2 : IdxExpr) :
    idxExprToLLExpr (.add e1 e2) =
    .binOp .add (idxExprToLLExpr e1) (idxExprToLLExpr e2) := rfl

@[simp] theorem idxExprToLLExpr_mul (c : Nat) (e : IdxExpr) :
    idxExprToLLExpr (.mul c e) =
    .binOp .mul (.litInt (Int.ofNat c)) (idxExprToLLExpr e) := rfl

/-! ## Index Expression Translation Correctness -/

/-- **Gate theorem**: idxExprToLLExpr is correct under the loop bridge.
    For any IdxExpr e, evaluating the translated LowLevelExpr in the low-level
    environment produces `some (.int (Int.ofNat (evalIdxExpr lEnv e)))`, provided
    the loop bridge holds between lEnv and llEnv. -/
theorem idxExprToLLExpr_correct
    (lEnv : LoopVar → Nat) (llEnv : LowLevelEnv)
    (hBridge : loopBridge lEnv llEnv)
    (e : IdxExpr) :
    evalExpr llEnv (idxExprToLLExpr e) = some (.int (Int.ofNat (evalIdxExpr lEnv e))) := by
  induction e with
  | const n =>
    simp [idxExprToLLExpr, evalIdxExpr]
  | var v =>
    simp [idxExprToLLExpr, evalIdxExpr, hBridge v]
  | affine base s v =>
    simp [idxExprToLLExpr, evalIdxExpr, hBridge v, evalBinOp]
  | add e1 e2 ih1 ih2 =>
    simp [idxExprToLLExpr, evalIdxExpr, ih1, ih2, evalBinOp]
  | mul c e ih =>
    simp [idxExprToLLExpr, evalIdxExpr, ih, evalBinOp]

/-! ## Structural Preservation Theorems -/

/-- Translation preserves addition structure (homomorphism). -/
theorem scalarExprToLLExpr_add_homo (e1 e2 : ScalarExpr) :
    scalarExprToLLExpr (.add e1 e2) =
    .binOp .add (scalarExprToLLExpr e1) (scalarExprToLLExpr e2) := rfl

/-- Translation preserves subtraction structure (homomorphism). -/
theorem scalarExprToLLExpr_sub_homo (e1 e2 : ScalarExpr) :
    scalarExprToLLExpr (.sub e1 e2) =
    .binOp .sub (scalarExprToLLExpr e1) (scalarExprToLLExpr e2) := rfl

/-- Translation preserves multiplication structure (homomorphism). -/
theorem scalarExprToLLExpr_mul_homo (e1 e2 : ScalarExpr) :
    scalarExprToLLExpr (.mul e1 e2) =
    .binOp .mul (scalarExprToLLExpr e1) (scalarExprToLLExpr e2) := rfl

/-- Translation preserves negation structure (homomorphism). -/
theorem scalarExprToLLExpr_neg_homo (e : ScalarExpr) :
    scalarExprToLLExpr (.neg e) =
    .unaryOp .neg (scalarExprToLLExpr e) := rfl

/-- idxExprToLLExpr preserves addition structure (homomorphism). -/
theorem idxExprToLLExpr_add_homo (e1 e2 : IdxExpr) :
    idxExprToLLExpr (.add e1 e2) =
    .binOp .add (idxExprToLLExpr e1) (idxExprToLLExpr e2) := rfl

/-- idxExprToLLExpr preserves scaled multiplication structure (homomorphism). -/
theorem idxExprToLLExpr_mul_homo (c : Nat) (e : IdxExpr) :
    idxExprToLLExpr (.mul c e) =
    .binOp .mul (.litInt (Int.ofNat c)) (idxExprToLLExpr e) := rfl

end TrustLean.Bridge
