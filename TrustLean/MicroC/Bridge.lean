/-
  Trust-Lean — Verified Code Generation Framework
  MicroC/Bridge.lean: Bridge predicate linking LowLevelEnv and MicroCEnv

  N11.2 (v2.0.0): CRITICO — defines the microCBridge predicate and proves
  key properties:
  - Bridge preservation under env updates
  - Expression evaluation bridge (evalExpr = evalMicroCExpr ∘ exprToMicroC)

  The bridge connects VarName-keyed environments (Core IR) to
  String-keyed environments (MicroC) via varNameToC.

  Well-formedness hypothesis: varNameToC must be injective on the
  VarNames used in the program. This excludes pathological cases like
  a user variable named "t0" (which would collide with temp 0).
-/

import TrustLean.MicroC.Translation
import TrustLean.MicroC.Eval
import TrustLean.Core.Eval

set_option autoImplicit false

namespace TrustLean

/-! ## Bridge Predicate -/

/-- The bridge predicate: links a Core IR environment (VarName → Value)
    to a MicroC environment (String → Value) via varNameToC.
    For every variable v, both environments agree on its value. -/
def microCBridge (env : LowLevelEnv) (mcEnv : MicroCEnv) : Prop :=
  ∀ v : VarName, env v = mcEnv (varNameToC v)

/-! ## Bridge Preservation -/

/-- Bridge holds for default environments. -/
theorem microCBridge_default :
    microCBridge LowLevelEnv.default MicroCEnv.default := by
  intro v; rfl

/-- Bridge is preserved by updating the same variable (requires local injectivity). -/
theorem microCBridge_update {env : LowLevelEnv} {mcEnv : MicroCEnv}
    (hb : microCBridge env mcEnv) (name : VarName) (v : Value)
    (hinj : ∀ w, varNameToC w = varNameToC name → w = name) :
    microCBridge (env.update name v) (mcEnv.update (varNameToC name) v) := by
  intro w
  unfold microCBridge at hb
  simp only [LowLevelEnv.update, MicroCEnv.update]
  by_cases hw : w = name
  · subst hw; simp
  · have hne : varNameToC w ≠ varNameToC name := fun h => hw (hinj w h)
    simp [hw, hne, hb w]

/-! ## Operator Bridge Lemmas -/

/-- Core lemma: operator evaluation is preserved across the translation.
    evalMicroCBinOp (binOpToMicroC op) = evalBinOp op -/
@[simp] theorem evalMicroCBinOp_eq_evalBinOp (op : BinOp) (v1 v2 : Value) :
    evalMicroCBinOp (binOpToMicroC op) v1 v2 = evalBinOp op v1 v2 := by
  simp [evalMicroCBinOp]

/-- Core lemma: unary operator evaluation is preserved across the translation. -/
@[simp] theorem evalMicroCUnaryOp_eq_evalUnaryOp (op : UnaryOp) (v : Value) :
    evalMicroCUnaryOp (unaryOpToMicroC op) v = evalUnaryOp op v := by
  simp [evalMicroCUnaryOp]

/-! ## Expression Bridge -/

/-- Expression bridge: evaluating a Core expression in env equals
    evaluating the translated MicroC expression in the bridged mcEnv.

    This is the key semantic preservation theorem for expressions.
    No fuel needed — both evalExpr and evalMicroCExpr are structural. -/
theorem exprToMicroC_bridge (env : LowLevelEnv) (mcEnv : MicroCEnv)
    (e : LowLevelExpr) (hb : microCBridge env mcEnv) :
    evalExpr env e = evalMicroCExpr mcEnv (exprToMicroC e) := by
  induction e with
  | litInt n => rfl
  | litBool b => rfl
  | varRef v =>
    simp only [evalExpr_varRef, exprToMicroC_varRef, evalMicroCExpr_varRef]
    exact congrArg some (hb v)
  | binOp op e1 e2 ih1 ih2 =>
    simp only [evalExpr_binOp, exprToMicroC_binOp, evalMicroCExpr_binOp]
    rw [ih1, ih2]
    generalize evalMicroCExpr mcEnv (exprToMicroC e1) = r1
    generalize evalMicroCExpr mcEnv (exprToMicroC e2) = r2
    cases r1 with
    | none => rfl
    | some v1 =>
      cases r2 with
      | none => rfl
      | some v2 => exact (evalMicroCBinOp_eq_evalBinOp op v1 v2).symm
  | unaryOp op e ih =>
    simp only [evalExpr_unaryOp, exprToMicroC_unaryOp, evalMicroCExpr_unaryOp]
    rw [ih]
    generalize evalMicroCExpr mcEnv (exprToMicroC e) = r
    cases r with
    | none => rfl
    | some v => exact (evalMicroCUnaryOp_eq_evalUnaryOp op v).symm
  | powCall base n ih =>
    simp only [evalExpr_powCall, exprToMicroC_powCall, evalMicroCExpr_powCall]
    rw [ih]
    generalize evalMicroCExpr mcEnv (exprToMicroC base) = r
    cases r with
    | none => rfl
    | some v => cases v with
      | int _ => rfl
      | bool _ => rfl

/-! ## Array Name Bridge -/

/-- Specialized: for user variable array bases (the common case),
    the MicroC array name is sanitizeIdentifier of the Core name. -/
theorem getArrayName_user_bridge (name : String) :
    getMicroCArrayName (exprToMicroC (.varRef (.user name))) =
      some (sanitizeIdentifier name) := by
  simp [exprToMicroC, getMicroCArrayName, varNameToC]

/-- getArrayName correspondence: if Core's getArrayName extracts a name
    from base, then getMicroCArrayName extracts a corresponding name
    from the translated expression. -/
theorem getArrayName_bridge (base : LowLevelExpr)
    (name : String) (h : getArrayName base = some name) :
    ∃ mcName, getMicroCArrayName (exprToMicroC base) = some mcName := by
  cases base with
  | varRef v =>
    cases v with
    | user s => exact ⟨_, getArrayName_user_bridge s⟩
    | array s idx =>
      simp only [exprToMicroC, getMicroCArrayName, varNameToC, varNameToStr]
      exact ⟨_, rfl⟩
    | temp _ => simp [getArrayName] at h
  | _ => simp [getArrayName] at h

end TrustLean
