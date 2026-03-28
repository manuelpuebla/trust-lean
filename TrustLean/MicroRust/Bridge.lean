/-
  Trust-Lean — Verified Code Generation Framework
  MicroRust/Bridge.lean: Bridge predicate linking LowLevelEnv and MicroRustEnv

  N24.2 (v4.0.0): FUND — defines the microRustBridge predicate and proves
  key properties. Structural clone of MicroC/Bridge.lean with varNameToRust
  replacing varNameToC. Shared AST + evaluators imported from MicroC.
-/

import TrustLean.MicroRust.Translation
import TrustLean.MicroC.Eval
import TrustLean.Core.Eval

set_option autoImplicit false

namespace TrustLean

/-! ## Bridge Predicate -/

/-- The bridge predicate: links a Core IR environment (VarName → Value)
    to a MicroRust environment (String → Value) via varNameToRust.
    For every variable v, both environments agree on its value. -/
def microRustBridge (env : LowLevelEnv) (mcEnv : MicroRustEnv) : Prop :=
  ∀ v : VarName, env v = mcEnv (varNameToRust v)

/-! ## Bridge Preservation -/

/-- Bridge holds for default environments. -/
theorem microRustBridge_default :
    microRustBridge LowLevelEnv.default MicroCEnv.default := by
  intro v; rfl

/-- Bridge is preserved by updating the same variable (requires local injectivity). -/
theorem microRustBridge_update {env : LowLevelEnv} {mcEnv : MicroRustEnv}
    (hb : microRustBridge env mcEnv) (name : VarName) (v : Value)
    (hinj : ∀ w, varNameToRust w = varNameToRust name → w = name) :
    microRustBridge (env.update name v) (mcEnv.update (varNameToRust name) v) := by
  intro w
  unfold microRustBridge at hb
  simp only [LowLevelEnv.update, MicroCEnv.update]
  by_cases hw : w = name
  · subst hw; simp
  · have hne : varNameToRust w ≠ varNameToRust name := fun h => hw (hinj w h)
    simp [hw, hne, hb w]

/-! ## Operator Bridge Lemmas -/

/-- Core lemma: operator evaluation is preserved across the Rust translation.
    binOpToMicroRust = binOpToMicroC, so this is exactly evalMicroCBinOp_eq_evalBinOp. -/
@[simp] theorem evalMicroRustBinOp_eq_evalBinOp (op : BinOp) (v1 v2 : Value) :
    evalMicroCBinOp (binOpToMicroRust op) v1 v2 = evalBinOp op v1 v2 := by
  simp [evalMicroCBinOp]

/-- Core lemma: unary operator evaluation is preserved across the Rust translation. -/
@[simp] theorem evalMicroRustUnaryOp_eq_evalUnaryOp (op : UnaryOp) (v : Value) :
    evalMicroCUnaryOp (unaryOpToMicroRust op) v = evalUnaryOp op v := by
  simp [evalMicroCUnaryOp]

/-! ## Expression Bridge -/

/-- Expression bridge: evaluating a Core expression in env equals
    evaluating the translated MicroRust expression in the bridged mcEnv.

    Key semantic preservation theorem for expressions.
    No fuel needed — both evalExpr and evalMicroCExpr are structural. -/
theorem exprToMicroRust_bridge (env : LowLevelEnv) (mcEnv : MicroRustEnv)
    (e : LowLevelExpr) (hb : microRustBridge env mcEnv) :
    evalExpr env e = evalMicroCExpr mcEnv (exprToMicroRust e) := by
  induction e with
  | litInt n => rfl
  | litBool b => rfl
  | varRef v =>
    simp only [evalExpr_varRef, exprToMicroRust_varRef, evalMicroCExpr_varRef]
    exact congrArg some (hb v)
  | binOp op e1 e2 ih1 ih2 =>
    simp only [evalExpr_binOp, exprToMicroRust_binOp, evalMicroCExpr_binOp]
    rw [ih1, ih2]
    generalize evalMicroCExpr mcEnv (exprToMicroRust e1) = r1
    generalize evalMicroCExpr mcEnv (exprToMicroRust e2) = r2
    cases r1 with
    | none => rfl
    | some v1 =>
      cases r2 with
      | none => rfl
      | some v2 => exact (evalMicroRustBinOp_eq_evalBinOp op v1 v2).symm
  | unaryOp op e ih =>
    simp only [evalExpr_unaryOp, exprToMicroRust_unaryOp, evalMicroCExpr_unaryOp]
    rw [ih]
    generalize evalMicroCExpr mcEnv (exprToMicroRust e) = r
    cases r with
    | none => rfl
    | some v => exact (evalMicroRustUnaryOp_eq_evalUnaryOp op v).symm
  | powCall base n ih =>
    simp only [evalExpr_powCall, exprToMicroRust_powCall, evalMicroCExpr_powCall]
    rw [ih]
    generalize evalMicroCExpr mcEnv (exprToMicroRust base) = r
    cases r with
    | none => rfl
    | some v => cases v with
      | int _ => rfl
      | bool _ => rfl

/-! ## Array Name Bridge -/

/-- Specialized: for user variable array bases,
    the MicroRust array name is sanitizeIdentifierRust of the Core name. -/
theorem getArrayName_user_bridge_rust (name : String) :
    getMicroCArrayName (exprToMicroRust (.varRef (.user name))) =
      some (sanitizeIdentifierRust name) := by
  simp [exprToMicroRust, getMicroCArrayName, varNameToRust]

/-- getArrayName correspondence for MicroRust. -/
theorem getArrayName_bridge_rust (base : LowLevelExpr)
    (name : String) (h : getArrayName base = some name) :
    ∃ mcName, getMicroCArrayName (exprToMicroRust base) = some mcName := by
  cases base with
  | varRef v =>
    cases v with
    | user s => exact ⟨_, getArrayName_user_bridge_rust s⟩
    | array s idx =>
      simp only [exprToMicroRust, getMicroCArrayName, varNameToRust, varNameToStr]
      exact ⟨_, rfl⟩
    | temp _ => simp [getArrayName] at h
  | _ => simp [getArrayName] at h

end TrustLean
