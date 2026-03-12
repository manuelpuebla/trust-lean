/-
  Trust-Lean — Verified Code Generation Framework
  MicroC/Int64Eval.lean: Int64 Evaluator with Wrapping Semantics (v3.0.0)

  N14.2: Int64 evaluator that wraps arithmetic operations through wrapInt64.
  Mirrors evalMicroC/evalMicroCExpr structure, replacing arithmetic with
  Int64 wrapping variants. Fuel monotonicity follows same proof strategy.

  Key definitions:
  - evalMicroCBinOp_int64: wraps arithmetic results via addInt64/subInt64/mulInt64
  - evalMicroCUnaryOp_int64: wraps negation via negInt64
  - evalMicroCExpr_int64: expression evaluator with int64 wrapping at operations
  - evalMicroC_int64: statement evaluator using int64 expressions

  Key theorems:
  - evalMicroC_int64_fuel_mono_full: if eval succeeds with oc ≠ outOfFuel at fuel f,
    succeeds with same result at any fuel f' ≥ f
  - evalMicroC_int64_fuel_mono: specialized to normal outcomes
-/

import TrustLean.MicroC.Eval
import TrustLean.MicroC.Int64

set_option autoImplicit false

namespace TrustLean

/-! ## Int64 Operator Evaluation -/

/-- Evaluate a MicroC binary operator with Int64 wrapping.
    Arithmetic results (add, sub, mul) are wrapped via addInt64/subInt64/mulInt64.
    Comparison and logical operations return Bool, unchanged from unbounded. -/
def evalMicroCBinOp_int64 (op : MicroCBinOp) (v1 v2 : Value) : Option Value :=
  match op, v1, v2 with
  | .add, .int a, .int b => some (.int (addInt64 a b))
  | .sub, .int a, .int b => some (.int (subInt64 a b))
  | .mul, .int a, .int b => some (.int (mulInt64 a b))
  | .eqOp, .int a, .int b => some (.bool (a == b))
  | .ltOp, .int a, .int b => some (.bool (decide (a < b)))
  | .land, .bool a, .bool b => some (.bool (a && b))
  | .lor, .bool a, .bool b => some (.bool (a || b))
  | _, _, _ => none

/-- Evaluate a MicroC unary operator with Int64 wrapping.
    Negation is wrapped via negInt64. Logical not unchanged. -/
def evalMicroCUnaryOp_int64 (op : MicroCUnaryOp) (v : Value) : Option Value :=
  match op, v with
  | .neg, .int n => some (.int (negInt64 n))
  | .lnot, .bool b => some (.bool (!b))
  | _, _ => none

/-! ## Int64 Operator @[simp] Lemmas -/

@[simp] theorem evalMicroCBinOp_int64_add (a b : Int) :
    evalMicroCBinOp_int64 .add (.int a) (.int b) = some (.int (addInt64 a b)) := rfl
@[simp] theorem evalMicroCBinOp_int64_sub (a b : Int) :
    evalMicroCBinOp_int64 .sub (.int a) (.int b) = some (.int (subInt64 a b)) := rfl
@[simp] theorem evalMicroCBinOp_int64_mul (a b : Int) :
    evalMicroCBinOp_int64 .mul (.int a) (.int b) = some (.int (mulInt64 a b)) := rfl
@[simp] theorem evalMicroCBinOp_int64_eqOp (a b : Int) :
    evalMicroCBinOp_int64 .eqOp (.int a) (.int b) = some (.bool (a == b)) := rfl
@[simp] theorem evalMicroCBinOp_int64_ltOp (a b : Int) :
    evalMicroCBinOp_int64 .ltOp (.int a) (.int b) = some (.bool (decide (a < b))) := rfl
@[simp] theorem evalMicroCBinOp_int64_land (a b : Bool) :
    evalMicroCBinOp_int64 .land (.bool a) (.bool b) = some (.bool (a && b)) := rfl
@[simp] theorem evalMicroCBinOp_int64_lor (a b : Bool) :
    evalMicroCBinOp_int64 .lor (.bool a) (.bool b) = some (.bool (a || b)) := rfl

@[simp] theorem evalMicroCUnaryOp_int64_neg (n : Int) :
    evalMicroCUnaryOp_int64 .neg (.int n) = some (.int (negInt64 n)) := rfl
@[simp] theorem evalMicroCUnaryOp_int64_lnot (b : Bool) :
    evalMicroCUnaryOp_int64 .lnot (.bool b) = some (.bool (!b)) := rfl

/-! ## Int64 Expression Evaluator -/

/-- Evaluate a MicroC expression with Int64 wrapping at arithmetic operations.
    Literals and variable references are NOT wrapped (assumed in range for
    well-formed programs). Wrapping occurs at: binOp (add/sub/mul),
    unaryOp (neg), powCall. -/
def evalMicroCExpr_int64 (env : MicroCEnv) : MicroCExpr → Option Value
  | .litInt n => some (.int n)
  | .litBool b => some (.bool b)
  | .varRef name => some (env name)
  | .binOp op e1 e2 =>
    match evalMicroCExpr_int64 env e1, evalMicroCExpr_int64 env e2 with
    | some v1, some v2 => evalMicroCBinOp_int64 op v1 v2
    | _, _ => none
  | .unaryOp op e =>
    match evalMicroCExpr_int64 env e with
    | some v => evalMicroCUnaryOp_int64 op v
    | none => none
  | .powCall base n =>
    match evalMicroCExpr_int64 env base with
    | some (.int i) => some (.int (wrapInt64 (i ^ n)))
    | _ => none
  | .arrayAccess base idx =>
    match getMicroCArrayName base, evalMicroCExpr_int64 env idx with
    | some name, some (.int i) => some (env (name ++ "[" ++ toString i ++ "]"))
    | _, _ => none

/-! ## evalMicroCExpr_int64 @[simp] Equation Lemmas -/

@[simp] theorem evalMicroCExpr_int64_litInt (env : MicroCEnv) (n : Int) :
    evalMicroCExpr_int64 env (.litInt n) = some (.int n) := rfl

@[simp] theorem evalMicroCExpr_int64_litBool (env : MicroCEnv) (b : Bool) :
    evalMicroCExpr_int64 env (.litBool b) = some (.bool b) := rfl

@[simp] theorem evalMicroCExpr_int64_varRef (env : MicroCEnv) (name : String) :
    evalMicroCExpr_int64 env (.varRef name) = some (env name) := rfl

@[simp] theorem evalMicroCExpr_int64_binOp (env : MicroCEnv) (op : MicroCBinOp)
    (e1 e2 : MicroCExpr) :
    evalMicroCExpr_int64 env (.binOp op e1 e2) =
      match evalMicroCExpr_int64 env e1, evalMicroCExpr_int64 env e2 with
      | some v1, some v2 => evalMicroCBinOp_int64 op v1 v2
      | _, _ => none := rfl

@[simp] theorem evalMicroCExpr_int64_unaryOp (env : MicroCEnv) (op : MicroCUnaryOp)
    (e : MicroCExpr) :
    evalMicroCExpr_int64 env (.unaryOp op e) =
      match evalMicroCExpr_int64 env e with
      | some v => evalMicroCUnaryOp_int64 op v
      | none => none := rfl

@[simp] theorem evalMicroCExpr_int64_powCall (env : MicroCEnv) (base : MicroCExpr) (n : Nat) :
    evalMicroCExpr_int64 env (.powCall base n) =
      match evalMicroCExpr_int64 env base with
      | some (.int i) => some (.int (wrapInt64 (i ^ n)))
      | _ => none := rfl

/-! ## Int64 Statement Evaluator -/

/-- Evaluate a MicroC statement with Int64 wrapping semantics.
    Identical control flow to evalMicroC, but uses evalMicroCExpr_int64
    for expression evaluation.
    Termination: lexicographic on (fuel, sizeOf stmt). -/
def evalMicroC_int64 (fuel : Nat) (env : MicroCEnv) (stmt : MicroCStmt) :
    Option (Outcome × MicroCEnv) :=
  match stmt with
  | .skip => some (.normal, env)
  | .break_ => some (.break_, env)
  | .continue_ => some (.continue_, env)
  | .return_ re =>
    match re with
    | some e =>
      match evalMicroCExpr_int64 env e with
      | some v => some (.return_ (some v), env)
      | none => none
    | none => some (.return_ none, env)
  | .assign name expr =>
    match evalMicroCExpr_int64 env expr with
    | some v => some (.normal, env.update name v)
    | none => none
  | .store base idx val =>
    match getMicroCArrayName base, evalMicroCExpr_int64 env idx, evalMicroCExpr_int64 env val with
    | some name, some (.int i), some v =>
      some (.normal, env.update (name ++ "[" ++ toString i ++ "]") v)
    | _, _, _ => none
  | .load var base idx =>
    match getMicroCArrayName base, evalMicroCExpr_int64 env idx with
    | some name, some (.int i) =>
      some (.normal, env.update var (env (name ++ "[" ++ toString i ++ "]")))
    | _, _ => none
  | .call _ _ _ => none
  | .seq s1 s2 =>
    match evalMicroC_int64 fuel env s1 with
    | some (.normal, env') => evalMicroC_int64 fuel env' s2
    | other => other
  | .ite cond thenB elseB =>
    match evalMicroCExpr_int64 env cond with
    | some (.bool true) => evalMicroC_int64 fuel env thenB
    | some (.bool false) => evalMicroC_int64 fuel env elseB
    | _ => none
  | .while_ cond body =>
    match fuel with
    | 0 => some (.outOfFuel, env)
    | fuel' + 1 =>
      match evalMicroCExpr_int64 env cond with
      | some (.bool false) => some (.normal, env)
      | some (.bool true) =>
        match evalMicroC_int64 fuel' env body with
        | some (.normal, env') => evalMicroC_int64 fuel' env' (.while_ cond body)
        | some (.continue_, env') => evalMicroC_int64 fuel' env' (.while_ cond body)
        | some (.break_, env') => some (.normal, env')
        | some (.return_ rv, env') => some (.return_ rv, env')
        | some (.outOfFuel, env') => some (.outOfFuel, env')
        | none => none
      | _ => none
termination_by (fuel, sizeOf stmt)

/-! ## evalMicroC_int64 @[simp] Equation Lemmas -/

@[simp] theorem evalMicroC_int64_skip (fuel : Nat) (env : MicroCEnv) :
    evalMicroC_int64 fuel env .skip = some (.normal, env) := by
  simp [evalMicroC_int64]

@[simp] theorem evalMicroC_int64_break (fuel : Nat) (env : MicroCEnv) :
    evalMicroC_int64 fuel env .break_ = some (.break_, env) := by
  simp [evalMicroC_int64]

@[simp] theorem evalMicroC_int64_continue (fuel : Nat) (env : MicroCEnv) :
    evalMicroC_int64 fuel env .continue_ = some (.continue_, env) := by
  simp [evalMicroC_int64]

@[simp] theorem evalMicroC_int64_return_none (fuel : Nat) (env : MicroCEnv) :
    evalMicroC_int64 fuel env (.return_ none) = some (.return_ none, env) := by
  simp [evalMicroC_int64]

@[simp] theorem evalMicroC_int64_return_some (fuel : Nat) (env : MicroCEnv) (e : MicroCExpr) :
    evalMicroC_int64 fuel env (.return_ (some e)) =
      match evalMicroCExpr_int64 env e with
      | some v => some (.return_ (some v), env)
      | none => none := by
  simp [evalMicroC_int64]

@[simp] theorem evalMicroC_int64_assign (fuel : Nat) (env : MicroCEnv)
    (name : String) (expr : MicroCExpr) :
    evalMicroC_int64 fuel env (.assign name expr) =
      match evalMicroCExpr_int64 env expr with
      | some v => some (.normal, env.update name v)
      | none => none := by
  simp [evalMicroC_int64]

@[simp] theorem evalMicroC_int64_seq (fuel : Nat) (env : MicroCEnv)
    (s1 s2 : MicroCStmt) :
    evalMicroC_int64 fuel env (.seq s1 s2) =
      match evalMicroC_int64 fuel env s1 with
      | some (.normal, env') => evalMicroC_int64 fuel env' s2
      | other => other := by
  simp [evalMicroC_int64]

@[simp] theorem evalMicroC_int64_ite (fuel : Nat) (env : MicroCEnv)
    (cond : MicroCExpr) (thenB elseB : MicroCStmt) :
    evalMicroC_int64 fuel env (.ite cond thenB elseB) =
      match evalMicroCExpr_int64 env cond with
      | some (.bool true) => evalMicroC_int64 fuel env thenB
      | some (.bool false) => evalMicroC_int64 fuel env elseB
      | _ => none := by
  simp [evalMicroC_int64]

@[simp] theorem evalMicroC_int64_while_zero (env : MicroCEnv)
    (cond : MicroCExpr) (body : MicroCStmt) :
    evalMicroC_int64 0 env (.while_ cond body) = some (.outOfFuel, env) := by
  simp [evalMicroC_int64]

@[simp] theorem evalMicroC_int64_while_succ (fuel : Nat) (env : MicroCEnv)
    (cond : MicroCExpr) (body : MicroCStmt) :
    evalMicroC_int64 (fuel + 1) env (.while_ cond body) =
      match evalMicroCExpr_int64 env cond with
      | some (.bool false) => some (.normal, env)
      | some (.bool true) =>
        match evalMicroC_int64 fuel env body with
        | some (.normal, env') => evalMicroC_int64 fuel env' (.while_ cond body)
        | some (.continue_, env') => evalMicroC_int64 fuel env' (.while_ cond body)
        | some (.break_, env') => some (.normal, env')
        | some (.return_ rv, env') => some (.return_ rv, env')
        | some (.outOfFuel, env') => some (.outOfFuel, env')
        | none => none
      | _ => none := by
  simp [evalMicroC_int64]

/-! ## Fuel Monotonicity -/

/-- Build fuel monotonicity for (seq s1 s2) given IHs for s1 and s2. -/
private theorem fuel_mono_seq_int64
    {s1 s2 : MicroCStmt}
    (ih1 : ∀ {fuel fuel' : Nat} {env env' : MicroCEnv} {oc : Outcome},
      evalMicroC_int64 fuel env s1 = some (oc, env') → fuel ≤ fuel' → oc ≠ .outOfFuel →
      evalMicroC_int64 fuel' env s1 = some (oc, env'))
    (ih2 : ∀ {fuel fuel' : Nat} {env env' : MicroCEnv} {oc : Outcome},
      evalMicroC_int64 fuel env s2 = some (oc, env') → fuel ≤ fuel' → oc ≠ .outOfFuel →
      evalMicroC_int64 fuel' env s2 = some (oc, env'))
    {fuel fuel' : Nat} {env env' : MicroCEnv} {oc : Outcome}
    (h : evalMicroC_int64 fuel env (.seq s1 s2) = some (oc, env'))
    (hle : fuel ≤ fuel')
    (hoc : oc ≠ .outOfFuel) :
    evalMicroC_int64 fuel' env (.seq s1 s2) = some (oc, env') := by
  simp only [evalMicroC_int64_seq] at h ⊢
  generalize hm : evalMicroC_int64 fuel env s1 = r at h
  cases r with
  | none => simp at h
  | some p =>
    cases p with
    | mk o e_mid =>
      cases o with
      | normal => simp only [ih1 hm hle (by simp)]; exact ih2 h hle hoc
      | break_ => simp only [ih1 hm hle (by simp)]; exact h
      | continue_ => simp only [ih1 hm hle (by simp)]; exact h
      | return_ rv => simp only [ih1 hm hle (by simp)]; exact h
      | outOfFuel =>
        simp only [] at h
        have : oc = .outOfFuel := by
          have := Option.some.inj h; exact (congrArg Prod.fst this).symm
        exact absurd this hoc

/-- Fuel monotonicity for MicroC int64 while loops, with nested induction on fuel. -/
private theorem fuel_mono_while_int64
    (cond : MicroCExpr) (body : MicroCStmt)
    (ih_body : ∀ {fuel fuel' : Nat} {env env' : MicroCEnv} {oc : Outcome},
      evalMicroC_int64 fuel env body = some (oc, env') → fuel ≤ fuel' → oc ≠ .outOfFuel →
      evalMicroC_int64 fuel' env body = some (oc, env'))
    {fuel : Nat} :
    ∀ {fuel' : Nat} {env env' : MicroCEnv} {oc : Outcome},
    evalMicroC_int64 fuel env (.while_ cond body) = some (oc, env') →
    fuel ≤ fuel' →
    oc ≠ .outOfFuel →
    evalMicroC_int64 fuel' env (.while_ cond body) = some (oc, env') := by
  induction fuel with
  | zero =>
    intro fuel' env env' oc h _ hoc
    simp only [evalMicroC_int64_while_zero] at h
    have : oc = .outOfFuel := by
      have := Option.some.inj h; exact (congrArg Prod.fst this).symm
    exact absurd this hoc
  | succ n ih_fuel =>
    intro fuel' env env' oc h hle hoc
    obtain ⟨m, rfl⟩ : ∃ m, fuel' = m + 1 := ⟨fuel' - 1, by omega⟩
    have hnm : n ≤ m := by omega
    simp only [evalMicroC_int64_while_succ] at h ⊢
    generalize hc : evalMicroCExpr_int64 env cond = c at h ⊢
    cases c with
    | none => simp at h
    | some v =>
      cases v with
      | int _ => simp at h
      | bool b =>
        cases b with
        | false => exact h
        | true =>
          generalize hb : evalMicroC_int64 n env body = rb at h
          cases rb with
          | none => simp at h
          | some p =>
            cases p with
            | mk ob e_mid =>
              cases ob with
              | normal =>
                simp only [ih_body hb hnm (by simp)]; exact ih_fuel h hnm hoc
              | continue_ =>
                simp only [ih_body hb hnm (by simp)]; exact ih_fuel h hnm hoc
              | break_ =>
                simp only [ih_body hb hnm (by simp)]; exact h
              | return_ rv =>
                simp only [ih_body hb hnm (by simp)]; exact h
              | outOfFuel =>
                simp only [] at h
                have : oc = .outOfFuel := by
                  have := Option.some.inj h; exact (congrArg Prod.fst this).symm
                exact absurd this hoc

/-- Fuel monotonicity for all MicroC int64 statements, generalized to all outcomes. -/
private theorem evalMicroC_int64_fuel_mono_gen (stmt : MicroCStmt) :
    ∀ {fuel fuel' : Nat} {env env' : MicroCEnv} {oc : Outcome},
    evalMicroC_int64 fuel env stmt = some (oc, env') →
    fuel ≤ fuel' →
    oc ≠ .outOfFuel →
    evalMicroC_int64 fuel' env stmt = some (oc, env') := by
  induction stmt with
  | skip => intro _ _ _ _ _ h _ _; simp_all
  | break_ => intro _ _ _ _ _ h _ _; simp_all
  | continue_ => intro _ _ _ _ _ h _ _; simp_all
  | return_ re =>
    intro fuel fuel' env env' oc h _ _
    cases re with
    | none => simp at h ⊢; exact h
    | some e => simp only [evalMicroC_int64_return_some] at h ⊢; exact h
  | assign name expr =>
    intro fuel fuel' env env' oc h _ _
    simp only [evalMicroC_int64_assign] at h ⊢; exact h
  | store base idx val =>
    intro fuel fuel' env env' oc h _ _
    simp [evalMicroC_int64] at h ⊢; exact h
  | load var base idx =>
    intro fuel fuel' env env' oc h _ _
    simp [evalMicroC_int64] at h ⊢; exact h
  | call f r args =>
    intro fuel fuel' env env' oc h _ _
    simp [evalMicroC_int64] at h
  | ite cond thenB elseB ih_then ih_else =>
    intro fuel fuel' env env' oc h hle hoc
    simp only [evalMicroC_int64_ite] at h ⊢
    generalize hc : evalMicroCExpr_int64 env cond = c at h ⊢
    cases c with
    | none => simp at h
    | some v =>
      cases v with
      | int _ => simp at h
      | bool b =>
        cases b with
        | true => exact ih_then h hle hoc
        | false => exact ih_else h hle hoc
  | seq s1 s2 ih1 ih2 => exact fuel_mono_seq_int64 ih1 ih2
  | while_ cond body ih_body => exact fuel_mono_while_int64 cond body ih_body

/-! ## Public API -/

/-- Fuel monotonicity: if evalMicroC_int64 succeeds with outcome `oc ≠ outOfFuel` at fuel f,
    it produces the same result at any fuel f' ≥ f.
    GATE theorem for Int64 MicroC — mirrors evalMicroC_fuel_mono_full. -/
theorem evalMicroC_int64_fuel_mono_full {fuel fuel' : Nat} {env : MicroCEnv} {stmt : MicroCStmt}
    {env' : MicroCEnv} {oc : Outcome}
    (h : evalMicroC_int64 fuel env stmt = some (oc, env'))
    (hle : fuel ≤ fuel')
    (hoc : oc ≠ .outOfFuel) :
    evalMicroC_int64 fuel' env stmt = some (oc, env') :=
  evalMicroC_int64_fuel_mono_gen stmt h hle hoc

/-- Fuel monotonicity specialized to normal outcomes.
    Most commonly used form in simulation proofs. -/
theorem evalMicroC_int64_fuel_mono {fuel fuel' : Nat} {env : MicroCEnv} {stmt : MicroCStmt}
    {env' : MicroCEnv}
    (h : evalMicroC_int64 fuel env stmt = some (.normal, env'))
    (hle : fuel ≤ fuel') :
    evalMicroC_int64 fuel' env stmt = some (.normal, env') :=
  evalMicroC_int64_fuel_mono_full h hle (by simp)

/-! ## Basic Properties -/

/-- evalMicroC_int64 on skip produces same result as evalMicroC. -/
theorem evalMicroC_int64_skip_eq (fuel : Nat) (env : MicroCEnv) :
    evalMicroC_int64 fuel env .skip = evalMicroC fuel env .skip := by simp

/-- evalMicroC_int64 is deterministic. -/
theorem evalMicroC_int64_deterministic (fuel : Nat) (env : MicroCEnv) (s : MicroCStmt)
    (r1 r2 : Outcome × MicroCEnv)
    (h1 : evalMicroC_int64 fuel env s = some r1)
    (h2 : evalMicroC_int64 fuel env s = some r2) : r1 = r2 := by
  rw [h1] at h2; exact Option.some.inj h2

/-! ## Smoke Tests -/

-- Simple assignment: no overflow → x = 42
#eval do
  let (oc, env) ← evalMicroC_int64 10 MicroCEnv.default (.assign "x" (.litInt 42))
  return (oc, env "x")

-- Overflow: maxInt64 + 1 wraps to minInt64
#eval do
  let env₀ : MicroCEnv := fun s => if s == "x" then Value.int maxInt64 else Value.int 0
  let (oc, env) ← evalMicroC_int64 10 env₀ (.assign "y" (.binOp .add (.varRef "x") (.litInt 1)))
  return (oc, env "y")

-- No overflow: 3 + 4 = 7
#eval do
  let (oc, env) ← evalMicroC_int64 10 MicroCEnv.default
    (.assign "x" (.binOp .add (.litInt 3) (.litInt 4)))
  return (oc, env "x")

-- Underflow: minInt64 - 1 wraps to maxInt64
#eval do
  let env₀ : MicroCEnv := fun s => if s == "x" then Value.int minInt64 else Value.int 0
  let (oc, env) ← evalMicroC_int64 10 env₀ (.assign "y" (.binOp .sub (.varRef "x") (.litInt 1)))
  return (oc, env "y")

-- Multiplication overflow: maxInt64 * 2
#eval do
  let env₀ : MicroCEnv := fun s => if s == "x" then Value.int maxInt64 else Value.int 0
  let (oc, env) ← evalMicroC_int64 10 env₀ (.assign "y" (.binOp .mul (.varRef "x") (.litInt 2)))
  return (oc, env "y")

end TrustLean
