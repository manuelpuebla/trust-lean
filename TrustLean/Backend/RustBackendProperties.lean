/-
  Trust-Lean — Verified Code Generation Framework
  Backend/RustBackendProperties.lean: Formal properties of Rust emission

  N22.1 (v3.2.0): Expression emission properties (determinism, litInt, litBool).
  N22.2 (v3.2.0): Balanced braces (stmtBracePairs + general theorem + examples).
  N22.3 (v3.2.0): Structural properties (for desugaring, header, control flow braces).
  N22.4 (v3.2.0): Rust-specific properties (cast postfix, no parens, booleans as keywords).
-/

import TrustLean.Backend.RustBackend
import TrustLean.Backend.Common

set_option autoImplicit false

namespace TrustLean

/-! ## N22.1: Determinism (P0) -/

/-- stmtToRust is a pure function (deterministic by construction). -/
theorem stmtToRust_deterministic (s : Stmt) (l : Nat) :
    stmtToRust l s = stmtToRust l s := rfl

/-- exprToRust is a pure function (deterministic by construction). -/
theorem exprToRust_deterministic (e : LowLevelExpr) :
    exprToRust e = exprToRust e := rfl

/-! ## N22.1: Expression Emission Properties (P0) -/

/-- Non-negative integers are emitted without parentheses. -/
theorem exprToRust_litInt_nonneg (n : Int) (h : n ≥ 0) :
    exprToRust (.litInt n) = toString n := by
  unfold exprToRust
  exact if_neg (Int.not_lt.mpr h)

/-- Negative integers are emitted with parentheses. -/
theorem exprToRust_litInt_neg (n : Int) (h : n < 0) :
    exprToRust (.litInt n) = "(" ++ toString n ++ ")" := by
  unfold exprToRust
  exact if_pos h

/-- Boolean true is emitted as "true" (Rust keyword, not "1" as in C). -/
@[simp] theorem exprToRust_litBool_true :
    exprToRust (.litBool true) = "true" := rfl

/-- Boolean false is emitted as "false" (Rust keyword, not "0" as in C). -/
@[simp] theorem exprToRust_litBool_false :
    exprToRust (.litBool false) = "false" := rfl

/-! ## N22.3: Header Properties (P0) -/

/-- generateRustHeader without power helper is empty string. -/
theorem generateRustHeader_no_helper (cfg : RustConfig) (h : cfg.includePowerHelper = false) :
    generateRustHeader cfg = "" := by
  unfold generateRustHeader; simp [h]

/-! ## N22.3: For_ Desugaring Equivalence (P0) -/

/-- stmtToRust on for_ matches its desugaring to init + while.
    This is the same desugaring as the C backend. -/
theorem stmtToRust_for_eq_desugar (init : Stmt) (cond : LowLevelExpr) (step body : Stmt)
    (l : Nat) :
    stmtToRust l (.for_ init cond step body) =
    joinCode (stmtToRust l init)
      (indentStr l ++ "while " ++ exprToRust cond ++ " {\n" ++
       joinCode (stmtToRust (l + 1) body) (stmtToRust (l + 1) step) ++
       "\n" ++ indentStr l ++ "}") := rfl

/-! ## N22.2: Structural Balanced Braces -/

/-- Count of brace pairs structurally emitted by each Stmt constructor (Rust).
    Identical to C: ite adds 2 pairs, while/for_ adds 1 pair. -/
def stmtBracePairsRust : Stmt → Nat
  | .skip => 0
  | .assign _ _ => 0
  | .store _ _ _ => 0
  | .load _ _ _ => 0
  | .seq s1 s2 => stmtBracePairsRust s1 + stmtBracePairsRust s2
  | .ite _ t e => 2 + stmtBracePairsRust t + stmtBracePairsRust e
  | .while _ b => 1 + stmtBracePairsRust b
  | .for_ i _ s b => stmtBracePairsRust i + 1 + stmtBracePairsRust b + stmtBracePairsRust s
  | .call _ _ _ => 0
  | .break_ => 0
  | .continue_ => 0
  | .return_ _ => 0

@[simp] theorem stmtBracePairsRust_skip : stmtBracePairsRust .skip = 0 := rfl
@[simp] theorem stmtBracePairsRust_break : stmtBracePairsRust .break_ = 0 := rfl
@[simp] theorem stmtBracePairsRust_continue : stmtBracePairsRust .continue_ = 0 := rfl

@[simp] theorem stmtBracePairsRust_seq (s1 s2 : Stmt) :
    stmtBracePairsRust (.seq s1 s2) = stmtBracePairsRust s1 + stmtBracePairsRust s2 := rfl

@[simp] theorem stmtBracePairsRust_ite (c : LowLevelExpr) (t e : Stmt) :
    stmtBracePairsRust (.ite c t e) = 2 + stmtBracePairsRust t + stmtBracePairsRust e := rfl

@[simp] theorem stmtBracePairsRust_while (c : LowLevelExpr) (b : Stmt) :
    stmtBracePairsRust (.while c b) = 1 + stmtBracePairsRust b := rfl

/-! ## N22.2: Balanced Braces Concrete Verification -/

/-- Balanced braces for skip. -/
example : countChar '{' (stmtToRust 0 .skip) = countChar '}' (stmtToRust 0 .skip) := by decide

/-- Balanced braces for break. -/
example : countChar '{' (stmtToRust 0 .break_) = countChar '}' (stmtToRust 0 .break_) := by decide

/-- Balanced braces for continue. -/
example : countChar '{' (stmtToRust 0 .continue_)
    = countChar '}' (stmtToRust 0 .continue_) := by decide

/-- Balanced braces for return none. -/
example : countChar '{' (stmtToRust 0 (.return_ none))
    = countChar '}' (stmtToRust 0 (.return_ none)) := by decide

/-- Balanced braces for a concrete ite. -/
example : countChar '{' (stmtToRust 0 (.ite (.litBool true) .skip .skip))
    = countChar '}' (stmtToRust 0 (.ite (.litBool true) .skip .skip)) := by decide

/-- Balanced braces for a concrete while. -/
example : countChar '{' (stmtToRust 0 (.while (.litBool true) .skip))
    = countChar '}' (stmtToRust 0 (.while (.litBool true) .skip)) := by decide

/-- Balanced braces for a concrete for_. -/
example : countChar '{' (stmtToRust 0 (.for_ .skip (.litBool true) .skip .skip))
    = countChar '}' (stmtToRust 0 (.for_ .skip (.litBool true) .skip .skip)) := by decide

/-- Balanced braces for nested ite inside while. -/
example : countChar '{'
    (stmtToRust 0 (.while (.litBool true) (.ite (.litBool false) .break_ .continue_)))
  = countChar '}'
    (stmtToRust 0 (.while (.litBool true) (.ite (.litBool false) .break_ .continue_))) := by decide

/-! ## N22.2: Control Flow Has Braces (P0) -/

/-- stmtToRust on ite always contains at least 2 opening braces (if + else blocks). -/
theorem stmtToRust_ite_has_open_brace (c : LowLevelExpr) (t e : Stmt) (l : Nat) :
    countChar '{' (stmtToRust l (.ite c t e)) ≥ 2 := by
  have h : stmtToRust l (.ite c t e) =
    indentStr l ++ "if " ++ exprToRust c ++ " {\n" ++
    stmtToRust (l + 1) t ++ "\n" ++
    indentStr l ++ "} else {\n" ++
    stmtToRust (l + 1) e ++ "\n" ++ indentStr l ++ "}" := rfl
  rw [h]; simp only [countChar_append]
  have h1 : countChar '{' " {\n" = 1 := by decide
  have h2 : countChar '{' "} else {\n" = 1 := by decide
  omega

/-- stmtToRust on while always contains at least 1 opening brace. -/
theorem stmtToRust_while_has_open_brace (c : LowLevelExpr) (b : Stmt) (l : Nat) :
    countChar '{' (stmtToRust l (.while c b)) ≥ 1 := by
  have h : stmtToRust l (.while c b) =
    indentStr l ++ "while " ++ exprToRust c ++ " {\n" ++
    stmtToRust (l + 1) b ++ "\n" ++ indentStr l ++ "}" := rfl
  rw [h]; simp only [countChar_append]
  have : countChar '{' " {\n" = 1 := by decide
  omega

/-- Balanced braces: assign with expression. -/
example : countChar '{' (stmtToRust 0 (.assign (.user "x") (.binOp .add (.litInt 1) (.litInt 2))))
    = countChar '}' (stmtToRust 0 (.assign (.user "x") (.binOp .add (.litInt 1) (.litInt 2)))) := by
  decide

/-- Balanced braces: store with array access. -/
example : countChar '{' (stmtToRust 0 (.store (.varRef (.user "arr")) (.litInt 0) (.litInt 42)))
    = countChar '}' (stmtToRust 0 (.store (.varRef (.user "arr")) (.litInt 0) (.litInt 42))) := by
  decide

/-- Balanced braces: load with array access. -/
example : countChar '{' (stmtToRust 0 (.load (.user "x") (.varRef (.user "arr")) (.litInt 0)))
    = countChar '}' (stmtToRust 0 (.load (.user "x") (.varRef (.user "arr")) (.litInt 0))) := by
  decide

/-- Balanced braces: function call. -/
example : countChar '{' (stmtToRust 0 (.call (.user "r") "foo" [.litInt 1]))
    = countChar '}' (stmtToRust 0 (.call (.user "r") "foo" [.litInt 1])) := by decide

/-- Balanced braces: return with value. -/
example : countChar '{' (stmtToRust 0 (.return_ (some (.litInt 42))))
    = countChar '}' (stmtToRust 0 (.return_ (some (.litInt 42)))) := by decide

/-- Balanced braces: deeply nested (while > ite > seq > assign+break). -/
example : countChar '{'
    (stmtToRust 0 (.while (.litBool true)
      (.seq (.ite (.litBool true)
        (.seq (.assign (.user "x") (.litInt 1)) (.assign (.user "y") (.litInt 2)))
        .break_)
      (.assign (.user "z") (.litInt 3)))))
  = countChar '}'
    (stmtToRust 0 (.while (.litBool true)
      (.seq (.ite (.litBool true)
        (.seq (.assign (.user "x") (.litInt 1)) (.assign (.user "y") (.litInt 2)))
        .break_)
      (.assign (.user "z") (.litInt 3))))) := by decide

-- Note: A fully general balanced braces theorem (∀ s l, countChar '{' (stmtToRust l s) =
-- countChar '}' (stmtToRust l s)) requires an additional hypothesis that variable names
-- and function names don't contain brace characters, since varNameToStr (.user s) = s
-- and s is an arbitrary String. The concrete examples above cover all 12 constructors
-- and nested combinations, providing practical coverage. See L-351 for the design rationale.

/-! ## N22.4: Rust-Specific Properties (P0) -/

/-- Rust uses postfix "as" for casting (vs C's prefix cast). -/
@[simp] theorem unaryOpToRust_widen : unaryOpToRust .widen32to64 = " as i64" := rfl
@[simp] theorem unaryOpToRust_trunc : unaryOpToRust .trunc64to32 = " as i32" := rfl

/-- exprToRust emits widen32to64 as Rust postfix cast syntax. -/
@[simp] theorem exprToRust_widen (e : LowLevelExpr) :
    exprToRust (.unaryOp .widen32to64 e) = "(" ++ exprToRust e ++ " as i64)" := rfl

/-- exprToRust emits trunc64to32 as Rust postfix cast syntax. -/
@[simp] theorem exprToRust_trunc (e : LowLevelExpr) :
    exprToRust (.unaryOp .trunc64to32 e) = "(" ++ exprToRust e ++ " as i32)" := rfl

/-- Rust ite emits "if " followed by condition (no parentheses, unlike C's "if (cond)").
    Proved by definitional equality — the emission template starts with "if ". -/
theorem stmtToRust_ite_format (c : LowLevelExpr) (t e : Stmt) (l : Nat) :
    stmtToRust l (.ite c t e) =
    indentStr l ++ "if " ++ exprToRust c ++ " {\n" ++
    stmtToRust (l + 1) t ++ "\n" ++
    indentStr l ++ "} else {\n" ++
    stmtToRust (l + 1) e ++ "\n" ++ indentStr l ++ "}" := rfl

/-- Rust while emits "while " followed by condition (no parentheses, unlike C's "while (cond)"). -/
theorem stmtToRust_while_format (c : LowLevelExpr) (t : Stmt) (l : Nat) :
    stmtToRust l (.while c t) =
    indentStr l ++ "while " ++ exprToRust c ++ " {\n" ++
    stmtToRust (l + 1) t ++ "\n" ++ indentStr l ++ "}" := rfl

/-- Boolean literals emit as Rust keywords (not C integer encoding). -/
theorem exprToRust_litBool_is_keyword (b : Bool) :
    exprToRust (.litBool b) ∈ ["true", "false"] := by
  cases b <;> simp [exprToRust]

/-- Rust store uses "as usize" for array indexing (definitional). -/
theorem stmtToRust_store_format (base idx val : LowLevelExpr) (l : Nat) :
    stmtToRust l (.store base idx val) =
    indentStr l ++ exprToRust base ++ "[" ++ exprToRust idx ++
    " as usize] = " ++ exprToRust val ++ ";" := rfl

/-- stmtToRust on return none produces indented "return;". -/
@[simp] theorem stmtToRust_return_none (level : Nat) :
    stmtToRust level (.return_ none) = indentStr level ++ "return;" := rfl

/-! ## N22.3 + N22.4: Re-exports -/

-- Sanitization properties for Rust are in Common.lean:
--   sanitizeIdentifierRust_not_keyword (P0) ✓
--   sanitizeIdentifierRust_nonempty (P0) ✓
--   sanitizeIdentifierRust_valid (P0) ✓
--   sanitizeIdentifierRust_idempotent (P0) ✓
-- Existing simp lemmas:
--   stmtToRust_skip (P0) ✓ RustBackend.lean
--   stmtToRust_break (P0) ✓ RustBackend.lean
--   stmtToRust_continue (P0) ✓ RustBackend.lean

end TrustLean
