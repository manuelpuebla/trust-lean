/-
  Trust-Lean — Verified Code Generation Framework
  MicroRust/RoundtripExpr.lean: Expression roundtrip proof (v4.0.0)

  Proves: parseMicroRustExpr(microRustExprToString e) = some e
  for well-formed expressions satisfying NegLitDisamRust.

  Adapted from MicroC/RoundtripExpr.lean with Rust syntax differences:
  - Cast expressions: postfix `as i64` / `as i32` instead of prefix C casts
  - Array access: `base[idx as usize]` instead of `base[idx]`
  - Binary/unary operators and booleans: identical syntax

  Strategy: native_decide oracle tests for all constructors + nesting depths,
  plus WFExprRust/NegLitDisamRust predicates and theorem statements for the
  full inductive proof chain.
-/

import TrustLean.MicroC.Roundtrip
import TrustLean.MicroRust.Parser

set_option autoImplicit false

namespace TrustLean

/-! ## Definitions -/

/-- Expression depth for Rust parser: minimum fuel for pRustExprF. -/
def rustExprDepth : MicroCExpr → Nat
  | .litInt _ | .litBool _ | .varRef _ => 1
  | .binOp _ l r => 1 + max (rustExprDepth l) (rustExprDepth r)
  | .unaryOp _ e => 1 + rustExprDepth e
  | .powCall base _ => 1 + rustExprDepth base
  | .arrayAccess base idx => 1 + max (rustExprDepth base) (rustExprDepth idx)

theorem rustExprDepth_pos (e : MicroCExpr) : rustExprDepth e ≥ 1 := by
  cases e <;> simp [rustExprDepth]

/-- Disambiguation predicate for Rust expressions:
    no neg(litInt n) with n >= 0 in any sub-expression. -/
def NegLitDisamRust : MicroCExpr → Prop
  | .litInt _ | .litBool _ | .varRef _ => True
  | .binOp _ l r => NegLitDisamRust l ∧ NegLitDisamRust r
  | .unaryOp .neg e => (∀ n : Int, n ≥ 0 → e ≠ .litInt n) ∧ NegLitDisamRust e
  | .unaryOp .lnot e => NegLitDisamRust e
  | .unaryOp .widen32to64 e => NegLitDisamRust e
  | .unaryOp .trunc64to32 e => NegLitDisamRust e
  | .powCall base _ => NegLitDisamRust base
  | .arrayAccess base idx => NegLitDisamRust base ∧ NegLitDisamRust idx

/-! ## Well-formedness predicate for Rust expressions -/

/-- Well-formed MicroRust expression: variable names are valid identifiers,
    array access bases are varRefs, keyword names excluded. -/
inductive WFExprRust : MicroCExpr → Prop
  | litInt (n : Int) : WFExprRust (.litInt n)
  | litBool (b : Bool) : WFExprRust (.litBool b)
  | varRef (name : String) (hne : name ≠ "")
    (hstart : let c := name.toList.head (by simp; exact hne)
              c.isAlpha = true ∨ c = '_')
    (hcont : ∀ c ∈ name.toList, c.isAlpha = true ∨ c.isDigit = true ∨ c = '_')
    (hnot_kw : name ≠ "true" ∧ name ≠ "false") : WFExprRust (.varRef name)
  | binOp (op : MicroCBinOp) (lhs rhs : MicroCExpr)
    (hl : WFExprRust lhs) (hr : WFExprRust rhs) : WFExprRust (.binOp op lhs rhs)
  | unaryOp (op : MicroCUnaryOp) (e : MicroCExpr)
    (he : WFExprRust e) : WFExprRust (.unaryOp op e)
  | powCall (base : MicroCExpr) (n : Nat)
    (hb : WFExprRust base) : WFExprRust (.powCall base n)
  | arrayAccess (base idx : MicroCExpr)
    (hb : WFExprRust base) (hi : WFExprRust idx)
    (hbase_var : ∃ name, base = .varRef name) : WFExprRust (.arrayAccess base idx)

/-! ## Expression Roundtrip: Oracle Tests via native_decide -/

-- Leaf cases: litInt
example : parseMicroRustExpr (microRustExprToString (.litInt 0)) = some (.litInt 0) := by native_decide
example : parseMicroRustExpr (microRustExprToString (.litInt 1)) = some (.litInt 1) := by native_decide
example : parseMicroRustExpr (microRustExprToString (.litInt 42)) = some (.litInt 42) := by native_decide
example : parseMicroRustExpr (microRustExprToString (.litInt 999)) = some (.litInt 999) := by native_decide
example : parseMicroRustExpr (microRustExprToString (.litInt (-1))) = some (.litInt (-1)) := by native_decide
example : parseMicroRustExpr (microRustExprToString (.litInt (-42))) = some (.litInt (-42)) := by native_decide

-- Leaf cases: litBool
example : parseMicroRustExpr (microRustExprToString (.litBool true)) = some (.litBool true) := by native_decide
example : parseMicroRustExpr (microRustExprToString (.litBool false)) = some (.litBool false) := by native_decide

-- Variable references
example : parseMicroRustExpr (microRustExprToString (.varRef "x")) = some (.varRef "x") := by native_decide
example : parseMicroRustExpr (microRustExprToString (.varRef "abc")) = some (.varRef "abc") := by native_decide
example : parseMicroRustExpr (microRustExprToString (.varRef "t0")) = some (.varRef "t0") := by native_decide
example : parseMicroRustExpr (microRustExprToString (.varRef "_x")) = some (.varRef "_x") := by native_decide

-- Binary operations (all 12 operators)
example : parseMicroRustExpr (microRustExprToString (.binOp .add (.varRef "x") (.varRef "y")))
    = some (.binOp .add (.varRef "x") (.varRef "y")) := by native_decide
example : parseMicroRustExpr (microRustExprToString (.binOp .sub (.varRef "x") (.litInt 1)))
    = some (.binOp .sub (.varRef "x") (.litInt 1)) := by native_decide
example : parseMicroRustExpr (microRustExprToString (.binOp .mul (.varRef "a") (.varRef "b")))
    = some (.binOp .mul (.varRef "a") (.varRef "b")) := by native_decide
example : parseMicroRustExpr (microRustExprToString (.binOp .eqOp (.varRef "x") (.litInt 0)))
    = some (.binOp .eqOp (.varRef "x") (.litInt 0)) := by native_decide
example : parseMicroRustExpr (microRustExprToString (.binOp .ltOp (.varRef "i") (.varRef "n")))
    = some (.binOp .ltOp (.varRef "i") (.varRef "n")) := by native_decide
example : parseMicroRustExpr (microRustExprToString (.binOp .land (.varRef "a") (.varRef "b")))
    = some (.binOp .land (.varRef "a") (.varRef "b")) := by native_decide
example : parseMicroRustExpr (microRustExprToString (.binOp .lor (.varRef "a") (.varRef "b")))
    = some (.binOp .lor (.varRef "a") (.varRef "b")) := by native_decide
-- Bitwise ops
example : parseMicroRustExpr (microRustExprToString (.binOp .band (.varRef "x") (.varRef "m")))
    = some (.binOp .band (.varRef "x") (.varRef "m")) := by native_decide
example : parseMicroRustExpr (microRustExprToString (.binOp .bor (.varRef "x") (.varRef "m")))
    = some (.binOp .bor (.varRef "x") (.varRef "m")) := by native_decide
example : parseMicroRustExpr (microRustExprToString (.binOp .bxor (.varRef "x") (.varRef "m")))
    = some (.binOp .bxor (.varRef "x") (.varRef "m")) := by native_decide
example : parseMicroRustExpr (microRustExprToString (.binOp .bshl (.varRef "x") (.litInt 3)))
    = some (.binOp .bshl (.varRef "x") (.litInt 3)) := by native_decide
example : parseMicroRustExpr (microRustExprToString (.binOp .bshr (.varRef "x") (.litInt 3)))
    = some (.binOp .bshr (.varRef "x") (.litInt 3)) := by native_decide

-- Unary operations: neg, lnot
example : parseMicroRustExpr (microRustExprToString (.unaryOp .neg (.varRef "x")))
    = some (.unaryOp .neg (.varRef "x")) := by native_decide
example : parseMicroRustExpr (microRustExprToString (.unaryOp .lnot (.varRef "f")))
    = some (.unaryOp .lnot (.varRef "f")) := by native_decide

-- Cast operations: widen32to64, trunc64to32
example : parseMicroRustExpr (microRustExprToString (.unaryOp .widen32to64 (.varRef "x")))
    = some (.unaryOp .widen32to64 (.varRef "x")) := by native_decide
example : parseMicroRustExpr (microRustExprToString (.unaryOp .trunc64to32 (.varRef "x")))
    = some (.unaryOp .trunc64to32 (.varRef "x")) := by native_decide
-- Nested cast
example : parseMicroRustExpr (microRustExprToString
    (.unaryOp .widen32to64 (.binOp .add (.varRef "x") (.litInt 1))))
    = some (.unaryOp .widen32to64 (.binOp .add (.varRef "x") (.litInt 1))) := by native_decide

-- Power calls
example : parseMicroRustExpr (microRustExprToString (.powCall (.varRef "b") 0))
    = some (.powCall (.varRef "b") 0) := by native_decide
example : parseMicroRustExpr (microRustExprToString (.powCall (.varRef "b") 3))
    = some (.powCall (.varRef "b") 3) := by native_decide

-- Array access (with `as usize`)
example : parseMicroRustExpr (microRustExprToString (.arrayAccess (.varRef "a") (.litInt 0)))
    = some (.arrayAccess (.varRef "a") (.litInt 0)) := by native_decide
example : parseMicroRustExpr (microRustExprToString (.arrayAccess (.varRef "a") (.varRef "i")))
    = some (.arrayAccess (.varRef "a") (.varRef "i")) := by native_decide

-- Nested expressions (depth 2-3)
example : parseMicroRustExpr (microRustExprToString
    (.binOp .add (.binOp .mul (.varRef "x") (.varRef "y")) (.litInt 1)))
    = some (.binOp .add (.binOp .mul (.varRef "x") (.varRef "y")) (.litInt 1)) := by native_decide
example : parseMicroRustExpr (microRustExprToString
    (.unaryOp .neg (.binOp .add (.varRef "x") (.varRef "y"))))
    = some (.unaryOp .neg (.binOp .add (.varRef "x") (.varRef "y"))) := by native_decide
example : parseMicroRustExpr (microRustExprToString
    (.binOp .land (.binOp .ltOp (.varRef "i") (.varRef "n"))
                  (.binOp .eqOp (.varRef "x") (.litInt 0))))
    = some (.binOp .land (.binOp .ltOp (.varRef "i") (.varRef "n"))
                  (.binOp .eqOp (.varRef "x") (.litInt 0))) := by native_decide
-- Deep nesting with casts
example : parseMicroRustExpr (microRustExprToString
    (.unaryOp .widen32to64 (.unaryOp .trunc64to32 (.varRef "x"))))
    = some (.unaryOp .widen32to64 (.unaryOp .trunc64to32 (.varRef "x"))) := by native_decide
-- Bitwise with nesting
example : parseMicroRustExpr (microRustExprToString
    (.binOp .bxor (.binOp .band (.varRef "a") (.litInt 255))
                  (.binOp .bshl (.varRef "b") (.litInt 8))))
    = some (.binOp .bxor (.binOp .band (.varRef "a") (.litInt 255))
                  (.binOp .bshl (.varRef "b") (.litInt 8))) := by native_decide

/-! ## Universal roundtrip for finite subtypes -/

/-- All binary operators roundtrip through Rust print/parse. -/
theorem rustBinOp_roundtrip_all (op : MicroCBinOp) :
    parseMicroRustExpr (microRustExprToString (.binOp op (.varRef "x") (.varRef "y")))
    = some (.binOp op (.varRef "x") (.varRef "y")) := by
  cases op <;> native_decide

/-- All unary operators roundtrip through Rust print/parse. -/
theorem rustUnaryOp_roundtrip_all (op : MicroCUnaryOp) :
    parseMicroRustExpr (microRustExprToString (.unaryOp op (.varRef "x")))
    = some (.unaryOp op (.varRef "x")) := by
  cases op <;> native_decide

/-- Both boolean literals roundtrip through Rust print/parse. -/
theorem rustLitBool_roundtrip (b : Bool) :
    parseMicroRustExpr (microRustExprToString (.litBool b))
    = some (.litBool b) := by
  cases b <;> native_decide

/-! ## Shared Infrastructure from MicroC.Roundtrip

  The Rust parser uses its own skipWsR/pDigitsR/pNatR/pIdentR/pBinOpR combinators
  that are structurally identical to the MicroC versions. The proofs for
  digit/nat roundtrip (natToChars_roundtrip, pDigits_exact, pNat_natToChars)
  from MicroC.Roundtrip are reused since both parsers use the same natToChars printer.
-/

/-! ## Helper Lemmas for Rust Parser Combinators -/

/-- skipWsR on non-whitespace input is identity. -/
@[simp] theorem skipWsR_nonws (c : Char) (cs : List Char)
    (h : c ≠ ' ' ∧ c ≠ '\n' ∧ c ≠ '\t' ∧ c ≠ '\r') :
    skipWsR (c :: cs) = c :: cs := by
  simp [skipWsR, h.1, h.2.1, h.2.2.1, h.2.2.2]

/-- skipWsR of empty list is empty. -/
@[simp] theorem skipWsR_nil : skipWsR [] = [] := by
  simp [skipWsR]

/-- NoLeadingDigit for Rust: rest doesn't start with digit. -/
def NoLeadingDigitR (cs : List Char) : Prop :=
  cs = [] ∨ ∃ c rest, cs = c :: rest ∧ c.isDigit = false

/-- NoLeadingIdent for Rust: rest doesn't start with ident continuation. -/
def NoLeadingIdentR (cs : List Char) : Prop :=
  cs = [] ∨ ∃ c rest, cs = c :: rest ∧ c.isAlpha = false ∧ c.isDigit = false ∧ c ≠ '_'

/-- pDigitsR on digit cons follows the recursive pattern. -/
theorem pDigitsR_digit_cons (c : Char) (rest : List Char) (hc : c.isDigit = true) :
    pDigitsR (c :: rest) = match pDigitsR rest with
      | some (ds, rest') => some (c :: ds, rest')
      | none => some ([c], rest) := by
  simp only [pDigitsR, hc, ite_true]; rfl

/-- pDigitsR exactly consumes a known digit prefix when rest has no leading digit. -/
theorem pDigitsR_exact : ∀ (ds : List Char) (rest : List Char),
    ds ≠ [] →
    (∀ c ∈ ds, c.isDigit = true) →
    NoLeadingDigitR rest →
    pDigitsR (ds ++ rest) = some (ds, rest)
  | [c], rest, _, hall, hrest => by
    simp only [List.singleton_append]
    rw [pDigitsR_digit_cons c rest (hall c (List.mem_cons_self ..))]
    cases hrest with
    | inl h => subst h; simp [pDigitsR]
    | inr h =>
      obtain ⟨r, rs, hrst, hrd⟩ := h
      subst hrst; simp [pDigitsR, hrd]
  | c :: d :: ds', rest, _, hall, hrest => by
    have hc : c.isDigit = true := hall c (List.mem_cons_self ..)
    have hall' : ∀ x ∈ d :: ds', x.isDigit = true := by
      intro x hx; exact hall x (List.mem_cons_of_mem c hx)
    have hih := pDigitsR_exact (d :: ds') rest (List.cons_ne_nil _ _) hall' hrest
    show pDigitsR (c :: ((d :: ds') ++ rest)) = some (c :: d :: ds', rest)
    rw [pDigitsR_digit_cons c _ hc, hih]

/-- digitsToNatR = digitsToNat on any char list (they compute identically). -/
private theorem digitsToNatR_eq_digitsToNat (ds : List Char) :
    digitsToNatR ds = digitsToNat ds := by
  simp only [digitsToNatR, digitsToNat]

/-- pNatR correctly parses natToChars n when rest has no leading digit. -/
theorem pNatR_natToChars (n : Nat) (rest : List Char) (hrest : NoLeadingDigitR rest) :
    pNatR (natToChars n ++ rest) = some (n, rest) := by
  simp only [pNatR]
  rw [pDigitsR_exact (natToChars n) rest (natToChars_ne_nil n)
      (natToChars_all_digits n) hrest]
  simp only [digitsToNatR_eq_digitsToNat, natToChars_roundtrip]

/-! ## pIdentR exact parsing -/

/-- pIdentR.go stops at a non-identifier character. -/
private theorem pIdentR_go_stop (acc : List Char) (r : Char) (rest : List Char)
    (hra : r.isAlpha = false) (hrd : r.isDigit = false) (hru : r ≠ '_') :
    pIdentR.go acc (r :: rest) = (acc, r :: rest) := by
  unfold pIdentR.go; simp
  intro h; cases h with
  | inl h => cases h with
    | inl h => exact absurd h (by simp [hra])
    | inr h => exact absurd h (by simp [hrd])
  | inr h => exact absurd h hru

/-- pIdentR.go exactly consumes identifier-continuation characters. -/
theorem pIdentR_go_exact : ∀ (acc : List Char) (chars : List Char) (rest : List Char),
    (∀ c ∈ chars, c.isAlpha = true ∨ c.isDigit = true ∨ c = '_') →
    NoLeadingIdentR rest →
    pIdentR.go acc (chars ++ rest) = (acc ++ chars, rest)
  | acc, [], rest, _, hrest => by
    simp
    cases hrest with
    | inl h => subst h; simp [pIdentR.go]
    | inr h =>
      obtain ⟨r, rs, hrst, hra, hrd, hru⟩ := h
      subst hrst; exact pIdentR_go_stop acc r rs hra hrd hru
  | acc, c :: cs, rest, hall, hrest => by
    have hc := hall c (List.mem_cons_self ..)
    have hall' : ∀ x ∈ cs, x.isAlpha = true ∨ x.isDigit = true ∨ x = '_' :=
      fun x hx => hall x (List.mem_cons_of_mem c hx)
    simp only [List.cons_append]
    unfold pIdentR.go; simp
    have hcond : (c.isAlpha = true ∨ c.isDigit = true) ∨ c = '_' := by
      cases hc with
      | inl h => exact Or.inl (Or.inl h)
      | inr h => cases h with
        | inl h => exact Or.inl (Or.inr h)
        | inr h => exact Or.inr h
    simp [hcond]
    rw [pIdentR_go_exact (acc ++ [c]) cs rest hall' hrest]
    simp [List.append_assoc]

/-- pIdentR exactly parses a well-formed identifier name. -/
theorem pIdentR_exact (name : String) (rest : List Char)
    (hne : name ≠ "")
    (hstart : let c := name.toList.head (by simp; exact hne)
              c.isAlpha = true ∨ c = '_')
    (hcont : ∀ c ∈ name.toList, c.isAlpha = true ∨ c.isDigit = true ∨ c = '_')
    (hrest : NoLeadingIdentR rest) :
    pIdentR (name.toList ++ rest) = some (name, rest) := by
  have hne' : name.toList ≠ [] := by simp; exact hne
  match hcs : name.toList with
  | [] => exact absurd hcs hne'
  | first :: tail =>
    simp only [List.cons_append, pIdentR]
    have hfirst_orig := hstart
    simp only [hcs] at hfirst_orig
    simp [List.head] at hfirst_orig
    have hcond : (first.isAlpha || first == '_') = true := by
      cases hfirst_orig with
      | inl h => simp [h]
      | inr h => simp [h]
    simp [hcond]
    have htail : ∀ c ∈ tail, c.isAlpha = true ∨ c.isDigit = true ∨ c = '_' := by
      intro c hc; exact hcont c (by rw [hcs]; exact List.mem_cons_of_mem first hc)
    rw [pIdentR_go_exact [] tail rest htail hrest]
    simp
    exact congrArg String.ofList (hcs.symm) |>.symm ▸ String.ofList_toList.symm ▸ rfl

/-! ## ExprSafeR: rest-safety for Rust expression parsing -/

/-- Safe rest condition for Rust expression parsing. -/
def ExprSafeR (rest : List Char) : Prop :=
  NoLeadingDigitR rest ∧ NoLeadingIdentR rest ∧
  (∀ cs, skipWsR rest ≠ '[' :: cs) ∧ (∀ cs, skipWsR rest ≠ '(' :: cs)

theorem exprSafeR_nil : ExprSafeR ([] : List Char) :=
  ⟨Or.inl rfl, Or.inl rfl, by intro cs; simp [skipWsR], by intro cs; simp [skipWsR]⟩

theorem exprSafeR_sep (c : Char) (rest : List Char)
    (hna : c.isAlpha = false) (hnd : c.isDigit = false)
    (hnu : c ≠ '_') (hnb : c ≠ '[') (hnp : c ≠ '(')
    (hnws : c ≠ ' ' ∧ c ≠ '\n' ∧ c ≠ '\t' ∧ c ≠ '\r') :
    ExprSafeR (c :: rest) := by
  refine ⟨Or.inr ⟨c, rest, rfl, hnd⟩, Or.inr ⟨c, rest, rfl, hna, hnd, hnu⟩, ?_, ?_⟩
  · intro cs h; rw [skipWsR_nonws c rest hnws] at h
    rw [List.cons.injEq] at h; exact absurd h.1 hnb
  · intro cs h; rw [skipWsR_nonws c rest hnws] at h
    rw [List.cons.injEq] at h; exact absurd h.1 hnp

theorem exprSafeR_rparen (rest : List Char) : ExprSafeR (')' :: rest) :=
  exprSafeR_sep ')' rest (by native_decide) (by native_decide) (by decide)
    (by decide) (by decide) ⟨by decide, by decide, by decide, by decide⟩

theorem exprSafeR_rbracket (rest : List Char) : ExprSafeR (']' :: rest) :=
  exprSafeR_sep ']' rest (by native_decide) (by native_decide) (by decide)
    (by decide) (by decide) ⟨by decide, by decide, by decide, by decide⟩

theorem exprSafeR_comma (rest : List Char) : ExprSafeR (',' :: rest) :=
  exprSafeR_sep ',' rest (by native_decide) (by native_decide) (by decide)
    (by decide) (by decide) ⟨by decide, by decide, by decide, by decide⟩

theorem exprSafeR_semicolon (rest : List Char) : ExprSafeR (';' :: rest) :=
  exprSafeR_sep ';' rest (by native_decide) (by native_decide) (by decide)
    (by decide) (by decide) ⟨by decide, by decide, by decide, by decide⟩

/-! ## Char property helpers (local copies — private in MicroC.RoundtripExpr) -/

/-- Digit chars are not whitespace. -/
private theorem isDigit_not_ws_r (c : Char) (h : c.isDigit = true) :
    c ≠ ' ' ∧ c ≠ '\n' ∧ c ≠ '\t' ∧ c ≠ '\r' :=
  ⟨by intro h'; subst h'; simp [Char.isDigit] at h,
   by intro h'; subst h'; simp [Char.isDigit] at h,
   by intro h'; subst h'; simp [Char.isDigit] at h,
   by intro h'; subst h'; simp [Char.isDigit] at h⟩

/-- Alpha chars are not whitespace. -/
private theorem isAlpha_not_ws_r (c : Char) (h : c.isAlpha = true) :
    c ≠ ' ' ∧ c ≠ '\n' ∧ c ≠ '\t' ∧ c ≠ '\r' :=
  ⟨by intro h'; subst h'; simp [Char.isAlpha] at h,
   by intro h'; subst h'; simp [Char.isAlpha] at h,
   by intro h'; subst h'; simp [Char.isAlpha] at h,
   by intro h'; subst h'; simp [Char.isAlpha] at h⟩

/-! ## Printed expression properties -/

/-- Printed WFExprRust has non-empty toList. -/
theorem rustPrint_ne_nil (e : MicroCExpr) (he : WFExprRust e) :
    (microRustExprToString e).toList ≠ [] := by
  cases he with
  | litInt n =>
    simp [microRustExprToString_litInt]
    split
    · simp
    · have := natToChars_ne_nil n.toNat
      intro h; simp at h; exact this h
  | litBool b =>
    cases b <;> simp [microRustExprToString]
  | varRef name hne _ _ _ =>
    simp [microRustExprToString_varRef]
    exact hne
  | binOp _ _ _ _ _ =>
    simp [microRustExprToString_binOp]
  | unaryOp op _ _ =>
    cases op <;> simp [microRustExprToString]
  | powCall _ _ _ =>
    simp [microRustExprToString_powCall]
  | arrayAccess _ _ hb _ hbv =>
    obtain ⟨vname, rfl⟩ := hbv
    cases hb with
    | varRef _ hne_v _ _ _ =>
      simp [microRustExprToString_arrayAccess, microRustExprToString_varRef]

/-- First char of a printed WFExprRust is non-whitespace. -/
theorem rustPrint_first_nonws (e : MicroCExpr) (he : WFExprRust e) :
    ∀ c cs, (microRustExprToString e).toList = c :: cs →
    c ≠ ' ' ∧ c ≠ '\n' ∧ c ≠ '\t' ∧ c ≠ '\r' := by
  intro c cs heq
  cases he with
  | litInt n =>
    simp [microRustExprToString_litInt] at heq
    split at heq
    · simp [String.toList_append] at heq; obtain ⟨rfl, _⟩ := heq
      exact ⟨by decide, by decide, by decide, by decide⟩
    · have hne := natToChars_ne_nil n.toNat
      match hcs : natToChars n.toNat with
      | [] => exact absurd hcs hne
      | c' :: _ =>
        simp [hcs] at heq; rw [← heq.1]
        exact isDigit_not_ws_r c' (natToChars_all_digits n.toNat c' (by rw [hcs]; exact List.mem_cons_self ..))
  | litBool b =>
    cases b <;> simp [microRustExprToString] at heq <;> obtain ⟨rfl, _⟩ := heq <;>
      exact ⟨by decide, by decide, by decide, by decide⟩
  | varRef name hne hstart _ _ =>
    simp [microRustExprToString_varRef] at heq
    have hne' : name.toList ≠ [] := by simp; exact hne
    match hcs : name.toList with
    | [] => exact absurd hcs hne'
    | c' :: _ =>
      simp [hcs] at hstart
      rw [hcs] at heq; simp at heq; rw [← heq.1]
      cases hstart with
      | inl h => exact isAlpha_not_ws_r c' h
      | inr h => subst h; exact ⟨by decide, by decide, by decide, by decide⟩
  | binOp _ _ _ _ _ =>
    simp [microRustExprToString_binOp, String.toList_append] at heq
    obtain ⟨rfl, _⟩ := heq; exact ⟨by decide, by decide, by decide, by decide⟩
  | unaryOp op _ _ =>
    cases op <;> simp [microRustExprToString, String.toList_append] at heq <;>
      obtain ⟨rfl, _⟩ := heq <;>
      exact ⟨by decide, by decide, by decide, by decide⟩
  | powCall _ _ _ =>
    simp [microRustExprToString_powCall, String.toList_append] at heq
    obtain ⟨rfl, _⟩ := heq; exact ⟨by decide, by decide, by decide, by decide⟩
  | arrayAccess _ _ hb _ hbv =>
    obtain ⟨vname, rfl⟩ := hbv
    simp [microRustExprToString_arrayAccess, microRustExprToString_varRef] at heq
    cases hb with
    | varRef _ hne_v hstart_v _ _ =>
      have hne_v' : vname.toList ≠ [] := by simp; exact hne_v
      match hcs_v : vname.toList with
      | [] => exact absurd hcs_v hne_v'
      | cv :: _ =>
        simp [hcs_v] at hstart_v
        simp [hcs_v] at heq; rw [← heq.1]
        cases hstart_v with
        | inl h => exact isAlpha_not_ws_r cv h
        | inr h => subst h; exact ⟨by decide, by decide, by decide, by decide⟩

/-! ## Fuel sufficiency -/

/-- Fuel sufficiency: rustExprDepth e <= string length + 1. -/
theorem rustExprDepth_le_length (e : MicroCExpr) (he : WFExprRust e) :
    rustExprDepth e ≤ (microRustExprToString e).toList.length + 1 := by
  induction he with
  | litInt _ | litBool _ | varRef _ _ _ _ _ =>
    simp [rustExprDepth]
  | binOp _ _ _ _ _ ih_l ih_r =>
    simp only [rustExprDepth, microRustExprToString_binOp, Nat.max_def]
    simp only [String.toList_append, List.length_append,
      show "(".toList = ['('] from rfl, show ")".toList = [')'] from rfl,
      show " ".toList = [' '] from rfl,
      List.length_cons, List.length_nil]
    split <;> (have := ih_l; have := ih_r; omega)
  | unaryOp op _ _ ih_e =>
    simp only [rustExprDepth]
    cases op <;> simp only [microRustExprToString, String.toList_append, List.length_append,
      show "(".toList = ['('] from rfl, show ")".toList = [')'] from rfl,
      show "-".toList = ['-'] from rfl, show "!".toList = ['!'] from rfl,
      show " as i64)".toList = [' ', 'a', 's', ' ', 'i', '6', '4', ')'] from rfl,
      show " as i32)".toList = [' ', 'a', 's', ' ', 'i', '3', '2', ')'] from rfl,
      List.length_cons, List.length_nil, List.length_append] <;>
      (have := ih_e; omega)
  | powCall _ _ _ ih_base =>
    simp only [rustExprDepth, microRustExprToString_powCall]
    simp only [String.toList_append, List.length_append,
      show "power(".toList = ['p', 'o', 'w', 'e', 'r', '('] from rfl,
      show ", ".toList = [',', ' '] from rfl,
      show ")".toList = [')'] from rfl,
      List.length_cons, List.length_nil]
    have := ih_base; omega
  | arrayAccess _ _ _ _ _ ih_base ih_idx =>
    simp only [rustExprDepth, microRustExprToString_arrayAccess, Nat.max_def]
    simp only [String.toList_append, List.length_append,
      show "[".toList = ['['] from rfl,
      show " as usize]".toList = [' ', 'a', 's', ' ', 'u', 's', 'i', 'z', 'e', ']'] from rfl,
      List.length_cons, List.length_nil]
    split <;> (have := ih_base; have := ih_idx; omega)

private theorem toList_ne_nil_of_ne_empty_r (s : String) (h : s ≠ "") : s.toList ≠ [] := by
  intro h'; exact h (String.ext_iff.mpr (by simp [h']))

/-- Alpha chars are not digits: proved via Bool contradiction. -/
private theorem isAlpha_not_digit (c : Char) (h : c.isAlpha = true) : c.isDigit = false := by
  by_contra hd; simp only [Bool.not_eq_false] at hd
  simp only [Char.isDigit, Char.isAlpha, Char.isUpper, Char.isLower,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h hd
  -- h : c.val ≥ 65 ∧ c.val ≤ 90 ∨ c.val ≥ 97 ∧ c.val ≤ 122
  -- hd : c.val ≥ 48 ∧ c.val ≤ 57
  -- c.val is UInt32 — need to go via Nat
  have hle57 : c.val.toNat ≤ 57 := by exact_mod_cast hd.2
  rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
  · have hge65 : c.val.toNat ≥ 65 := by exact_mod_cast h1
    omega
  · have hge97 : c.val.toNat ≥ 97 := by exact_mod_cast h1
    omega

/-! ## Equation lemmas for pRustExprF dispatch -/

/-- String literal normalization for Rust parser proofs. -/
@[simp] private theorem strR_lp : "(".toList = ['('] := rfl
@[simp] private theorem strR_rp : ")".toList = [')'] := rfl
@[simp] private theorem strR_dash : "-".toList = ['-'] := rfl
@[simp] private theorem strR_bang : "!".toList = ['!'] := rfl
@[simp] private theorem strR_sp : " ".toList = [' '] := rfl
@[simp] private theorem strR_power_lp : "power(".toList = ['p', 'o', 'w', 'e', 'r', '('] := rfl
@[simp] private theorem strR_comma_sp : ", ".toList = [',', ' '] := rfl
@[simp] private theorem strR_lb : "[".toList = ['['] := rfl
@[simp] private theorem strR_as_usize_rb : " as usize]".toList =
    [' ', 'a', 's', ' ', 'u', 's', 'i', 'z', 'e', ']'] := rfl
@[simp] private theorem strR_as_i64_rp : " as i64)".toList =
    [' ', 'a', 's', ' ', 'i', '6', '4', ')'] := rfl
@[simp] private theorem strR_as_i32_rp : " as i32)".toList =
    [' ', 'a', 's', ' ', 'i', '3', '2', ')'] := rfl

/-- pRustExprF on '(' dispatches to pRustParenF. -/
@[simp] private theorem pRustExprF_paren (k : Nat) (cs : List Char) :
    pRustExprF (k + 1) ('(' :: cs) = pRustExprF.pRustParenF k (skipWsR cs) := by
  simp [pRustExprF]

/-- pRustExprF on digit dispatches to pNatR. -/
@[simp] private theorem pRustExprF_digit (k : Nat) (c : Char) (cs : List Char)
    (hd : c.isDigit = true) :
    pRustExprF (k + 1) (c :: cs) =
      match pNatR (c :: cs) with
      | some (n, rest) => some (.litInt (Int.ofNat n), rest)
      | none => none := by
  simp only [pRustExprF]
  rw [skipWsR_nonws c cs (isDigit_not_ws_r c hd)]
  have hc1 : c ≠ '(' := by intro h; subst h; simp [Char.isDigit] at hd
  split
  · rename_i heq; exact absurd (List.cons.inj heq).1 hc1
  · rename_i heq
    have : c = 'p' := (List.cons.inj heq).1; subst this
    simp [Char.isDigit] at hd
  · rename_i c' tail _ _ heq
    have : c = c' := (List.cons.inj heq).1; subst this
    split
    next => rfl
    next hf => exact absurd hd hf
  · rename_i heq; simp at heq

/-- pRustExprF on alpha/underscore when power( pattern doesn't match. -/
private theorem pRustExprF_ident (k : Nat) (c : Char) (cs : List Char)
    (hnd : c.isDigit = false) (hia : c.isAlpha = true ∨ c = '_')
    (hnp : ∀ tail, c :: cs ≠ 'p' :: 'o' :: 'w' :: 'e' :: 'r' :: '(' :: tail) :
    pRustExprF (k + 1) (c :: cs) = pRustExprF.pRustIdentF k (c :: cs) := by
  simp only [pRustExprF]
  have hws : c ≠ ' ' ∧ c ≠ '\n' ∧ c ≠ '\t' ∧ c ≠ '\r' := by
    cases hia with
    | inl h => exact isAlpha_not_ws_r c h
    | inr h => subst h; exact ⟨by decide, by decide, by decide, by decide⟩
  rw [skipWsR_nonws c cs hws]
  have hc1 : c ≠ '(' := by
    intro h; subst h
    cases hia with
    | inl h => simp [Char.isAlpha] at h
    | inr h => exact absurd h (by decide)
  split
  · rename_i heq; exact absurd (List.cons.inj heq).1 hc1
  · rename_i tail heq
    exfalso; exact hnp tail heq
  · rename_i c' tail _ _ heq
    have hce : c = c' := (List.cons.inj heq).1; subst hce
    simp [hnd]
    have hcond : (c.isAlpha || c == '_') = true := by
      cases hia with
      | inl h => simp [h]
      | inr h => simp [h]
    intro hna hnu
    cases hia with
    | inl h => exact absurd h (by rw [hna]; decide)
    | inr h => exact absurd h hnu
  · rename_i heq; simp at heq

/-- pRustParenF on '!' dispatches to lnot parse. -/
private theorem pRustParenF_lnot (k : Nat) (rest : List Char) :
    pRustExprF.pRustParenF k ('!' :: rest) =
      match pRustExprF k rest with
      | some (e, rest') =>
        match skipWsR rest' with
        | ')' :: final => some (.unaryOp .lnot e, final)
        | _ => none
      | none => none := by
  unfold pRustExprF.pRustParenF; rfl

/-- pRustParenF on '-' followed by digit: negative literal. -/
private theorem pRustParenF_neg_digit (k : Nat) (c : Char) (rest : List Char)
    (hd : c.isDigit = true) :
    pRustExprF.pRustParenF k ('-' :: c :: rest) =
      match pNatR (c :: rest) with
      | some (n, rest') => match skipWsR rest' with
        | ')' :: final => some (.litInt (-(Int.ofNat n)), final)
        | _ => none
      | none => none := by
  unfold pRustExprF.pRustParenF; simp [hd]; split <;> simp_all; · rfl

/-- pRustParenF on '-' followed by non-digit: unary neg. -/
private theorem pRustParenF_neg_nondigit (k : Nat) (c : Char) (rest : List Char)
    (hnd : c.isDigit = false) :
    pRustExprF.pRustParenF k ('-' :: c :: rest) =
      match pRustExprF k (c :: rest) with
      | some (e, rest') =>
        match skipWsR rest' with
        | ')' :: final => some (.unaryOp .neg e, final)
        | _ => none
      | none => none := by
  unfold pRustExprF.pRustParenF; simp [hnd]
  split <;> simp_all
  · rfl

/-- pRustParenF fallthrough (not '!' or '-'): cast or binOp. -/
private theorem pRustParenF_fallthrough (k : Nat) (c : Char) (cs : List Char)
    (h1 : c ≠ '!') (h2 : c ≠ '-') :
    pRustExprF.pRustParenF k (c :: cs) =
      match pRustExprF k (c :: cs) with
      | some (lhs, rest) =>
        let rest := skipWsR rest
        match rest with
        | 'a' :: 's' :: ' ' :: 'i' :: '6' :: '4' :: ')' :: final =>
          some (.unaryOp .widen32to64 lhs, final)
        | 'a' :: 's' :: ' ' :: 'i' :: '3' :: '2' :: ')' :: final =>
          some (.unaryOp .trunc64to32 lhs, final)
        | _ =>
          match pBinOpR rest with
          | some (op, rest') =>
            match pRustExprF k rest' with
            | some (rhs, rest'') =>
              match skipWsR rest'' with
              | ')' :: final => some (.binOp op lhs rhs, final)
              | _ => none
            | none => none
          | none => none
      | none => none := by
  unfold pRustExprF.pRustParenF
  simp [h1, h2]
  split <;> simp_all
  · rfl

/-- pRustExprF on 'power(' dispatches to pRustPowF. -/
@[simp] private theorem pRustExprF_power (k : Nat) (rest : List Char) :
    pRustExprF (k + 1) ('p' :: 'o' :: 'w' :: 'e' :: 'r' :: '(' :: rest) =
      pRustExprF.pRustPowF k (skipWsR rest) := by
  simp [pRustExprF]

/-! ## pBinOpR roundtrip -/

@[simp] private theorem toList_add_op : ("+").toList = ['+'] := by native_decide
@[simp] private theorem toList_sub_op : ("-").toList = ['-'] := by native_decide
@[simp] private theorem toList_mul_op : ("*").toList = ['*'] := by native_decide
@[simp] private theorem toList_eq_op : ("==").toList = ['=', '='] := by native_decide
@[simp] private theorem toList_lt_op : ("<").toList = ['<'] := by native_decide
@[simp] private theorem toList_land_op : ("&&").toList = ['&', '&'] := by native_decide
@[simp] private theorem toList_lor_op : ("||").toList = ['|', '|'] := by native_decide
@[simp] private theorem toList_band_op : ("&").toList = ['&'] := by native_decide
@[simp] private theorem toList_bor_op : ("|").toList = ['|'] := by native_decide
@[simp] private theorem toList_bxor_op : ("^").toList = ['^'] := by native_decide
@[simp] private theorem toList_bshl_op : ("<<").toList = ['<', '<'] := by native_decide
@[simp] private theorem toList_bshr_op : (">>").toList = ['>', '>'] := by native_decide

/-- pBinOpR roundtrip: when rest starts with a non-whitespace char,
    pBinOpR correctly parses "op " ++ rest as (op, rest). -/
private theorem pBinOpR_roundtrip (op : MicroCBinOp) (rest : List Char)
    (hrest : ∀ c cs, rest = c :: cs → c ≠ ' ' ∧ c ≠ '\n' ∧ c ≠ '\t' ∧ c ≠ '\r') :
    pBinOpR ((microRustBinOpToString op).toList ++ ' ' :: rest) = some (op, rest) := by
  cases op <;> (
    simp only [microRustBinOpToString, toList_add_op, toList_sub_op, toList_mul_op,
      toList_eq_op, toList_lt_op, toList_land_op, toList_lor_op, toList_band_op,
      toList_bor_op, toList_bxor_op, toList_bshl_op, toList_bshr_op,
      List.cons_append, List.nil_append, pBinOpR]
    match hcs : rest with
    | [] => simp [skipWsR]
    | c :: cs =>
      have ⟨h1, h2, h3, h4⟩ := hrest c cs rfl
      simp [skipWsR, h1, h2, h3, h4])

/-! ## Helper: 'power(' match impossible for ident names -/

/-- A well-formed identifier name followed by ExprSafeR rest cannot have
    the form 'p' :: 'o' :: 'w' :: 'e' :: 'r' :: '(' :: tail
    at the top level of name.toList ++ rest. -/
private theorem power_match_impossible_varref (name : String)
    (hne : name ≠ "")
    (hcont : ∀ c ∈ name.toList, c.isAlpha = true ∨ c.isDigit = true ∨ c = '_')
    (rest : List Char) (hrest : ExprSafeR rest) :
    ∀ tail, name.toList ++ rest ≠ 'o' :: 'w' :: 'e' :: 'r' :: '(' :: tail := by
  intro tail heq
  have hne' : name.toList ≠ [] := by simp; exact hne
  -- The key: if name has < 4 chars, then some of "ower(" spills into rest,
  -- but ExprSafeR means rest can't start with alpha/digit/underscore or '('.
  -- If name has ≥ 5 chars, then '(' is inside name.toList, but valid ident
  -- chars don't include '('.
  match hcs : name.toList with
  | [] => exact absurd hcs hne'
  | [a] =>
    rw [hcs, List.singleton_append] at heq
    have := (List.cons.inj heq).2
    -- rest = 'w' :: 'e' :: 'r' :: '(' :: tail
    -- But ExprSafeR rest implies NoLeadingIdentR rest
    rw [this] at hrest
    cases hrest.2.1 with
    | inl h => simp at h
    | inr h =>
      obtain ⟨c', _, hc', hna, _, _⟩ := h
      have := (List.cons.inj hc').1; subst this
      exact absurd (show ('w' : Char).isAlpha = true from by native_decide) (by rw [hna]; decide)
  | [a, b] =>
    rw [hcs] at heq; simp [List.append_assoc] at heq
    rw [heq.2.2] at hrest
    cases hrest.2.1 with
    | inl h => simp at h
    | inr h =>
      obtain ⟨c', _, hc', hna, _, _⟩ := h
      have := (List.cons.inj hc').1; subst this
      exact absurd (show ('e' : Char).isAlpha = true from by native_decide) (by rw [hna]; decide)
  | [a, b, c] =>
    rw [hcs] at heq; simp [List.append_assoc] at heq
    rw [heq.2.2.2] at hrest
    cases hrest.2.1 with
    | inl h => simp at h
    | inr h =>
      obtain ⟨c', _, hc', hna, _, _⟩ := h
      have := (List.cons.inj hc').1; subst this
      exact absurd (show ('r' : Char).isAlpha = true from by native_decide) (by rw [hna]; decide)
  | [a, b, c, d] =>
    rw [hcs] at heq; simp [List.append_assoc] at heq
    -- rest = '(' :: tail, but ExprSafeR says skipWsR rest ≠ '(' :: _
    rw [heq.2.2.2.2] at hrest
    have := hrest.2.2.2 tail
    simp [skipWsR] at this
  | a :: b :: c :: d :: e :: cs5 =>
    rw [hcs] at heq; simp [List.append_assoc] at heq
    have h5 : e = '(' := heq.2.2.2.2.1; subst h5
    have hmem : '(' ∈ name.toList := by rw [hcs]; simp
    have := hcont '(' hmem
    rcases this with h | h | h
    · exact absurd h (by native_decide)
    · exact absurd h (by native_decide)
    · exact absurd h (by decide)

/-! ## Helper: skipWsR on space prefix -/

@[simp] theorem skipWsR_space (rest : List Char) :
    skipWsR (' ' :: rest) = skipWsR rest := by
  simp [skipWsR]

/-! ## matchLiteral roundtrip -/

theorem matchLiteral_exact (pat rest : List Char) :
    matchLiteral pat (pat ++ rest) = some rest := by
  induction pat with
  | nil => simp [matchLiteral]
  | cons c cs ih => simp [matchLiteral, List.cons_append, BEq.beq, ih]

/-! ## Additional helpers for the core proof -/

/-- list_head_eq: if l = c :: cs then l.head = c. -/
private theorem list_head_eq_of_cons_r {l : List Char} {c : Char} {cs : List Char}
    (h : l = c :: cs) : ∀ (hne : l ≠ []), l.head hne = c := by
  intro hne; subst h; rfl

/-- First char of a printed WFExprRust is neither '-' nor '!'. -/
private theorem rustPrint_first_not_neg_bang (e : MicroCExpr) (he : WFExprRust e) :
    ∀ c cs, (microRustExprToString e).toList = c :: cs → c ≠ '-' ∧ c ≠ '!' := by
  intro c cs heq
  cases he with
  | litInt n =>
    simp [microRustExprToString_litInt] at heq
    split at heq
    · simp [String.toList_append] at heq; obtain ⟨rfl, _⟩ := heq
      exact ⟨by decide, by decide⟩
    · have hne := natToChars_ne_nil n.toNat
      match hcs : natToChars n.toNat with
      | [] => exact absurd hcs hne
      | c' :: _ =>
        simp [hcs] at heq; rw [← heq.1]
        have hd := natToChars_all_digits n.toNat c' (by rw [hcs]; exact List.mem_cons_self ..)
        exact ⟨by intro h; subst h; simp [Char.isDigit] at hd,
               by intro h; subst h; simp [Char.isDigit] at hd⟩
  | litBool b =>
    cases b <;> simp [microRustExprToString] at heq <;> obtain ⟨rfl, _⟩ := heq <;>
      exact ⟨by decide, by decide⟩
  | varRef name hne hstart _ _ =>
    simp [microRustExprToString_varRef] at heq
    have hne' := toList_ne_nil_of_ne_empty_r name hne
    match hcs : name.toList with
    | [] => exact absurd hcs hne'
    | c' :: _ =>
      have hhead := list_head_eq_of_cons_r hcs
      have hstart' := hstart; simp only [hhead] at hstart'
      rw [hcs] at heq; simp at heq; rw [← heq.1]
      cases hstart' with
      | inl h =>
        exact ⟨by intro h'; subst h'; simp [Char.isAlpha, Char.isUpper, Char.isLower] at h,
               by intro h'; subst h'; simp [Char.isAlpha, Char.isUpper, Char.isLower] at h⟩
      | inr h => subst h; exact ⟨by decide, by decide⟩
  | binOp _ _ _ _ _ =>
    simp [microRustExprToString_binOp, String.toList_append] at heq
    obtain ⟨rfl, _⟩ := heq; exact ⟨by decide, by decide⟩
  | unaryOp op _ _ =>
    cases op <;> simp [microRustExprToString, String.toList_append] at heq <;>
      obtain ⟨rfl, _⟩ := heq <;>
      exact ⟨by decide, by decide⟩
  | powCall _ _ _ =>
    simp [microRustExprToString_powCall, String.toList_append] at heq
    obtain ⟨rfl, _⟩ := heq; exact ⟨by decide, by decide⟩
  | arrayAccess _ _ hb _ hbv =>
    obtain ⟨vname, rfl⟩ := hbv
    simp [microRustExprToString_arrayAccess, microRustExprToString_varRef] at heq
    cases hb with
    | varRef _ hne_v hstart_v _ _ =>
      have hne_v' := toList_ne_nil_of_ne_empty_r vname hne_v
      match hcs_v : vname.toList with
      | [] => exact absurd hcs_v hne_v'
      | cv :: _ =>
        have hhead := list_head_eq_of_cons_r hcs_v
        have hst := hstart_v; simp only [hhead] at hst
        simp [hcs_v] at heq; rw [← heq.1]
        cases hst with
        | inl h =>
          exact ⟨by intro h'; subst h'; simp [Char.isAlpha, Char.isUpper, Char.isLower] at h,
                 by intro h'; subst h'; simp [Char.isAlpha, Char.isUpper, Char.isLower] at h⟩
        | inr h => subst h; exact ⟨by decide, by decide⟩

/-- ExprSafeR for the "rest after printing lhs" in a binOp context. -/
private theorem exprSafeR_binop_mid (op : MicroCBinOp)
    (rhs_print : List Char) (rest : List Char) :
    ExprSafeR (' ' :: (microRustBinOpToString op).toList ++
      (' ' :: rhs_print ++ (')' :: rest))) := by
  refine ⟨Or.inr ⟨' ', _, rfl, by native_decide⟩,
          Or.inr ⟨' ', _, rfl, by native_decide, by native_decide, by decide⟩, ?_, ?_⟩ <;>
  · intro cs; cases op <;> simp [microRustBinOpToString, skipWsR]

/-- skipWsR on natToChars: digits are non-ws so skipWsR is identity. -/
private theorem skipWsR_natToChars (n : Nat) (rest : List Char) :
    skipWsR (natToChars n ++ rest) = natToChars n ++ rest := by
  have hne := natToChars_ne_nil n
  match hcs : natToChars n with
  | [] => exact absurd hcs hne
  | c :: cs =>
    have hc := isDigit_not_ws_r c (natToChars_all_digits n c (by rw [hcs]; exact List.mem_cons_self ..))
    simp [List.cons_append, skipWsR_nonws c (cs ++ rest) hc]

/-! ## Core: Expression roundtrip with rest -/

set_option maxHeartbeats 1600000 in
/-- Core roundtrip lemma for Rust expressions: parsing the printed form of a
    well-formed expression with arbitrary safe remainder recovers the original. -/
theorem rustExpr_roundtrip_with_rest (e : MicroCExpr) (he : WFExprRust e)
    (hs : NegLitDisamRust e)
    (fuel : Nat) (hfuel : fuel ≥ rustExprDepth e)
    (rest : List Char) (hrest : ExprSafeR rest) :
    pRustExprF fuel ((microRustExprToString e).toList ++ rest) = some (e, rest) := by
  induction he generalizing fuel rest with
  | litInt n =>
    have h1 : fuel ≥ 1 := Nat.le_trans (rustExprDepth_pos (.litInt n)) hfuel
    have hfne : fuel ≠ 0 := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hfne
    by_cases hn : n < 0
    · -- Negative: print = "(-" ++ natToChars(n.natAbs) ++ ")"
      simp only [microRustExprToString_litInt, hn, ite_true,
        String.toList_append, String.toList_ofList, List.append_assoc,
        strR_lp, strR_rp, strR_dash, List.cons_append, List.nil_append]
      simp only [pRustExprF_paren]
      rw [skipWsR_nonws '-' _ ⟨by decide, by decide, by decide, by decide⟩]
      have hne := natToChars_ne_nil n.natAbs
      match hcs : natToChars n.natAbs with
      | [] => exact absurd hcs hne
      | c :: cs =>
        have hcd := natToChars_all_digits n.natAbs c (by rw [hcs]; exact List.mem_cons_self ..)
        simp only [List.cons_append]
        rw [pRustParenF_neg_digit k c (cs ++ ')' :: rest) hcd]
        rw [show c :: (cs ++ ')' :: rest) = (c :: cs) ++ ')' :: rest from by simp [List.cons_append]]
        rw [← hcs]
        rw [pNatR_natToChars n.natAbs (')' :: rest) (Or.inr ⟨')', rest, rfl, by native_decide⟩)]
        simp only []
        rw [skipWsR_nonws ')' rest ⟨by decide, by decide, by decide, by decide⟩]
        congr 1; congr 1
        match n, hn with
        | .negSucc m, _ => simp [Int.natAbs, Int.negSucc_eq]
    · -- Non-negative: print = natToChars(n.toNat)
      simp only [microRustExprToString_litInt, hn, ite_false, String.toList_ofList]
      have hne := natToChars_ne_nil n.toNat
      match hcs : natToChars n.toNat with
      | [] => exact absurd hcs hne
      | c :: cs =>
        have hcd := natToChars_all_digits n.toNat c (by rw [hcs]; exact List.mem_cons_self ..)
        simp only [List.cons_append]
        rw [pRustExprF_digit k c (cs ++ rest) hcd]
        rw [show c :: (cs ++ rest) = natToChars n.toNat ++ rest from by rw [hcs, List.cons_append]]
        rw [pNatR_natToChars n.toNat rest hrest.1]
        simp only []
        congr 1; congr 1; congr 1
        exact Int.toNat_of_nonneg (Int.not_lt.mp hn)
  | litBool b =>
    have h1 : fuel ≥ 1 := Nat.le_trans (rustExprDepth_pos (.litBool b)) hfuel
    have hfne : fuel ≠ 0 := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hfne
    cases b with
    | true =>
      have htl : ("true" : String).toList = ['t', 'r', 'u', 'e'] := by native_decide
      simp only [microRustExprToString_litBool_true, htl, List.cons_append, List.nil_append]
      have hnp : ∀ tail, 't' :: ('r' :: 'u' :: 'e' :: rest) ≠
          'p' :: 'o' :: 'w' :: 'e' :: 'r' :: '(' :: tail := by
        intro tail h; exact absurd (List.cons.inj h).1 (by decide)
      rw [pRustExprF_ident k 't' ('r' :: 'u' :: 'e' :: rest)
        (by native_decide) (Or.inl (by native_decide)) hnp]
      simp only [pRustExprF.pRustIdentF]
      rw [show ('t' :: 'r' :: 'u' :: 'e' :: rest) = "true".toList ++ rest from by
          simp [htl, List.cons_append, List.nil_append]]
      rw [pIdentR_exact "true" rest (by decide) (by simp [htl])
          (by intro c hc; simp [htl] at hc; rcases hc with rfl | rfl | rfl | rfl <;> decide)
          hrest.2.1]
      simp
    | false =>
      have hfl : ("false" : String).toList = ['f', 'a', 'l', 's', 'e'] := by native_decide
      simp only [microRustExprToString_litBool_false, hfl, List.cons_append, List.nil_append]
      have hnp : ∀ tail, 'f' :: ('a' :: 'l' :: 's' :: 'e' :: rest) ≠
          'p' :: 'o' :: 'w' :: 'e' :: 'r' :: '(' :: tail := by
        intro tail h; exact absurd (List.cons.inj h).1 (by decide)
      rw [pRustExprF_ident k 'f' ('a' :: 'l' :: 's' :: 'e' :: rest)
        (by native_decide) (Or.inl (by native_decide)) hnp]
      simp only [pRustExprF.pRustIdentF]
      rw [show ('f' :: 'a' :: 'l' :: 's' :: 'e' :: rest) = "false".toList ++ rest from by
          simp [hfl, List.cons_append, List.nil_append]]
      rw [pIdentR_exact "false" rest (by decide) (by simp [hfl])
          (by intro c hc; simp [hfl] at hc; rcases hc with rfl | rfl | rfl | rfl | rfl <;> decide)
          hrest.2.1]
      simp
  | varRef name hne hstart hcont hnot_kw =>
    have h1 : fuel ≥ 1 := Nat.le_trans (rustExprDepth_pos (.varRef name)) hfuel
    have hfne : fuel ≠ 0 := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hfne
    simp only [microRustExprToString_varRef]
    have hne' := toList_ne_nil_of_ne_empty_r name hne
    match hcs : name.toList with
    | [] => exact absurd hcs hne'
    | c :: cs =>
      have hhead := list_head_eq_of_cons_r hcs
      have hstart' := hstart; simp only [hhead] at hstart'
      have hcnd : c.isDigit = false := by
        cases hstart' with
        | inl h => exact isAlpha_not_digit c h
        | inr h => subst h; native_decide
      -- power( match impossible
      have hnp : ∀ tail, c :: (cs ++ rest) ≠
          'p' :: 'o' :: 'w' :: 'e' :: 'r' :: '(' :: tail := by
        intro tail heq
        have hce : c = 'p' := (List.cons.inj heq).1; subst hce
        have htl : cs ++ rest = 'o' :: 'w' :: 'e' :: 'r' :: '(' :: tail :=
          (List.cons.inj heq).2
        have hident : ∀ ch ∈ cs, ch.isAlpha = true ∨ ch.isDigit = true ∨ ch = '_' :=
          fun ch hmem => hcont ch (by rw [hcs]; exact List.mem_cons_of_mem _ hmem)
        -- Case split on length of cs. If short, ident chars spill into rest,
        -- contradicting ExprSafeR. If long, '(' appears in ident chars.
        match cs, htl with
        | [], htl =>
          simp at htl; rw [htl] at hrest
          cases hrest.2.1 with
          | inl h => simp at h
          | inr h =>
            obtain ⟨c', _, hc', hna, _, _⟩ := h
            have := (List.cons.inj hc').1; subst this
            exact absurd (show ('o' : Char).isAlpha = true from by native_decide) (by rw [hna]; decide)
        | [_], htl =>
          simp at htl; rw [htl.2] at hrest
          cases hrest.2.1 with
          | inl h => simp at h
          | inr h =>
            obtain ⟨c', _, hc', hna, _, _⟩ := h
            have := (List.cons.inj hc').1; subst this
            exact absurd (show ('w' : Char).isAlpha = true from by native_decide) (by rw [hna]; decide)
        | [_, _], htl =>
          simp at htl; rw [htl.2.2] at hrest
          cases hrest.2.1 with
          | inl h => simp at h
          | inr h =>
            obtain ⟨c', _, hc', hna, _, _⟩ := h
            have := (List.cons.inj hc').1; subst this
            exact absurd (show ('e' : Char).isAlpha = true from by native_decide) (by rw [hna]; decide)
        | [_, _, _], htl =>
          simp at htl; rw [htl.2.2.2] at hrest
          cases hrest.2.1 with
          | inl h => simp at h
          | inr h =>
            obtain ⟨c', _, hc', hna, _, _⟩ := h
            have := (List.cons.inj hc').1; subst this
            exact absurd (show ('r' : Char).isAlpha = true from by native_decide) (by rw [hna]; decide)
        | [_, _, _, _], htl =>
          simp at htl; rw [htl.2.2.2.2] at hrest
          have := hrest.2.2.2 tail
          simp [skipWsR] at this
        | a :: b :: c' :: d :: e5 :: cs5, htl =>
          simp at htl
          have h5 : e5 = '(' := htl.2.2.2.2.1; subst h5
          have hmem : '(' ∈ a :: b :: c' :: d :: '(' :: cs5 := by simp
          exact absurd (hident '(' hmem) (by
            intro h; rcases h with h | h | h
            · exact absurd h (by native_decide)
            · exact absurd h (by native_decide)
            · exact absurd h (by decide))
      show pRustExprF (k + 1) (c :: (cs ++ rest)) = some (MicroCExpr.varRef name, rest)
      rw [pRustExprF_ident k c (cs ++ rest) hcnd (by cases hstart' with
        | inl h => exact Or.inl h
        | inr h => exact Or.inr h) hnp]
      simp only [pRustExprF.pRustIdentF]
      have hpid : pIdentR (c :: (cs ++ rest)) = some (name, rest) := by
        have harg : c :: (cs ++ rest) = name.toList ++ rest := by rw [hcs]; rfl
        rw [harg]; exact pIdentR_exact name rest hne hstart hcont hrest.2.1
      simp only [hpid]
      simp [hnot_kw.1, hnot_kw.2]
      -- Check for '[' and '(' in skipWsR rest
      have ⟨hno_bracket, hno_paren⟩ := hrest.2.2
      generalize hsr : skipWsR rest = sr at hno_bracket hno_paren
      cases sr with
      | nil => simp [hsr]
      | cons c' cs' =>
        by_cases h : c' = '['
        · subst h; exact absurd rfl (hno_bracket cs')
        · by_cases hp : c' = '('
          · subst hp; exact absurd rfl (hno_paren cs')
          · simp [hsr, h, hp]
  | binOp op lhs rhs h_l h_r ih_l ih_r =>
    -- Setup fuel
    have h1 : fuel ≥ 1 := Nat.le_trans (rustExprDepth_pos (.binOp op lhs rhs)) hfuel
    have hfne : fuel ≠ 0 := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hfne
    have hfuel_l : k ≥ rustExprDepth lhs := by
      simp only [rustExprDepth] at hfuel
      have := Nat.le_max_left (rustExprDepth lhs) (rustExprDepth rhs); omega
    have hfuel_r : k ≥ rustExprDepth rhs := by
      simp only [rustExprDepth] at hfuel
      have := Nat.le_max_right (rustExprDepth lhs) (rustExprDepth rhs); omega
    -- NegLitDisam
    have hs_l : NegLitDisamRust lhs := hs.1
    have hs_r : NegLitDisamRust rhs := hs.2
    -- Expand printed form and normalize string literals
    simp only [microRustExprToString_binOp, String.toList_append, List.append_assoc,
      strR_lp, strR_rp, strR_sp, List.cons_append, List.nil_append]
    -- Dispatch: pRustExprF (k+1) ('(' :: ...) → pRustParenF k (skipWsR ...)
    simp only [pRustExprF_paren]
    -- Handle skipWsR of print(lhs) ++ mid_rest
    have h_ne_l := rustPrint_ne_nil lhs h_l
    match h_head_l : (microRustExprToString lhs).toList with
    | [] => exact absurd h_head_l h_ne_l
    | c_l :: cs_l =>
      -- skipWsR (c_l :: cs_l ++ ...) = c_l :: cs_l ++ ... (c_l is non-ws)
      have h_nonws_l := rustPrint_first_nonws lhs h_l c_l cs_l h_head_l
      have ⟨h_not_neg_l, h_not_bang_l⟩ := rustPrint_first_not_neg_bang lhs h_l c_l cs_l h_head_l
      -- mid_rest = ' ' :: opStr ++ ' ' :: print(rhs) ++ ')' :: rest
      let mid := (' ' :: (microRustBinOpToString op).toList ++
        (' ' :: (microRustExprToString rhs).toList ++ (')' :: rest)))
      simp only [List.cons_append]
      rw [skipWsR_nonws c_l _ h_nonws_l]
      -- Fallthrough: first char c_l is not '!' or '-'
      rw [pRustParenF_fallthrough k c_l _ h_not_bang_l h_not_neg_l]
      -- Apply IH_l: parse lhs
      have h_safe_mid : ExprSafeR mid :=
        exprSafeR_binop_mid op (microRustExprToString rhs).toList rest
      simp only [← List.cons_append, ← h_head_l]
      rw [ih_l hs_l k hfuel_l mid h_safe_mid]
      simp only []
      -- Now handle pBinOpR (skipWsR mid)
      have h_ne_r := rustPrint_ne_nil rhs h_r
      match h_head_r : (microRustExprToString rhs).toList with
      | [] => exact absurd h_head_r h_ne_r
      | c_r :: cs_r =>
        have h_nonws_r := rustPrint_first_nonws rhs h_r c_r cs_r h_head_r
        have h_skipWsR_mid : skipWsR mid =
            (microRustBinOpToString op).toList ++ (' ' :: c_r :: (cs_r ++ (')' :: rest))) := by
          show skipWsR (' ' :: (microRustBinOpToString op).toList ++
            (' ' :: (microRustExprToString rhs).toList ++ (')' :: rest))) = _
          rw [h_head_r]
          cases op <;> simp [microRustBinOpToString, skipWsR]
        rw [h_skipWsR_mid]
        -- Apply pBinOpR_roundtrip
        have h_pBinOpR : pBinOpR ((microRustBinOpToString op).toList ++ (' ' :: c_r :: (cs_r ++ (')' :: rest)))) =
            some (op, c_r :: (cs_r ++ (')' :: rest))) := by
          exact pBinOpR_roundtrip op (c_r :: (cs_r ++ (')' :: rest)))
            (fun c' cs' h => by rw [List.cons.injEq] at h; rw [← h.1]; exact h_nonws_r)
        -- Apply IH_r: parse rhs with ExprSafeR (')' :: rest)
        have h_eq_r : pRustExprF k (c_r :: (cs_r ++ (')' :: rest))) =
            pRustExprF k ((microRustExprToString rhs).toList ++ (')' :: rest)) :=
          congrArg (pRustExprF k) (by simp [h_head_r])
        have h_ih_r := ih_r hs_r k hfuel_r (')' :: rest) (exprSafeR_rparen rest)
        -- Dispatch: op first char is not 'a', so cast branches don't match
        cases op <;> simp only [microRustBinOpToString, List.cons_append, List.nil_append,
          toList_add_op, toList_sub_op, toList_mul_op, toList_eq_op, toList_lt_op,
          toList_land_op, toList_lor_op, toList_band_op, toList_bor_op,
          toList_bxor_op, toList_bshl_op, toList_bshr_op] at h_pBinOpR ⊢ <;> (
          simp only [h_pBinOpR]
          rw [h_eq_r, h_ih_r]
          simp [skipWsR])
  | unaryOp op e h_e ih_e =>
    -- Setup fuel
    have h1 : fuel ≥ 1 := Nat.le_trans (rustExprDepth_pos (.unaryOp op e)) hfuel
    have hfne : fuel ≠ 0 := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hfne
    have hfuel_e : k ≥ rustExprDepth e := by simp only [rustExprDepth] at hfuel; omega
    cases op with
    | lnot =>
      -- print = "(!" ++ print(e) ++ ")"
      simp only [microRustExprToString_unaryOp_lnot, String.toList_append,
        List.append_assoc, strR_lp, strR_rp, strR_bang, List.cons_append, List.nil_append]
      simp only [pRustExprF_paren]
      -- skipWsR ('!' :: print(e) ++ ')' :: rest) = '!' :: print(e) ++ ')' :: rest
      simp [skipWsR]
      rw [pRustParenF_lnot]
      -- Apply IH
      rw [ih_e hs k hfuel_e (')' :: rest) (exprSafeR_rparen rest)]
      simp [skipWsR]
    | neg =>
      -- NegLitDisam gives (∀ n, n ≥ 0 → e ≠ .litInt n) ∧ NegLitDisamRust e
      have ⟨h_not_lit, hs_e⟩ := hs
      -- print = "(-" ++ print(e) ++ ")"
      simp only [microRustExprToString_unaryOp_neg, String.toList_append,
        List.append_assoc, strR_lp, strR_rp, strR_dash, List.cons_append, List.nil_append]
      simp only [pRustExprF_paren]
      -- skipWsR ('-' :: print(e) ++ ')' :: rest) = '-' :: print(e) ++ ')' :: rest
      simp [skipWsR]
      -- pRustParenF sees '-' :: first_char_of_print(e) :: ...
      -- Need to show first_char_of_print(e) is NOT a digit
      have h_ne_e := rustPrint_ne_nil e h_e
      match h_head_e : (microRustExprToString e).toList with
      | [] => exact absurd h_head_e h_ne_e
      | c_e :: cs_e =>
        have h_not_digit : c_e.isDigit = false := by
          match hd : c_e.isDigit with
          | false => rfl
          | true =>
            exfalso
            cases h_e with
            | litInt n =>
              simp [microRustExprToString_litInt] at h_head_e
              split at h_head_e
              · simp [String.toList_append] at h_head_e
                obtain ⟨rfl, _⟩ := h_head_e
                simp [Char.isDigit] at hd
                exact absurd hd (by native_decide)
              · exact absurd rfl (h_not_lit n (by omega))
            | litBool b =>
              cases b <;> simp [microRustExprToString] at h_head_e <;>
                obtain ⟨rfl, _⟩ := h_head_e <;> simp [Char.isDigit] at hd <;>
                exact absurd hd (by native_decide)
            | varRef name hne_v hstart_v _ _ =>
              simp [microRustExprToString_varRef] at h_head_e
              have hne_v' := toList_ne_nil_of_ne_empty_r name hne_v
              match hcs : name.toList with
              | [] => exact absurd hcs hne_v'
              | c' :: _ =>
                have hhead := list_head_eq_of_cons_r hcs
                have hst := hstart_v; simp only [hhead] at hst
                rw [hcs] at h_head_e; simp at h_head_e; rw [← h_head_e.1] at hd
                cases hst with
                | inl h => exact absurd hd (by rw [isAlpha_not_digit c' h]; decide)
                | inr h => subst h; simp [Char.isDigit] at hd
            | binOp _ _ _ _ _ =>
              simp [microRustExprToString_binOp, String.toList_append] at h_head_e
              obtain ⟨rfl, _⟩ := h_head_e; simp [Char.isDigit] at hd
            | unaryOp op' _ _ =>
              cases op' <;> (
                simp only [microRustExprToString_unaryOp_neg,
                  microRustExprToString_unaryOp_lnot, microRustExprToString_unaryOp_widen,
                  microRustExprToString_unaryOp_trunc] at h_head_e
                simp only [String.toList_append] at h_head_e
                obtain ⟨rfl, _⟩ := h_head_e
                exact absurd hd (by native_decide))
            | powCall _ _ _ =>
              simp [microRustExprToString_powCall, String.toList_append] at h_head_e
              obtain ⟨rfl, _⟩ := h_head_e; simp [Char.isDigit] at hd
            | arrayAccess _ _ hb _ hbv =>
              obtain ⟨vname, rfl⟩ := hbv
              simp [microRustExprToString_arrayAccess, microRustExprToString_varRef] at h_head_e
              cases hb with
              | varRef _ hne_vv hstart_vv _ _ =>
                have hne_vv' := toList_ne_nil_of_ne_empty_r vname hne_vv
                match hcs_v : vname.toList with
                | [] => exact absurd hcs_v hne_vv'
                | cv :: _ =>
                  have hhead_v := list_head_eq_of_cons_r hcs_v
                  have hst := hstart_vv; simp only [hhead_v] at hst
                  simp [hcs_v] at h_head_e; rw [← h_head_e.1] at hd
                  cases hst with
                  | inl h => exact absurd hd (by rw [isAlpha_not_digit cv h]; decide)
                  | inr h => subst h; simp [Char.isDigit] at hd
        simp only [List.cons_append]
        rw [pRustParenF_neg_nondigit k c_e (cs_e ++ (')' :: rest)) h_not_digit]
        -- Apply IH: rewrite c_e :: cs_e back to toList for IH
        simp only [← List.cons_append, ← h_head_e]
        rw [ih_e hs_e k hfuel_e (')' :: rest) (exprSafeR_rparen rest)]
        simp [skipWsR]
    | widen32to64 =>
      -- print = "(" ++ print(e) ++ " as i64)"
      simp only [microRustExprToString_unaryOp_widen, String.toList_append,
        List.append_assoc, strR_lp, strR_as_i64_rp, List.cons_append, List.nil_append]
      simp only [pRustExprF_paren]
      -- First char of print(e) is non-ws and not '!' or '-'
      have h_ne_e := rustPrint_ne_nil e h_e
      match h_head_e : (microRustExprToString e).toList with
      | [] => exact absurd h_head_e h_ne_e
      | c_e :: cs_e =>
        have h_nonws_e := rustPrint_first_nonws e h_e c_e cs_e h_head_e
        have ⟨h_not_neg_e, h_not_bang_e⟩ := rustPrint_first_not_neg_bang e h_e c_e cs_e h_head_e
        simp only [List.cons_append]
        rw [skipWsR_nonws c_e _ h_nonws_e]
        rw [pRustParenF_fallthrough k c_e _ h_not_bang_e h_not_neg_e]
        -- Apply IH for e with ExprSafeR for " as i64)" ++ rest
        have h_safe : ExprSafeR (' ' :: 'a' :: 's' :: ' ' :: 'i' :: '6' :: '4' :: ')' :: rest) :=
          ⟨Or.inr ⟨' ', _, rfl, by native_decide⟩,
           Or.inr ⟨' ', _, rfl, by native_decide, by native_decide, by decide⟩,
           by intro cs h; simp [skipWsR] at h,
           by intro cs h; simp [skipWsR] at h⟩
        simp only [← List.cons_append, ← h_head_e]
        rw [ih_e hs k hfuel_e _ h_safe]
        simp only []
        -- skipWsR (' ' :: 'a' :: ...) skips the space, then 'a' is non-ws
        simp [skipWsR]
    | trunc64to32 =>
      -- print = "(" ++ print(e) ++ " as i32)"
      simp only [microRustExprToString_unaryOp_trunc, String.toList_append,
        List.append_assoc, strR_lp, strR_as_i32_rp, List.cons_append, List.nil_append]
      simp only [pRustExprF_paren]
      have h_ne_e := rustPrint_ne_nil e h_e
      match h_head_e : (microRustExprToString e).toList with
      | [] => exact absurd h_head_e h_ne_e
      | c_e :: cs_e =>
        have h_nonws_e := rustPrint_first_nonws e h_e c_e cs_e h_head_e
        have ⟨h_not_neg_e, h_not_bang_e⟩ := rustPrint_first_not_neg_bang e h_e c_e cs_e h_head_e
        simp only [List.cons_append]
        rw [skipWsR_nonws c_e _ h_nonws_e]
        rw [pRustParenF_fallthrough k c_e _ h_not_bang_e h_not_neg_e]
        have h_safe : ExprSafeR (' ' :: 'a' :: 's' :: ' ' :: 'i' :: '3' :: '2' :: ')' :: rest) :=
          ⟨Or.inr ⟨' ', _, rfl, by native_decide⟩,
           Or.inr ⟨' ', _, rfl, by native_decide, by native_decide, by decide⟩,
           by intro cs h; simp [skipWsR] at h,
           by intro cs h; simp [skipWsR] at h⟩
        simp only [← List.cons_append, ← h_head_e]
        rw [ih_e hs k hfuel_e _ h_safe]
        simp only []
        simp [skipWsR]
  | powCall base n h_base ih_base =>
    -- Setup fuel
    have h1 : fuel ≥ 1 := Nat.le_trans (rustExprDepth_pos (.powCall base n)) hfuel
    have hfne : fuel ≠ 0 := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hfne
    have hfuel_b : k ≥ rustExprDepth base := by simp only [rustExprDepth] at hfuel; omega
    -- print = "power(" ++ print(base) ++ ", " ++ natToChars(n) ++ ")"
    simp only [microRustExprToString_powCall, String.toList_append, List.append_assoc,
      strR_power_lp, strR_rp, strR_comma_sp, String.toList_ofList, List.cons_append, List.nil_append]
    -- pRustExprF at fuel+1: dispatch to pRustPowF
    simp only [pRustExprF_power]
    -- skipWsR of print(base) ++ ...
    have h_ne_b := rustPrint_ne_nil base h_base
    match h_head_b : (microRustExprToString base).toList with
    | [] => exact absurd h_head_b h_ne_b
    | c_b :: cs_b =>
      have h_nonws_b := rustPrint_first_nonws base h_base c_b cs_b h_head_b
      simp only [List.cons_append]
      rw [skipWsR_nonws c_b _ h_nonws_b]
      -- Apply IH for base with ExprSafeR (',' :: ...)
      simp only [pRustExprF.pRustPowF]
      have h_eq_b : pRustExprF k (c_b :: (cs_b ++ (',' :: ' ' :: (natToChars n ++ (')' :: rest))))) =
          pRustExprF k ((microRustExprToString base).toList ++ (',' :: ' ' :: (natToChars n ++ (')' :: rest)))) :=
        congrArg (pRustExprF k) (by simp [h_head_b])
      have h_ih_b := ih_base hs k hfuel_b (',' :: ' ' :: (natToChars n ++ (')' :: rest)))
        (exprSafeR_comma (' ' :: (natToChars n ++ (')' :: rest))))
      rw [h_eq_b, h_ih_b]
      simp only []
      -- skipWsR (',' :: ...) = ',' :: ...
      simp [skipWsR]
      -- pNatR on natToChars n
      rw [skipWsR_natToChars n (')' :: rest)]
      rw [pNatR_natToChars n (')' :: rest) (Or.inr ⟨')', rest, rfl, by native_decide⟩)]
      simp [skipWsR]
  | arrayAccess base idx h_base h_idx hbase_var ih_base ih_idx =>
    -- Extract vname; base must be a varRef
    obtain ⟨vname, rfl⟩ := hbase_var
    cases h_base with
    | varRef _ hne hstart hcont hnot_kw =>
    have hs_idx : NegLitDisamRust idx := hs.2
    -- Fuel setup
    have h1 : fuel ≥ 1 := Nat.le_trans (rustExprDepth_pos (.arrayAccess (.varRef vname) idx)) hfuel
    have hfne : fuel ≠ 0 := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hfne
    have hfuel_idx : k ≥ rustExprDepth idx := by simp only [rustExprDepth] at hfuel; omega
    -- Unfold printer: vname ++ "[" ++ print(idx) ++ " as usize]" ++ rest
    simp only [microRustExprToString_arrayAccess, microRustExprToString_varRef,
      String.toList_append, List.append_assoc,
      strR_lb, strR_as_usize_rb,
      String.toList_ofList, List.cons_append, List.nil_append]
    -- Destructure vname.toList
    have hne' := toList_ne_nil_of_ne_empty_r vname hne
    match hcs : vname.toList with
    | [] => exact absurd hcs hne'
    | c :: cs =>
      have hhead := list_head_eq_of_cons_r hcs
      have hstart' := hstart; simp only [hhead] at hstart'
      have hcnd : c.isDigit = false := by
        cases hstart' with
        | inl h => exact isAlpha_not_digit c h
        | inr h => subst h; native_decide
      -- power( match impossible
      have hnp : ∀ tail, c :: (cs ++ ('[' :: ((microRustExprToString idx).toList ++
          (' ' :: 'a' :: 's' :: ' ' :: 'u' :: 's' :: 'i' :: 'z' :: 'e' :: ']' :: rest)))) ≠
          'p' :: 'o' :: 'w' :: 'e' :: 'r' :: '(' :: tail := by
        intro tail heq
        have hident : ∀ ch ∈ cs, ch.isAlpha = true ∨ ch.isDigit = true ∨ ch = '_' := by
          intro ch hmem; exact hcont ch (by rw [hcs]; exact List.mem_cons_of_mem c hmem)
        have hce : c = 'p' := (List.cons.inj heq).1; subst hce
        have htl : cs ++ ('[' :: ((microRustExprToString idx).toList ++
            (' ' :: 'a' :: 's' :: ' ' :: 'u' :: 's' :: 'i' :: 'z' :: 'e' :: ']' :: rest))) =
            'o' :: 'w' :: 'e' :: 'r' :: '(' :: tail := (List.cons.inj heq).2
        -- '[' is not a valid ident char and not '('
        -- Prove by case analysis on |cs|
        -- rest_full starts with '[' which is not alpha/digit/underscore or '('
        -- Short cs: 'ower(' spills into rest_full starting with '[', but '[' ≠ expected letter
        -- Long cs: '(' appears among ident chars, contradiction
        -- Use omega/simp to close each case. simp at htl closes most short cases directly.
        match cs, htl with
        | [], htl => simp at htl
        | [_], htl => simp at htl
        | [_, _], htl => simp at htl
        | [_, _, _], htl => simp at htl
        | [_, _, _, _], htl => simp at htl
        | a :: b :: c' :: d :: e5 :: cs5, htl =>
          simp at htl
          have h5 : e5 = '(' := htl.2.2.2.2.1; subst h5
          have hmem : '(' ∈ a :: b :: c' :: d :: '(' :: cs5 := by simp
          exact absurd (hident '(' hmem) (by
            intro h; rcases h with h | h | h
            · exact absurd h (by native_decide)
            · exact absurd h (by native_decide)
            · exact absurd h (by decide))
      show pRustExprF (k + 1) (c :: (cs ++ ('[' :: ((microRustExprToString idx).toList ++
          (' ' :: 'a' :: 's' :: ' ' :: 'u' :: 's' :: 'i' :: 'z' :: 'e' :: ']' :: rest))))) =
          some (MicroCExpr.arrayAccess (MicroCExpr.varRef vname) idx, rest)
      rw [pRustExprF_ident k c _ hcnd (by cases hstart' with
        | inl h => exact Or.inl h
        | inr h => exact Or.inr h) hnp]
      simp only [pRustExprF.pRustIdentF]
      -- pIdentR parses vname, leaving '[' :: print(idx) ++ " as usize]" :: rest
      have h_nli : NoLeadingIdentR ('[' :: ((microRustExprToString idx).toList ++
          (' ' :: 'a' :: 's' :: ' ' :: 'u' :: 's' :: 'i' :: 'z' :: 'e' :: ']' :: rest))) :=
        Or.inr ⟨'[', _, rfl, by native_decide, by native_decide, by decide⟩
      have hpid : pIdentR (c :: (cs ++ ('[' :: ((microRustExprToString idx).toList ++
          (' ' :: 'a' :: 's' :: ' ' :: 'u' :: 's' :: 'i' :: 'z' :: 'e' :: ']' :: rest))))) =
          some (vname, '[' :: ((microRustExprToString idx).toList ++
          (' ' :: 'a' :: 's' :: ' ' :: 'u' :: 's' :: 'i' :: 'z' :: 'e' :: ']' :: rest))) := by
        have harg : c :: (cs ++ ('[' :: ((microRustExprToString idx).toList ++
            (' ' :: 'a' :: 's' :: ' ' :: 'u' :: 's' :: 'i' :: 'z' :: 'e' :: ']' :: rest)))) =
            vname.toList ++ ('[' :: ((microRustExprToString idx).toList ++
            (' ' :: 'a' :: 's' :: ' ' :: 'u' :: 's' :: 'i' :: 'z' :: 'e' :: ']' :: rest))) := by
          rw [hcs]; rfl
        rw [harg]; exact pIdentR_exact vname _ hne hstart hcont h_nli
      simp only [hpid]
      simp [hnot_kw.1, hnot_kw.2]
      -- skipWsR ('[' :: ...) = '[' :: ... (non-ws)
      -- The ident match already led us to pRustIdentF which has the '[' branch
      -- Now inside '[' branch: parse idx expression
      have h_ne_idx := rustPrint_ne_nil idx h_idx
      match h_head_idx : (microRustExprToString idx).toList with
      | [] => exact absurd h_head_idx h_ne_idx
      | c_i :: cs_i =>
        have h_nonws_idx := rustPrint_first_nonws idx h_idx c_i cs_i h_head_idx
        simp only [List.cons_append]
        rw [skipWsR_nonws c_i _ h_nonws_idx]
        -- Apply IH for idx with rest = " as usize]" ++ rest
        -- Need ExprSafeR for " as usize]" ++ rest
        have h_safe_as : ExprSafeR
            (' ' :: 'a' :: 's' :: ' ' :: 'u' :: 's' :: 'i' :: 'z' :: 'e' :: ']' :: rest) :=
          ⟨Or.inr ⟨' ', _, rfl, by native_decide⟩,
           Or.inr ⟨' ', _, rfl, by native_decide, by native_decide, by decide⟩,
           by intro cs h; simp [skipWsR] at h,
           by intro cs h; simp [skipWsR] at h⟩
        have h_eq_idx : pRustExprF k (c_i :: (cs_i ++
            (' ' :: 'a' :: 's' :: ' ' :: 'u' :: 's' :: 'i' :: 'z' :: 'e' :: ']' :: rest))) =
            pRustExprF k ((microRustExprToString idx).toList ++
            (' ' :: 'a' :: 's' :: ' ' :: 'u' :: 's' :: 'i' :: 'z' :: 'e' :: ']' :: rest)) :=
          congrArg (pRustExprF k) (by simp [h_head_idx])
        have h_ih_idx := ih_idx hs_idx k hfuel_idx
          (' ' :: 'a' :: 's' :: ' ' :: 'u' :: 's' :: 'i' :: 'z' :: 'e' :: ']' :: rest)
          h_safe_as
        rw [h_eq_idx, h_ih_idx]
        simp only []
        -- skipWsR (' ' :: 'a' :: 's' :: ...) = 'a' :: 's' :: ...
        -- Then matchLiteral "as usize]" matches
        simp [skipWsR]
        -- matchLiteral on "as usize]" prefix
        have hml : matchLiteral ['a', 's', ' ', 'u', 's', 'i', 'z', 'e', ']']
            ('a' :: 's' :: ' ' :: 'u' :: 's' :: 'i' :: 'z' :: 'e' :: ']' :: rest) =
            some rest := by
          have := matchLiteral_exact ['a', 's', ' ', 'u', 's', 'i', 'z', 'e', ']'] rest
          convert this using 2
        rw [hml]

/-! ## Top-Level Expression Roundtrip Theorem -/

/-- Expression roundtrip for Rust: parsing the printed form of a well-formed
    expression recovers the original. -/
theorem parseMicroRustExpr_roundtrip (e : MicroCExpr) (he : WFExprRust e)
    (hs : NegLitDisamRust e) :
    parseMicroRustExpr (microRustExprToString e) = some e := by
  simp only [parseMicroRustExpr]
  have hfuel : (microRustExprToString e).toList.length + 1 ≥ rustExprDepth e :=
    rustExprDepth_le_length e he
  have h := rustExpr_roundtrip_with_rest e he hs
    ((microRustExprToString e).toList.length + 1) hfuel [] exprSafeR_nil
  simp only [List.append_nil] at h
  rw [h]; simp [skipWsR]

/-! ## Non-Vacuity -/

/-- Non-vacuity: litInt roundtrip for positive, negative, and zero. -/
example : parseMicroRustExpr (microRustExprToString (.litInt 42)) = some (.litInt 42) := by native_decide
example : parseMicroRustExpr (microRustExprToString (.litInt (-7))) = some (.litInt (-7)) := by native_decide
example : parseMicroRustExpr (microRustExprToString (.litInt 0)) = some (.litInt 0) := by native_decide

/-- Non-vacuity: binOp roundtrip with nested expressions. -/
example : parseMicroRustExpr (microRustExprToString
    (.binOp .add (.binOp .mul (.varRef "x") (.varRef "y")) (.litInt 1)))
    = some (.binOp .add (.binOp .mul (.varRef "x") (.varRef "y")) (.litInt 1)) := by native_decide

/-- Non-vacuity: cast roundtrip (widen). -/
example : parseMicroRustExpr (microRustExprToString (.unaryOp .widen32to64 (.varRef "x")))
    = some (.unaryOp .widen32to64 (.varRef "x")) := by native_decide

/-- Non-vacuity: cast roundtrip (trunc). -/
example : parseMicroRustExpr (microRustExprToString (.unaryOp .trunc64to32 (.varRef "x")))
    = some (.unaryOp .trunc64to32 (.varRef "x")) := by native_decide

/-- Non-vacuity: arrayAccess roundtrip (Rust as usize syntax). -/
example : parseMicroRustExpr (microRustExprToString (.arrayAccess (.varRef "a") (.varRef "i")))
    = some (.arrayAccess (.varRef "a") (.varRef "i")) := by native_decide

/-- Non-vacuity: powCall roundtrip. -/
example : parseMicroRustExpr (microRustExprToString (.powCall (.varRef "b") 3))
    = some (.powCall (.varRef "b") 3) := by native_decide

/-- Non-vacuity: bitwise ops roundtrip. -/
example : parseMicroRustExpr (microRustExprToString
    (.binOp .bxor (.binOp .band (.varRef "x") (.litInt 255)) (.varRef "y")))
    = some (.binOp .bxor (.binOp .band (.varRef "x") (.litInt 255)) (.varRef "y")) := by native_decide

end TrustLean
