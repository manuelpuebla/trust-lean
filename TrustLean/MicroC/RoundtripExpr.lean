/-
  Trust-Lean — Verified Code Generation Framework
  MicroC/RoundtripExpr.lean: Expression roundtrip proof (v3.0.0)

  N16.1: CRIT — proves ∀ e, WFExpr e → NegLitDisam e →
    parseMicroCExpr(microCExprToString e) = some e
  by structural induction on WFExpr.

  Strategy: "with-remainder" lemma
    pExprF fuel (print(e).toList ++ rest) = some (e, rest)
  for sufficient fuel and safe rest. Top-level theorem follows with rest=[].

  Key insight: NegLitDisam excludes .unaryOp .neg (.litInt n) when n ≥ 0,
  which is ambiguous (prints as "(-N)" same as .litInt (-N)).
-/

import TrustLean.MicroC.Roundtrip

set_option autoImplicit false

namespace TrustLean

/-! ## Definitions -/

/-- Expression depth: minimum fuel for pExprF to parse the expression. -/
def exprDepth : MicroCExpr → Nat
  | .litInt _ | .litBool _ | .varRef _ => 1
  | .binOp _ l r => 1 + max (exprDepth l) (exprDepth r)
  | .unaryOp _ e => 1 + exprDepth e
  | .powCall base _ => 1 + exprDepth base
  | .arrayAccess base idx => 1 + max (exprDepth base) (exprDepth idx)

theorem exprDepth_pos (e : MicroCExpr) : exprDepth e ≥ 1 := by
  cases e <;> simp [exprDepth] <;> omega

/-- Disambiguation predicate: no neg(litInt n) with n ≥ 0 in any sub-expression.
    Such expressions are ambiguous: "(-5)" parses as litInt(-5), not neg(litInt 5). -/
def NegLitDisam : MicroCExpr → Prop
  | .litInt _ | .litBool _ | .varRef _ => True
  | .binOp _ l r => NegLitDisam l ∧ NegLitDisam r
  | .unaryOp .neg e => (∀ n : Int, n ≥ 0 → e ≠ .litInt n) ∧ NegLitDisam e
  | .unaryOp .lnot e => NegLitDisam e
  | .powCall base _ => NegLitDisam base
  | .arrayAccess base idx => NegLitDisam base ∧ NegLitDisam idx

/-- Safe rest condition: remaining characters after an expression won't extend
    the parsed token (no leading digit, ident char, or bracket after whitespace). -/
def ExprSafe (rest : List Char) : Prop :=
  NoLeadingDigit rest ∧ NoLeadingIdent rest ∧
  (∀ cs, skipWs rest ≠ '[' :: cs) ∧ (∀ cs, skipWs rest ≠ '(' :: cs)

/-! ## ExprSafe instances -/

theorem exprSafe_nil : ExprSafe ([] : List Char) :=
  ⟨Or.inl rfl, Or.inl rfl, by intro cs; simp [skipWs], by intro cs; simp [skipWs]⟩

theorem exprSafe_sep (c : Char) (rest : List Char)
    (hna : c.isAlpha = false) (hnd : c.isDigit = false)
    (hnu : c ≠ '_') (hnb : c ≠ '[') (hnp : c ≠ '(')
    (hnws : c ≠ ' ' ∧ c ≠ '\n' ∧ c ≠ '\t' ∧ c ≠ '\r') :
    ExprSafe (c :: rest) := by
  refine ⟨Or.inr ⟨c, rest, rfl, hnd⟩, Or.inr ⟨c, rest, rfl, hna, hnd, hnu⟩, ?_, ?_⟩
  · intro cs h; rw [skipWs_nonws c rest hnws] at h
    rw [List.cons.injEq] at h; exact absurd h.1 hnb
  · intro cs h; rw [skipWs_nonws c rest hnws] at h
    rw [List.cons.injEq] at h; exact absurd h.1 hnp

theorem exprSafe_rparen (rest : List Char) : ExprSafe (')' :: rest) :=
  exprSafe_sep ')' rest (by native_decide) (by native_decide) (by decide)
    (by decide) (by decide) ⟨by decide, by decide, by decide, by decide⟩

theorem exprSafe_rbracket (rest : List Char) : ExprSafe (']' :: rest) :=
  exprSafe_sep ']' rest (by native_decide) (by native_decide) (by decide)
    (by decide) (by decide) ⟨by decide, by decide, by decide, by decide⟩

theorem exprSafe_comma (rest : List Char) : ExprSafe (',' :: rest) :=
  exprSafe_sep ',' rest (by native_decide) (by native_decide) (by decide)
    (by decide) (by decide) ⟨by decide, by decide, by decide, by decide⟩

/-! ## Char property helpers -/

/-- Alpha chars are never digits (disjoint UInt32 ranges). -/
private theorem isAlpha_not_isDigit (c : Char) (h : c.isAlpha = true) : c.isDigit = false := by
  match hd : c.isDigit with
  | false => rfl
  | true =>
    exfalso
    simp only [Char.isAlpha, Char.isUpper, Char.isLower, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at hd
    obtain ⟨_, hd2⟩ := hd
    have hd2n : c.val.toNat ≤ 57 := by exact_mod_cast hd2
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
    · have h1n : c.val.toNat ≥ 65 := by exact_mod_cast h1
      omega
    · have h1n : c.val.toNat ≥ 97 := by exact_mod_cast h1
      omega

/-- Digit chars are not whitespace. -/
private theorem isDigit_not_ws (c : Char) (h : c.isDigit = true) :
    c ≠ ' ' ∧ c ≠ '\n' ∧ c ≠ '\t' ∧ c ≠ '\r' :=
  ⟨by intro h'; subst h'; simp [Char.isDigit] at h,
   by intro h'; subst h'; simp [Char.isDigit] at h,
   by intro h'; subst h'; simp [Char.isDigit] at h,
   by intro h'; subst h'; simp [Char.isDigit] at h⟩

/-- Alpha chars are not whitespace. -/
private theorem isAlpha_not_ws (c : Char) (h : c.isAlpha = true) :
    c ≠ ' ' ∧ c ≠ '\n' ∧ c ≠ '\t' ∧ c ≠ '\r' :=
  ⟨by intro h'; subst h'; simp [Char.isAlpha] at h,
   by intro h'; subst h'; simp [Char.isAlpha] at h,
   by intro h'; subst h'; simp [Char.isAlpha] at h,
   by intro h'; subst h'; simp [Char.isAlpha] at h⟩

/-- String.toList preserves non-empty. -/
private theorem toList_ne_nil_of_ne_empty (s : String) (h : s ≠ "") : s.toList ≠ [] := by
  intro heq; exact h (by rw [← @String.ofList_toList s, heq])

/-! ## List.head helper -/

/-- Extracting the head from a cons-equal list. Used to simplify
    WFExpr's hstart which contains a `let c := l.head _; ...` binding. -/
private theorem list_head_eq_of_cons {l : List Char} {c : Char} {cs : List Char}
    (h : l = c :: cs) : ∀ (hne : l ≠ []), l.head hne = c := by
  intro hne; subst h; rfl

/-! ## Helper: skipWs on printed expressions -/

private theorem natToChars_head_nonws (n : Nat) :
    ∀ c ∈ natToChars n, c ≠ ' ' ∧ c ≠ '\n' ∧ c ≠ '\t' ∧ c ≠ '\r' := by
  intro c hc; exact isDigit_not_ws c (natToChars_all_digits n c hc)

private theorem skipWs_natToChars (n : Nat) (rest : List Char) :
    skipWs (natToChars n ++ rest) = natToChars n ++ rest := by
  have hne := natToChars_ne_nil n
  match hcs : natToChars n with
  | [] => exact absurd hcs hne
  | c :: cs =>
    have hc := natToChars_head_nonws n c (by rw [hcs]; exact List.mem_cons_self ..)
    simp [List.cons_append, skipWs_nonws c (cs ++ rest) hc]

/-! ## Helper: pBinOp roundtrip -/

/-- pBinOp correctly parses the operator string followed by a space and non-ws content. -/
theorem pBinOp_roundtrip (op : MicroCBinOp) (c : Char) (cs : List Char)
    (hc : c ≠ ' ' ∧ c ≠ '\n' ∧ c ≠ '\t' ∧ c ≠ '\r') :
    pBinOp ((microCBinOpToString op).toList ++ (' ' :: c :: cs)) = some (op, c :: cs) := by
  have hskip : skipWs (' ' :: c :: cs) = c :: cs := by
    simp [skipWs, skipWs_nonws c cs hc]
  cases op <;> simp only [microCBinOpToString] <;> (
    first
    | change pBinOp ('+' :: ' ' :: c :: cs) = _
    | change pBinOp ('-' :: ' ' :: c :: cs) = _
    | change pBinOp ('*' :: ' ' :: c :: cs) = _
    | change pBinOp ('=' :: '=' :: ' ' :: c :: cs) = _
    | change pBinOp ('<' :: ' ' :: c :: cs) = _
    | change pBinOp ('&' :: '&' :: ' ' :: c :: cs) = _
    | change pBinOp ('|' :: '|' :: ' ' :: c :: cs) = _
  ) <;> simp [pBinOp, hskip]

/-! ## Helper: ExprSafe for binOp middle rest -/

/-- ExprSafe for the "rest after printing lhs" in a binOp context. -/
private theorem exprSafe_binop_mid (op : MicroCBinOp)
    (rhs_print : List Char) (rest : List Char) :
    ExprSafe (' ' :: (microCBinOpToString op).toList ++
      (' ' :: rhs_print ++ (')' :: rest))) := by
  refine ⟨Or.inr ⟨' ', _, rfl, by native_decide⟩,
          Or.inr ⟨' ', _, rfl, by native_decide, by native_decide, by decide⟩, ?_, ?_⟩
  · intro cs
    cases op <;> simp only [microCBinOpToString] <;> (
      first
      | change skipWs (' ' :: '+' :: (' ' :: rhs_print ++ (')' :: rest))) ≠ _
      | change skipWs (' ' :: '-' :: (' ' :: rhs_print ++ (')' :: rest))) ≠ _
      | change skipWs (' ' :: '*' :: (' ' :: rhs_print ++ (')' :: rest))) ≠ _
      | change skipWs (' ' :: '=' :: ('=' :: ' ' :: rhs_print ++ (')' :: rest))) ≠ _
      | change skipWs (' ' :: '<' :: (' ' :: rhs_print ++ (')' :: rest))) ≠ _
      | change skipWs (' ' :: '&' :: ('&' :: ' ' :: rhs_print ++ (')' :: rest))) ≠ _
      | change skipWs (' ' :: '|' :: ('|' :: ' ' :: rhs_print ++ (')' :: rest))) ≠ _
    ) <;> (intro h; simp [skipWs] at h)
  · intro cs
    cases op <;> simp only [microCBinOpToString] <;> (
      first
      | change skipWs (' ' :: '+' :: (' ' :: rhs_print ++ (')' :: rest))) ≠ _
      | change skipWs (' ' :: '-' :: (' ' :: rhs_print ++ (')' :: rest))) ≠ _
      | change skipWs (' ' :: '*' :: (' ' :: rhs_print ++ (')' :: rest))) ≠ _
      | change skipWs (' ' :: '=' :: ('=' :: ' ' :: rhs_print ++ (')' :: rest))) ≠ _
      | change skipWs (' ' :: '<' :: (' ' :: rhs_print ++ (')' :: rest))) ≠ _
      | change skipWs (' ' :: '&' :: ('&' :: ' ' :: rhs_print ++ (')' :: rest))) ≠ _
      | change skipWs (' ' :: '|' :: ('|' :: ' ' :: rhs_print ++ (')' :: rest))) ≠ _
    ) <;> (intro h; simp [skipWs] at h)

/-! ## Equation lemmas for pExprF and pParenF -/

/-- pExprF dispatches '(' prefix to pParenF. -/
@[simp] private theorem pExprF_paren (k : Nat) (cs : List Char) :
    pExprF (k + 1) ('(' :: cs) = pExprF.pParenF k (skipWs cs) := by
  simp [pExprF]

/-- pParenF fallthrough case: when first char is not '!' or '-'. -/
private theorem pParenF_fallthrough (k : Nat) (c : Char) (cs : List Char)
    (h1 : c ≠ '!') (h2 : c ≠ '-') :
    pExprF.pParenF k (c :: cs) =
      match pExprF k (c :: cs) with
      | some (lhs, rest) =>
        match pBinOp (skipWs rest) with
        | some (op, rest') =>
          match pExprF k rest' with
          | some (rhs, rest'') =>
            match skipWs rest'' with
            | ')' :: final => some (.binOp op lhs rhs, final)
            | _ => none
          | none => none
        | none => none
      | none => none := by
  unfold pExprF.pParenF
  simp [h1, h2]
  split <;> simp_all
  · rfl

/-- pParenF '!' case: unaryOp .lnot. -/
private theorem pParenF_lnot (k : Nat) (rest : List Char) :
    pExprF.pParenF k ('!' :: rest) =
      match pExprF k rest with
      | some (e, rest') =>
        match skipWs rest' with
        | ')' :: final => some (.unaryOp .lnot e, final)
        | _ => none
      | none => none := by
  unfold pExprF.pParenF; rfl

/-- pParenF '-' case with non-digit: unaryOp .neg. -/
private theorem pParenF_neg (k : Nat) (c : Char) (rest : List Char)
    (hnd : c.isDigit = false) :
    pExprF.pParenF k ('-' :: c :: rest) =
      match pExprF k (c :: rest) with
      | some (e, rest') =>
        match skipWs rest' with
        | ')' :: final => some (.unaryOp .neg e, final)
        | _ => none
      | none => none := by
  unfold pExprF.pParenF; simp [hnd]
  split <;> simp_all
  · rfl

/-! ## String literal normalization -/

-- simp lemmas to reduce "str".toList to ['c', ...] for parser proofs
@[simp] private theorem str_lp : "(".toList = ['('] := rfl
@[simp] private theorem str_rp : ")".toList = [')'] := rfl
@[simp] private theorem str_dash : "-".toList = ['-'] := rfl
@[simp] private theorem str_bang : "!".toList = ['!'] := rfl
@[simp] private theorem str_sp : " ".toList = [' '] := rfl
@[simp] private theorem str_power_lp : "power(".toList = ['p', 'o', 'w', 'e', 'r', '('] := rfl
@[simp] private theorem str_comma_sp : ", ".toList = [',', ' '] := rfl
@[simp] private theorem str_lb : "[".toList = ['['] := rfl
@[simp] private theorem str_rb : "]".toList = [']'] := rfl

/-! ## Equation lemmas: digit and negative literal -/

/-- Digit chars are never whitespace. -/
private theorem isDigit_not_ws' (c : Char) (h : c.isDigit = true) :
    c ≠ ' ' ∧ c ≠ '\n' ∧ c ≠ '\t' ∧ c ≠ '\r' :=
  ⟨by intro h'; subst h'; simp [Char.isDigit] at h,
   by intro h'; subst h'; simp [Char.isDigit] at h,
   by intro h'; subst h'; simp [Char.isDigit] at h,
   by intro h'; subst h'; simp [Char.isDigit] at h⟩

/-- pExprF dispatches digit-first input to pNat. -/
@[simp] private theorem pExprF_digit (k : Nat) (c : Char) (cs : List Char)
    (hd : c.isDigit = true) :
    pExprF (k + 1) (c :: cs) =
      match pNat (c :: cs) with
      | some (n, rest) => some (.litInt (Int.ofNat n), rest)
      | none => none := by
  simp only [pExprF]
  rw [skipWs_nonws c cs (isDigit_not_ws' c hd)]
  have hc1 : c ≠ '(' := by intro h; subst h; simp [Char.isDigit] at hd
  split
  · rename_i heq; exact absurd (List.cons.inj heq).1 hc1
  · rename_i heq; exact absurd (List.cons.inj heq).1
      (by intro h; subst h; simp [Char.isDigit] at hd)
  · rename_i c' tail _ _ heq
    have : c = c' := (List.cons.inj heq).1; subst this
    split
    next => rfl
    next hf => exact absurd hd hf
  · rename_i heq; simp at heq

/-- pParenF '-' followed by digit: parse negative literal. -/
private theorem pParenF_neg_digit (k : Nat) (c : Char) (rest : List Char)
    (hd : c.isDigit = true) :
    pExprF.pParenF k ('-' :: c :: rest) =
      match pNat (c :: rest) with
      | some (n, rest') => match skipWs rest' with
        | ')' :: final => some (.litInt (-(Int.ofNat n)), final)
        | _ => none
      | none => none := by
  unfold pExprF.pParenF; simp [hd]; split <;> simp_all; · rfl

/-! ## Helper: NoLeadingIdent + alpha contradiction -/

/-- Alpha char at list head contradicts NoLeadingIdent. -/
private theorem noLeadingIdent_alpha_false (c : Char) (rest : List Char)
    (hna : c.isAlpha = true) (hni : NoLeadingIdent (c :: rest)) : False := by
  cases hni with
  | inl h => exact absurd h (by simp)
  | inr h =>
    let ⟨c', _, hc', hna', _, _⟩ := h
    have := List.cons.inj hc' |>.1
    rw [← this] at hna'
    exact absurd hna (by rw [hna']; decide)

/-- The power( match branch is impossible when cs are ident chars
    and rest has NoLeadingIdent + no leading '('. -/
private theorem power_paren_impossible (cs rest tail : List Char)
    (hident : ∀ ch ∈ cs, ch.isAlpha = true ∨ ch.isDigit = true ∨ ch = '_')
    (hni : NoLeadingIdent rest) (hnp : ∀ cs', skipWs rest ≠ '(' :: cs')
    (heq : cs ++ rest = 'o' :: 'w' :: 'e' :: 'r' :: '(' :: tail) : False := by
  match cs, heq with
  | [], heq =>
    simp at heq; rw [heq] at hni
    exact noLeadingIdent_alpha_false 'o' _ (by native_decide) hni
  | [_], heq =>
    simp at heq; rw [heq.2] at hni
    exact noLeadingIdent_alpha_false 'w' _ (by native_decide) hni
  | [_, _], heq =>
    simp at heq; rw [heq.2.2] at hni
    exact noLeadingIdent_alpha_false 'e' _ (by native_decide) hni
  | [_, _, _], heq =>
    simp at heq; rw [heq.2.2.2] at hni
    exact noLeadingIdent_alpha_false 'r' _ (by native_decide) hni
  | [_, _, _, _], heq =>
    simp at heq; rw [heq.2.2.2.2] at hnp
    exact absurd (skipWs_nonws '(' tail ⟨by decide, by decide, by decide, by decide⟩) (hnp tail)
  | a :: b :: c :: d :: e :: cs5, heq =>
    simp at heq
    have h5 : e = '(' := heq.2.2.2.2.1
    subst h5
    have hmem : '(' ∈ a :: b :: c :: d :: '(' :: cs5 := by simp [List.mem_cons]
    have := hident '(' hmem
    rcases this with h | h | h
    · exact absurd h (by native_decide)
    · exact absurd h (by native_decide)
    · exact absurd h (by decide)

/-! ## Helper: First char of printed WFExpr -/

/-- Printed WFExpr has non-empty toList. -/
theorem print_ne_nil (e : MicroCExpr) (he : WFExpr e) :
    (microCExprToString e).toList ≠ [] := by
  cases he with
  | litInt n =>
    simp [microCExprToString_litInt]
    split
    · simp [String.toList_append]
    · have := natToChars_ne_nil n.toNat
      intro h; simp [String.toList_ofList] at h; exact this h
  | litBool b =>
    cases b <;> simp [microCExprToString]
  | varRef name hne _ _ _ =>
    simp [microCExprToString_varRef]
    exact hne
  | binOp _ _ _ _ _ =>
    simp [microCExprToString_binOp]
  | unaryOp _ _ _ =>
    simp [microCExprToString_unaryOp]
  | powCall _ _ _ =>
    simp [microCExprToString_powCall]
  | arrayAccess _ _ hb _ hbv =>
    obtain ⟨vname, rfl⟩ := hbv
    cases hb with
    | varRef _ hne_v _ _ _ =>
      simp [microCExprToString_arrayAccess, microCExprToString_varRef]

/-- First char of a printed WFExpr is not '-' or '!'.
    Needed for pParenF to take the fallthrough branch. -/
private theorem print_first_not_neg_bang (e : MicroCExpr) (he : WFExpr e) :
    ∀ c cs, (microCExprToString e).toList = c :: cs → c ≠ '-' ∧ c ≠ '!' := by
  intro c cs heq
  cases he with
  | litInt n =>
    simp [microCExprToString_litInt] at heq
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
    cases b <;> simp [microCExprToString] at heq <;> obtain ⟨rfl, _⟩ := heq <;>
      exact ⟨by decide, by decide⟩
  | varRef name hne hstart _ _ =>
    simp [microCExprToString_varRef] at heq
    have hne' := toList_ne_nil_of_ne_empty name hne
    match hcs : name.toList with
    | [] => exact absurd hcs hne'
    | c' :: _ =>
      have hhead := list_head_eq_of_cons hcs
      have hstart' := hstart; simp only [hhead] at hstart'
      rw [hcs] at heq; simp at heq; rw [← heq.1]
      cases hstart' with
      | inl h =>
        exact ⟨by intro h'; subst h'; simp [Char.isAlpha, Char.isUpper, Char.isLower] at h,
               by intro h'; subst h'; simp [Char.isAlpha, Char.isUpper, Char.isLower] at h⟩
      | inr h => subst h; exact ⟨by decide, by decide⟩
  | binOp _ _ _ _ _ =>
    simp [microCExprToString_binOp, String.toList_append] at heq
    obtain ⟨rfl, _⟩ := heq; exact ⟨by decide, by decide⟩
  | unaryOp _ _ _ =>
    simp [microCExprToString_unaryOp, String.toList_append] at heq
    obtain ⟨rfl, _⟩ := heq; exact ⟨by decide, by decide⟩
  | powCall _ _ _ =>
    simp [microCExprToString_powCall, String.toList_append] at heq
    obtain ⟨rfl, _⟩ := heq; exact ⟨by decide, by decide⟩
  | arrayAccess _ _ hb _ hbv =>
    obtain ⟨vname, rfl⟩ := hbv
    simp [microCExprToString_arrayAccess, microCExprToString_varRef] at heq
    cases hb with
    | varRef _ hne_v hstart_v _ _ =>
      have hne_v' := toList_ne_nil_of_ne_empty vname hne_v
      match hcs_v : vname.toList with
      | [] => exact absurd hcs_v hne_v'
      | cv :: _ =>
        have hhead := list_head_eq_of_cons hcs_v
        have hst := hstart_v; simp only [hhead] at hst
        simp [hcs_v] at heq; rw [← heq.1]
        cases hst with
        | inl h =>
          exact ⟨by intro h'; subst h'; simp [Char.isAlpha, Char.isUpper, Char.isLower] at h,
                 by intro h'; subst h'; simp [Char.isAlpha, Char.isUpper, Char.isLower] at h⟩
        | inr h => subst h; exact ⟨by decide, by decide⟩

/-- First char of a printed WFExpr is non-whitespace. -/
theorem print_first_nonws (e : MicroCExpr) (he : WFExpr e) :
    ∀ c cs, (microCExprToString e).toList = c :: cs →
    c ≠ ' ' ∧ c ≠ '\n' ∧ c ≠ '\t' ∧ c ≠ '\r' := by
  intro c cs heq
  cases he with
  | litInt n =>
    simp [microCExprToString_litInt] at heq
    split at heq
    · simp [String.toList_append] at heq; obtain ⟨rfl, _⟩ := heq
      exact ⟨by decide, by decide, by decide, by decide⟩
    · have hne := natToChars_ne_nil n.toNat
      match hcs : natToChars n.toNat with
      | [] => exact absurd hcs hne
      | c' :: _ =>
        simp [hcs] at heq; rw [← heq.1]
        exact isDigit_not_ws c' (natToChars_all_digits n.toNat c' (by rw [hcs]; exact List.mem_cons_self ..))
  | litBool b =>
    cases b <;> simp [microCExprToString] at heq <;> obtain ⟨rfl, _⟩ := heq <;>
      exact ⟨by decide, by decide, by decide, by decide⟩
  | varRef name hne hstart _ _ =>
    simp [microCExprToString_varRef] at heq
    have hne' := toList_ne_nil_of_ne_empty name hne
    match hcs : name.toList with
    | [] => exact absurd hcs hne'
    | c' :: _ =>
      have hhead := list_head_eq_of_cons hcs
      have hst := hstart; simp only [hhead] at hst
      rw [hcs] at heq; simp at heq; rw [← heq.1]
      cases hst with
      | inl h => exact isAlpha_not_ws c' h
      | inr h => subst h; exact ⟨by decide, by decide, by decide, by decide⟩
  | binOp _ _ _ _ _ =>
    simp [microCExprToString_binOp, String.toList_append] at heq
    obtain ⟨rfl, _⟩ := heq; exact ⟨by decide, by decide, by decide, by decide⟩
  | unaryOp _ _ _ =>
    simp [microCExprToString_unaryOp, String.toList_append] at heq
    obtain ⟨rfl, _⟩ := heq; exact ⟨by decide, by decide, by decide, by decide⟩
  | powCall _ _ _ =>
    simp [microCExprToString_powCall, String.toList_append] at heq
    obtain ⟨rfl, _⟩ := heq; exact ⟨by decide, by decide, by decide, by decide⟩
  | arrayAccess _ _ hb _ hbv =>
    obtain ⟨vname, rfl⟩ := hbv
    simp [microCExprToString_arrayAccess, microCExprToString_varRef] at heq
    cases hb with
    | varRef _ hne_v hstart_v _ _ =>
      have hne_v' := toList_ne_nil_of_ne_empty vname hne_v
      match hcs_v : vname.toList with
      | [] => exact absurd hcs_v hne_v'
      | cv :: _ =>
        have hhead := list_head_eq_of_cons hcs_v
        have hst := hstart_v; simp only [hhead] at hst
        simp [hcs_v] at heq; rw [← heq.1]
        cases hst with
        | inl h => exact isAlpha_not_ws cv h
        | inr h => subst h; exact ⟨by decide, by decide, by decide, by decide⟩

/-! ## Main Theorem: Expression Roundtrip with Remainder -/

/-- Core roundtrip: parsing the printed form of a WFExpr recovers the original,
    with arbitrary safe remainder. -/
theorem expr_roundtrip_with_rest (e : MicroCExpr) (he : WFExpr e) (hs : NegLitDisam e)
    (fuel : Nat) (hfuel : fuel ≥ exprDepth e)
    (rest : List Char) (hrest : ExprSafe rest) :
    pExprF fuel ((microCExprToString e).toList ++ rest) = some (e, rest) := by
  induction he generalizing fuel rest hrest with
  | litInt n =>
    have h1 : fuel ≥ 1 := Nat.le_trans (exprDepth_pos (.litInt n)) hfuel
    have hfne : fuel ≠ 0 := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hfne
    by_cases hn : n < 0
    · -- Negative: print = "(-" ++ natToChars(n.natAbs) ++ ")"
      simp only [microCExprToString_litInt, hn, ite_true,
        String.toList_append, String.toList_ofList, List.append_assoc,
        str_lp, str_rp, str_dash, List.cons_append, List.nil_append]
      simp only [pExprF_paren]
      rw [skipWs_nonws '-' _ ⟨by decide, by decide, by decide, by decide⟩]
      have hne := natToChars_ne_nil n.natAbs
      match hcs : natToChars n.natAbs with
      | [] => exact absurd hcs hne
      | c :: cs =>
        have hcd := natToChars_all_digits n.natAbs c (by rw [hcs]; exact List.mem_cons_self ..)
        simp only [List.cons_append]
        rw [pParenF_neg_digit k c (cs ++ ')' :: rest) hcd]
        rw [show c :: (cs ++ ')' :: rest) = (c :: cs) ++ ')' :: rest from by simp [List.cons_append]]
        rw [← hcs]
        rw [pNat_natToChars n.natAbs (')' :: rest) (Or.inr ⟨')', rest, rfl, by native_decide⟩)]
        simp only []
        rw [skipWs_nonws ')' rest ⟨by decide, by decide, by decide, by decide⟩]
        congr 1; congr 1
        match n, hn with
        | .negSucc m, _ => simp [Int.natAbs, Int.negSucc_eq]
    · -- Non-negative: print = natToChars(n.toNat)
      simp only [microCExprToString_litInt, hn, ite_false, String.toList_ofList]
      have hne := natToChars_ne_nil n.toNat
      match hcs : natToChars n.toNat with
      | [] => exact absurd hcs hne
      | c :: cs =>
        have hcd := natToChars_all_digits n.toNat c (by rw [hcs]; exact List.mem_cons_self ..)
        simp only [List.cons_append]
        rw [pExprF_digit k c (cs ++ rest) hcd]
        rw [show c :: (cs ++ rest) = natToChars n.toNat ++ rest from by rw [hcs, List.cons_append]]
        rw [pNat_natToChars n.toNat rest hrest.1]
        simp only []
        congr 1; congr 1; congr 1
        exact Int.toNat_of_nonneg (Int.not_lt.mp hn)
  | litBool b =>
    have h1 : fuel ≥ 1 := Nat.le_trans (exprDepth_pos (.litBool b)) hfuel
    have hfne : fuel ≠ 0 := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hfne
    cases b with
    | true =>
      have htl : ("true" : String).toList = ['t', 'r', 'u', 'e'] := by native_decide
      simp only [microCExprToString_litBool_true, htl, List.cons_append, List.nil_append]
      -- Dispatch pExprF: 't' is not '(' or 'p', not digit, is alpha
      simp only [pExprF]
      rw [skipWs_nonws 't' _ ⟨by decide, by decide, by decide, by decide⟩]
      split
      · rename_i heq; exact absurd (List.cons.inj heq).1 (by decide)
      · rename_i heq; exact absurd (List.cons.inj heq).1 (by decide)
      · rename_i c' tail _ _ heq
        have := (List.cons.inj heq).1; subst this
        simp [show ('t' : Char).isDigit = false from by native_decide]
        simp only [pExprF.pIdentF]
        have htrue : ("true" : String).toList = ['t', 'r', 'u', 'e'] := by native_decide
        rw [show ('t' :: 'r' :: 'u' :: 'e' :: rest) = "true".toList ++ rest from by
            simp [htrue, List.cons_append, List.nil_append]]
        rw [pIdent_exact "true" rest (by decide) (by simp [htrue])
            (by intro c hc; simp [htrue] at hc; rcases hc with rfl | rfl | rfl | rfl <;> decide)
            hrest.2.1]
        simp
      · rename_i heq; exact absurd heq (by simp)
    | false =>
      have hfl : ("false" : String).toList = ['f', 'a', 'l', 's', 'e'] := by native_decide
      simp only [microCExprToString_litBool_false, hfl, List.cons_append, List.nil_append]
      simp only [pExprF]
      rw [skipWs_nonws 'f' _ ⟨by decide, by decide, by decide, by decide⟩]
      split
      · rename_i heq; exact absurd (List.cons.inj heq).1 (by decide)
      · rename_i heq; exact absurd (List.cons.inj heq).1 (by decide)
      · rename_i c' tail _ _ heq
        have := (List.cons.inj heq).1; subst this
        simp [show ('f' : Char).isDigit = false from by native_decide]
        simp only [pExprF.pIdentF]
        have hfalse : ("false" : String).toList = ['f', 'a', 'l', 's', 'e'] := by native_decide
        rw [show ('f' :: 'a' :: 'l' :: 's' :: 'e' :: rest) = "false".toList ++ rest from by
            simp [hfalse, List.cons_append, List.nil_append]]
        rw [pIdent_exact "false" rest (by decide) (by simp [hfalse])
            (by intro c hc; simp [hfalse] at hc; rcases hc with rfl | rfl | rfl | rfl | rfl <;> decide)
            hrest.2.1]
        simp
      · rename_i heq; exact absurd heq (by simp)
  | varRef name hne hstart hcont hnot_kw =>
    have h1 : fuel ≥ 1 := Nat.le_trans (exprDepth_pos (.varRef name)) hfuel
    have hfne : fuel ≠ 0 := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hfne
    simp only [microCExprToString_varRef, pExprF]
    have hne' := toList_ne_nil_of_ne_empty name hne
    match hcs : name.toList with
    | [] => exact absurd hcs hne'
    | c :: cs =>
      have hhead := list_head_eq_of_cons hcs
      have hstart' := hstart; simp only [hhead] at hstart'
      have hcnws : c ≠ ' ' ∧ c ≠ '\n' ∧ c ≠ '\t' ∧ c ≠ '\r' := by
        cases hstart' with
        | inl h => exact isAlpha_not_ws c h
        | inr h => subst h; exact ⟨by decide, by decide, by decide, by decide⟩
      have hcnd : c.isDigit = false := by
        cases hstart' with
        | inl h => exact isAlpha_not_isDigit c h
        | inr h => subst h; native_decide
      have hcid : (c.isAlpha || c == '_') = true := by
        cases hstart' with
        | inl h => simp [h]
        | inr h => subst h; simp
      have hc_ne_paren : c ≠ '(' := by
        cases hstart' with
        | inl h => intro hc; subst hc; simp [Char.isAlpha] at h
        | inr h => subst h; decide
      simp only [List.cons_append]
      rw [skipWs_nonws c (cs ++ rest) hcnws]
      -- Dispatch the outer match via split
      split
      · -- '(' :: ... branch: c ≠ '('
        rename_i heq; exact absurd (List.cons.inj heq).1 hc_ne_paren
      · -- power( branch: impossible via ExprSafe + ident chars
        rename_i tail heq
        exfalso
        have htl := (List.cons.inj heq).2
        have hident : ∀ ch ∈ cs, ch.isAlpha = true ∨ ch.isDigit = true ∨ ch = '_' := by
          intro ch hmem; exact hcont ch (by rw [hcs]; exact List.mem_cons_of_mem c hmem)
        exact power_paren_impossible cs rest tail hident hrest.2.1 hrest.2.2.2 htl
      · -- c :: tail branch: our target
        rename_i c' tail _ _ heq
        have := (List.cons.inj heq).1; subst this
        simp [hcnd, hcid]
        simp only [pExprF.pIdentF]
        have hpid : pIdent (c :: (cs ++ rest)) = some (name, rest) := by
          have harg : c :: (cs ++ rest) = name.toList ++ rest := by rw [hcs]; rfl
          rw [harg]; exact pIdent_exact name rest hne hstart hcont hrest.2.1
        simp only [hpid]
        simp [hnot_kw.1, hnot_kw.2]
        -- Check for '[' and '(' in skipWs rest
        have ⟨hno_bracket, hno_paren⟩ := hrest.2.2
        generalize hsr : skipWs rest = sr at hno_bracket hno_paren
        cases sr with
        | nil => simp [hsr]
        | cons c' cs' =>
          by_cases h : c' = '['
          · subst h; exact absurd rfl (hno_bracket cs')
          · by_cases hp : c' = '('
            · subst hp; exact absurd rfl (hno_paren cs')
            · simp [hsr, h, hp]
      · -- [] branch: impossible
        rename_i heq; exact absurd heq (by simp)
  | binOp op lhs rhs h_l h_r ih_l ih_r =>
    -- Setup fuel
    have h1 : fuel ≥ 1 := Nat.le_trans (exprDepth_pos (.binOp op lhs rhs)) hfuel
    have hfne : fuel ≠ 0 := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hfne
    have hfuel_l : k ≥ exprDepth lhs := by
      simp only [exprDepth] at hfuel
      have := Nat.le_max_left (exprDepth lhs) (exprDepth rhs); omega
    have hfuel_r : k ≥ exprDepth rhs := by
      simp only [exprDepth] at hfuel
      have := Nat.le_max_right (exprDepth lhs) (exprDepth rhs); omega
    -- NegLitDisam
    have hs_l : NegLitDisam lhs := hs.1
    have hs_r : NegLitDisam rhs := hs.2
    -- Expand printed form and normalize string literals
    simp only [microCExprToString_binOp, String.toList_append, List.append_assoc,
      str_lp, str_rp, str_sp, List.cons_append, List.nil_append]
    -- Dispatch: pExprF (k+1) ('(' :: ...) → pParenF k (skipWs ...)
    simp only [pExprF_paren]
    -- Handle skipWs of print(lhs) ++ mid_rest
    have h_ne_l := print_ne_nil lhs h_l
    match h_head_l : (microCExprToString lhs).toList with
    | [] => exact absurd h_head_l h_ne_l
    | c_l :: cs_l =>
      -- skipWs (c_l :: cs_l ++ ...) = c_l :: cs_l ++ ... (c_l is non-ws)
      have h_nonws_l := print_first_nonws lhs h_l c_l cs_l h_head_l
      have ⟨h_not_neg_l, h_not_bang_l⟩ := print_first_not_neg_bang lhs h_l c_l cs_l h_head_l
      -- mid_rest = ' ' :: opStr ++ ' ' :: print(rhs) ++ ')' :: rest
      let mid := (' ' :: (microCBinOpToString op).toList ++
        (' ' :: (microCExprToString rhs).toList ++ (')' :: rest)))
      simp only [List.cons_append]
      rw [skipWs_nonws c_l _ h_nonws_l]
      -- Fallthrough: first char c_l is not '!' or '-'
      rw [pParenF_fallthrough k c_l _ h_not_bang_l h_not_neg_l]
      -- Apply IH_l: parse lhs
      have h_safe_mid : ExprSafe mid :=
        exprSafe_binop_mid op (microCExprToString rhs).toList rest
      simp only [← List.cons_append, ← h_head_l]
      rw [ih_l hs_l k hfuel_l mid h_safe_mid]
      simp only []
      -- Handle skipWs of mid = ' ' :: opStr ++ ' ' :: print(rhs) ++ ')' :: rest
      -- After skipWs ' ', next char is opStr[0] which is non-ws
      -- Then pBinOp parses the operator
      -- Need first char of print(rhs)
      have h_ne_r := print_ne_nil rhs h_r
      match h_head_r : (microCExprToString rhs).toList with
      | [] => exact absurd h_head_r h_ne_r
      | c_r :: cs_r =>
        have h_nonws_r := print_first_nonws rhs h_r c_r cs_r h_head_r
        -- skipWs (' ' :: opStr ++ ' ' :: c_r :: cs_r ++ ')' :: rest)
        -- = opStr ++ ' ' :: c_r :: cs_r ++ ')' :: rest (after skipping the leading space)
        -- Wait, skipWs skips ALL leading whitespace. The first char of opStr is non-ws.
        -- Actually we need: skipWs mid = opStr.toList ++ ' ' :: c_r :: cs_r ++ ')' :: rest
        -- This is because mid = ' ' :: opStr ++ ...
        -- And the operator chars are all non-ws.
        -- Let me show: skipWs mid = skipWs (' ' :: opStr ++ ...)
        show (match pBinOp (skipWs mid) with
          | some (op', rest') =>
            match pExprF k rest' with
            | some (rhs', rest'') =>
              match skipWs rest'' with
              | ')' :: final => some (MicroCExpr.binOp op' lhs rhs', final)
              | _ => none
            | none => none
          | none => none) = some (MicroCExpr.binOp op lhs rhs, rest)
        -- Now handle pBinOp (skipWs mid)
        -- skipWs (' ' :: opStr ++ ' ' :: print_r ++ ')' :: rest)
        -- The first char of opStr is non-ws, so skipWs skips the leading ' '
        -- and leaves opStr ++ ' ' :: print_r ++ ')' :: rest
        -- This matches pBinOp_roundtrip format
        -- Actually, pBinOp_roundtrip needs: pBinOp (opStr.toList ++ (' ' :: c_r :: cs_r ++ ')' :: rest))
        -- And skipWs mid should equal opStr.toList ++ (' ' :: c_r :: cs_r ++ ')' :: rest)
        -- Because mid = ' ' :: opStr.toList ++ (' ' :: c_r :: cs_r ++ (')' :: rest))
        -- and skipWs skips the leading ' ', next char is opStr[0] which is non-ws
        have h_skipWs_mid : skipWs mid =
            (microCBinOpToString op).toList ++ (' ' :: c_r :: (cs_r ++ (')' :: rest))) := by
          show skipWs (' ' :: (microCBinOpToString op).toList ++
            (' ' :: (microCExprToString rhs).toList ++ (')' :: rest))) = _
          rw [h_head_r]
          cases op <;> simp only [microCBinOpToString] <;> (
            first
            | change skipWs (' ' :: '+' :: (' ' :: c_r :: cs_r ++ (')' :: rest))) = _
            | change skipWs (' ' :: '-' :: (' ' :: c_r :: cs_r ++ (')' :: rest))) = _
            | change skipWs (' ' :: '*' :: (' ' :: c_r :: cs_r ++ (')' :: rest))) = _
            | change skipWs (' ' :: '=' :: ('=' :: ' ' :: c_r :: cs_r ++ (')' :: rest))) = _
            | change skipWs (' ' :: '<' :: (' ' :: c_r :: cs_r ++ (')' :: rest))) = _
            | change skipWs (' ' :: '&' :: ('&' :: ' ' :: c_r :: cs_r ++ (')' :: rest))) = _
            | change skipWs (' ' :: '|' :: ('|' :: ' ' :: c_r :: cs_r ++ (')' :: rest))) = _
          ) <;> simp [skipWs] <;> rfl
        rw [h_skipWs_mid]
        -- Apply pBinOp_roundtrip
        rw [pBinOp_roundtrip op c_r (cs_r ++ (')' :: rest)) h_nonws_r]
        simp only []
        -- Apply IH_r: parse rhs with ExprSafe (')' :: rest)
        have h_eq_r : pExprF k (c_r :: (cs_r ++ (')' :: rest))) =
            pExprF k ((microCExprToString rhs).toList ++ (')' :: rest)) :=
          congrArg (pExprF k) (by simp [h_head_r])
        have h_ih_r := ih_r hs_r k hfuel_r (')' :: rest) (exprSafe_rparen rest)
        rw [h_eq_r, h_ih_r]
        simp only []
        -- skipWs (')' :: rest) = ')' :: rest
        simp [skipWs]
  | unaryOp op e h_e ih_e =>
    -- Setup fuel
    have h1 : fuel ≥ 1 := Nat.le_trans (exprDepth_pos (.unaryOp op e)) hfuel
    have hfne : fuel ≠ 0 := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hfne
    have hfuel_e : k ≥ exprDepth e := by simp only [exprDepth] at hfuel; omega
    cases op with
    | lnot =>
      -- print = "(!" ++ print(e) ++ ")"
      simp only [microCExprToString_unaryOp, microCUnaryOpToString, String.toList_append,
        List.append_assoc, str_lp, str_rp, str_bang, List.cons_append, List.nil_append]
      simp only [pExprF_paren]
      -- skipWs ('!' :: print(e) ++ ')' :: rest) = '!' :: print(e) ++ ')' :: rest
      simp [skipWs]
      rw [pParenF_lnot]
      -- Apply IH
      rw [ih_e hs k hfuel_e (')' :: rest) (exprSafe_rparen rest)]
      simp [skipWs]
    | neg =>
      -- NegLitDisam gives (∀ n, n ≥ 0 → e ≠ .litInt n) ∧ NegLitDisam e
      have ⟨h_not_lit, hs_e⟩ := hs
      -- print = "(-" ++ print(e) ++ ")"
      simp only [microCExprToString_unaryOp, microCUnaryOpToString, String.toList_append,
        List.append_assoc, str_lp, str_rp, str_dash, List.cons_append, List.nil_append]
      simp only [pExprF_paren]
      -- skipWs ('-' :: print(e) ++ ')' :: rest) = '-' :: print(e) ++ ')' :: rest
      simp [skipWs]
      -- pParenF sees '-' :: first_char_of_print(e) :: ...
      -- Need to show first_char_of_print(e) is NOT a digit
      have h_ne_e := print_ne_nil e h_e
      match h_head_e : (microCExprToString e).toList with
      | [] => exact absurd h_head_e h_ne_e
      | c_e :: cs_e =>
        -- Need: c_e.isDigit = false
        -- This follows from NegLitDisam: e is not .litInt n for n ≥ 0
        -- If c_e were a digit, then print(e) starts with a digit, meaning e = .litInt n for n ≥ 0
        -- (since pExprF prints non-negative ints as natToChars)
        -- This contradicts h_not_lit
        have h_not_digit : c_e.isDigit = false := by
          match hd : c_e.isDigit with
          | false => rfl
          | true =>
            exfalso
            -- If first char is digit, e must be .litInt n for n ≥ 0
            cases h_e with
            | litInt n =>
              simp [microCExprToString_litInt] at h_head_e
              split at h_head_e
              · -- n < 0: first char is '(' which is not a digit
                simp [String.toList_append] at h_head_e
                obtain ⟨rfl, _⟩ := h_head_e
                simp [Char.isDigit] at hd
                exact absurd hd (by native_decide)
              · -- n ≥ 0: digit OK, contradicts h_not_lit
                exact absurd rfl (h_not_lit n (by omega))
            | litBool b =>
              cases b <;> simp [microCExprToString] at h_head_e <;>
                obtain ⟨rfl, _⟩ := h_head_e <;> simp [Char.isDigit] at hd <;>
                exact absurd hd (by native_decide)
            | varRef name hne hstart _ _ =>
              simp [microCExprToString_varRef] at h_head_e
              have hne' := toList_ne_nil_of_ne_empty name hne
              match hcs : name.toList with
              | [] => exact absurd hcs hne'
              | c' :: _ =>
                have hhead := list_head_eq_of_cons hcs
                have hst := hstart; simp only [hhead] at hst
                rw [hcs] at h_head_e; simp at h_head_e; rw [← h_head_e.1] at hd
                cases hst with
                | inl h => exact absurd hd (by rw [isAlpha_not_isDigit c' h]; decide)
                | inr h => subst h; simp [Char.isDigit] at hd
            | binOp _ _ _ _ _ =>
              simp [microCExprToString_binOp, String.toList_append] at h_head_e
              obtain ⟨rfl, _⟩ := h_head_e; simp [Char.isDigit] at hd
            | unaryOp _ _ _ =>
              simp [microCExprToString_unaryOp, String.toList_append] at h_head_e
              obtain ⟨rfl, _⟩ := h_head_e; simp [Char.isDigit] at hd
            | powCall _ _ _ =>
              simp [microCExprToString_powCall, String.toList_append] at h_head_e
              obtain ⟨rfl, _⟩ := h_head_e; simp [Char.isDigit] at hd
            | arrayAccess _ _ hb _ hbv =>
              obtain ⟨vname, rfl⟩ := hbv
              simp [microCExprToString_arrayAccess, microCExprToString_varRef] at h_head_e
              cases hb with
              | varRef _ hne_v hstart_v _ _ =>
                have hne_v' := toList_ne_nil_of_ne_empty vname hne_v
                match hcs_v : vname.toList with
                | [] => exact absurd hcs_v hne_v'
                | cv :: _ =>
                  have hhead_v := list_head_eq_of_cons hcs_v
                  have hst := hstart_v; simp only [hhead_v] at hst
                  simp [hcs_v] at h_head_e; rw [← h_head_e.1] at hd
                  cases hst with
                  | inl h => exact absurd hd (by rw [isAlpha_not_isDigit cv h]; decide)
                  | inr h => subst h; simp [Char.isDigit] at hd
        simp only [List.cons_append]
        rw [pParenF_neg k c_e (cs_e ++ (')' :: rest)) h_not_digit]
        -- Apply IH: rewrite c_e :: cs_e back to toList for IH
        simp only [← List.cons_append, ← h_head_e]
        rw [ih_e hs_e k hfuel_e (')' :: rest) (exprSafe_rparen rest)]
        simp [skipWs]
  | powCall base n h_base ih_base =>
    -- Setup fuel
    have h1 : fuel ≥ 1 := Nat.le_trans (exprDepth_pos (.powCall base n)) hfuel
    have hfne : fuel ≠ 0 := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hfne
    have hfuel_b : k ≥ exprDepth base := by simp only [exprDepth] at hfuel; omega
    -- print = "power(" ++ print(base) ++ ", " ++ natToChars(n) ++ ")"
    simp only [microCExprToString_powCall, String.toList_append, List.append_assoc,
      str_power_lp, str_rp, str_comma_sp, String.toList_ofList, List.cons_append, List.nil_append]
    -- pExprF at fuel+1: unfold pExprF
    simp only [pExprF]
    -- Reduce skipWs for non-ws 'p'
    rw [skipWs_nonws 'p' _ ⟨by decide, by decide, by decide, by decide⟩]
    simp only [pExprF.pPowF]
    -- skipWs of print(base) ++ ...
    have h_ne_b := print_ne_nil base h_base
    match h_head_b : (microCExprToString base).toList with
    | [] => exact absurd h_head_b h_ne_b
    | c_b :: cs_b =>
      have h_nonws_b := print_first_nonws base h_base c_b cs_b h_head_b
      simp only [List.cons_append]
      rw [skipWs_nonws c_b _ h_nonws_b]
      -- Apply IH for base with ExprSafe (',' :: ...)
      have h_eq_b : pExprF k (c_b :: (cs_b ++ (',' :: ' ' :: (natToChars n ++ (')' :: rest))))) =
          pExprF k ((microCExprToString base).toList ++ (',' :: ' ' :: (natToChars n ++ (')' :: rest)))) :=
        congrArg (pExprF k) (by simp [h_head_b])
      have h_ih_b := ih_base hs k hfuel_b (',' :: ' ' :: (natToChars n ++ (')' :: rest)))
        (exprSafe_comma (' ' :: (natToChars n ++ (')' :: rest))))
      rw [h_eq_b, h_ih_b]
      simp only []
      -- skipWs (',' :: ...) = ',' :: ...
      simp [skipWs]
      -- pNat on natToChars n
      rw [skipWs_natToChars n (')' :: rest)]
      rw [pNat_natToChars n (')' :: rest) (Or.inr ⟨')', rest, rfl, by native_decide⟩)]
      simp [skipWs]
  | arrayAccess base idx h_base h_idx hbase_var ih_base ih_idx =>
    -- Extract vname; base must be a varRef
    obtain ⟨vname, rfl⟩ := hbase_var
    cases h_base with
    | varRef _ hne hstart hcont hnot_kw =>
    have hs_idx : NegLitDisam idx := hs.2
    -- Fuel setup
    have h1 : fuel ≥ 1 := Nat.le_trans (exprDepth_pos (.arrayAccess (.varRef vname) idx)) hfuel
    have hfne : fuel ≠ 0 := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hfne
    have hfuel_idx : k ≥ exprDepth idx := by simp only [exprDepth] at hfuel; omega
    -- Unfold printer: vname ++ "[" ++ print(idx) ++ "]" ++ rest
    simp only [microCExprToString_arrayAccess, microCExprToString_varRef,
      String.toList_append, List.append_assoc,
      show "[".toList = ['['] from rfl, show "]".toList = [']'] from rfl,
      String.toList_ofList, List.cons_append, List.nil_append]
    simp only [pExprF]
    -- Destructure vname.toList
    have hne' := toList_ne_nil_of_ne_empty vname hne
    match hcs : vname.toList with
    | [] => exact absurd hcs hne'
    | c :: cs =>
      have hhead := list_head_eq_of_cons hcs
      have hstart' := hstart; simp only [hhead] at hstart'
      have hcnws : c ≠ ' ' ∧ c ≠ '\n' ∧ c ≠ '\t' ∧ c ≠ '\r' := by
        cases hstart' with
        | inl h => exact isAlpha_not_ws c h
        | inr h => subst h; exact ⟨by decide, by decide, by decide, by decide⟩
      have hcnd : c.isDigit = false := by
        cases hstart' with
        | inl h => exact isAlpha_not_isDigit c h
        | inr h => subst h; native_decide
      have hcid : (c.isAlpha || c == '_') = true := by
        cases hstart' with
        | inl h => simp [h]
        | inr h => subst h; simp
      have hc_ne_paren : c ≠ '(' := by
        cases hstart' with
        | inl h => intro hc; subst hc; simp [Char.isAlpha] at h
        | inr h => subst h; decide
      simp only [List.cons_append]
      rw [skipWs_nonws c _ hcnws]
      -- Dispatch outer match (same 4 branches as varRef)
      split
      · -- '(' branch: impossible since c is alpha/underscore
        rename_i heq; exact absurd (List.cons.inj heq).1 hc_ne_paren
      · -- power( branch: impossible
        rename_i tail heq; exfalso
        have htl := (List.cons.inj heq).2
        have hident : ∀ ch ∈ cs, ch.isAlpha = true ∨ ch.isDigit = true ∨ ch = '_' := by
          intro ch hmem; exact hcont ch (by rw [hcs]; exact List.mem_cons_of_mem c hmem)
        have h_nli : NoLeadingIdent ('[' :: ((microCExprToString idx).toList ++ (']' :: rest))) :=
          Or.inr ⟨'[', _, rfl, by native_decide, by native_decide, by decide⟩
        have h_npa : ∀ xs, skipWs ('[' :: ((microCExprToString idx).toList ++ (']' :: rest))) ≠ '(' :: xs := by
          intro xs h; rw [skipWs_nonws '[' _ ⟨by decide, by decide, by decide, by decide⟩] at h
          exact absurd (List.cons.inj h).1 (by decide)
        exact power_paren_impossible cs _ tail hident h_nli h_npa htl
      · -- c :: tail branch: identifier parsing
        rename_i c' tail _ _ heq
        have := (List.cons.inj heq).1; subst this
        simp [hcnd, hcid]
        simp only [pExprF.pIdentF]
        -- pIdent parses vname, leaving '[' :: print(idx) ++ ']' :: rest
        have h_nli : NoLeadingIdent ('[' :: ((microCExprToString idx).toList ++ (']' :: rest))) :=
          Or.inr ⟨'[', _, rfl, by native_decide, by native_decide, by decide⟩
        have hpid : pIdent (c :: (cs ++ ('[' :: ((microCExprToString idx).toList ++ (']' :: rest))))) =
            some (vname, '[' :: ((microCExprToString idx).toList ++ (']' :: rest))) := by
          have harg : c :: (cs ++ ('[' :: ((microCExprToString idx).toList ++ (']' :: rest)))) =
              vname.toList ++ ('[' :: ((microCExprToString idx).toList ++ (']' :: rest))) := by
            rw [hcs]; rfl
          rw [harg]; exact pIdent_exact vname _ hne hstart hcont h_nli
        simp only [hpid]
        simp [hnot_kw.1, hnot_kw.2]
        -- simp already consumed keyword check + skipWs + '[' branch match
        -- Now inside '[' branch: parse idx expression
        have h_ne_idx := print_ne_nil idx h_idx
        match h_head_idx : (microCExprToString idx).toList with
        | [] => exact absurd h_head_idx h_ne_idx
        | c_i :: cs_i =>
          have h_nonws_idx := print_first_nonws idx h_idx c_i cs_i h_head_idx
          simp only [List.cons_append]
          rw [skipWs_nonws c_i _ h_nonws_idx]
          -- Apply IH for idx with rest = ']' :: rest
          have h_eq_idx : pExprF k (c_i :: (cs_i ++ (']' :: rest))) =
              pExprF k ((microCExprToString idx).toList ++ (']' :: rest)) :=
            congrArg (pExprF k) (by simp [h_head_idx])
          have h_ih_idx := ih_idx hs_idx k hfuel_idx (']' :: rest) (exprSafe_rbracket rest)
          rw [h_eq_idx, h_ih_idx]
          simp only []
          -- skipWs (']' :: rest) = ']' :: rest, then match on ']'
          simp [skipWs]
      · -- [] branch: impossible
        rename_i heq; exact absurd heq (by simp)

/-! ## Top-Level Theorem -/

/-- Fuel sufficiency: exprDepth e ≤ string length + 1. -/
theorem exprDepth_le_length (e : MicroCExpr) (he : WFExpr e) :
    exprDepth e ≤ (microCExprToString e).toList.length + 1 := by
  induction he with
  | litInt _ | litBool _ | varRef _ _ _ _ _ =>
    simp [exprDepth]
  | binOp _ _ _ _ _ ih_l ih_r =>
    simp only [exprDepth, microCExprToString_binOp, Nat.max_def]
    simp only [String.toList_append, List.length_append,
      show "(".toList = ['('] from rfl, show ")".toList = [')'] from rfl,
      show " ".toList = [' '] from rfl,
      List.length_cons, List.length_nil]
    split <;> (have := ih_l; have := ih_r; omega)
  | unaryOp _ _ _ ih_e =>
    simp only [exprDepth, microCExprToString_unaryOp]
    simp only [String.toList_append, List.length_append,
      show "(".toList = ['('] from rfl, show ")".toList = [')'] from rfl,
      List.length_cons, List.length_nil]
    have := ih_e; omega
  | powCall _ _ _ ih_base =>
    simp only [exprDepth, microCExprToString_powCall]
    simp only [String.toList_append, List.length_append,
      show "power(".toList = ['p', 'o', 'w', 'e', 'r', '('] from rfl,
      show ", ".toList = [',', ' '] from rfl,
      show ")".toList = [')'] from rfl,
      List.length_cons, List.length_nil]
    have := ih_base; omega
  | arrayAccess _ _ _ _ _ ih_base ih_idx =>
    simp only [exprDepth, microCExprToString_arrayAccess, Nat.max_def]
    simp only [String.toList_append, List.length_append,
      show "[".toList = ['['] from rfl, show "]".toList = [']'] from rfl,
      List.length_cons, List.length_nil]
    split <;> (have := ih_base; have := ih_idx; omega)

/-- Expression roundtrip: parsing the printed form of a well-formed expression
    recovers the original. -/
theorem parseMicroCExpr_roundtrip (e : MicroCExpr) (he : WFExpr e)
    (hs : NegLitDisam e) :
    parseMicroCExpr (microCExprToString e) = some e := by
  simp only [parseMicroCExpr]
  have hfuel : (microCExprToString e).toList.length + 1 ≥ exprDepth e :=
    exprDepth_le_length e he
  have h := expr_roundtrip_with_rest e he hs
    ((microCExprToString e).toList.length + 1) hfuel [] exprSafe_nil
  simp only [List.append_nil] at h
  rw [h]; simp [skipWs]

/-! ## Non-Vacuity -/

/-- Non-vacuity: litInt roundtrip for positive, negative, and zero. -/
example : parseMicroCExpr (microCExprToString (.litInt 42)) = some (.litInt 42) := by native_decide
example : parseMicroCExpr (microCExprToString (.litInt (-7))) = some (.litInt (-7)) := by native_decide
example : parseMicroCExpr (microCExprToString (.litInt 0)) = some (.litInt 0) := by native_decide

/-- Non-vacuity: binOp roundtrip with nested expressions. -/
example : parseMicroCExpr (microCExprToString
    (.binOp .add (.binOp .mul (.varRef "x") (.varRef "y")) (.litInt 1)))
    = some (.binOp .add (.binOp .mul (.varRef "x") (.varRef "y")) (.litInt 1)) := by native_decide

/-- Non-vacuity: arrayAccess roundtrip. -/
example : parseMicroCExpr (microCExprToString (.arrayAccess (.varRef "a") (.varRef "i")))
    = some (.arrayAccess (.varRef "a") (.varRef "i")) := by native_decide

/-- Non-vacuity: powCall roundtrip. -/
example : parseMicroCExpr (microCExprToString (.powCall (.varRef "b") 3))
    = some (.powCall (.varRef "b") 3) := by native_decide

end TrustLean
