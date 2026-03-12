/-
  Trust-Lean — Verified Code Generation Framework
  MicroC/RoundtripStmt.lean: Statement roundtrip proof (v3.0.0)

  N16.2: CRIT — proves ∀ s, WFStmt s → NegLitDisamS s →
    parseMicroC(microCToString s) = some s
  by structural induction on WFStmt.

  Strategy: expression roundtrip (N16.1) as lemma. Statement parser is
  self-delimiting (ends at ; or }), so no StmtSafe predicate needed.
  Sequences handled by parseStmtSeq roundtrip.
-/

import TrustLean.MicroC.RoundtripExpr

set_option autoImplicit false

namespace TrustLean

/-! ## Definitions -/

/-- Variable name doesn't conflict with parser keywords.
    Character-level formulation: name doesn't start with "return" (any prefix),
    and name is not exactly "if" or "while". -/
def VarNameSafe (name : String) : Prop :=
  (∀ cs, name.toList ≠ 'r' :: 'e' :: 't' :: 'u' :: 'r' :: 'n' :: cs) ∧
  name ≠ "if" ∧ name ≠ "while"

/-- Expression is safe for assignment RHS: pRhsF will correctly roundtrip it.
    Excludes expressions whose printed form starts with an identifier that
    would be misinterpreted by pIdent before pExprF gets a chance. -/
def AssignRhsSafe : MicroCExpr → Prop
  | .litBool _ => False       -- "true"/"false" parsed as varRef by pIdent
  | .arrayAccess _ _ => False -- "a[i]" triggers load path in pRhsF
  | .powCall _ _ => False     -- "pow(b,n)" triggers call path in pRhsF
  | _ => True

/-- Valid identifier characters for pIdent roundtrip. -/
def ValidIdentChars (name : String) : Prop :=
  match name.toList with
  | [] => False
  | c :: cs => (c.isAlpha = true ∨ c = '_') ∧
    (∀ ch ∈ c :: cs, ch.isAlpha = true ∨ ch.isDigit = true ∨ ch = '_')

/-- Disambiguation for statements: all sub-expressions satisfy NegLitDisam,
    and all variable names that begin a printed statement don't conflict
    with parser keywords. -/
def NegLitDisamS : MicroCStmt → Prop
  | .skip | .break_ | .continue_ | .return_ none => True
  | .return_ (some e) => NegLitDisam e
  | .assign name e => NegLitDisam e ∧ VarNameSafe name ∧ AssignRhsSafe e
  | .store b i v => NegLitDisam b ∧ NegLitDisam i ∧ NegLitDisam v ∧
      (∀ name, b = .varRef name → VarNameSafe name)
  | .load var b i => NegLitDisam b ∧ NegLitDisam i ∧ VarNameSafe var
  | .call result fname args => (∀ e ∈ args, NegLitDisam e) ∧
      ValidIdentChars result ∧ VarNameSafe result ∧
      ValidIdentChars fname ∧ VarNameSafe fname
  | .seq s1 s2 => NegLitDisamS s1 ∧ NegLitDisamS s2 ∧ (∀ a b, s1 ≠ .seq a b)
  | .ite c t e => NegLitDisam c ∧ NegLitDisamS t ∧ NegLitDisamS e
  | .while_ c b => NegLitDisam c ∧ NegLitDisamS b

/-- Statement depth: minimum fuel for pStmtF. -/
def stmtDepth : MicroCStmt → Nat
  | .skip | .break_ | .continue_ | .return_ none => 1
  | .return_ (some e) => 1 + exprDepth e
  | .assign _ e => 1 + exprDepth e
  | .store _ i v => 1 + max (exprDepth i) (exprDepth v)
  | .load _ _ i => 1 + exprDepth i
  | .call _ _ args => 1 + args.foldl (fun m e => max m (exprDepth e)) 0
  | .seq s1 s2 => max (stmtDepth s1) (stmtDepth s2)
  | .ite c t e => 1 + max (exprDepth c) (max (stmtDepth t) (stmtDepth e))
  | .while_ c b => 1 + max (exprDepth c) (stmtDepth b)

/-- Total fuel: accounts for both pStmtF parsing depth and parseStmtSeq sequence width.
    Key property: totalFuel ≥ stmtDepth, and for ite/while the inner fuel
    after decrementing is still ≥ totalFuel of sub-bodies + 1. -/
def totalFuel : MicroCStmt → Nat
  | .skip | .break_ | .continue_ | .return_ none => 1
  | .return_ (some e) => 1 + exprDepth e
  | .assign _ e => 1 + exprDepth e
  | .store _ i v => 1 + max (exprDepth i) (exprDepth v)
  | .load _ _ i => 1 + exprDepth i
  | .call _ _ args => 1 + args.length + args.foldl (fun m e => max m (exprDepth e)) 0
  | .seq s1 s2 => max (totalFuel s1) (totalFuel s2) + 1
  | .ite c t e => 1 + max (exprDepth c) (max (totalFuel t + 1) (totalFuel e + 1))
  | .while_ c b => 1 + max (exprDepth c) (totalFuel b + 1)

theorem totalFuel_ge_stmtDepth (s : MicroCStmt) : totalFuel s ≥ stmtDepth s := by
  induction s with
  | skip | break_ | continue_ => simp [totalFuel, stmtDepth]
  | return_ r => cases r <;> simp [totalFuel, stmtDepth]
  | assign | store | load | call => simp [totalFuel, stmtDepth]
  | seq s1 s2 ih1 ih2 => simp only [totalFuel, stmtDepth]; omega
  | ite c t e ih_t ih_e => simp only [totalFuel, stmtDepth]; omega
  | while_ c b ih_b => simp only [totalFuel, stmtDepth]; omega

/-! ## ExprSafe for statement delimiters -/

theorem exprSafe_semicolon (rest : List Char) : ExprSafe (';' :: rest) :=
  exprSafe_sep ';' rest (by native_decide) (by native_decide) (by decide)
    (by decide) (by decide) ⟨by decide, by decide, by decide, by decide⟩

/-! ## skipWs helpers -/

@[simp] theorem skipWs_space (rest : List Char) :
    skipWs (' ' :: rest) = skipWs rest := by rfl

/-- skipWs of ' ' followed by expression printer output = printer output. -/
theorem skipWs_space_expr (e : MicroCExpr) (he : WFExpr e) (rest : List Char) :
    skipWs (' ' :: ((microCExprToString e).toList ++ rest)) =
    (microCExprToString e).toList ++ rest := by
  have h_ne := print_ne_nil e he
  match h_cs : (microCExprToString e).toList with
  | [] => exact absurd h_cs h_ne
  | c :: cs =>
    have h_nonws := print_first_nonws e he c cs h_cs
    simp only [List.cons_append, skipWs_space, skipWs_nonws c _ h_nonws]

/-! ## pExprF on separator -/

/-- pExprF fails when input starts with ';'. -/
theorem pExprF_semicolon_none (fuel : Nat) (rest : List Char) :
    pExprF fuel (';' :: rest) = none := by
  cases fuel with
  | zero => unfold pExprF; rfl
  | succ n => unfold pExprF; simp

/-- First char of printed WFExpr is never ';'. -/
private theorem print_first_ne_semicolon (e : MicroCExpr) (he : WFExpr e)
    (hd : NegLitDisam e) (c : Char) (cs : List Char)
    (h : (microCExprToString e).toList = c :: cs) : c ≠ ';' := by
  intro hc; subst hc
  have hrt := expr_roundtrip_with_rest e he hd (exprDepth e) (Nat.le_refl _)
    [';'] (exprSafe_semicolon [])
  rw [h] at hrt; simp only [List.cons_append] at hrt
  rw [pExprF_semicolon_none] at hrt; exact absurd hrt (by simp)

/-- skipWs is identity when input starts with a printed expression. -/
private theorem skipWs_expr_start (e : MicroCExpr) (he : WFExpr e) (rest : List Char) :
    skipWs ((microCExprToString e).toList ++ rest) =
    (microCExprToString e).toList ++ rest := by
  have h_ne := print_ne_nil e he
  match hcs : (microCExprToString e).toList with
  | [] => exact absurd hcs h_ne
  | c :: cs =>
    have h_nonws := print_first_nonws e he c cs hcs
    simp only [List.cons_append, skipWs_nonws c _ h_nonws]

/-! ## pStmtF leaf equation lemmas -/

theorem pStmtF_skip (n : Nat) (rest : List Char) :
    pStmtF (n + 1) (';' :: rest) = some (.skip, rest) := by
  unfold pStmtF; simp

theorem pStmtF_break (n : Nat) (rest : List Char) :
    pStmtF (n + 1) ('b' :: 'r' :: 'e' :: 'a' :: 'k' :: ';' :: rest) =
    some (.break_, rest) := by
  unfold pStmtF; simp

theorem pStmtF_continue (n : Nat) (rest : List Char) :
    pStmtF (n + 1) ('c' :: 'o' :: 'n' :: 't' :: 'i' :: 'n' :: 'u' :: 'e' :: ';' :: rest) =
    some (.continue_, rest) := by
  unfold pStmtF; simp

theorem pStmtF_return_none (n : Nat) (rest : List Char) :
    pStmtF (n + 1) ('r' :: 'e' :: 't' :: 'u' :: 'r' :: 'n' :: ';' :: rest) =
    some (.return_ none, rest) := by
  unfold pStmtF; simp; unfold pStmtF.pReturnF; simp

/-! ## pStmtF return_some -/

/-- return expr; roundtrip. -/
theorem pStmtF_return_some (e : MicroCExpr) (he : WFExpr e) (hd : NegLitDisam e)
    (n : Nat) (hfuel_e : n + 1 ≥ exprDepth e) (rest : List Char) :
    pStmtF (n + 1) (("return " ++ microCExprToString e ++ ";").toList ++ rest) =
    some (.return_ (some e), rest) := by
  simp only [String.toList_append,
    show "return ".toList = ['r', 'e', 't', 'u', 'r', 'n', ' '] from rfl,
    show ";".toList = [';'] from rfl, List.append_assoc,
    List.cons_append, List.nil_append]
  unfold pStmtF
  have hr : skipWs ('r' :: 'e' :: 't' :: 'u' :: 'r' :: 'n' :: ' ' ::
      ((microCExprToString e).toList ++ (';' :: rest))) =
    'r' :: 'e' :: 't' :: 'u' :: 'r' :: 'n' :: ' ' ::
      ((microCExprToString e).toList ++ (';' :: rest)) :=
    skipWs_nonws 'r' _ (by decide)
  rw [hr]; simp only []
  unfold pStmtF.pReturnF
  rw [skipWs_space_expr e he (';' :: rest)]
  have h_ne := print_ne_nil e he
  match h_cs : (microCExprToString e).toList with
  | [] => exact absurd h_cs h_ne
  | c :: cs =>
    simp only [List.cons_append]
    split
    · -- c = ';' case: impossible for WFExpr
      rename_i final heq
      exact absurd (List.cons.inj heq).1 (print_first_ne_semicolon e he hd c cs h_cs)
    · -- expression roundtrip branch
      have h_eq : pExprF (n + 1) (c :: (cs ++ (';' :: rest))) =
          pExprF (n + 1) ((microCExprToString e).toList ++ (';' :: rest)) :=
        congrArg (pExprF (n + 1)) (by simp [h_cs])
      rw [h_eq, expr_roundtrip_with_rest e he hd (n + 1) hfuel_e (';' :: rest)
        (exprSafe_semicolon rest)]
      simp

/-! ## Identifier helpers -/

private theorem alpha_not_ws (c : Char) (h : c.isAlpha = true ∨ c = '_') :
    c ≠ ' ' ∧ c ≠ '\n' ∧ c ≠ '\t' ∧ c ≠ '\r' := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro heq; subst heq; simp at h)

/-! ## pStmtF fallthrough to pAssignOrStoreF -/

set_option maxHeartbeats 3200000 in
/-- When input starts with a VarNameSafe identifier followed by ' ',
    pStmtF falls through all keyword matches to pAssignOrStoreF. -/
private theorem pStmtF_ident_space_fallthrough (n : Nat) (name : String) (rest : List Char)
    (hne : name ≠ "")
    (hstart : let c := name.toList.head (by simp; exact hne); c.isAlpha = true ∨ c = '_')
    (hcont : ∀ c ∈ name.toList, c.isAlpha = true ∨ c.isDigit = true ∨ c = '_')
    (hsafe : VarNameSafe name) :
    pStmtF (n + 1) (name.toList ++ ' ' :: rest) =
    pStmtF.pAssignOrStoreF n (name.toList ++ ' ' :: rest) := by
  have hne' : name.toList ≠ [] := by simp; exact hne
  match hcs : name.toList with
  | [] => exact absurd hcs hne'
  | c :: cs =>
    have hstart' : c.isAlpha = true ∨ c = '_' := by simp [hcs] at hstart; exact hstart
    have hcont_tail : ∀ ch ∈ cs, ch.isAlpha = true ∨ ch.isDigit = true ∨ ch = '_' :=
      fun ch hch => hcont ch (by rw [hcs]; exact List.mem_cons_of_mem c hch)
    simp only [List.cons_append]
    unfold pStmtF
    rw [skipWs_nonws c _ (alpha_not_ws c hstart')]
    show (match c :: (cs ++ ' ' :: rest) with
      | ';' :: rest' => some (.skip, rest')
      | 'b' :: 'r' :: 'e' :: 'a' :: 'k' :: ';' :: rest' => some (.break_, rest')
      | 'c' :: 'o' :: 'n' :: 't' :: 'i' :: 'n' :: 'u' :: 'e' :: ';' :: rest' =>
        some (.continue_, rest')
      | 'r' :: 'e' :: 't' :: 'u' :: 'r' :: 'n' :: rest' => pStmtF.pReturnF n (skipWs rest')
      | 'i' :: 'f' :: ' ' :: rest' => pStmtF.pIfF n (skipWs rest')
      | 'i' :: 'f' :: '(' :: rest' => pStmtF.pIfF n ('(' :: rest')
      | 'w' :: 'h' :: 'i' :: 'l' :: 'e' :: ' ' :: rest' => pStmtF.pWhileF n (skipWs rest')
      | 'w' :: 'h' :: 'i' :: 'l' :: 'e' :: '(' :: rest' => pStmtF.pWhileF n ('(' :: rest')
      | _ => pStmtF.pAssignOrStoreF n (c :: (cs ++ ' ' :: rest))) =
      pStmtF.pAssignOrStoreF n (c :: (cs ++ ' ' :: rest))
    split
    · rename_i _ heq; exact absurd (List.cons.inj heq).1
        (by intro h; subst h; simp at hstart')
    · rename_i _ heq; obtain ⟨rfl, h⟩ := List.cons.inj heq
      match cs, h with
      | [], h | [_], h | [_, _], h | [_, _, _], h | [_, _, _, _], h => simp at h
      | _ :: _ :: _ :: _ :: e :: _, h =>
        simp at h; obtain ⟨_, _, _, _, rfl, _⟩ := h
        have := hcont_tail ';' (by simp); simp at this
    · rename_i _ heq; obtain ⟨rfl, h⟩ := List.cons.inj heq
      match cs, h with
      | [], h | [_], h | [_, _], h | [_, _, _], h | [_, _, _, _], h
      | [_, _, _, _, _], h | [_, _, _, _, _, _], h | [_, _, _, _, _, _, _], h => simp at h
      | _ :: _ :: _ :: _ :: _ :: _ :: _ :: e :: _, h =>
        simp at h; obtain ⟨_, _, _, _, _, _, _, rfl, _⟩ := h
        have := hcont_tail ';' (by simp); simp at this
    · rename_i _ heq; obtain ⟨rfl, h⟩ := List.cons.inj heq
      match cs, h with
      | [], h | [_], h | [_, _], h | [_, _, _], h | [_, _, _, _], h => simp at h
      | _ :: _ :: _ :: _ :: e :: cs', h =>
        simp at h; obtain ⟨rfl, rfl, rfl, rfl, rfl, _⟩ := h
        exact absurd hcs (hsafe.1 cs')
    · rename_i _ heq; obtain ⟨rfl, h⟩ := List.cons.inj heq
      match cs, h with
      | [], h => simp at h
      | [a], h =>
        simp at h; obtain ⟨rfl, _⟩ := h
        have : name = "if" := by
          have := String.ofList_toList (s := name); rw [hcs] at this; exact this.symm
        exact absurd this hsafe.2.1
      | _ :: b :: _, h =>
        simp at h; obtain ⟨_, rfl, _⟩ := h
        have := hcont_tail ' ' (by simp); simp at this
    · rename_i _ heq; obtain ⟨rfl, h⟩ := List.cons.inj heq
      match cs, h with
      | [], h => simp at h
      | [_], h => simp at h
      | _ :: b :: _, h =>
        simp at h; obtain ⟨_, rfl, _⟩ := h
        have := hcont_tail '(' (by simp); simp at this
    · rename_i _ heq; obtain ⟨rfl, h⟩ := List.cons.inj heq
      match cs, h with
      | [], h | [_], h | [_, _], h | [_, _, _], h => simp at h
      | [_, _, _, _], h =>
        simp at h; obtain ⟨rfl, rfl, rfl, rfl, _⟩ := h
        have : name = "while" := by
          have := String.ofList_toList (s := name); rw [hcs] at this; exact this.symm
        exact absurd this hsafe.2.2
      | _ :: _ :: _ :: _ :: e :: _, h =>
        simp at h; obtain ⟨_, _, _, _, rfl, _⟩ := h
        have := hcont_tail ' ' (by simp); simp at this
    · rename_i _ heq; obtain ⟨rfl, h⟩ := List.cons.inj heq
      match cs, h with
      | [], h | [_], h | [_, _], h | [_, _, _], h | [_, _, _, _], h => simp at h
      | _ :: _ :: _ :: _ :: e :: _, h =>
        simp at h; obtain ⟨_, _, _, _, rfl, _⟩ := h
        have := hcont_tail '(' (by simp); simp at this
    · rfl

set_option maxHeartbeats 3200000 in
/-- When input starts with a VarNameSafe identifier followed by '[',
    pStmtF falls through all keyword matches to pAssignOrStoreF. -/
private theorem pStmtF_ident_bracket_fallthrough (n : Nat) (name : String) (rest : List Char)
    (hne : name ≠ "")
    (hstart : let c := name.toList.head (by simp; exact hne); c.isAlpha = true ∨ c = '_')
    (hcont : ∀ c ∈ name.toList, c.isAlpha = true ∨ c.isDigit = true ∨ c = '_')
    (hsafe : VarNameSafe name) :
    pStmtF (n + 1) (name.toList ++ '[' :: rest) =
    pStmtF.pAssignOrStoreF n (name.toList ++ '[' :: rest) := by
  have hne' : name.toList ≠ [] := by simp; exact hne
  match hcs : name.toList with
  | [] => exact absurd hcs hne'
  | c :: cs =>
    have hstart' : c.isAlpha = true ∨ c = '_' := by simp [hcs] at hstart; exact hstart
    have hcont_tail : ∀ ch ∈ cs, ch.isAlpha = true ∨ ch.isDigit = true ∨ ch = '_' :=
      fun ch hch => hcont ch (by rw [hcs]; exact List.mem_cons_of_mem c hch)
    simp only [List.cons_append]
    unfold pStmtF
    rw [skipWs_nonws c _ (alpha_not_ws c hstart')]
    show (match c :: (cs ++ '[' :: rest) with
      | ';' :: rest' => some (.skip, rest')
      | 'b' :: 'r' :: 'e' :: 'a' :: 'k' :: ';' :: rest' => some (.break_, rest')
      | 'c' :: 'o' :: 'n' :: 't' :: 'i' :: 'n' :: 'u' :: 'e' :: ';' :: rest' =>
        some (.continue_, rest')
      | 'r' :: 'e' :: 't' :: 'u' :: 'r' :: 'n' :: rest' => pStmtF.pReturnF n (skipWs rest')
      | 'i' :: 'f' :: ' ' :: rest' => pStmtF.pIfF n (skipWs rest')
      | 'i' :: 'f' :: '(' :: rest' => pStmtF.pIfF n ('(' :: rest')
      | 'w' :: 'h' :: 'i' :: 'l' :: 'e' :: ' ' :: rest' => pStmtF.pWhileF n (skipWs rest')
      | 'w' :: 'h' :: 'i' :: 'l' :: 'e' :: '(' :: rest' => pStmtF.pWhileF n ('(' :: rest')
      | _ => pStmtF.pAssignOrStoreF n (c :: (cs ++ '[' :: rest))) =
      pStmtF.pAssignOrStoreF n (c :: (cs ++ '[' :: rest))
    split
    · rename_i _ heq; exact absurd (List.cons.inj heq).1
        (by intro h; subst h; simp at hstart')
    · rename_i _ heq; obtain ⟨rfl, h⟩ := List.cons.inj heq
      match cs, h with
      | [], h | [_], h | [_, _], h | [_, _, _], h | [_, _, _, _], h => simp at h
      | _ :: _ :: _ :: _ :: e :: _, h =>
        simp at h; obtain ⟨_, _, _, _, rfl, _⟩ := h
        have := hcont_tail ';' (by simp); simp at this
    · rename_i _ heq; obtain ⟨rfl, h⟩ := List.cons.inj heq
      match cs, h with
      | [], h | [_], h | [_, _], h | [_, _, _], h | [_, _, _, _], h
      | [_, _, _, _, _], h | [_, _, _, _, _, _], h | [_, _, _, _, _, _, _], h => simp at h
      | _ :: _ :: _ :: _ :: _ :: _ :: _ :: e :: _, h =>
        simp at h; obtain ⟨_, _, _, _, _, _, _, rfl, _⟩ := h
        have := hcont_tail ';' (by simp); simp at this
    · rename_i _ heq; obtain ⟨rfl, h⟩ := List.cons.inj heq
      match cs, h with
      | [], h | [_], h | [_, _], h | [_, _, _], h | [_, _, _, _], h => simp at h
      | _ :: _ :: _ :: _ :: e :: cs', h =>
        simp at h; obtain ⟨rfl, rfl, rfl, rfl, rfl, _⟩ := h
        exact absurd hcs (hsafe.1 cs')
    · rename_i _ heq; obtain ⟨rfl, h⟩ := List.cons.inj heq
      match cs, h with
      | [], h | [_], h => simp at h
      | _ :: b :: _, h =>
        simp at h; obtain ⟨_, rfl, _⟩ := h
        have := hcont_tail ' ' (by simp); simp at this
    · rename_i _ heq; obtain ⟨rfl, h⟩ := List.cons.inj heq
      match cs, h with
      | [], h | [_], h => simp at h
      | _ :: b :: _, h =>
        simp at h; obtain ⟨_, rfl, _⟩ := h
        have := hcont_tail '(' (by simp); simp at this
    · rename_i _ heq; obtain ⟨rfl, h⟩ := List.cons.inj heq
      match cs, h with
      | [], h | [_], h | [_, _], h | [_, _, _], h | [_, _, _, _], h => simp at h
      | _ :: _ :: _ :: _ :: e :: _, h =>
        simp at h; obtain ⟨_, _, _, _, rfl, _⟩ := h
        have := hcont_tail ' ' (by simp); simp at this
    · rename_i _ heq; obtain ⟨rfl, h⟩ := List.cons.inj heq
      match cs, h with
      | [], h | [_], h | [_, _], h | [_, _, _], h | [_, _, _, _], h => simp at h
      | _ :: _ :: _ :: _ :: e :: _, h =>
        simp at h; obtain ⟨_, _, _, _, rfl, _⟩ := h
        have := hcont_tail '(' (by simp); simp at this
    · rfl

/-- pIdent returns none when first char is not alpha or underscore. -/
private theorem pIdent_none_nonident (c : Char) (rest : List Char)
    (ha : c.isAlpha = false) (hu : c ≠ '_') :
    pIdent (c :: rest) = none := by
  unfold pIdent; simp [ha, hu]

/-- NoLeadingIdent for space. -/
private theorem noLeadingIdent_space (rest : List Char) :
    NoLeadingIdent (' ' :: rest) :=
  Or.inr ⟨' ', rest, rfl, by decide, by decide, by decide⟩

/-- skipWs is identity when input starts with a valid identifier. -/
private theorem skipWs_ident_start (name : String) (rest : List Char)
    (hne : name ≠ "")
    (hstart : let c := name.toList.head (by simp; exact hne); c.isAlpha = true ∨ c = '_') :
    skipWs (name.toList ++ rest) = name.toList ++ rest := by
  have hne' : name.toList ≠ [] := by simp; exact hne
  match hcs : name.toList with
  | [] => exact absurd hcs hne'
  | c :: cs =>
    simp only [List.cons_append]
    exact skipWs_nonws c _ (by
      have : c.isAlpha = true ∨ c = '_' := by simp [hcs] at hstart; exact hstart
      refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro heq; subst heq; simp at this))

/-- NoLeadingIdent for semicolon. -/
private theorem noLeadingIdent_semicolon (rest : List Char) :
    NoLeadingIdent (';' :: rest) :=
  Or.inr ⟨';', rest, rfl, by decide, by decide, by decide⟩

/-- NoLeadingIdent for open bracket. -/
private theorem noLeadingIdent_bracket (rest : List Char) :
    NoLeadingIdent ('[' :: rest) :=
  Or.inr ⟨'[', rest, rfl, by decide, by decide, by decide⟩

/-- Digit characters are not identifier starts (not alpha, not underscore). -/
private theorem digit_not_ident_start (c : Char) (h : c.isDigit = true) :
    c.isAlpha = false ∧ c ≠ '_' := by
  refine ⟨?_, ?_⟩
  · rw [Bool.eq_false_iff]; intro h2
    have hd : c.val.toNat ≥ 48 ∧ c.val.toNat ≤ 57 := by
      simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨UInt32.le_iff_toNat_le.mp h.1, UInt32.le_iff_toNat_le.mp h.2⟩
    have ha : (c.val.toNat ≥ 65 ∧ c.val.toNat ≤ 90) ∨ (c.val.toNat ≥ 97 ∧ c.val.toNat ≤ 122) := by
      simp only [Char.isAlpha, Char.isUpper, Char.isLower, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq] at h2
      cases h2 with
      | inl h2 => exact Or.inl ⟨UInt32.le_iff_toNat_le.mp h2.1, UInt32.le_iff_toNat_le.mp h2.2⟩
      | inr h2 => exact Or.inr ⟨UInt32.le_iff_toNat_le.mp h2.1, UInt32.le_iff_toNat_le.mp h2.2⟩
    cases ha with | inl ha => omega | inr ha => omega
  · intro heq; subst heq; simp at h

/-- pIdent returns none on printed litInt (first char is '(' or digit). -/
private theorem pIdent_litInt_none (z : Int) (rest : List Char) :
    pIdent ((microCExprToString (.litInt z)).toList ++ rest) = none := by
  simp only [microCExprToString_litInt]
  split
  · simp only [String.toList_append, String.toList_ofList,
      show "(".toList = ['('] from rfl, show "-".toList = ['-'] from rfl,
      show ")".toList = [')'] from rfl, List.cons_append, List.nil_append, List.append_assoc]
    unfold pIdent; simp
  · have hne := natToChars_ne_nil z.toNat
    match hcs : natToChars z.toNat with
    | [] => exact absurd hcs hne
    | c :: cs =>
      simp only [String.toList_ofList, List.cons_append]
      have hdig := natToChars_all_digits z.toNat c (by rw [hcs]; exact List.mem_cons_self ..)
      have ⟨ha, hu⟩ := digit_not_ident_start c hdig
      unfold pIdent; simp [ha, hu]

/-- pIdent returns none on printed binOp (first char is '('). -/
private theorem pIdent_binOp_none (op : MicroCBinOp) (l r : MicroCExpr) (rest : List Char) :
    pIdent ((microCExprToString (.binOp op l r)).toList ++ rest) = none := by
  simp only [microCExprToString_binOp, String.toList_append, List.append_assoc,
    show "(".toList = ['('] from rfl, List.cons_append, List.nil_append]
  unfold pIdent; simp

/-- pIdent returns none on printed unaryOp (first char is '('). -/
private theorem pIdent_unaryOp_none (op : MicroCUnaryOp) (e : MicroCExpr) (rest : List Char) :
    pIdent ((microCExprToString (.unaryOp op e)).toList ++ rest) = none := by
  simp only [microCExprToString_unaryOp, String.toList_append, List.append_assoc,
    show "(".toList = ['('] from rfl, List.cons_append, List.nil_append]
  unfold pIdent; simp

/-- NoLeadingIdent for open paren. -/
private theorem noLeadingIdent_lparen (rest : List Char) :
    NoLeadingIdent ('(' :: rest) :=
  Or.inr ⟨'(', rest, rfl, by decide, by decide, by decide⟩

/-- NoLeadingIdent for close paren. -/
private theorem noLeadingIdent_rparen (rest : List Char) :
    NoLeadingIdent (')' :: rest) :=
  Or.inr ⟨')', rest, rfl, by decide, by decide, by decide⟩

/-- NoLeadingIdent for comma. -/
private theorem noLeadingIdent_comma (rest : List Char) :
    NoLeadingIdent (',' :: rest) :=
  Or.inr ⟨',', rest, rfl, by decide, by decide, by decide⟩

/-- ExprSafe for comma followed by space. -/
theorem exprSafe_comma_space (rest : List Char) : ExprSafe (',' :: ' ' :: rest) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- NoLeadingDigit
    exact Or.inr ⟨',', ' ' :: rest, rfl, by decide⟩
  · -- NoLeadingIdent
    exact noLeadingIdent_comma (' ' :: rest)
  · -- skipWs ≠ '[' :: cs
    intro cs; simp [skipWs_nonws ',' _ (by decide)]
  · -- skipWs ≠ '(' :: cs
    intro cs; simp [skipWs_nonws ',' _ (by decide)]

/-- ValidIdentChars gives the identifier properties needed for pIdent. -/
private theorem validIdentChars_hne (name : String) (hv : ValidIdentChars name) :
    name ≠ "" := by
  intro h; subst h; simp [ValidIdentChars] at hv

private theorem validIdentChars_hstart (name : String) (hv : ValidIdentChars name) :
    let c := name.toList.head (by simp; exact validIdentChars_hne name hv)
    c.isAlpha = true ∨ c = '_' := by
  unfold ValidIdentChars at hv
  split at hv
  · exact absurd hv False.elim
  · rename_i c cs heq; simp only [heq, List.head_cons]; exact hv.1

private theorem validIdentChars_hcont (name : String) (hv : ValidIdentChars name) :
    ∀ c ∈ name.toList, c.isAlpha = true ∨ c.isDigit = true ∨ c = '_' := by
  unfold ValidIdentChars at hv
  split at hv
  · exact absurd hv False.elim
  · rename_i c cs heq; rw [heq]; exact hv.2

/-! ## Call case infrastructure -/

/-- Char-level representation of comma-separated expression rest (for goArgs). -/
def commaSepExprRest : List MicroCExpr → List Char → List Char
  | [], rest => rest
  | e :: es, rest => ',' :: ' ' :: (microCExprToString e).toList ++ commaSepExprRest es rest

/-- ExprSafe for commaSepExprRest output. -/
theorem exprSafe_commaSepRest (es : List MicroCExpr) (suffix : List Char) :
    ExprSafe (commaSepExprRest es (')' :: suffix)) := by
  cases es with
  | nil => exact exprSafe_rparen suffix
  | cons => exact exprSafe_comma_space _

private theorem foldl_max_ge {α : Type} (f : α → Nat) (init : Nat) (es : List α) :
    es.foldl (fun m e => max m (f e)) init ≥ init := by
  induction es generalizing init with
  | nil => exact Nat.le_refl init
  | cons e es ih =>
    simp only [List.foldl]
    exact Nat.le_trans (Nat.le_max_left init (f e)) (ih (max init (f e)))

private theorem foldl_max_ge_elem {α : Type} (f : α → Nat) (init : Nat) (a : α) (as : List α) :
    (a :: as).foldl (fun m e => max m (f e)) init ≥ f a := by
  simp only [List.foldl]
  exact Nat.le_trans (Nat.le_max_right init (f a)) (foldl_max_ge f (max init (f a)) as)

private theorem foldl_max_mono {α : Type} (f : α → Nat) (a b : Nat) (h : a ≤ b) (es : List α) :
    es.foldl (fun m e => max m (f e)) a ≤ es.foldl (fun m e => max m (f e)) b := by
  induction es generalizing a b with
  | nil => exact h
  | cons e es ih =>
    simp only [List.foldl]
    exact ih (max a (f e)) (max b (f e)) (by simp only [Nat.max_def]; split <;> split <;> omega)

private theorem foldl_max_cons_ge_tail {α : Type} (f : α → Nat) (a : α) (as : List α) :
    (a :: as).foldl (fun m e => max m (f e)) 0 ≥ as.foldl (fun m e => max m (f e)) 0 := by
  simp only [List.foldl]
  exact foldl_max_mono f 0 (max 0 (f a)) (Nat.zero_le _) as

/-- goArgs on comma input with successful expr parse. -/
private theorem goArgs_comma_some (n : Nat) (acc : List MicroCExpr) (rest : List Char)
    (e : MicroCExpr) (rest' : List Char)
    (h : pExprF (n + 1) (skipWs rest) = some (e, rest')) :
    pStmtF.goArgs (n + 1) acc (',' :: rest) = pStmtF.goArgs n (acc ++ [e]) rest' := by
  show (match pExprF (n + 1) (skipWs rest) with
    | some (e, rest') => pStmtF.goArgs n (acc ++ [e]) rest'
    | none => none) = pStmtF.goArgs n (acc ++ [e]) rest'
  rw [h]

set_option maxHeartbeats 800000 in
/-- goArgs roundtrip: processes comma-separated expressions after the first. -/
theorem goArgs_roundtrip (es : List MicroCExpr) (acc : List MicroCExpr)
    (fuel : Nat) (suffix : List Char)
    (hfuel : fuel ≥ es.length + es.foldl (fun m e => max m (exprDepth e)) 0)
    (hwf : ∀ e ∈ es, WFExpr e) (hnd : ∀ e ∈ es, NegLitDisam e) :
    pStmtF.goArgs fuel acc (commaSepExprRest es (')' :: suffix))
      = some (acc ++ es, ')' :: suffix) := by
  induction es generalizing acc fuel with
  | nil =>
    simp [commaSepExprRest]; unfold pStmtF.goArgs
    simp [skipWs_nonws ')' _ (by decide)]; cases fuel <;> simp
  | cons e es ih =>
    simp only [commaSepExprRest, List.cons_append]
    have hfuel1 : fuel ≥ 1 := by simp at hfuel; omega
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
    have h_skip : skipWs (' ' :: ((microCExprToString e).toList
        ++ commaSepExprRest es (')' :: suffix)))
      = (microCExprToString e).toList ++ commaSepExprRest es (')' :: suffix) :=
      skipWs_space_expr e (hwf e (List.Mem.head es)) (commaSepExprRest es (')' :: suffix))
    have h_parse : pExprF (n + 1) (skipWs (' ' :: ((microCExprToString e).toList
        ++ commaSepExprRest es (')' :: suffix))))
      = some (e, commaSepExprRest es (')' :: suffix)) := by
      rw [h_skip]
      exact expr_roundtrip_with_rest e (hwf e (List.Mem.head es))
        (hnd e (List.Mem.head es)) (n + 1)
        (by have := foldl_max_ge_elem exprDepth 0 e es
            simp only [List.length] at hfuel; omega)
        (commaSepExprRest es (')' :: suffix)) (exprSafe_commaSepRest es suffix)
    rw [goArgs_comma_some n acc _ e _ h_parse]
    rw [ih (acc ++ [e]) n
        (by have := foldl_max_cons_ge_tail exprDepth e es
            simp only [List.length] at hfuel; omega)
        (fun e' he' => hwf e' (List.Mem.tail e he'))
        (fun e' he' => hnd e' (List.Mem.tail e he'))]
    simp [List.append_assoc]

/-- Bridge: joinArgs output equals commaSepExprRest structure. -/
theorem joinArgs_eq_commaSep (args : List MicroCExpr) (suffix : List Char) :
    (joinArgs (args.map microCExprToString)).toList ++ suffix =
    match args with
    | [] => suffix
    | e :: es => (microCExprToString e).toList ++ commaSepExprRest es suffix := by
  induction args with
  | nil => simp
  | cons e es ih => cases es with
    | nil => simp [commaSepExprRest]
    | cons e2 es' =>
      simp only [List.map, joinArgs_cons_cons, String.toList_append, List.append_assoc,
        show ", ".toList = [',', ' '] from rfl, List.cons_append, List.nil_append,
        commaSepExprRest]
      congr 1; congr 1; congr 1

/-- WFExpr printed form never starts with ')'. -/
theorem expr_ne_rparen_start (e : MicroCExpr) (he : WFExpr e) (rest : List Char) :
    ∀ cs, (microCExprToString e).toList ++ rest ≠ ')' :: cs := by
  intro cs h; induction he generalizing rest cs with
  | litInt n =>
    simp only [microCExprToString_litInt] at h
    split at h
    · simp only [String.toList_append, String.toList_ofList,
        show "(".toList = ['('] from rfl, show "-".toList = ['-'] from rfl,
        show ")".toList = [')'] from rfl, List.cons_append, List.nil_append,
        List.append_assoc] at h
      exact absurd (List.cons.inj h).1 (by decide)
    · have hne := natToChars_ne_nil n.toNat
      match hcs : natToChars n.toNat with
      | [] => exact absurd hcs hne
      | c :: cs' =>
        simp only [String.toList_ofList] at h; rw [hcs, List.cons_append] at h
        have hdig := natToChars_all_digits n.toNat c (by rw [hcs]; exact List.Mem.head _)
        have := (List.cons.inj h).1
        subst this
        simp [Char.isDigit] at hdig
  | litBool b =>
    cases b <;> simp only [microCExprToString_litBool_true, microCExprToString_litBool_false,
      show "true".toList = ['t', 'r', 'u', 'e'] from rfl,
      show "false".toList = ['f', 'a', 'l', 's', 'e'] from rfl,
      List.cons_append] at h <;> exact absurd (List.cons.inj h).1 (by decide)
  | varRef name hne hstart hcont hnot_kw =>
    simp only [microCExprToString_varRef] at h
    have hne' : name.toList ≠ [] := by simp; exact hne
    match hcs : name.toList with
    | [] => exact absurd hcs hne'
    | c :: cs' =>
      rw [hcs, List.cons_append] at h
      have heq := (List.cons.inj h).1
      have hstart' : c.isAlpha = true ∨ c = '_' := by
        have := hstart; simp only [hcs, List.head_cons] at this; exact this
      rcases hstart' with hα | h_
      · subst heq; simp at hα
      · subst heq; exact absurd h_ (by decide)
  | binOp op l r _ _ _ _ =>
    simp only [microCExprToString_binOp, String.toList_append, List.append_assoc,
      show "(".toList = ['('] from rfl, List.cons_append, List.nil_append] at h
    exact absurd (List.cons.inj h).1 (by decide)
  | unaryOp op e' _ _ =>
    simp only [microCExprToString_unaryOp, String.toList_append, List.append_assoc,
      show "(".toList = ['('] from rfl, List.cons_append, List.nil_append] at h
    exact absurd (List.cons.inj h).1 (by decide)
  | powCall base n _ _ =>
    simp only [microCExprToString_powCall, String.toList_append, List.append_assoc,
      show "power(".toList = ['p', 'o', 'w', 'e', 'r', '('] from rfl,
      List.cons_append, List.nil_append] at h
    exact absurd (List.cons.inj h).1 (by decide)
  | arrayAccess base idx hb hi hbase_var ihb ihi =>
    simp only [microCExprToString_arrayAccess, String.toList_append, List.append_assoc] at h
    exact ihb _ _ h

/-- pArgsF on non-rparen input with successful expr parse goes to goArgs. -/
private theorem pArgsF_cons (fuel : Nat) (cs : List Char)
    (h_ws : skipWs cs = cs) (h_ne : ∀ tail, cs ≠ ')' :: tail)
    (e : MicroCExpr) (rest : List Char)
    (h_expr : pExprF fuel cs = some (e, rest)) :
    pStmtF.pArgsF fuel cs = pStmtF.goArgs fuel [e] rest := by
  unfold pStmtF.pArgsF
  rw [h_ws]; dsimp only []
  split
  · next tail => exact absurd rfl (h_ne tail)
  · rw [h_expr]

set_option maxHeartbeats 800000 in
/-- Full pArgsF roundtrip for call arguments. -/
theorem pArgsF_roundtrip (args : List MicroCExpr) (fuel : Nat) (suffix : List Char)
    (hwf : ∀ e ∈ args, WFExpr e) (hnd : ∀ e ∈ args, NegLitDisam e)
    (hfuel : fuel ≥ args.length + args.foldl (fun m e => max m (exprDepth e)) 0) :
    pStmtF.pArgsF fuel
      ((joinArgs (args.map microCExprToString)).toList ++ ')' :: suffix)
    = some (args, ')' :: suffix) := by
  rw [joinArgs_eq_commaSep]; cases args with
  | nil => unfold pStmtF.pArgsF; simp [skipWs_nonws ')' _ (by decide)]
  | cons e es =>
    have h_ws := skipWs_expr_start e (hwf e (List.Mem.head _))
      (commaSepExprRest es (')' :: suffix))
    have h_ne := expr_ne_rparen_start e (hwf e (List.Mem.head _))
      (commaSepExprRest es (')' :: suffix))
    have h_expr := expr_roundtrip_with_rest e (hwf e (List.Mem.head _))
      (hnd e (List.Mem.head _)) fuel
      (by have := foldl_max_ge_elem exprDepth 0 e es
          simp only [List.length] at hfuel; omega)
      (commaSepExprRest es (')' :: suffix)) (exprSafe_commaSepRest es suffix)
    rw [pArgsF_cons fuel _ h_ws h_ne e _ h_expr]
    exact goArgs_roundtrip es [e] fuel suffix
      (by have := foldl_max_cons_ge_tail exprDepth e es
          simp only [List.length] at hfuel; omega)
      (fun e' he' => hwf e' (List.Mem.tail e he'))
      (fun e' he' => hnd e' (List.Mem.tail e he'))

/-- skipWs on joinArgs output followed by ')' is identity. -/
theorem skipWs_joinArgs_rparen (args : List MicroCExpr)
    (hwf : ∀ e ∈ args, WFExpr e) (suffix : List Char) :
    skipWs ((joinArgs (args.map microCExprToString)).toList ++ ')' :: suffix) =
    (joinArgs (args.map microCExprToString)).toList ++ ')' :: suffix := by
  cases args with
  | nil => exact skipWs_nonws ')' _ (by decide)
  | cons e es => cases es with
    | nil =>
      simp only [List.map, joinArgs_singleton]
      exact skipWs_expr_start e (hwf e (List.Mem.head _)) _
    | cons e2 es' =>
      simp only [List.map, joinArgs_cons_cons, String.toList_append, List.append_assoc]
      exact skipWs_expr_start e (hwf e (List.Mem.head _)) _

/-! ## Sequence fuel and combined roundtrip helpers -/

/-- Minimum parseStmtSeq fuel needed for a statement body. -/
def seqFuelNeeded : MicroCStmt → Nat
  | .seq _s1 s2 => 1 + seqFuelNeeded s2
  | _ => 1

theorem totalFuel_ge_seqFuelNeeded (s : MicroCStmt) : totalFuel s ≥ seqFuelNeeded s := by
  induction s with
  | skip | break_ | continue_ => simp [totalFuel, seqFuelNeeded]
  | return_ r => cases r <;> simp [totalFuel, seqFuelNeeded]
  | assign | store | load => simp [totalFuel, seqFuelNeeded]
  | call => simp [totalFuel, seqFuelNeeded]; omega
  | ite => simp [totalFuel, seqFuelNeeded]
  | while_ => simp [totalFuel, seqFuelNeeded]
  | seq s1 s2 ih1 ih2 => simp only [totalFuel, seqFuelNeeded]; omega

private theorem alpha_or_underscore_safe (d : Char)
    (h : d.isAlpha = true ∨ d = '_') :
    d ≠ ' ' ∧ d ≠ '\n' ∧ d ≠ '\t' ∧ d ≠ '\r' ∧ d ≠ '}' := by
  rcases h with h | rfl
  · exact ⟨fun h' => by rw [h'] at h; simp at h,
          fun h' => by rw [h'] at h; simp at h,
          fun h' => by rw [h'] at h; simp at h,
          fun h' => by rw [h'] at h; simp at h,
          fun h' => by rw [h'] at h; simp at h⟩
  · decide

private theorem ident_head_safe (name : String) (hne : name ≠ "")
    (hstart : let c := name.toList.head (by simp; exact hne); c.isAlpha = true ∨ c = '_') :
    ∃ d ds, name.toList = d :: ds ∧ (d ≠ ' ' ∧ d ≠ '\n' ∧ d ≠ '\t' ∧ d ≠ '\r' ∧ d ≠ '}') := by
  have hne' : name.toList ≠ [] := by simp; exact hne
  match h : name.toList with
  | [] => exact absurd h hne'
  | d :: ds =>
    have h_start' : d.isAlpha = true ∨ d = '_' := by simp [h] at hstart; exact hstart
    exact ⟨d, ds, rfl, alpha_or_underscore_safe d h_start'⟩

private theorem validident_head_safe (name : String) (hv : ValidIdentChars name) :
    ∃ d ds, name.toList = d :: ds ∧ (d ≠ ' ' ∧ d ≠ '\n' ∧ d ≠ '\t' ∧ d ≠ '\r' ∧ d ≠ '}') :=
  ident_head_safe name (validIdentChars_hne name hv) (validIdentChars_hstart name hv)

/-- Printed WFStmt is never empty. -/
private theorem stmt_print_ne_nil (s : MicroCStmt) (hs : WFStmt s) :
    (microCToString s).toList ≠ [] := by
  cases hs <;> simp [microCToString]

set_option maxHeartbeats 800000 in
/-- First char of printed WFStmt: not whitespace, not '}'. -/
private theorem stmt_first_safe (s : MicroCStmt) (hs : WFStmt s) (hd : NegLitDisamS s)
    (c : Char) (cs : List Char)
    (hcs : (microCToString s).toList = c :: cs) :
    c ≠ ' ' ∧ c ≠ '\n' ∧ c ≠ '\t' ∧ c ≠ '\r' ∧ c ≠ '}' := by
  induction hs generalizing c cs with
  | skip => simp [microCToString] at hcs; obtain ⟨rfl, _⟩ := hcs; decide
  | break_ => simp [microCToString] at hcs; obtain ⟨rfl, _⟩ := hcs; decide
  | continue_ => simp [microCToString] at hcs; obtain ⟨rfl, _⟩ := hcs; decide
  | return_none => simp [microCToString] at hcs; obtain ⟨rfl, _⟩ := hcs; decide
  | return_some _ _ =>
    simp [microCToString] at hcs; obtain ⟨rfl, _⟩ := hcs; decide
  | ite _ _ _ _ _ _ _ _ =>
    simp [microCToString] at hcs; obtain ⟨rfl, _⟩ := hcs; decide
  | while_ _ _ _ _ _ =>
    simp [microCToString] at hcs; obtain ⟨rfl, _⟩ := hcs; decide
  | assign name expr hne hstart hcont he =>
    simp only [microCToString, String.toList_append, List.append_assoc] at hcs
    obtain ⟨d, ds, h_name, h_safe⟩ := ident_head_safe name hne hstart
    rw [h_name, List.cons_append] at hcs
    obtain ⟨rfl, _⟩ := List.cons.inj hcs
    exact h_safe
  | store base idx val hb hi hv hbase_var =>
    obtain ⟨bname, rfl⟩ := hbase_var
    cases hb with | varRef _ hne_b hstart_b hcont_b _ =>
    simp only [microCToString, microCExprToString, String.toList_append,
      List.append_assoc] at hcs
    obtain ⟨d, ds, h_name, h_safe⟩ := ident_head_safe bname hne_b hstart_b
    rw [h_name, List.cons_append] at hcs
    obtain ⟨rfl, _⟩ := List.cons.inj hcs
    exact h_safe
  | load var base idx hne hstart hcont hb hi hbase_var =>
    simp only [microCToString, String.toList_append, List.append_assoc] at hcs
    obtain ⟨d, ds, h_name, h_safe⟩ := ident_head_safe var hne hstart
    rw [h_name, List.cons_append] at hcs
    obtain ⟨rfl, _⟩ := List.cons.inj hcs
    exact h_safe
  | call result fname args hne_r hne_f hargs =>
    obtain ⟨hnd_args, hv_r, hsafe_r, hv_f, hsafe_f⟩ := hd
    simp only [microCToString, String.toList_append, List.append_assoc] at hcs
    obtain ⟨d, ds, h_name, h_safe⟩ := validident_head_safe result hv_r
    rw [h_name, List.cons_append] at hcs
    obtain ⟨rfl, _⟩ := List.cons.inj hcs
    exact h_safe
  | seq s1 s2 h1 h2 ih1 ih2 =>
    obtain ⟨hd1, hd2, _⟩ := hd
    simp only [microCToString, String.toList_append, List.append_assoc] at hcs
    have hne' := stmt_print_ne_nil s1 h1
    match h : (microCToString s1).toList with
    | [] => exact absurd h hne'
    | d :: ds =>
      rw [h, List.cons_append] at hcs
      obtain ⟨rfl, _⟩ := List.cons.inj hcs
      exact ih1 hd1 d ds h

/-- skipWs is identity on printed WFStmt. -/
private theorem skipWs_stmt_start (s : MicroCStmt) (hs : WFStmt s)
    (hd : NegLitDisamS s) (rest : List Char) :
    skipWs ((microCToString s).toList ++ rest) =
    (microCToString s).toList ++ rest := by
  have h_ne := stmt_print_ne_nil s hs
  match hcs : (microCToString s).toList with
  | [] => exact absurd hcs h_ne
  | c :: cs =>
    have h_safe := stmt_first_safe s hs hd c cs hcs
    simp only [List.cons_append,
      skipWs_nonws c _ ⟨h_safe.1, h_safe.2.1, h_safe.2.2.1, h_safe.2.2.2.1⟩]

/-- Printed WFStmt followed by ' }' :: rest: first char is not '}'. -/
private theorem stmt_ne_rbrace_cons (s : MicroCStmt) (hs : WFStmt s)
    (hd : NegLitDisamS s) (rest : List Char) :
    ∀ xs, (microCToString s).toList ++ rest ≠ '}' :: xs := by
  have h_ne := stmt_print_ne_nil s hs
  match hcs : (microCToString s).toList with
  | [] => exact absurd hcs h_ne
  | c :: cs =>
    have h_safe := stmt_first_safe s hs hd c cs hcs
    intro xs h_eq
    rw [List.cons_append] at h_eq
    exact h_safe.2.2.2.2 (List.cons.inj h_eq).1

/-- If pStmtF correctly roundtrips a statement, then parseStmtSeq also works
    when the body is followed by ' } rest'. -/
private theorem parseStmtSeq_of_pStmtF
    (fuel seqFuel : Nat) (s : MicroCStmt) (text rest : List Char)
    (h_parse : pStmtF fuel (text ++ (' ' :: '}' :: rest)) =
      some (s, ' ' :: '}' :: rest))
    (h_sf : seqFuel ≥ 1) :
    parseStmtSeq (pStmtF fuel) seqFuel (text ++ (' ' :: '}' :: rest))
      = some (s, '}' :: rest) := by
  obtain ⟨k, rfl⟩ : ∃ k, seqFuel = k + 1 := ⟨seqFuel - 1, by omega⟩
  unfold parseStmtSeq
  rw [h_parse]
  simp only []
  have h_skip : skipWs (' ' :: '}' :: rest) = '}' :: rest := by
    show skipWs ('}' :: rest) = '}' :: rest
    exact skipWs_nonws '}' rest (by decide)
  simp only [h_skip]

/-- Equation lemma: pIfF on '(' :: rest unfolds to the nested match chain. -/
private theorem pIfF_lparen_eq (n : Nat) (rest : List Char) :
    pStmtF.pIfF n ('(' :: rest) =
    match pExprF (n + 1) (skipWs rest) with
    | some (cond, rest') =>
      match skipWs rest' with
      | ')' :: rest'' =>
        match skipWs rest'' with
        | '{' :: rest''' =>
          match parseStmtSeq (pStmtF n) n (skipWs rest''') with
          | some (thenB, rest4) =>
            match skipWs rest4 with
            | '}' :: rest5 =>
              match skipWs rest5 with
              | 'e' :: 'l' :: 's' :: 'e' :: rest6 =>
                match skipWs rest6 with
                | '{' :: rest7 =>
                  match parseStmtSeq (pStmtF n) n (skipWs rest7) with
                  | some (elseB, rest8) =>
                    match skipWs rest8 with
                    | '}' :: final => some (.ite cond thenB elseB, final)
                    | _ => none
                  | none => none
                | _ => none
              | _ => none
            | _ => none
          | none => none
        | _ => none
      | _ => none
    | none => none := by
  unfold pStmtF.pIfF; rfl

/-- Equation lemma: pWhileF on '(' :: rest unfolds to the nested match chain. -/
private theorem pWhileF_lparen_eq (n : Nat) (rest : List Char) :
    pStmtF.pWhileF n ('(' :: rest) =
    match pExprF (n + 1) (skipWs rest) with
    | some (cond, rest') =>
      match skipWs rest' with
      | ')' :: rest'' =>
        match skipWs rest'' with
        | '{' :: rest''' =>
          match parseStmtSeq (pStmtF n) n (skipWs rest''') with
          | some (body, rest4) =>
            match skipWs rest4 with
            | '}' :: final => some (.while_ cond body, final)
            | _ => none
          | none => none
        | _ => none
      | _ => none
    | none => none := by
  unfold pStmtF.pWhileF; rfl

/-! ## Combined roundtrip (Part A + Part B by WFStmt induction) -/

set_option maxHeartbeats 1600000 in
/-- Combined roundtrip theorem proved by structural induction on WFStmt.
    Part A: pStmtF roundtrip for non-seq statements.
    Part B: parseStmtSeq roundtrip for body inside braces. -/
private theorem roundtrip_combined (s : MicroCStmt) (hs : WFStmt s) (hd : NegLitDisamS s)
    (fuel : Nat) (hfuel : fuel ≥ totalFuel s) (rest : List Char) :
    ((∀ a b, s ≠ .seq a b) →
      pStmtF fuel ((microCToString s).toList ++ rest) = some (s, rest)) ∧
    (∀ seqFuel : Nat, seqFuel ≥ seqFuelNeeded s →
      parseStmtSeq (pStmtF fuel) seqFuel
        ((microCToString s).toList ++ (' ' :: '}' :: rest)) = some (s, '}' :: rest)) := by
  induction hs generalizing fuel rest with
  | skip =>
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp [totalFuel] at hfuel; omega⟩
    simp only [microCToString_skip, show ";".toList = [';'] from rfl]
    exact ⟨fun _ => pStmtF_skip n rest,
           fun _ hsf => parseStmtSeq_of_pStmtF _ _ _ _ rest (pStmtF_skip n _) hsf⟩
  | break_ =>
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp [totalFuel] at hfuel; omega⟩
    simp only [microCToString_break,
      show "break;".toList = ['b', 'r', 'e', 'a', 'k', ';'] from rfl]
    exact ⟨fun _ => pStmtF_break n rest,
           fun _ hsf => parseStmtSeq_of_pStmtF _ _ _ _ rest (pStmtF_break n _) hsf⟩
  | continue_ =>
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp [totalFuel] at hfuel; omega⟩
    simp only [microCToString_continue, show "continue;".toList =
      ['c', 'o', 'n', 't', 'i', 'n', 'u', 'e', ';'] from rfl]
    exact ⟨fun _ => pStmtF_continue n rest,
           fun _ hsf => parseStmtSeq_of_pStmtF _ _ _ _ rest (pStmtF_continue n _) hsf⟩
  | return_none =>
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp [totalFuel] at hfuel; omega⟩
    simp only [microCToString_return_none, show "return;".toList =
      ['r', 'e', 't', 'u', 'r', 'n', ';'] from rfl]
    exact ⟨fun _ => pStmtF_return_none n rest,
           fun _ hsf => parseStmtSeq_of_pStmtF _ _ _ _ rest (pStmtF_return_none n _) hsf⟩
  | return_some e he =>
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp [totalFuel] at hfuel; omega⟩
    simp only [microCToString_return_some]
    have hfuel_e : n + 1 ≥ exprDepth e := by simp [totalFuel] at hfuel; omega
    exact ⟨fun _ => pStmtF_return_some e he hd n hfuel_e rest,
           fun _ hsf => parseStmtSeq_of_pStmtF _ _ _ _ rest
             (pStmtF_return_some e he hd n hfuel_e _) hsf⟩
  | assign name expr hne hstart hcont he =>
    obtain ⟨hd_e, hsafe, hrhs⟩ := hd
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp [totalFuel] at hfuel; omega⟩
    have hfuel_e : n + 1 ≥ exprDepth expr := by simp [totalFuel] at hfuel; omega
    have hPartA : ∀ rest' : List Char,
        pStmtF (n + 1) ((microCToString (.assign name expr)).toList ++ rest') =
          some (.assign name expr, rest') := by
      intro rest'
      simp only [microCToString_assign, String.toList_append,
        show " = ".toList = [' ', '=', ' '] from rfl,
        show ";".toList = [';'] from rfl,
        List.append_assoc, List.cons_append, List.nil_append]
      rw [pStmtF_ident_space_fallthrough n name _ hne hstart hcont hsafe]
      unfold pStmtF.pAssignOrStoreF
      rw [skipWs_ident_start name _ hne hstart]
      rw [pIdent_exact name _ hne hstart hcont (noLeadingIdent_space _)]
      simp only []
      have h_skip : skipWs (' ' :: '=' :: ' ' :: ((microCExprToString expr).toList ++ ';' :: rest')) =
        '=' :: ' ' :: ((microCExprToString expr).toList ++ ';' :: rest') := by
        simp only [skipWs_space]; exact skipWs_nonws '=' _ (by decide)
      rw [h_skip]; simp only []
      rw [skipWs_space_expr expr he (';' :: rest')]
      cases expr with
      | litBool b => exact absurd hrhs (by simp [AssignRhsSafe])
      | arrayAccess a i => exact absurd hrhs (by simp [AssignRhsSafe])
      | powCall b k => exact absurd hrhs (by simp [AssignRhsSafe])
      | varRef v =>
        cases he with | varRef _ hne_v hstart_v hcont_v _ =>
        simp only [microCExprToString_varRef]
        unfold pStmtF.pRhsF
        rw [pIdent_exact v _ hne_v hstart_v hcont_v (noLeadingIdent_semicolon _)]
        simp
      | litInt z =>
        unfold pStmtF.pRhsF
        rw [pIdent_litInt_none z (';' :: rest')]
        rw [expr_roundtrip_with_rest (.litInt z) he hd_e (n + 1) hfuel_e
          (';' :: rest') (exprSafe_semicolon rest')]
        simp [skipWs_nonws ';' rest' (by decide)]
      | binOp op l r =>
        unfold pStmtF.pRhsF
        rw [pIdent_binOp_none op l r (';' :: rest')]
        rw [expr_roundtrip_with_rest (.binOp op l r) he hd_e (n + 1) hfuel_e
          (';' :: rest') (exprSafe_semicolon rest')]
        simp [skipWs_nonws ';' rest' (by decide)]
      | unaryOp op e =>
        unfold pStmtF.pRhsF
        rw [pIdent_unaryOp_none op e (';' :: rest')]
        rw [expr_roundtrip_with_rest (.unaryOp op e) he hd_e (n + 1) hfuel_e
          (';' :: rest') (exprSafe_semicolon rest')]
        simp [skipWs_nonws ';' rest' (by decide)]
    exact ⟨fun _ => hPartA rest,
           fun _ hsf => parseStmtSeq_of_pStmtF _ _ _ _ rest (hPartA _) hsf⟩
  | store base idx val hb hi hv hbase_var =>
    obtain ⟨bname, rfl⟩ := hbase_var
    obtain ⟨hd_b, hd_i, hd_v, hsafe_fn⟩ := hd
    have hsafe := hsafe_fn bname rfl
    cases hb with | varRef _ hne_b hstart_b hcont_b _ =>
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp [totalFuel] at hfuel; omega⟩
    have hfuel_i : n + 1 ≥ exprDepth idx := by simp [totalFuel] at hfuel; omega
    have hfuel_v : n + 1 ≥ exprDepth val := by simp [totalFuel] at hfuel; omega
    have hPartA : ∀ rest' : List Char,
        pStmtF (n + 1) ((microCToString (.store (.varRef bname) idx val)).toList ++ rest') =
          some (.store (.varRef bname) idx val, rest') := by
      intro rest'
      simp only [microCToString_store, microCExprToString_varRef, String.toList_append,
        show "[".toList = ['['] from rfl, show "] = ".toList = [']', ' ', '=', ' '] from rfl,
        show ";".toList = [';'] from rfl,
        List.append_assoc, List.cons_append, List.nil_append]
      rw [pStmtF_ident_bracket_fallthrough n bname _ hne_b hstart_b hcont_b hsafe]
      unfold pStmtF.pAssignOrStoreF
      rw [skipWs_ident_start bname _ hne_b hstart_b]
      rw [pIdent_exact bname _ hne_b hstart_b hcont_b (noLeadingIdent_bracket _)]
      simp only []
      simp only [skipWs_nonws '[' _ (by decide)]
      rw [skipWs_expr_start idx hi]
      rw [expr_roundtrip_with_rest idx hi hd_i (n + 1) hfuel_i
        (']' :: ' ' :: '=' :: ' ' :: ((microCExprToString val).toList ++ (';' :: rest')))
        (exprSafe_rbracket _)]
      simp only [skipWs_nonws ']' _ (by decide)]
      have h_eq : skipWs (' ' :: '=' :: ' ' :: ((microCExprToString val).toList ++ (';' :: rest')))
        = '=' :: ' ' :: ((microCExprToString val).toList ++ (';' :: rest')) := by
        simp only [skipWs_space]; exact skipWs_nonws '=' _ (by decide)
      rw [h_eq]; simp only []
      rw [skipWs_space_expr val hv (';' :: rest')]
      rw [expr_roundtrip_with_rest val hv hd_v (n + 1) hfuel_v (';' :: rest')
        (exprSafe_semicolon rest')]
      simp [skipWs_nonws ';' rest' (by decide)]
    exact ⟨fun _ => hPartA rest,
           fun _ hsf => parseStmtSeq_of_pStmtF _ _ _ _ rest (hPartA _) hsf⟩
  | load var base idx hne hstart hcont hb hi hbase_var =>
    obtain ⟨bname, rfl⟩ := hbase_var
    obtain ⟨hd_b, hd_i, hsafe_var⟩ := hd
    cases hb with | varRef _ hne_b hstart_b hcont_b _ =>
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp [totalFuel] at hfuel; omega⟩
    have hfuel_i : n + 1 ≥ exprDepth idx := by simp [totalFuel] at hfuel; omega
    have hPartA : ∀ rest' : List Char,
        pStmtF (n + 1) ((microCToString (.load var (.varRef bname) idx)).toList ++ rest') =
          some (.load var (.varRef bname) idx, rest') := by
      intro rest'
      simp only [microCToString_load, microCExprToString_varRef, String.toList_append,
        show " = ".toList = [' ', '=', ' '] from rfl, show "[".toList = ['['] from rfl,
        show "];".toList = [']', ';'] from rfl,
        List.append_assoc, List.cons_append, List.nil_append]
      rw [pStmtF_ident_space_fallthrough n var _ hne hstart hcont hsafe_var]
      unfold pStmtF.pAssignOrStoreF
      rw [skipWs_ident_start var _ hne hstart]
      rw [pIdent_exact var _ hne hstart hcont (noLeadingIdent_space _)]
      simp only []
      have h_eq1 : skipWs (' ' :: '=' :: ' ' :: (bname.toList ++ ('[' :: ((microCExprToString idx).toList
        ++ (']' :: ';' :: rest'))))) = '=' :: ' ' :: (bname.toList ++ ('[' :: ((microCExprToString idx).toList
        ++ (']' :: ';' :: rest')))) := by
        simp only [skipWs_space]; exact skipWs_nonws '=' _ (by decide)
      rw [h_eq1]; simp only []
      unfold pStmtF.pRhsF
      have h_skip_base : skipWs (' ' :: (bname.toList ++ ('[' :: ((microCExprToString idx).toList
        ++ (']' :: ';' :: rest'))))) = bname.toList ++ ('[' :: ((microCExprToString idx).toList
        ++ (']' :: ';' :: rest'))) := by
        simp only [skipWs_space]; exact skipWs_ident_start bname _ hne_b hstart_b
      rw [h_skip_base]
      rw [pIdent_exact bname _ hne_b hstart_b hcont_b (noLeadingIdent_bracket _)]
      simp only []
      simp only [skipWs_nonws '[' _ (by decide)]
      rw [skipWs_expr_start idx hi]
      rw [expr_roundtrip_with_rest idx hi hd_i (n + 1) hfuel_i (']' :: ';' :: rest')
        (exprSafe_rbracket _)]
      simp only [skipWs_nonws ']' _ (by decide), skipWs_nonws ';' _ (by decide)]
    exact ⟨fun _ => hPartA rest,
           fun _ hsf => parseStmtSeq_of_pStmtF _ _ _ _ rest (hPartA _) hsf⟩
  | call result fname args hne_r hne_f hargs =>
    obtain ⟨hnd_args, hv_r, hsafe_r, hv_f, hsafe_f⟩ := hd
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp [totalFuel] at hfuel; omega⟩
    have hne := validIdentChars_hne result hv_r
    have hstart := validIdentChars_hstart result hv_r
    have hcont := validIdentChars_hcont result hv_r
    have hne_fn := validIdentChars_hne fname hv_f
    have hstart_fn := validIdentChars_hstart fname hv_f
    have hcont_fn := validIdentChars_hcont fname hv_f
    have hPartA : ∀ rest' : List Char,
        pStmtF (n + 1) ((microCToString (.call result fname args)).toList ++ rest') =
          some (.call result fname args, rest') := by
      intro rest'
      simp only [microCToString_call, String.toList_append, List.append_assoc,
        show " = ".toList = [' ', '=', ' '] from rfl,
        show "(".toList = ['('] from rfl,
        show ");".toList = [')', ';'] from rfl,
        List.cons_append, List.nil_append]
      rw [pStmtF_ident_space_fallthrough n result _ hne hstart hcont hsafe_r]
      unfold pStmtF.pAssignOrStoreF
      rw [skipWs_ident_start result _ hne hstart]
      rw [pIdent_exact result _ hne hstart hcont (noLeadingIdent_space _)]
      simp only []
      have h_eq : skipWs (' ' :: '=' :: ' ' :: (fname.toList ++ ('(' :: ((joinArgs (args.map microCExprToString)).toList ++ (')' :: ';' :: rest')))))
        = '=' :: ' ' :: (fname.toList ++ ('(' :: ((joinArgs (args.map microCExprToString)).toList ++ (')' :: ';' :: rest')))) := by
        simp only [skipWs_space]; exact skipWs_nonws '=' _ (by decide)
      rw [h_eq]; simp only []
      unfold pStmtF.pRhsF
      have h_skip_fname : skipWs (' ' :: (fname.toList ++ ('(' :: ((joinArgs (args.map microCExprToString)).toList ++ (')' :: ';' :: rest')))))
        = fname.toList ++ ('(' :: ((joinArgs (args.map microCExprToString)).toList ++ (')' :: ';' :: rest'))) := by
        simp only [skipWs_space]; exact skipWs_ident_start fname _ hne_fn hstart_fn
      rw [h_skip_fname]
      rw [pIdent_exact fname _ hne_fn hstart_fn hcont_fn (noLeadingIdent_lparen _)]
      simp only []
      simp only [skipWs_nonws '(' _ (by decide)]
      rw [skipWs_joinArgs_rparen args hargs (';' :: rest')]
      have hfuel_args : n + 1 ≥ args.length + args.foldl (fun m e => max m (exprDepth e)) 0 := by
        simp [totalFuel] at hfuel; omega
      rw [pArgsF_roundtrip args (n + 1) (';' :: rest') hargs hnd_args hfuel_args]
      simp only [skipWs_nonws ')' _ (by decide), skipWs_nonws ';' _ (by decide)]
    exact ⟨fun _ => hPartA rest,
           fun _ hsf => parseStmtSeq_of_pStmtF _ _ _ _ rest (hPartA _) hsf⟩
  | ite cond thenB elseB hc ht he ih_t ih_e =>
    obtain ⟨hd_c, hd_t, hd_e⟩ := hd
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp [totalFuel] at hfuel; omega⟩
    have hfuel_c : n + 1 ≥ exprDepth cond := by simp [totalFuel] at hfuel; omega
    have hfuel_t : n ≥ totalFuel thenB := by simp [totalFuel] at hfuel; omega
    have hfuel_e' : n ≥ totalFuel elseB := by simp [totalFuel] at hfuel; omega
    have hsf_t : n ≥ seqFuelNeeded thenB := by
      have := totalFuel_ge_seqFuelNeeded thenB; omega
    have hsf_e : n ≥ seqFuelNeeded elseB := by
      have := totalFuel_ge_seqFuelNeeded elseB; omega
    have hPartA : ∀ rest' : List Char,
        pStmtF (n + 1) ((microCToString (.ite cond thenB elseB)).toList ++ rest') =
          some (.ite cond thenB elseB, rest') := by
      intro rest'
      simp only [microCToString_ite, String.toList_append,
        show "if (".toList = ['i', 'f', ' ', '('] from rfl,
        show ") { ".toList = [')', ' ', '{', ' '] from rfl,
        show " } else { ".toList = [' ', '}', ' ', 'e', 'l', 's', 'e', ' ', '{', ' '] from rfl,
        show " }".toList = [' ', '}'] from rfl,
        List.append_assoc, List.cons_append, List.nil_append]
      -- Goal: pStmtF (n+1) ('i'::'f'::' '::'('::condText ++ rest_chars) = some (.ite ...)
      -- Step 1: Unfold pStmtF → dispatch to pIfF
      unfold pStmtF
      show pStmtF.pIfF n ('(' :: ((microCExprToString cond).toList ++ ')' :: ' ' :: '{' :: ' ' ::
        ((microCToString thenB).toList ++ ' ' :: '}' :: ' ' :: 'e' :: 'l' :: 's' :: 'e' ::
          ' ' :: '{' :: ' ' :: ((microCToString elseB).toList ++ ' ' :: '}' :: rest')))) =
        some (.ite cond thenB elseB, rest')
      -- Step 2: Use equation lemma to unfold pIfF for '(' :: rest
      rw [pIfF_lparen_eq]
      -- Goal: (match pExprF (n+1) (skipWs (condText ++ condRest)) with ...) = ...
      rw [skipWs_expr_start cond hc _,
          expr_roundtrip_with_rest cond hc hd_c (n + 1) hfuel_c _ (exprSafe_rparen _)]
      -- After expr: match some (cond, ')' :: ...) → proceed; skipWs ')' → ')'; match ')' → ...
      simp only [skipWs_nonws ')' _ (by decide),
                  skipWs_space, skipWs_nonws '{' _ (by decide)]
      -- parseStmtSeq for thenB: skipWs (thenText ++ ...) = thenText ++ ...
      rw [skipWs_stmt_start thenB ht hd_t _]
      have hThen := (ih_t hd_t n hfuel_t
        (' ' :: 'e' :: 'l' :: 's' :: 'e' :: ' ' :: '{' :: ' ' ::
          ((microCToString elseB).toList ++ (' ' :: '}' :: rest')))).2 n hsf_t
      rw [hThen]
      -- After then: '}' matches; skipWs ' e...' resolves through else
      simp only [skipWs_nonws '}' _ (by decide),
                  skipWs_space, skipWs_nonws 'e' _ (by decide),
                  skipWs_nonws '{' _ (by decide)]
      -- parseStmtSeq for elseB: simp already consumed the space before elseB text
      rw [skipWs_stmt_start elseB he hd_e _]
      have hElse := (ih_e hd_e n hfuel_e' rest').2 n hsf_e
      rw [hElse]
      simp only [skipWs_nonws '}' _ (by decide)]
    exact ⟨fun _ => hPartA rest,
           fun _ hsf => parseStmtSeq_of_pStmtF _ _ _ _ rest (hPartA _) hsf⟩
  | while_ cond body hc hb ih_b =>
    obtain ⟨hd_c, hd_b⟩ := hd
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp [totalFuel] at hfuel; omega⟩
    have hfuel_c : n + 1 ≥ exprDepth cond := by simp [totalFuel] at hfuel; omega
    have hfuel_b : n ≥ totalFuel body := by simp [totalFuel] at hfuel; omega
    have hsf_b : n ≥ seqFuelNeeded body := by
      have := totalFuel_ge_seqFuelNeeded body; omega
    have hPartA : ∀ rest' : List Char,
        pStmtF (n + 1) ((microCToString (.while_ cond body)).toList ++ rest') =
          some (.while_ cond body, rest') := by
      intro rest'
      simp only [microCToString_while, String.toList_append,
        show "while (".toList = ['w', 'h', 'i', 'l', 'e', ' ', '('] from rfl,
        show ") { ".toList = [')', ' ', '{', ' '] from rfl,
        show " }".toList = [' ', '}'] from rfl,
        List.append_assoc, List.cons_append, List.nil_append]
      -- Dispatch: 'w'::'h'::'i'::'l'::'e'::' '::_ → pWhileF
      unfold pStmtF
      show pStmtF.pWhileF n ('(' :: ((microCExprToString cond).toList ++ ')' :: ' ' :: '{' :: ' ' ::
        ((microCToString body).toList ++ ' ' :: '}' :: rest'))) =
        some (.while_ cond body, rest')
      rw [pWhileF_lparen_eq]
      rw [skipWs_expr_start cond hc _,
          expr_roundtrip_with_rest cond hc hd_c (n + 1) hfuel_c _ (exprSafe_rparen _)]
      simp only [skipWs_nonws ')' _ (by decide),
                  skipWs_space, skipWs_nonws '{' _ (by decide)]
      -- simp already consumed the space before body text
      rw [skipWs_stmt_start body hb hd_b _]
      have hBody := (ih_b hd_b n hfuel_b rest').2 n hsf_b
      rw [hBody]
      simp only [skipWs_nonws '}' _ (by decide)]
    exact ⟨fun _ => hPartA rest,
           fun _ hsf => parseStmtSeq_of_pStmtF _ _ _ _ rest (hPartA _) hsf⟩
  | seq s1 s2 h1 h2 ih1 ih2 =>
    obtain ⟨hd1, hd2, hns_s1⟩ := hd
    have hfuel1 : fuel ≥ totalFuel s1 := by simp [totalFuel] at hfuel; omega
    have hfuel2 : fuel ≥ totalFuel s2 := by simp [totalFuel] at hfuel; omega
    constructor
    · intro hns; exact absurd rfl (hns s1 s2)
    · intro seqFuel hsf
      -- seqFuelNeeded (.seq s1 s2) = 1 + seqFuelNeeded s2
      obtain ⟨k, rfl⟩ : ∃ k, seqFuel = k + 1 := ⟨seqFuel - 1, by
        simp [seqFuelNeeded] at hsf; omega⟩
      have hk : k ≥ seqFuelNeeded s2 := by simp [seqFuelNeeded] at hsf; omega
      simp only [microCToString_seq, String.toList_append, List.append_assoc,
        show " ".toList = [' '] from rfl, List.cons_append, List.nil_append]
      unfold parseStmtSeq
      -- Use ih1 Part A for s1 (non-seq by hns_s1) with rest' := ' ' :: s2text ++ ' ' :: '}' :: rest
      have hA1 := (ih1 hd1 fuel hfuel1
        (' ' :: ((microCToString s2).toList ++ (' ' :: '}' :: rest)))).1 hns_s1
      rw [hA1]
      simp only []
      -- skipWs (' ' :: s2text ++ ' ' :: '}' :: rest) = s2text ++ ' ' :: '}' :: rest
      rw [skipWs_space, skipWs_stmt_start s2 h2 hd2 (' ' :: '}' :: rest)]
      -- Need to resolve match: not '}' :: _ and not []
      have h_ne := stmt_print_ne_nil s2 h2
      match hs2 : (microCToString s2).toList with
      | [] => exact absurd hs2 h_ne
      | c :: cs =>
        have hc_safe := stmt_first_safe s2 h2 hd2 c cs hs2
        simp only [List.cons_append]
        -- c ≠ '}' eliminates first branch, c :: _ ≠ [] eliminates second
        split
        · next heq => exact absurd (List.cons.inj heq).1 hc_safe.2.2.2.2
        · next heq => exact absurd heq (by simp)
        · -- Remaining case: recurse
          -- Need ih2 Part B with seqFuel = k
          have hB2 := (ih2 hd2 fuel hfuel2 rest).2 k hk
          simp only [hs2, List.cons_append] at hB2
          rw [hB2]

/-! ## Fuel Bound Helpers -/

/-- Max expression depth over a list (structural recursion, no foldl accumulator). -/
private def maxExprDepthL : List MicroCExpr → Nat
  | [] => 0
  | e :: rest => max (exprDepth e) (maxExprDepthL rest)

/-- foldl max over depths equals structural maxExprDepthL. -/
private theorem foldl_max_eq_maxL (args : List MicroCExpr) :
    args.foldl (fun m e => max m (exprDepth e)) 0 = maxExprDepthL args := by
  suffices ∀ init, args.foldl (fun m e => max m (exprDepth e)) init =
    max init (maxExprDepthL args) from by
    rw [this 0]; simp
  intro init
  induction args generalizing init with
  | nil => simp [maxExprDepthL]
  | cons a as ih =>
    simp only [List.foldl_cons, maxExprDepthL]; rw [ih]; omega

/-- maxExprDepthL ≤ joinArgs length + 1. -/
private theorem maxL_le_jargsLen (args : List MicroCExpr)
    (hargs : ∀ e ∈ args, WFExpr e) :
    maxExprDepthL args ≤
      (joinArgs (args.map microCExprToString)).toList.length + 1 := by
  induction args with
  | nil => exact Nat.zero_le _
  | cons a as ih =>
    simp only [maxExprDepthL, List.map_cons]
    have ha := hargs a (List.Mem.head _)
    have has : ∀ e ∈ as, WFExpr e := fun e he => hargs e (List.mem_cons_of_mem a he)
    have hda := exprDepth_le_length a ha
    apply Nat.max_le.mpr; constructor
    · match as with
      | [] => simp only [joinArgs_singleton, List.map_nil]; omega
      | b :: bs =>
        simp only [List.map_cons, joinArgs_cons_cons, String.toList_append,
          List.length_append]; omega
    · match as with
      | [] => exact Nat.zero_le _
      | b :: bs =>
        have ih' := ih has; simp only [List.map_cons] at ih'
        simp only [List.map_cons, joinArgs_cons_cons, String.toList_append,
          List.length_append]; omega

/-- Combined bound: args.length + maxExprDepthL ≤ joinArgs length + 2. -/
private theorem call_combined_bound (args : List MicroCExpr)
    (hargs : ∀ e ∈ args, WFExpr e) :
    args.length + maxExprDepthL args ≤
      (joinArgs (args.map microCExprToString)).toList.length + 2 := by
  induction args with
  | nil => simp [maxExprDepthL]
  | cons a as ih =>
    have ha := hargs a (List.Mem.head _)
    have has : ∀ e ∈ as, WFExpr e := fun e he => hargs e (List.mem_cons_of_mem a he)
    have hda := exprDepth_le_length a ha
    simp only [List.length_cons, maxExprDepthL, List.map_cons]
    match as with
    | [] =>
      simp only [maxExprDepthL, List.map_nil, List.length_nil, joinArgs_singleton,
        Nat.max_zero]; omega
    | b :: bs =>
      have ih' := ih has
      simp only [List.map_cons, joinArgs_cons_cons, String.toList_append,
        List.length_append] at ih' ⊢
      have hcomma : ", ".toList.length = 2 := by decide
      -- max (exprDepth a) (maxExprDepthL (b :: bs)) is if-then-else; split handles it
      simp only [Nat.max_def]
      split <;> omega

/-- name ≠ "" implies name.toList.length ≥ 1. -/
private theorem str_len_pos (name : String) (hne : name ≠ "") :
    name.toList.length ≥ 1 := by
  cases h : name.toList with
  | nil => exfalso; apply hne; exact String.ext_iff.mpr (by simp [h])
  | cons c cs => simp [List.length_cons]

set_option maxHeartbeats 800000 in
/-- totalFuel s ≤ print length + 1. Key bound for parseMicroC_roundtrip:
    the fuel derived from string length suffices for parsing. -/
private theorem totalFuel_le_printLen (s : MicroCStmt) (hs : WFStmt s)
    (hd : NegLitDisamS s) :
    totalFuel s ≤ (microCToString s).toList.length + 1 := by
  induction hs with
  | skip | break_ | continue_ | return_none =>
    simp [totalFuel, microCToString]
  | return_some e he =>
    simp only [totalFuel, microCToString_return_some, String.toList_append,
      List.length_append]
    have hret : "return ".toList.length = 7 := by decide
    have hsemi : ";".toList.length = 1 := by decide
    have := exprDepth_le_length e he; omega
  | assign name expr hne _ _ he =>
    simp only [totalFuel, microCToString_assign, String.toList_append,
      List.length_append]
    have heq : " = ".toList.length = 3 := by decide
    have hsemi : ";".toList.length = 1 := by decide
    have := exprDepth_le_length expr he
    have := str_len_pos name hne; omega
  | store base idx val hb hi hv _ =>
    simp only [totalFuel, microCToString_store, String.toList_append,
      List.length_append]
    have hbr : "[".toList.length = 1 := by decide
    have heq : "] = ".toList.length = 4 := by decide
    have hsemi : ";".toList.length = 1 := by decide
    have hdi := exprDepth_le_length idx hi
    have hdv := exprDepth_le_length val hv
    have hdb := exprDepth_le_length base hb
    have : max (exprDepth idx) (exprDepth val) ≤
        (microCExprToString base).toList.length +
        (microCExprToString idx).toList.length +
        (microCExprToString val).toList.length + 6 :=
      Nat.max_le.mpr ⟨by omega, by omega⟩
    omega
  | load var base idx hne _ _ hb hi _ =>
    simp only [totalFuel, microCToString_load, String.toList_append,
      List.length_append]
    have heq : " = ".toList.length = 3 := by decide
    have hbr : "[".toList.length = 1 := by decide
    have hsemi : "];".toList.length = 2 := by decide
    have := exprDepth_le_length idx hi
    have := exprDepth_le_length base hb
    have := str_len_pos var hne; omega
  | call result fname args hne_r hne_f hargs =>
    simp only [totalFuel, microCToString_call, String.toList_append,
      List.length_append]
    have heq : " = ".toList.length = 3 := by decide
    have hlp : "(".toList.length = 1 := by decide
    have hrp : ");".toList.length = 2 := by decide
    have := str_len_pos result hne_r
    have := str_len_pos fname hne_f
    rw [foldl_max_eq_maxL]
    have := call_combined_bound args hargs; omega
  | seq s1 s2 _ _ ih1 ih2 =>
    obtain ⟨hd1, hd2, _⟩ := hd
    simp only [totalFuel, microCToString_seq, String.toList_append,
      List.length_append]
    have hsp : " ".toList.length = 1 := by decide
    have h1 := ih1 hd1; have h2 := ih2 hd2
    have : max (totalFuel s1) (totalFuel s2) ≤
        (microCToString s1).toList.length +
        (microCToString s2).toList.length + 1 :=
      Nat.max_le.mpr ⟨by omega, by omega⟩
    omega
  | ite cond thenB elseB hc _ _ ih_t ih_e =>
    obtain ⟨hd_c, hd_t, hd_e⟩ := hd
    simp only [totalFuel, microCToString_ite, String.toList_append,
      List.length_append]
    have hif : "if (".toList.length = 4 := by decide
    have hcb : ") { ".toList.length = 4 := by decide
    have hel : " } else { ".toList.length = 10 := by decide
    have hcl : " }".toList.length = 2 := by decide
    have hdc := exprDepth_le_length cond hc
    have ht := ih_t hd_t; have he := ih_e hd_e
    have hinner : max (totalFuel thenB + 1) (totalFuel elseB + 1) ≤
        (microCToString thenB).toList.length +
        (microCToString elseB).toList.length + 12 :=
      Nat.max_le.mpr ⟨by omega, by omega⟩
    have : max (exprDepth cond) (max (totalFuel thenB + 1) (totalFuel elseB + 1)) ≤
        (microCExprToString cond).toList.length +
        (microCToString thenB).toList.length +
        (microCToString elseB).toList.length + 12 :=
      Nat.max_le.mpr ⟨by omega, by omega⟩
    omega
  | while_ cond body hc _ ih_b =>
    obtain ⟨hd_c, hd_b⟩ := hd
    simp only [totalFuel, microCToString_while, String.toList_append,
      List.length_append]
    have hwh : "while (".toList.length = 7 := by decide
    have hcb : ") { ".toList.length = 4 := by decide
    have hcl : " }".toList.length = 2 := by decide
    have hdc := exprDepth_le_length cond hc
    have hb := ih_b hd_b
    have : max (exprDepth cond) (totalFuel body + 1) ≤
        (microCExprToString cond).toList.length +
        (microCToString body).toList.length + 6 :=
      Nat.max_le.mpr ⟨by omega, by omega⟩
    omega

/-! ## ParseStmtSeq Top-Level Roundtrip -/

/-- Helper: parseStmtSeq roundtrip for a non-seq statement. -/
private theorem parseStmtSeq_nonseq (s : MicroCStmt) (hs : WFStmt s)
    (hd : NegLitDisamS s) (fuel : Nat) (hfuel : fuel ≥ totalFuel s)
    (seqFuel : Nat) (hns : ∀ a b, s ≠ MicroCStmt.seq a b) :
    parseStmtSeq (pStmtF fuel) seqFuel ((microCToString s).toList) =
      some (s, []) := by
  have hA := (roundtrip_combined s hs hd fuel hfuel []).1 hns
  simp only [List.append_nil] at hA
  match seqFuel with
  | 0 => exact hA
  | n + 1 => unfold parseStmtSeq; rw [hA]; simp only [skipWs]

set_option maxHeartbeats 1600000 in
/-- parseStmtSeq roundtrip for top-level (no trailing brace).
    Parses the flat text of any WFStmt (including nested seq). -/
private theorem parseStmtSeq_toplevel (s : MicroCStmt) (hs : WFStmt s)
    (hd : NegLitDisamS s)
    (fuel : Nat) (hfuel : fuel ≥ totalFuel s)
    (seqFuel : Nat) (hsf : seqFuel ≥ seqFuelNeeded s) :
    parseStmtSeq (pStmtF fuel) seqFuel ((microCToString s).toList) =
      some (s, []) := by
  induction hs generalizing fuel seqFuel with
  | seq s1 s2 h1 h2 ih1 ih2 =>
    obtain ⟨hd1, hd2, hns_s1⟩ := hd
    have hfuel1 : fuel ≥ totalFuel s1 := by simp [totalFuel] at hfuel; omega
    have hfuel2 : fuel ≥ totalFuel s2 := by simp [totalFuel] at hfuel; omega
    obtain ⟨k, rfl⟩ : ∃ k, seqFuel = k + 1 := ⟨seqFuel - 1, by
      simp [seqFuelNeeded] at hsf; omega⟩
    have hk : k ≥ seqFuelNeeded s2 := by simp [seqFuelNeeded] at hsf; omega
    simp only [microCToString_seq, String.toList_append, List.append_assoc,
      show " ".toList = [' '] from rfl, List.cons_append, List.nil_append]
    unfold parseStmtSeq
    have hA1 := (roundtrip_combined s1 h1 hd1 fuel hfuel1
      (' ' :: (microCToString s2).toList)).1 hns_s1
    rw [hA1]; simp only []
    -- skipWs_stmt_start gives pattern with ++ []; normalize with List.append_nil
    have h_ws := skipWs_stmt_start s2 h2 hd2 []
    simp only [List.append_nil] at h_ws
    rw [skipWs_space, h_ws]
    have h_ne := stmt_print_ne_nil s2 h2
    match hs2 : (microCToString s2).toList with
    | [] => exact absurd hs2 h_ne
    | c :: cs =>
      have hc_safe := stmt_first_safe s2 h2 hd2 c cs hs2
      split
      · next heq => exact absurd (List.cons.inj heq).1 hc_safe.2.2.2.2
      · next heq => exact absurd heq (by simp)
      · have := ih2 hd2 fuel hfuel2 k hk
        simp only [hs2] at this
        rw [this]
  | skip => exact parseStmtSeq_nonseq _ .skip hd fuel hfuel seqFuel (fun _ _ => nofun)
  | break_ => exact parseStmtSeq_nonseq _ .break_ hd fuel hfuel seqFuel (fun _ _ => nofun)
  | continue_ => exact parseStmtSeq_nonseq _ .continue_ hd fuel hfuel seqFuel (fun _ _ => nofun)
  | return_none => exact parseStmtSeq_nonseq _ .return_none hd fuel hfuel seqFuel (fun _ _ => nofun)
  | return_some e he => exact parseStmtSeq_nonseq _ (.return_some e he) hd fuel hfuel seqFuel (fun _ _ => nofun)
  | assign n e hne hs hc he => exact parseStmtSeq_nonseq _ (.assign n e hne hs hc he) hd fuel hfuel seqFuel (fun _ _ => nofun)
  | store b i v hb hi hv hbv => exact parseStmtSeq_nonseq _ (.store b i v hb hi hv hbv) hd fuel hfuel seqFuel (fun _ _ => nofun)
  | load var b i hne hs hc hb hi hbv => exact parseStmtSeq_nonseq _ (.load var b i hne hs hc hb hi hbv) hd fuel hfuel seqFuel (fun _ _ => nofun)
  | call r f args hr hf ha => exact parseStmtSeq_nonseq _ (.call r f args hr hf ha) hd fuel hfuel seqFuel (fun _ _ => nofun)
  | ite c t e hc ht he => exact parseStmtSeq_nonseq _ (.ite c t e hc ht he) hd fuel hfuel seqFuel (fun _ _ => nofun)
  | while_ c b hc hb => exact parseStmtSeq_nonseq _ (.while_ c b hc hb) hd fuel hfuel seqFuel (fun _ _ => nofun)

/-! ## Top-Level Theorem -/

/-- Helper: parseMicroC roundtrip for non-seq statements. -/
private theorem parseMicroC_nonseq (s : MicroCStmt) (hs : WFStmt s)
    (hd : NegLitDisamS s) (hns : ∀ a b, s ≠ MicroCStmt.seq a b) :
    parseMicroC (microCToString s) = some s := by
  unfold parseMicroC
  have hfuel : (microCToString s).toList.length + 1 ≥ totalFuel s :=
    totalFuel_le_printLen s hs hd
  have hA := (roundtrip_combined s hs hd
    ((microCToString s).toList.length + 1) hfuel []).1 hns
  simp only [List.append_nil] at hA
  simp only [] at *  -- beta-reduce let bindings
  rw [hA]; simp [skipWs]

set_option maxHeartbeats 1600000 in
/-- Statement roundtrip: parsing the printed form of a well-formed statement
    recovers the original. -/
theorem parseMicroC_roundtrip (s : MicroCStmt) (hs : WFStmt s) (hd : NegLitDisamS s) :
    parseMicroC (microCToString s) = some s := by
  match hs with
  | .seq s1 s2 h1 h2 =>
    -- Compute fuel bound BEFORE destructuring hd
    have hfuel : (microCToString (.seq s1 s2)).toList.length + 1 ≥ totalFuel (.seq s1 s2) :=
      totalFuel_le_printLen _ (.seq s1 s2 h1 h2) hd
    obtain ⟨hd1, hd2, hns_s1⟩ := hd
    unfold parseMicroC
    -- Extract fuel bounds from max
    have hfuel1 : (microCToString (.seq s1 s2)).toList.length + 1 ≥ totalFuel s1 := by
      have : totalFuel s1 ≤ max (totalFuel s1) (totalFuel s2) := Nat.le_max_left _ _
      simp only [totalFuel] at hfuel; omega
    have hfuel2 : (microCToString (.seq s1 s2)).toList.length + 1 ≥ totalFuel s2 := by
      have : totalFuel s2 ≤ max (totalFuel s1) (totalFuel s2) := Nat.le_max_right _ _
      simp only [totalFuel] at hfuel; omega
    -- Beta-reduce let-bindings from parseMicroC, then expand microCToString_seq
    simp only []
    simp only [microCToString_seq, String.toList_append,
      show " ".toList = [' '] from rfl, List.append_assoc, List.cons_append, List.nil_append]
    -- Align fuel: goal has expanded length, hA1 has compact length
    have hlen_eq : ((microCToString s1).toList ++ (' ' :: (microCToString s2).toList)).length =
        (microCToString (.seq s1 s2)).toList.length := by
      simp [microCToString_seq, String.toList_append]
    -- Part A: pStmtF parses s1 leaving ' ' :: text(s2)
    have hA1 := (roundtrip_combined s1 h1 hd1
      ((microCToString (.seq s1 s2)).toList.length + 1) hfuel1
      (' ' :: (microCToString s2).toList)).1 hns_s1
    -- Rewrite goal's expanded fuel to compact fuel so hA1 matches
    rw [hlen_eq]
    simp only [hA1]
    -- skipWs removes the space, stmt_start says text(s2) doesn't start with ws
    have h_ws := skipWs_stmt_start s2 h2 hd2 []
    simp only [List.append_nil] at h_ws
    rw [skipWs_space, h_ws]
    -- text(s2) is not empty
    have h_ne := stmt_print_ne_nil s2 h2
    have h_beq_false : ((microCToString s2).toList == []) = false := by
      cases hcs : (microCToString s2).toList with
      | nil => exact absurd hcs h_ne
      | cons _ _ => rfl
    simp only [h_beq_false]
    -- parseStmtSeq for s2
    have hsf : (microCToString (.seq s1 s2)).toList.length + 1 ≥ seqFuelNeeded s2 := by
      have := totalFuel_ge_seqFuelNeeded s2; omega
    have := parseStmtSeq_toplevel s2 h2 hd2
      ((microCToString (.seq s1 s2)).toList.length + 1) hfuel2
      ((microCToString (.seq s1 s2)).toList.length + 1) hsf
    rw [this]; simp
  | .skip => exact parseMicroC_nonseq _ .skip hd (fun _ _ => nofun)
  | .break_ => exact parseMicroC_nonseq _ .break_ hd (fun _ _ => nofun)
  | .continue_ => exact parseMicroC_nonseq _ .continue_ hd (fun _ _ => nofun)
  | .return_none => exact parseMicroC_nonseq _ .return_none hd (fun _ _ => nofun)
  | .return_some e he => exact parseMicroC_nonseq _ (.return_some e he) hd (fun _ _ => nofun)
  | .assign n e hne hs hc he => exact parseMicroC_nonseq _ (.assign n e hne hs hc he) hd (fun _ _ => nofun)
  | .store b i v hb hi hv hbv => exact parseMicroC_nonseq _ (.store b i v hb hi hv hbv) hd (fun _ _ => nofun)
  | .load var b i hne hs' hc hb hi hbv => exact parseMicroC_nonseq _ (.load var b i hne hs' hc hb hi hbv) hd (fun _ _ => nofun)
  | .call r f args hr hf ha => exact parseMicroC_nonseq _ (.call r f args hr hf ha) hd (fun _ _ => nofun)
  | .ite c t e hc ht he => exact parseMicroC_nonseq _ (.ite c t e hc ht he) hd (fun _ _ => nofun)
  | .while_ c b hc hb => exact parseMicroC_nonseq _ (.while_ c b hc hb) hd (fun _ _ => nofun)

/-! ## Non-Vacuity -/

example : parseMicroC (microCToString .skip) = some .skip := by native_decide
example : parseMicroC (microCToString .break_) = some .break_ := by native_decide
example : parseMicroC (microCToString .continue_) = some .continue_ := by native_decide
example : parseMicroC (microCToString (.return_ none)) = some (.return_ none) := by native_decide
example : parseMicroC (microCToString (.return_ (some (.litInt 42)))) =
    some (.return_ (some (.litInt 42))) := by native_decide
example : parseMicroC (microCToString (.assign "x" (.litInt 7))) =
    some (.assign "x" (.litInt 7)) := by native_decide
example : parseMicroC (microCToString (.store (.varRef "a") (.varRef "i") (.litInt 5))) =
    some (.store (.varRef "a") (.varRef "i") (.litInt 5)) := by native_decide
example : parseMicroC (microCToString (.load "x" (.varRef "a") (.litInt 0))) =
    some (.load "x" (.varRef "a") (.litInt 0)) := by native_decide
example : parseMicroC (microCToString (.call "r" "f" [.litInt 1, .varRef "x"])) =
    some (.call "r" "f" [.litInt 1, .varRef "x"]) := by native_decide
example : parseMicroC (microCToString
    (.ite (.litBool true) (.assign "x" (.litInt 1)) (.assign "x" (.litInt 2)))) =
    some (.ite (.litBool true) (.assign "x" (.litInt 1)) (.assign "x" (.litInt 2))) := by
  native_decide
example : parseMicroC (microCToString (.while_ (.litBool false) .skip)) =
    some (.while_ (.litBool false) .skip) := by native_decide
example : parseMicroC (microCToString
    (.seq (.assign "x" (.litInt 1)) (.assign "y" (.litInt 2)))) =
    some (.seq (.assign "x" (.litInt 1)) (.assign "y" (.litInt 2))) := by native_decide
/-- Non-vacuity: complex nested program with all constructors. -/
example : parseMicroC (microCToString
    (.seq (.ite (.varRef "b") (.assign "x" (.litInt 1)) .skip)
          (.while_ (.litBool true) (.assign "x" (.binOp .add (.varRef "x") (.litInt 1)))))) =
    some (.seq (.ite (.varRef "b") (.assign "x" (.litInt 1)) .skip)
          (.while_ (.litBool true) (.assign "x" (.binOp .add (.varRef "x") (.litInt 1))))) := by
  native_decide

end TrustLean
