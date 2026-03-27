/-
  Trust-Lean — Verified Code Generation Framework
  Backend/Common.lean: Shared emission helpers for backends

  N4.1: PAR — shared utilities used by both C and Rust backends.
  N9.1 (v1.2.0): Added c99Keywords, cReservedIdentifiers, sanitizeIdentifier,
  isValidCIdent, filterCIdentChars, formatArrayAccess with correctness theorems.
  N21.1 (v3.2.0): Added countChar shared infrastructure, rustKeywords (Rust 2021 edition,
  Rust Reference S2.1), rustReservedIdentifiers, sanitizeIdentifierRust with theorems.
-/

import TrustLean.Core.Value

set_option autoImplicit false

namespace TrustLean

/-! ## Indentation -/

/-- Generate indentation string (2 spaces per level). -/
def indentStr (level : Nat) : String :=
  String.join (List.replicate level "  ")

@[simp] theorem indentStr_zero : indentStr 0 = "" := rfl

/-! ## Variable Name Conversion -/

/-- Convert a VarName to a string suitable for emission.
    User variables pass through; temps become t0, t1, etc.;
    array elements become base[idx]. -/
def varNameToStr : VarName → String
  | .user s => s
  | .temp k => s!"t{k}"
  | .array base idx => s!"{base}[{idx}]"

@[simp] theorem varNameToStr_user (s : String) :
    varNameToStr (.user s) = s := rfl
@[simp] theorem varNameToStr_temp (k : Nat) :
    varNameToStr (.temp k) = s!"t{k}" := rfl

/-! ## Code Joining -/

/-- Join two code fragments with a newline, skipping empty fragments. -/
def joinCode (c1 c2 : String) : String :=
  if c1.isEmpty then c2
  else if c2.isEmpty then c1
  else c1 ++ "\n" ++ c2

/-! ## C99 Keyword Sanitization (N9.1, v1.2.0) -/

/-- C99 reserved words (37 keywords per ISO/IEC 9899:1999 §6.4.1). -/
def c99Keywords : List String :=
  ["auto", "break", "case", "char", "const", "continue", "default", "do",
   "double", "else", "enum", "extern", "float", "for", "goto", "if",
   "inline", "int", "long", "register", "restrict", "return", "short",
   "signed", "sizeof", "static", "struct", "switch", "typedef", "union",
   "unsigned", "void", "volatile", "while",
   "_Bool", "_Complex", "_Imaginary"]

/-- Additional reserved identifiers: C11 keywords (ISO/IEC 9899:2011 §6.4.1),
    stdint.h types, and common stdlib names.
    C11 additions included for robustness; explicitly listed rather than excluded. -/
def cReservedExtra : List String :=
  ["_Alignas", "_Atomic", "_Generic", "_Noreturn", "_Static_assert", "_Thread_local",
   "int8_t", "int16_t", "int32_t", "int64_t",
   "uint8_t", "uint16_t", "uint32_t", "uint64_t",
   "size_t", "ptrdiff_t", "bool", "true", "false",
   "NULL", "main", "printf", "malloc", "free", "exit", "abort"]

/-- All C reserved identifiers (C99 keywords + C11 + stdint.h + stdlib). -/
def cReservedIdentifiers : List String := c99Keywords ++ cReservedExtra

/-- Check if a character is valid in a C identifier (letter, digit, or underscore). -/
def isValidCIdentChar (c : Char) : Bool :=
  c.isAlpha || c.isDigit || c == '_'

/-- Check if a string is a valid C identifier:
    non-empty, starts with letter or underscore, all characters valid. -/
def isValidCIdent (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => (c.isAlpha || c == '_') && (c :: cs).all isValidCIdentChar

/-- Remove characters that are not valid in C identifiers. -/
def filterCIdentChars (s : String) : String :=
  String.ofList (s.toList.filter isValidCIdentChar)

/-- Sanitize a string to produce a valid, non-reserved C identifier.
    Removes invalid characters, then prefixes with "tl_" if needed. -/
def sanitizeIdentifier (s : String) : String :=
  match s.toList.filter isValidCIdentChar with
  | [] => "tl_empty"
  | c :: cs =>
    if c.isDigit then "tl_" ++ String.ofList (c :: cs)
    else if cReservedIdentifiers.contains (String.ofList (c :: cs))
      then "tl_" ++ String.ofList (c :: cs)
    else String.ofList (c :: cs)

/-! ## Sanitization Properties (N9.1) -/

/-- No C99 keyword's character list starts with "tl_". -/
private theorem c99_no_tl_prefix :
    ∀ k ∈ c99Keywords, k.toList.take 3 ≠ ['t', 'l', '_'] := by decide

/-- No reserved identifier's character list starts with "tl_". -/
private theorem reserved_no_tl_prefix :
    ∀ k ∈ cReservedIdentifiers, k.toList.take 3 ≠ ['t', 'l', '_'] := by decide

/-- "tl_empty" is not a C99 keyword. -/
private theorem tl_empty_not_c99 : "tl_empty" ∉ c99Keywords := by decide

/-- "tl_".toList equals ['t', 'l', '_']. -/
private theorem tl_toList : "tl_".toList = ['t', 'l', '_'] := by decide

/-- The toList of "tl_" ++ s starts with ['t', 'l', '_']. -/
private theorem tl_append_toList_take (s : String) :
    ("tl_" ++ s).toList.take 3 = ['t', 'l', '_'] := by
  rw [String.toList_append, tl_toList]
  show List.take 3 ('t' :: 'l' :: '_' :: s.toList) = ['t', 'l', '_']
  rfl

/-- No string prefixed with "tl_" is a C99 keyword (P0). -/
theorem tl_prefix_not_c99 (s : String) : ("tl_" ++ s) ∉ c99Keywords := by
  intro hmem
  exact c99_no_tl_prefix ("tl_" ++ s) hmem (tl_append_toList_take s)

/-- Helper: every element of a filtered list satisfies the predicate. -/
private theorem all_filter_pred {α : Type} (l : List α) (p : α → Bool) :
    (l.filter p).all p = true :=
  List.all_eq_true.mpr (fun _ hx => (List.mem_filter.mp hx).2)

/-- sanitizeIdentifier never produces a C99 keyword (P0). -/
theorem sanitizeIdentifier_not_keyword (s : String) :
    sanitizeIdentifier s ∉ c99Keywords := by
  unfold sanitizeIdentifier
  split
  · exact tl_empty_not_c99
  · rename_i c cs hfilter
    split
    · exact tl_prefix_not_c99 _
    · split
      · exact tl_prefix_not_c99 _
      · rename_i hnotdigit hnotreserved
        intro hmem
        have hres : String.ofList (c :: cs) ∈ cReservedIdentifiers :=
          List.mem_append_left _ hmem
        rw [List.contains_iff_mem] at hnotreserved
        exact hnotreserved hres

/-- sanitizeIdentifier always produces a non-empty string (P0). -/
theorem sanitizeIdentifier_nonempty (s : String) :
    (sanitizeIdentifier s).toList ≠ [] := by
  unfold sanitizeIdentifier
  split
  · -- "tl_empty"
    decide
  · rename_i c cs _hfilter
    split
    · -- "tl_" ++ ...
      rw [String.toList_append, tl_toList]
      exact List.cons_ne_nil _ _
    · split
      · -- "tl_" ++ ...
        rw [String.toList_append, tl_toList]
        exact List.cons_ne_nil _ _
      · -- String.ofList (c :: cs)
        rw [String.toList_ofList]
        exact List.cons_ne_nil _ _

/-- Helper: isValidCIdent holds for "tl_" ++ String.ofList chars
    when chars come from a filter on isValidCIdentChar. -/
private theorem isValidCIdent_tl_prefix (chars : List Char)
    (hall : chars.all isValidCIdentChar = true) :
    isValidCIdent ("tl_" ++ String.ofList chars) = true := by
  unfold isValidCIdent
  rw [String.toList_append, tl_toList, String.toList_ofList]
  show (('t'.isAlpha || 't' == '_') && ('t' :: 'l' :: '_' :: chars).all isValidCIdentChar) = true
  simp only [Bool.and_eq_true]
  constructor
  · decide
  · simp only [List.all_cons, Bool.and_eq_true]
    exact ⟨by decide, by decide, by decide, hall⟩

/-- sanitizeIdentifier output is a valid C identifier (P0). -/
theorem sanitizeIdentifier_valid (s : String) :
    isValidCIdent (sanitizeIdentifier s) = true := by
  unfold sanitizeIdentifier
  split
  · -- "tl_empty"
    unfold isValidCIdent; decide
  · rename_i c cs hfilter
    have hall : (c :: cs).all isValidCIdentChar = true :=
      hfilter ▸ all_filter_pred s.toList isValidCIdentChar
    split
    · -- "tl_" ++ ... where c is digit
      exact isValidCIdent_tl_prefix (c :: cs) hall
    · split
      · -- "tl_" ++ ... where cleaned is reserved
        exact isValidCIdent_tl_prefix (c :: cs) hall
      · -- String.ofList (c :: cs) passes through
        rename_i hnotdigit _hnotreserved
        unfold isValidCIdent
        rw [String.toList_ofList]
        simp only [Bool.and_eq_true]
        constructor
        · -- First char c is alpha or underscore
          have hvalid : isValidCIdentChar c = true :=
            List.all_eq_true.mp hall c List.mem_cons_self
          unfold isValidCIdentChar at hvalid
          have hd : c.isDigit = false := Bool.eq_false_iff.mpr hnotdigit
          rw [hd] at hvalid
          simp only [Bool.or_false] at hvalid
          exact hvalid
        · exact hall

/-! ## Array Access Helper (N9.1) -/

/-- Format an array access expression. For generated code,
    the base expression is assumed to already be parenthesized by exprToC. -/
def formatArrayAccess (base : String) (idx : String) : String :=
  base ++ "[" ++ idx ++ "]"

@[simp] theorem formatArrayAccess_def (base idx : String) :
    formatArrayAccess base idx = base ++ "[" ++ idx ++ "]" := rfl

/-! ## Character Counting Infrastructure (shared C + Rust) (N21.1) -/

/-- Count occurrences of a character in a string. -/
def countChar (c : Char) (s : String) : Nat :=
  s.toList.countP (· == c)

@[simp] theorem countChar_empty (c : Char) : countChar c "" = 0 := by
  unfold countChar; rfl

theorem countChar_append (c : Char) (s1 s2 : String) :
    countChar c (s1 ++ s2) = countChar c s1 + countChar c s2 := by
  unfold countChar
  rw [String.toList_append, List.countP_append]

/-- countChar is additive over joinCode for non-newline characters. -/
private theorem isEmpty_eq_empty {s : String} (h : s.isEmpty = true) : s = "" := by
  simp [String.isEmpty] at h; exact h

theorem countChar_joinCode (c : Char) (s1 s2 : String) (hc : c ≠ '\n') :
    countChar c (joinCode s1 s2) = countChar c s1 + countChar c s2 := by
  unfold joinCode
  split
  · -- s1 empty
    rename_i h; rw [isEmpty_eq_empty h]; simp [countChar_empty]
  · split
    · -- s2 empty
      rename_i _ h; rw [isEmpty_eq_empty h]; simp [countChar_empty]
    · -- both non-empty: s1 ++ "\n" ++ s2
      rw [countChar_append, countChar_append]
      have : countChar c "\n" = 0 := by
        unfold countChar
        have htl : "\n".toList = ['\n'] := by native_decide
        rw [htl, List.countP_cons, List.countP_nil]
        simp [beq_iff_eq, Ne.symm hc]
      omega

/-! ## Rust Keyword Infrastructure (N21.1)
    Source: Rust 2021 edition, The Rust Reference §2.1 (Keywords) -/

/-- Rust strict keywords (39): cannot be used as identifiers. -/
def rustStrictKeywords : List String :=
  ["as", "async", "await", "break", "const", "continue", "crate", "dyn",
   "else", "enum", "extern", "false", "fn", "for", "if", "impl", "in",
   "let", "loop", "match", "mod", "move", "mut", "pub", "ref", "return",
   "self", "Self", "static", "struct", "super", "trait", "true", "type",
   "unsafe", "use", "where", "while"]

/-- Rust reserved keywords (14): reserved for future use. -/
def rustReservedKeywords : List String :=
  ["abstract", "become", "box", "do", "final", "gen", "macro", "override",
   "priv", "try", "typeof", "unsized", "virtual", "yield"]

/-- All Rust keywords (53 = 39 strict + 14 reserved). -/
def rustKeywords : List String :=
  rustStrictKeywords ++ rustReservedKeywords

/-- Rust standard library prelude names to avoid. -/
def rustStdlibNames : List String :=
  ["std", "alloc", "core", "usize", "isize",
   "i8", "i16", "i32", "i64", "i128",
   "u8", "u16", "u32", "u64", "u128",
   "f32", "f64", "bool", "str", "char",
   "Vec", "String", "Box", "Result", "Option",
   "Some", "None", "Ok", "Err",
   "panic", "println", "print", "assert", "main"]

/-- All Rust reserved identifiers (keywords + stdlib prelude). -/
def rustReservedIdentifiers : List String :=
  rustKeywords ++ rustStdlibNames

/-- Sanitize a string to produce a valid, non-reserved Rust identifier.
    Same strategy as C sanitization: removes invalid chars, prefixes "tl_" if needed. -/
def sanitizeIdentifierRust (s : String) : String :=
  match s.toList.filter isValidCIdentChar with
  | [] => "tl_empty"
  | c :: cs =>
    if c.isDigit then "tl_" ++ String.ofList (c :: cs)
    else if rustReservedIdentifiers.contains (String.ofList (c :: cs))
      then "tl_" ++ String.ofList (c :: cs)
    else String.ofList (c :: cs)

/-- Rust identifier validity uses the same ASCII rules as C
    (Trust-Lean only generates ASCII identifiers from its AST). -/
abbrev isValidRustIdent := isValidCIdent

/-! ## Rust Sanitization Properties (N21.2) -/

/-- No Rust keyword starts with "tl_". -/
private theorem rustKeywords_no_tl_prefix :
    ∀ k ∈ rustKeywords, k.toList.take 3 ≠ ['t', 'l', '_'] := by decide

/-- No Rust reserved identifier starts with "tl_". -/
private theorem rustReserved_no_tl_prefix :
    ∀ k ∈ rustReservedIdentifiers, k.toList.take 3 ≠ ['t', 'l', '_'] := by decide

/-- "tl_empty" is not a Rust keyword. -/
private theorem tl_empty_not_rustKeyword : "tl_empty" ∉ rustKeywords := by decide

/-- No string prefixed with "tl_" is a Rust keyword. -/
theorem tl_prefix_not_rustKeyword (s : String) : ("tl_" ++ s) ∉ rustKeywords := by
  intro hmem
  exact rustKeywords_no_tl_prefix ("tl_" ++ s) hmem (tl_append_toList_take s)

/-- sanitizeIdentifierRust never produces a Rust keyword (P0). -/
theorem sanitizeIdentifierRust_not_keyword (s : String) :
    sanitizeIdentifierRust s ∉ rustKeywords := by
  unfold sanitizeIdentifierRust
  split
  · exact tl_empty_not_rustKeyword
  · rename_i c cs hfilter
    split
    · exact tl_prefix_not_rustKeyword _
    · split
      · exact tl_prefix_not_rustKeyword _
      · rename_i _hnotdigit hnotreserved
        intro hmem
        have hres : String.ofList (c :: cs) ∈ rustReservedIdentifiers :=
          List.mem_append_left _ hmem
        rw [List.contains_iff_mem] at hnotreserved
        exact hnotreserved hres

/-- sanitizeIdentifierRust always produces a non-empty string (P0). -/
theorem sanitizeIdentifierRust_nonempty (s : String) :
    (sanitizeIdentifierRust s).toList ≠ [] := by
  unfold sanitizeIdentifierRust
  split
  · decide
  · rename_i c cs _hfilter
    split
    · rw [String.toList_append, tl_toList]; exact List.cons_ne_nil _ _
    · split
      · rw [String.toList_append, tl_toList]; exact List.cons_ne_nil _ _
      · rw [String.toList_ofList]; exact List.cons_ne_nil _ _

/-- sanitizeIdentifierRust output is a valid identifier (P0). -/
theorem sanitizeIdentifierRust_valid (s : String) :
    isValidRustIdent (sanitizeIdentifierRust s) = true := by
  unfold sanitizeIdentifierRust
  split
  · unfold isValidRustIdent isValidCIdent; decide
  · rename_i c cs hfilter
    have hall : (c :: cs).all isValidCIdentChar = true :=
      hfilter ▸ all_filter_pred s.toList isValidCIdentChar
    split
    · exact isValidCIdent_tl_prefix (c :: cs) hall
    · split
      · exact isValidCIdent_tl_prefix (c :: cs) hall
      · rename_i hnotdigit _hnotreserved
        unfold isValidRustIdent isValidCIdent
        rw [String.toList_ofList]
        simp only [Bool.and_eq_true]
        constructor
        · have hvalid : isValidCIdentChar c = true :=
            List.all_eq_true.mp hall c List.mem_cons_self
          unfold isValidCIdentChar at hvalid
          have hd : c.isDigit = false := Bool.eq_false_iff.mpr hnotdigit
          rw [hd] at hvalid
          simp only [Bool.or_false] at hvalid
          exact hvalid
        · exact hall

/-- No string prefixed with "tl_" is in rustReservedIdentifiers. -/
theorem tl_prefix_not_rustReserved (s : String) :
    ("tl_" ++ s) ∉ rustReservedIdentifiers := by
  intro hmem
  exact rustReserved_no_tl_prefix ("tl_" ++ s) hmem (tl_append_toList_take s)

/-- "tl_empty" is not in rustReservedIdentifiers. -/
private theorem tl_empty_not_rustReserved : "tl_empty" ∉ rustReservedIdentifiers := by decide

/-- Helper: if all chars are valid, filter is identity. -/
private theorem filter_valid_id (l : List Char) (h : l.all isValidCIdentChar = true) :
    l.filter isValidCIdentChar = l :=
  List.filter_eq_self.mpr (List.all_eq_true.mp h)

/-- Helper: output of sanitizeIdentifierRust has all valid ident chars. -/
private theorem sanitizeIdentifierRust_allValid (s : String) :
    (sanitizeIdentifierRust s).toList.all isValidCIdentChar = true := by
  have h := sanitizeIdentifierRust_valid s
  unfold isValidRustIdent isValidCIdent at h
  cases hlist : (sanitizeIdentifierRust s).toList with
  | nil => simp [List.all_eq_true]
  | cons c cs =>
    rw [hlist] at h; simp only [Bool.and_eq_true] at h; exact h.2

/-- Helper: output of sanitizeIdentifierRust starts with non-digit. -/
private theorem sanitizeIdentifierRust_notDigitStart (s : String) :
    ∀ c cs, (sanitizeIdentifierRust s).toList = c :: cs → c.isDigit = false := by
  unfold sanitizeIdentifierRust
  split
  · -- "tl_empty": first char 't'
    intro c cs h
    have heq : "tl_empty".toList = ['t', 'l', '_', 'e', 'm', 'p', 't', 'y'] := by native_decide
    rw [heq] at h; rw [(List.cons.inj h.symm).1]; decide
  · rename_i c' cs' _
    split
    · -- "tl_" ++ ...: first char 't'
      intro c cs h; rw [String.toList_append, tl_toList] at h
      have : c = 't' := by simp at h; exact h.1.symm
      rw [this]; decide
    · split
      · -- "tl_" ++ ...: first char 't'
        intro c cs h; rw [String.toList_append, tl_toList] at h
        have : c = 't' := by simp at h; exact h.1.symm
        rw [this]; decide
      · -- pass-through: c'.isDigit is false
        rename_i hnotdigit _
        intro c cs h; rw [String.toList_ofList] at h
        have : c = c' := (List.cons.inj h).1.symm
        rw [this]; exact Bool.eq_false_iff.mpr hnotdigit

/-- Helper: output of sanitizeIdentifierRust is not in rustReservedIdentifiers. -/
private theorem sanitizeIdentifierRust_notReserved (s : String) :
    sanitizeIdentifierRust s ∉ rustReservedIdentifiers := by
  unfold sanitizeIdentifierRust
  split
  · exact tl_empty_not_rustReserved
  · rename_i c cs _hfilter
    split
    · exact tl_prefix_not_rustReserved _
    · split
      · exact tl_prefix_not_rustReserved _
      · rename_i _ hnotres
        intro hmem
        exact absurd (List.contains_iff_mem.mpr hmem) hnotres

/-- sanitizeIdentifierRust is idempotent: applying it twice = once (P0).
    Relies on three properties of the output: all chars valid, non-digit start,
    not in rustReservedIdentifiers. -/
theorem sanitizeIdentifierRust_idempotent (s : String) :
    sanitizeIdentifierRust (sanitizeIdentifierRust s) = sanitizeIdentifierRust s := by
  set r := sanitizeIdentifierRust s
  have hallValid := sanitizeIdentifierRust_allValid s
  have hnotempty := sanitizeIdentifierRust_nonempty s
  have hnotres := sanitizeIdentifierRust_notReserved s
  -- r.toList.filter isValidCIdentChar = r.toList (all chars are valid)
  have hfilterId := filter_valid_id r.toList hallValid
  -- Unfold the second application
  show sanitizeIdentifierRust r = r
  unfold sanitizeIdentifierRust
  rw [hfilterId]
  cases hlist : r.toList with
  | nil => exact absurd hlist hnotempty
  | cons c cs =>
    have hnotdigit := sanitizeIdentifierRust_notDigitStart s c cs hlist
    -- r.toList = c :: cs, so String.ofList (c :: cs) = r
    have heq_r : String.ofList (c :: cs) = r := by
      rw [← hlist, String.ofList_toList]
    -- Not reserved as Bool (needed for if-then-else reduction)
    have hnotresOL : rustReservedIdentifiers.contains (String.ofList (c :: cs)) = false := by
      apply Bool.eq_false_iff.mpr; intro h
      have hmem := List.contains_iff_mem.mp h
      rw [heq_r] at hmem; exact hnotres hmem
    simp only [hnotdigit, hnotresOL, ite_false]
    exact heq_r

end TrustLean
