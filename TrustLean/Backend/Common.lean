/-
  Trust-Lean — Verified Code Generation Framework
  Backend/Common.lean: Shared emission helpers for backends

  N4.1: PAR — shared utilities used by both C and Rust backends.
  N9.1 (v1.2.0): Added c99Keywords, cReservedIdentifiers, sanitizeIdentifier,
  isValidCIdent, filterCIdentChars, formatArrayAccess with correctness theorems.
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

end TrustLean
