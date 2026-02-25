/-
  Trust-Lean — Tests/Integration/SanitizacionHelpers.lean
  N9.1: Integration tests for sanitizeIdentifier and helper functions.
  Each test prints [PASS] or [FAIL].
-/

import TrustLean.Backend.Common

set_option autoImplicit false

open TrustLean

-- T1: sanitizeIdentifier leaves valid identifier unchanged
def T1_basic_valid : IO Bool := do
  let s := "my_variable_name"
  let result := sanitizeIdentifier s
  let ok := result == "my_variable_name"
  IO.println (if ok then "[PASS] T1_basic_valid" else s!"[FAIL] T1_basic_valid: got '{result}'")
  return ok

-- T2: sanitizeIdentifier prefixes C99 keyword
def T2_keyword : IO Bool := do
  let s := "while"
  let result := sanitizeIdentifier s
  let ok := result == "tl_while"
  IO.println (if ok then "[PASS] T2_keyword" else s!"[FAIL] T2_keyword: got '{result}'")
  return ok

-- T3: sanitizeIdentifier prefixes identifier starting with digit
def T3_starts_with_digit : IO Bool := do
  let s := "2_turtles"
  let result := sanitizeIdentifier s
  let ok := result == "tl_2_turtles"
  IO.println (if ok then "[PASS] T3_starts_with_digit" else s!"[FAIL] T3_starts_with_digit: got '{result}'")
  return ok

-- T4: sanitizeIdentifier strips invalid characters
def T4_invalid_chars : IO Bool := do
  let s := "a-b(c)d!e"
  let result := sanitizeIdentifier s
  let ok := result == "abcde"
  IO.println (if ok then "[PASS] T4_invalid_chars" else s!"[FAIL] T4_invalid_chars: got '{result}'")
  return ok

-- T5: sanitizeIdentifier handles string that becomes keyword after stripping
def T5_strip_to_keyword : IO Bool := do
  let s := "v*o*i*d"
  let result := sanitizeIdentifier s
  let ok := result == "tl_void"
  IO.println (if ok then "[PASS] T5_strip_to_keyword" else s!"[FAIL] T5_strip_to_keyword: got '{result}'")
  return ok

-- T6: sanitizeIdentifier handles empty string
def T6_empty : IO Bool := do
  let s := ""
  let result := sanitizeIdentifier s
  -- The implementation returns "tl_empty" for empty input
  let ok := result == "tl_empty"
  IO.println (if ok then "[PASS] T6_empty" else s!"[FAIL] T6_empty: got '{result}'")
  return ok

-- T7: sanitizeIdentifier handles string that becomes empty after stripping
def T7_strip_to_empty : IO Bool := do
  let s := "!@#$%^"
  let result := sanitizeIdentifier s
  -- After stripping all invalid chars, nothing remains → "tl_empty"
  let ok := result == "tl_empty"
  IO.println (if ok then "[PASS] T7_strip_to_empty" else s!"[FAIL] T7_strip_to_empty: got '{result}'")
  return ok

-- T8: indentStr adds correct number of spaces
def T8_indent : IO Bool := do
  let s := "code_line"
  let result := indentStr 2 ++ s  -- indentStr uses 2 spaces per level
  let ok := result == "    code_line"
  IO.println (if ok then "[PASS] T8_indent" else s!"[FAIL] T8_indent: got '{result}'")
  return ok

-- T9: joinCode joins with newlines
def T9_joinCode : IO Bool := do
  -- joinCode takes 2 strings, so we fold
  let lines := ["int main() {", "  return 0;", "}"]
  let result := lines.foldl joinCode ""
  let expected := "int main() {\n  return 0;\n}"
  let ok := result == expected
  IO.println (if ok then "[PASS] T9_joinCode" else s!"[FAIL] T9_joinCode: got '{result}'")
  return ok

-- T10: joinCode handles empty input
def T10_joinCode_empty : IO Bool := do
  let result := joinCode "" ""
  let ok := result == ""
  IO.println (if ok then "[PASS] T10_joinCode_empty" else s!"[FAIL] T10_joinCode_empty: got '{result}'")
  return ok

-- T11: joinCode handles single string
def T11_joinCode_single : IO Bool := do
  let result := joinCode "" "one_line"
  let ok := result == "one_line"
  IO.println (if ok then "[PASS] T11_joinCode_single" else s!"[FAIL] T11_joinCode_single: got '{result}'")
  return ok

-- T12: formatArrayAccess correctly formats
def T12_formatArrayAccess : IO Bool := do
  let base := "my_array"
  let idx := "i + 1"
  let result := formatArrayAccess base idx
  let ok := result == "my_array[i + 1]"
  IO.println (if ok then "[PASS] T12_formatArrayAccess" else s!"[FAIL] T12_formatArrayAccess: got '{result}'")
  return ok

def main : IO UInt32 := do
  let results := #[
    (← T1_basic_valid),
    (← T2_keyword),
    (← T3_starts_with_digit),
    (← T4_invalid_chars),
    (← T5_strip_to_keyword),
    (← T6_empty),
    (← T7_strip_to_empty),
    (← T8_indent),
    (← T9_joinCode),
    (← T10_joinCode_empty),
    (← T11_joinCode_single),
    (← T12_formatArrayAccess)
  ]
  let passed := results.filter (· == true) |>.size
  let total := results.size
  IO.println s!"\nN9.1 Integration: {passed}/{total} passed"
  return if passed == total then 0 else 1

-- #eval calls for test runner (lake env lean captures this output)
#eval T1_basic_valid
#eval T2_keyword
#eval T3_starts_with_digit
#eval T4_invalid_chars
#eval T5_strip_to_keyword
#eval T6_empty
#eval T7_strip_to_empty
#eval T8_indent
#eval T9_joinCode
#eval T10_joinCode_empty
#eval T11_joinCode_single
#eval T12_formatArrayAccess
