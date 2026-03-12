/-
  Trust-Lean — Verified Code Generation Framework
  MicroC/PrettyPrint.lean: Pretty-printer for MicroC AST

  N12.1 (v2.0.0): PAR — defines microCExprToString and microCToString.
  Fully parenthesized canonical form matching exprToC/stmtToC output.
  No indentation (flat form for roundtrip proofs).

  Design decisions:
  - Full parenthesization of binary expressions (like exprToC)
  - Negative integer literals parenthesized: "(-5)"
  - Bool as "true"/"false" (C stdbool.h convention, unambiguous for roundtrip)
  - No indentation in microCToString (canonical flat form)
  - stmtToC compatibility is proved in Integration module
-/

import TrustLean.MicroC.AST

set_option autoImplicit false

namespace TrustLean

/-! ## Operator Strings -/

/-- Convert MicroCBinOp to its C infix operator string. -/
def microCBinOpToString : MicroCBinOp → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .eqOp => "=="
  | .ltOp => "<"
  | .land => "&&"
  | .lor => "||"

/-- Convert MicroCUnaryOp to its C prefix operator string. -/
def microCUnaryOpToString : MicroCUnaryOp → String
  | .neg => "-"
  | .lnot => "!"

/-! ## microCBinOpToString @[simp] Equation Lemmas -/

@[simp] theorem microCBinOpToString_add : microCBinOpToString .add = "+" := rfl
@[simp] theorem microCBinOpToString_sub : microCBinOpToString .sub = "-" := rfl
@[simp] theorem microCBinOpToString_mul : microCBinOpToString .mul = "*" := rfl
@[simp] theorem microCBinOpToString_eqOp : microCBinOpToString .eqOp = "==" := rfl
@[simp] theorem microCBinOpToString_ltOp : microCBinOpToString .ltOp = "<" := rfl
@[simp] theorem microCBinOpToString_land : microCBinOpToString .land = "&&" := rfl
@[simp] theorem microCBinOpToString_lor : microCBinOpToString .lor = "||" := rfl

@[simp] theorem microCUnaryOpToString_neg : microCUnaryOpToString .neg = "-" := rfl
@[simp] theorem microCUnaryOpToString_lnot : microCUnaryOpToString .lnot = "!" := rfl

/-! ## Nat-to-Chars (for provable roundtrip) -/

/-- Convert a natural number to its decimal digit characters.
    Unlike Nat.repr/toString, this function is transparent to the kernel,
    enabling formal roundtrip proofs. -/
def natToChars (n : Nat) : List Char :=
  if h : n < 10 then [Char.ofNat (n + 48)]
  else natToChars (n / 10) ++ [Char.ofNat (n % 10 + 48)]
termination_by n

/-! ## Expression Pretty-Printer -/

/-- Convert a MicroCExpr to a canonical C expression string.
    Fully parenthesized binary expressions. Negative literals parenthesized.
    Booleans as "true"/"false". Uses natToChars for provable roundtrip. -/
def microCExprToString : MicroCExpr → String
  | .litInt n =>
    if n < 0 then "(" ++ "-" ++ String.ofList (natToChars n.natAbs) ++ ")"
    else String.ofList (natToChars n.toNat)
  | .litBool true => "true"
  | .litBool false => "false"
  | .varRef name => name
  | .binOp op lhs rhs =>
    "(" ++ microCExprToString lhs ++ " " ++ microCBinOpToString op ++
      " " ++ microCExprToString rhs ++ ")"
  | .unaryOp op e =>
    "(" ++ microCUnaryOpToString op ++ microCExprToString e ++ ")"
  | .powCall base n =>
    "power(" ++ microCExprToString base ++ ", " ++
      String.ofList (natToChars n) ++ ")"
  | .arrayAccess base idx =>
    microCExprToString base ++ "[" ++ microCExprToString idx ++ "]"

/-! ## microCExprToString @[simp] Equation Lemmas -/

@[simp] theorem microCExprToString_litInt (n : Int) :
    microCExprToString (.litInt n) =
      if n < 0 then "(" ++ "-" ++ String.ofList (natToChars n.natAbs) ++ ")"
      else String.ofList (natToChars n.toNat) := rfl

@[simp] theorem microCExprToString_litBool_true :
    microCExprToString (.litBool true) = "true" := rfl

@[simp] theorem microCExprToString_litBool_false :
    microCExprToString (.litBool false) = "false" := rfl

@[simp] theorem microCExprToString_varRef (name : String) :
    microCExprToString (.varRef name) = name := rfl

@[simp] theorem microCExprToString_binOp (op : MicroCBinOp) (lhs rhs : MicroCExpr) :
    microCExprToString (.binOp op lhs rhs) =
      "(" ++ microCExprToString lhs ++ " " ++ microCBinOpToString op ++
        " " ++ microCExprToString rhs ++ ")" := rfl

@[simp] theorem microCExprToString_unaryOp (op : MicroCUnaryOp) (e : MicroCExpr) :
    microCExprToString (.unaryOp op e) =
      "(" ++ microCUnaryOpToString op ++ microCExprToString e ++ ")" := rfl

@[simp] theorem microCExprToString_powCall (base : MicroCExpr) (n : Nat) :
    microCExprToString (.powCall base n) =
      "power(" ++ microCExprToString base ++ ", " ++
        String.ofList (natToChars n) ++ ")" := rfl

@[simp] theorem microCExprToString_arrayAccess (base idx : MicroCExpr) :
    microCExprToString (.arrayAccess base idx) =
      microCExprToString base ++ "[" ++ microCExprToString idx ++ "]" := rfl

/-! ## joinArgs: transparent join for proof support -/

/-- Join a list of strings with ", " separator.
    Equivalent to `", ".intercalate ss` but fully transparent for proofs.
    String.intercalate uses a private `go✝` auxiliary that blocks proof decomposition. -/
def joinArgs : List String → String
  | [] => ""
  | [s] => s
  | s :: rest => s ++ ", " ++ joinArgs rest

@[simp] theorem joinArgs_nil : joinArgs [] = "" := rfl
@[simp] theorem joinArgs_singleton (s : String) : joinArgs [s] = s := rfl
@[simp] theorem joinArgs_cons_cons (s t : String) (ts : List String) :
    joinArgs (s :: t :: ts) = s ++ ", " ++ joinArgs (t :: ts) := rfl

/-! ## Statement Pretty-Printer -/

/-- Convert a MicroCStmt to canonical C source code (flat form, no indentation).
    Mandatory braces on all control flow. Semicolons on leaf statements. -/
def microCToString : MicroCStmt → String
  | .skip => ";"
  | .break_ => "break;"
  | .continue_ => "continue;"
  | .return_ none => "return;"
  | .return_ (some e) => "return " ++ microCExprToString e ++ ";"
  | .assign name expr =>
    name ++ " = " ++ microCExprToString expr ++ ";"
  | .store base idx val =>
    microCExprToString base ++ "[" ++ microCExprToString idx ++ "] = " ++
      microCExprToString val ++ ";"
  | .load var base idx =>
    var ++ " = " ++ microCExprToString base ++ "[" ++
      microCExprToString idx ++ "];"
  | .call result fname args =>
    result ++ " = " ++ fname ++ "(" ++ joinArgs (args.map microCExprToString) ++ ");"
  | .seq s1 s2 =>
    microCToString s1 ++ " " ++ microCToString s2
  | .ite cond thenB elseB =>
    "if (" ++ microCExprToString cond ++ ") { " ++
      microCToString thenB ++ " } else { " ++
      microCToString elseB ++ " }"
  | .while_ cond body =>
    "while (" ++ microCExprToString cond ++ ") { " ++
      microCToString body ++ " }"

/-! ## microCToString @[simp] Equation Lemmas -/

@[simp] theorem microCToString_skip :
    microCToString .skip = ";" := rfl

@[simp] theorem microCToString_break :
    microCToString .break_ = "break;" := rfl

@[simp] theorem microCToString_continue :
    microCToString .continue_ = "continue;" := rfl

@[simp] theorem microCToString_return_none :
    microCToString (.return_ none) = "return;" := rfl

@[simp] theorem microCToString_return_some (e : MicroCExpr) :
    microCToString (.return_ (some e)) =
      "return " ++ microCExprToString e ++ ";" := rfl

@[simp] theorem microCToString_assign (name : String) (expr : MicroCExpr) :
    microCToString (.assign name expr) =
      name ++ " = " ++ microCExprToString expr ++ ";" := rfl

@[simp] theorem microCToString_store (base idx val : MicroCExpr) :
    microCToString (.store base idx val) =
      microCExprToString base ++ "[" ++ microCExprToString idx ++ "] = " ++
        microCExprToString val ++ ";" := rfl

@[simp] theorem microCToString_load (var : String) (base idx : MicroCExpr) :
    microCToString (.load var base idx) =
      var ++ " = " ++ microCExprToString base ++ "[" ++
        microCExprToString idx ++ "];" := rfl

@[simp] theorem microCToString_call (result fname : String) (args : List MicroCExpr) :
    microCToString (.call result fname args) =
      result ++ " = " ++ fname ++ "(" ++ joinArgs (args.map microCExprToString) ++ ");" := rfl

@[simp] theorem microCToString_seq (s1 s2 : MicroCStmt) :
    microCToString (.seq s1 s2) =
      microCToString s1 ++ " " ++ microCToString s2 := rfl

@[simp] theorem microCToString_ite (cond : MicroCExpr) (thenB elseB : MicroCStmt) :
    microCToString (.ite cond thenB elseB) =
      "if (" ++ microCExprToString cond ++ ") { " ++
        microCToString thenB ++ " } else { " ++
        microCToString elseB ++ " }" := rfl

@[simp] theorem microCToString_while (cond : MicroCExpr) (body : MicroCStmt) :
    microCToString (.while_ cond body) =
      "while (" ++ microCExprToString cond ++ ") { " ++
        microCToString body ++ " }" := rfl

/-! ## Basic Properties -/

/-- microCToString on skip produces ";". -/
theorem microCToString_skip_eq : microCToString .skip = ";" := rfl

/-- microCExprToString on varRef is identity on the name. -/
theorem microCExprToString_varRef_eq (name : String) :
    microCExprToString (.varRef name) = name := rfl

end TrustLean
