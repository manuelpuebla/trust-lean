/-
  Trust-Lean — Verified Code Generation Framework
  MicroRust/PrettyPrint.lean: Pretty-printer for MicroRust AST (Rust syntax)

  Adapted from MicroC/PrettyPrint.lean with Rust syntax differences:
  - if/while: no parens around condition (`if cond {` not `if (cond) {`)
  - Array access: `base[idx as usize]` not `base[idx]`
  - Store: `base[idx as usize] = val;`
  - Load: `var = base[idx as usize];`
  - Cast: `(e as i64)` / `(e as i32)` not `((int64_t)e)` / `((int32_t)e)`
  - Booleans: `true`/`false` (same as MicroC)

  Fully parenthesized canonical form. No indentation (flat form for roundtrip proofs).
-/

import TrustLean.MicroC.AST
import TrustLean.MicroC.PrettyPrint
import TrustLean.Backend.Common

set_option autoImplicit false

namespace TrustLean

/-! ## Operator Strings (Rust) -/

/-- Convert MicroCBinOp to its Rust infix operator string.
    Identical to C — all binary operators share the same syntax. -/
def microRustBinOpToString : MicroCBinOp → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .eqOp => "=="
  | .ltOp => "<"
  | .land => "&&"
  | .lor => "||"
  | .band => "&"
  | .bor => "|"
  | .bxor => "^"
  | .bshl => "<<"
  | .bshr => ">>"

/-- Convert MicroCUnaryOp to its Rust prefix operator string.
    Casts use `as i64`/`as i32` postfix syntax (rendered inside parens by expr printer). -/
def microRustUnaryOpToString : MicroCUnaryOp → String
  | .neg => "-"
  | .lnot => "!"
  | .widen32to64 => " as i64"
  | .trunc64to32 => " as i32"

/-! ## microRustBinOpToString @[simp] Equation Lemmas -/

@[simp] theorem microRustBinOpToString_add : microRustBinOpToString .add = "+" := rfl
@[simp] theorem microRustBinOpToString_sub : microRustBinOpToString .sub = "-" := rfl
@[simp] theorem microRustBinOpToString_mul : microRustBinOpToString .mul = "*" := rfl
@[simp] theorem microRustBinOpToString_eqOp : microRustBinOpToString .eqOp = "==" := rfl
@[simp] theorem microRustBinOpToString_ltOp : microRustBinOpToString .ltOp = "<" := rfl
@[simp] theorem microRustBinOpToString_land : microRustBinOpToString .land = "&&" := rfl
@[simp] theorem microRustBinOpToString_lor : microRustBinOpToString .lor = "||" := rfl
@[simp] theorem microRustBinOpToString_band : microRustBinOpToString .band = "&" := rfl
@[simp] theorem microRustBinOpToString_bor : microRustBinOpToString .bor = "|" := rfl
@[simp] theorem microRustBinOpToString_bxor : microRustBinOpToString .bxor = "^" := rfl
@[simp] theorem microRustBinOpToString_bshl : microRustBinOpToString .bshl = "<<" := rfl
@[simp] theorem microRustBinOpToString_bshr : microRustBinOpToString .bshr = ">>" := rfl

@[simp] theorem microRustUnaryOpToString_neg : microRustUnaryOpToString .neg = "-" := rfl
@[simp] theorem microRustUnaryOpToString_lnot : microRustUnaryOpToString .lnot = "!" := rfl
@[simp] theorem microRustUnaryOpToString_widen : microRustUnaryOpToString .widen32to64 = " as i64" := rfl
@[simp] theorem microRustUnaryOpToString_trunc : microRustUnaryOpToString .trunc64to32 = " as i32" := rfl

/-! ## Expression Pretty-Printer (Rust syntax) -/

/-- Convert a MicroCExpr to a canonical Rust expression string.
    Fully parenthesized binary expressions. Negative literals parenthesized.
    Booleans as "true"/"false". Array access uses `as usize`.
    Casts use postfix `as i64`/`as i32` syntax.
    Uses natToChars for provable roundtrip. -/
def microRustExprToString : MicroCExpr → String
  | .litInt n =>
    if n < 0 then "(" ++ "-" ++ String.ofList (natToChars n.natAbs) ++ ")"
    else String.ofList (natToChars n.toNat)
  | .litBool true => "true"
  | .litBool false => "false"
  | .varRef name => name
  | .binOp op lhs rhs =>
    "(" ++ microRustExprToString lhs ++ " " ++ microRustBinOpToString op ++
      " " ++ microRustExprToString rhs ++ ")"
  | .unaryOp .neg e =>
    "(" ++ "-" ++ microRustExprToString e ++ ")"
  | .unaryOp .lnot e =>
    "(" ++ "!" ++ microRustExprToString e ++ ")"
  | .unaryOp .widen32to64 e =>
    "(" ++ microRustExprToString e ++ " as i64)"
  | .unaryOp .trunc64to32 e =>
    "(" ++ microRustExprToString e ++ " as i32)"
  | .powCall base n =>
    "power(" ++ microRustExprToString base ++ ", " ++
      String.ofList (natToChars n) ++ ")"
  | .arrayAccess base idx =>
    microRustExprToString base ++ "[" ++ microRustExprToString idx ++ " as usize]"

/-! ## microRustExprToString @[simp] Equation Lemmas -/

@[simp] theorem microRustExprToString_litInt (n : Int) :
    microRustExprToString (.litInt n) =
      if n < 0 then "(" ++ "-" ++ String.ofList (natToChars n.natAbs) ++ ")"
      else String.ofList (natToChars n.toNat) := rfl

@[simp] theorem microRustExprToString_litBool_true :
    microRustExprToString (.litBool true) = "true" := rfl

@[simp] theorem microRustExprToString_litBool_false :
    microRustExprToString (.litBool false) = "false" := rfl

@[simp] theorem microRustExprToString_varRef (name : String) :
    microRustExprToString (.varRef name) = name := rfl

@[simp] theorem microRustExprToString_binOp (op : MicroCBinOp) (lhs rhs : MicroCExpr) :
    microRustExprToString (.binOp op lhs rhs) =
      "(" ++ microRustExprToString lhs ++ " " ++ microRustBinOpToString op ++
        " " ++ microRustExprToString rhs ++ ")" := rfl

@[simp] theorem microRustExprToString_unaryOp_neg (e : MicroCExpr) :
    microRustExprToString (.unaryOp .neg e) =
      "(" ++ "-" ++ microRustExprToString e ++ ")" := rfl

@[simp] theorem microRustExprToString_unaryOp_lnot (e : MicroCExpr) :
    microRustExprToString (.unaryOp .lnot e) =
      "(" ++ "!" ++ microRustExprToString e ++ ")" := rfl

@[simp] theorem microRustExprToString_unaryOp_widen (e : MicroCExpr) :
    microRustExprToString (.unaryOp .widen32to64 e) =
      "(" ++ microRustExprToString e ++ " as i64)" := rfl

@[simp] theorem microRustExprToString_unaryOp_trunc (e : MicroCExpr) :
    microRustExprToString (.unaryOp .trunc64to32 e) =
      "(" ++ microRustExprToString e ++ " as i32)" := rfl

@[simp] theorem microRustExprToString_powCall (base : MicroCExpr) (n : Nat) :
    microRustExprToString (.powCall base n) =
      "power(" ++ microRustExprToString base ++ ", " ++
        String.ofList (natToChars n) ++ ")" := rfl

@[simp] theorem microRustExprToString_arrayAccess (base idx : MicroCExpr) :
    microRustExprToString (.arrayAccess base idx) =
      microRustExprToString base ++ "[" ++ microRustExprToString idx ++ " as usize]" := rfl

/-! ## Statement Pretty-Printer (Rust syntax) -/

/-- Convert a MicroCStmt to canonical Rust source code (flat form, no indentation).
    Mandatory braces on all control flow. Semicolons on leaf statements.
    Rust differences: no parens on if/while conditions, `as usize` on array indices. -/
def microRustToString : MicroCStmt → String
  | .skip => ";"
  | .break_ => "break;"
  | .continue_ => "continue;"
  | .return_ none => "return;"
  | .return_ (some e) => "return " ++ microRustExprToString e ++ ";"
  | .assign name expr =>
    name ++ " = " ++ microRustExprToString expr ++ ";"
  | .store base idx val =>
    microRustExprToString base ++ "[" ++ microRustExprToString idx ++
      " as usize] = " ++ microRustExprToString val ++ ";"
  | .load var base idx =>
    var ++ " = " ++ microRustExprToString base ++ "[" ++
      microRustExprToString idx ++ " as usize];"
  | .call result fname args =>
    result ++ " = " ++ fname ++ "(" ++ joinArgs (args.map microRustExprToString) ++ ");"
  | .seq s1 s2 =>
    microRustToString s1 ++ " " ++ microRustToString s2
  | .ite cond thenB elseB =>
    "if " ++ microRustExprToString cond ++ " { " ++
      microRustToString thenB ++ " } else { " ++
      microRustToString elseB ++ " }"
  | .while_ cond body =>
    "while " ++ microRustExprToString cond ++ " { " ++
      microRustToString body ++ " }"

/-! ## microRustToString @[simp] Equation Lemmas -/

@[simp] theorem microRustToString_skip :
    microRustToString .skip = ";" := rfl

@[simp] theorem microRustToString_break :
    microRustToString .break_ = "break;" := rfl

@[simp] theorem microRustToString_continue :
    microRustToString .continue_ = "continue;" := rfl

@[simp] theorem microRustToString_return_none :
    microRustToString (.return_ none) = "return;" := rfl

@[simp] theorem microRustToString_return_some (e : MicroCExpr) :
    microRustToString (.return_ (some e)) =
      "return " ++ microRustExprToString e ++ ";" := rfl

@[simp] theorem microRustToString_assign (name : String) (expr : MicroCExpr) :
    microRustToString (.assign name expr) =
      name ++ " = " ++ microRustExprToString expr ++ ";" := rfl

@[simp] theorem microRustToString_store (base idx val : MicroCExpr) :
    microRustToString (.store base idx val) =
      microRustExprToString base ++ "[" ++ microRustExprToString idx ++
        " as usize] = " ++ microRustExprToString val ++ ";" := rfl

@[simp] theorem microRustToString_load (var : String) (base idx : MicroCExpr) :
    microRustToString (.load var base idx) =
      var ++ " = " ++ microRustExprToString base ++ "[" ++
        microRustExprToString idx ++ " as usize];" := rfl

@[simp] theorem microRustToString_call (result fname : String) (args : List MicroCExpr) :
    microRustToString (.call result fname args) =
      result ++ " = " ++ fname ++ "(" ++ joinArgs (args.map microRustExprToString) ++ ");" := rfl

@[simp] theorem microRustToString_seq (s1 s2 : MicroCStmt) :
    microRustToString (.seq s1 s2) =
      microRustToString s1 ++ " " ++ microRustToString s2 := rfl

@[simp] theorem microRustToString_ite (cond : MicroCExpr) (thenB elseB : MicroCStmt) :
    microRustToString (.ite cond thenB elseB) =
      "if " ++ microRustExprToString cond ++ " { " ++
        microRustToString thenB ++ " } else { " ++
        microRustToString elseB ++ " }" := rfl

@[simp] theorem microRustToString_while (cond : MicroCExpr) (body : MicroCStmt) :
    microRustToString (.while_ cond body) =
      "while " ++ microRustExprToString cond ++ " { " ++
        microRustToString body ++ " }" := rfl

/-! ## Basic Properties -/

/-- microRustToString on skip produces ";". -/
theorem microRustToString_skip_eq : microRustToString .skip = ";" := rfl

/-- microRustExprToString on varRef is identity on the name. -/
theorem microRustExprToString_varRef_eq (name : String) :
    microRustExprToString (.varRef name) = name := rfl

end TrustLean
