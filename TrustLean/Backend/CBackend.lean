/-
  Trust-Lean — Verified Code Generation Framework
  Backend/CBackend.lean: C code generation from Core IR

  N4.1 (v1.0.0): C backend (C99/C11 compatible).
  N9.2 (v1.2.0): Industrial upgrade — sanitized identifiers, autocontained headers,
  mandatory braces on all control flow. All 12 Stmt constructors handled.
  Based on LeanScribe's CBackend.lean, extended for Trust-Lean's full IR.
-/

import TrustLean.Backend.Common
import TrustLean.Core.Stmt
import TrustLean.Typeclass.BackendEmitter

set_option autoImplicit false

namespace TrustLean

/-! ## C Configuration -/

/-- Configuration for the C backend. -/
structure CConfig where
  /-- Use int64_t (true) or long long (false) for integers. -/
  useInt64 : Bool := true
  /-- Include power helper function in output. -/
  includePowerHelper : Bool := true
  deriving Repr, Inhabited

/-- Integer type name based on config. -/
def CConfig.intType (cfg : CConfig) : String :=
  if cfg.useInt64 then "int64_t" else "long long"

/-! ## Operator Conversion -/

/-- Convert a BinOp to the corresponding C infix operator. -/
def binOpToC : BinOp → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .eqOp => "=="
  | .ltOp => "<"
  | .land => "&&"
  | .lor => "||"

/-- Convert a UnaryOp to the corresponding C prefix operator. -/
def unaryOpToC : UnaryOp → String
  | .neg => "-"
  | .lnot => "!"

/-! ## C-Safe Variable Names (N9.2) -/

/-- Convert VarName to a C-safe identifier string.
    Applies sanitizeIdentifier to user variables to avoid C keyword collisions.
    Temps and array accesses are structurally safe by construction. -/
def varNameToC : VarName → String
  | .user s => sanitizeIdentifier s
  | v => varNameToStr v

/-! ## Expression Emission -/

/-- Convert a LowLevelExpr to a C expression string.
    All binary sub-expressions are fully parenthesized to avoid precedence ambiguity.
    Unary operations are parenthesized. Negative literals are parenthesized. -/
def exprToC : LowLevelExpr → String
  | .litInt n => if n < 0 then s!"({n})" else s!"{n}"
  | .litBool true => "1"
  | .litBool false => "0"
  | .varRef v => varNameToC v
  | .binOp op lhs rhs =>
    "(" ++ exprToC lhs ++ " " ++ binOpToC op ++ " " ++ exprToC rhs ++ ")"
  | .unaryOp op e => "(" ++ unaryOpToC op ++ exprToC e ++ ")"
  | .powCall base n => "power(" ++ exprToC base ++ ", " ++ toString n ++ ")"

/-! ## Statement Emission -/

/-- Convert a Stmt to C source code at the given indentation level.
    Handles all 12 Stmt constructors. Mandatory braces on all control flow.
    All identifiers sanitized via varNameToC. -/
def stmtToC (level : Nat) : Stmt → String
  | .skip => ""
  | .assign name expr =>
    indentStr level ++ varNameToC name ++ " = " ++ exprToC expr ++ ";"
  | .store base idx val =>
    indentStr level ++ exprToC base ++ "[" ++ exprToC idx ++ "] = " ++ exprToC val ++ ";"
  | .load var base idx =>
    indentStr level ++ varNameToC var ++ " = " ++
      exprToC base ++ "[" ++ exprToC idx ++ "];"
  | .seq s1 s2 => joinCode (stmtToC level s1) (stmtToC level s2)
  | .ite cond thenB elseB =>
    let pad := indentStr level
    let tc := stmtToC (level + 1) thenB
    let ec := stmtToC (level + 1) elseB
    pad ++ "if (" ++ exprToC cond ++ ") {\n" ++ tc ++ "\n" ++
    pad ++ "} else {\n" ++ ec ++ "\n" ++ pad ++ "}"
  | .while cond body =>
    let pad := indentStr level
    let bc := stmtToC (level + 1) body
    pad ++ "while (" ++ exprToC cond ++ ") {\n" ++ bc ++ "\n" ++ pad ++ "}"
  | .for_ init cond step body =>
    let initC := stmtToC level init
    let bodyC := stmtToC (level + 1) body
    let stepC := stmtToC (level + 1) step
    let pad := indentStr level
    let innerBody := joinCode bodyC stepC
    let whileBlock := pad ++ "while (" ++ exprToC cond ++ ") {\n" ++
      innerBody ++ "\n" ++ pad ++ "}"
    joinCode initC whileBlock
  | .call result fname args =>
    let argsStr := ", ".intercalate (args.map exprToC)
    indentStr level ++ varNameToC result ++ " = " ++
      sanitizeIdentifier fname ++ "(" ++ argsStr ++ ");"
  | .break_ => indentStr level ++ "break;"
  | .continue_ => indentStr level ++ "continue;"
  | .return_ (some e) => indentStr level ++ "return " ++ exprToC e ++ ";"
  | .return_ none => indentStr level ++ "return;"

/-! ## Structural Properties -/

/-- stmtToC on skip produces an empty string. -/
@[simp] theorem stmtToC_skip (level : Nat) : stmtToC level .skip = "" := rfl

/-- stmtToC on break_ produces indented "break;". -/
@[simp] theorem stmtToC_break (level : Nat) :
    stmtToC level .break_ = indentStr level ++ "break;" := rfl

/-- stmtToC on continue_ produces indented "continue;". -/
@[simp] theorem stmtToC_continue (level : Nat) :
    stmtToC level .continue_ = indentStr level ++ "continue;" := rfl

/-- stmtToC on return_ none produces indented "return;". -/
@[simp] theorem stmtToC_return_none (level : Nat) :
    stmtToC level (.return_ none) = indentStr level ++ "return;" := rfl

/-! ## Function Generation -/

/-- Build a comma-separated C parameter list with sanitized names.
    Each pair is (name, type), e.g., ("x", "int64_t"). -/
private def buildParamList (params : List (String × String)) : String :=
  ", ".intercalate (params.map fun (n, t) => t ++ " " ++ sanitizeIdentifier n)

/-- Generate a complete C function wrapping a statement body and return expression.
    Function name and parameter names are sanitized. -/
def generateCFunction (cfg : CConfig) (funcName : String)
    (params : List (String × String)) (body : Stmt) (result : LowLevelExpr) : String :=
  let safeName := sanitizeIdentifier funcName
  let signature := cfg.intType ++ " " ++ safeName ++ "(" ++ buildParamList params ++ ")"
  let bodyStr := stmtToC 1 body
  let returnStmt := "  return " ++ exprToC result ++ ";"
  let inner := joinCode bodyStr returnStmt
  signature ++ " {\n" ++ inner ++ "\n}"

/-- Generate C preamble with necessary includes.
    Autocontained: includes stdint.h (int64_t), stdbool.h (bool), stdlib.h (general). -/
def generateCHeader (cfg : CConfig) : String :=
  let base := "#include <stdint.h>\n#include <stdbool.h>\n#include <stdlib.h>"
  if cfg.includePowerHelper then
    base ++ "\n\n" ++
    "static " ++ cfg.intType ++ " power(" ++ cfg.intType ++ " base, unsigned int exp) {\n" ++
    "  " ++ cfg.intType ++ " result = 1;\n" ++
    "  while (exp > 0) {\n" ++
    "    if (exp % 2 == 1) result *= base;\n" ++
    "    base *= base;\n" ++
    "    exp /= 2;\n" ++
    "  }\n" ++
    "  return result;\n" ++
    "}"
  else base

/-! ## BackendEmitter Instance -/

/-- C backend implements BackendEmitter. -/
instance : BackendEmitter CConfig where
  name := "C"
  emitStmt _cfg level stmt := stmtToC level stmt
  emitFunction cfg name params body result := generateCFunction cfg name params body result
  emitHeader cfg := generateCHeader cfg

end TrustLean
