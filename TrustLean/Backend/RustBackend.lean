/-
  Trust-Lean — Verified Code Generation Framework
  Backend/RustBackend.lean: Rust code generation from Core IR

  N4.2: HOJA — Rust backend.
  Converts Stmt IR to Rust source code. All 12 Stmt constructors handled.
  Uses i64 as the integer type. Boolean values emitted as true/false.
  Follows the same structure as CBackend.lean for consistency.
-/

import TrustLean.Backend.Common
import TrustLean.Core.Stmt
import TrustLean.Typeclass.BackendEmitter

set_option autoImplicit false

namespace TrustLean

/-! ## Rust Configuration -/

/-- Configuration for the Rust backend. -/
structure RustConfig where
  /-- Use mutable bindings (let mut) for variables. -/
  useMut : Bool := true
  /-- Include power helper function in output. -/
  includePowerHelper : Bool := true
  deriving Repr, Inhabited

/-- Integer type name for Rust. -/
def RustConfig.intType (_ : RustConfig) : String := "i64"

/-! ## Operator Conversion -/

/-- Convert a BinOp to the corresponding Rust infix operator. -/
def binOpToRust : BinOp → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .eqOp => "=="
  | .ltOp => "<"
  | .land => "&&"
  | .lor => "||"

/-- Convert a UnaryOp to the corresponding Rust prefix operator. -/
def unaryOpToRust : UnaryOp → String
  | .neg => "-"
  | .lnot => "!"

/-! ## Expression Emission -/

/-- Convert a LowLevelExpr to a Rust expression string.
    Binary sub-expressions are parenthesized to avoid precedence ambiguity.
    Negative literals use parentheses. Booleans emit as true/false. -/
def exprToRust : LowLevelExpr → String
  | .litInt n => if n < 0 then s!"({n})" else s!"{n}"
  | .litBool true => "true"
  | .litBool false => "false"
  | .varRef v => varNameToStr v
  | .binOp op lhs rhs =>
    "(" ++ exprToRust lhs ++ " " ++ binOpToRust op ++ " " ++ exprToRust rhs ++ ")"
  | .unaryOp op e => "(" ++ unaryOpToRust op ++ exprToRust e ++ ")"
  | .powCall base n => "power(" ++ exprToRust base ++ ", " ++ toString n ++ ")"

/-! ## Statement Emission -/

/-- Convert a Stmt to Rust source code at the given indentation level.
    Handles all 12 Stmt constructors. Rust uses no parens around
    if/while conditions, and uses let mut for assignments. -/
def stmtToRust (level : Nat) : Stmt → String
  | .skip => ""
  | .assign name expr =>
    indentStr level ++ varNameToStr name ++ " = " ++ exprToRust expr ++ ";"
  | .store base idx val =>
    indentStr level ++ exprToRust base ++ "[" ++ exprToRust idx ++ " as usize] = " ++
      exprToRust val ++ ";"
  | .load var base idx =>
    indentStr level ++ varNameToStr var ++ " = " ++
      exprToRust base ++ "[" ++ exprToRust idx ++ " as usize];"
  | .seq s1 s2 => joinCode (stmtToRust level s1) (stmtToRust level s2)
  | .ite cond thenB elseB =>
    let pad := indentStr level
    let tc := stmtToRust (level + 1) thenB
    let ec := stmtToRust (level + 1) elseB
    pad ++ "if " ++ exprToRust cond ++ " {\n" ++ tc ++ "\n" ++
    pad ++ "} else {\n" ++ ec ++ "\n" ++ pad ++ "}"
  | .while cond body =>
    let pad := indentStr level
    let bc := stmtToRust (level + 1) body
    pad ++ "while " ++ exprToRust cond ++ " {\n" ++ bc ++ "\n" ++ pad ++ "}"
  | .for_ init cond step body =>
    let initR := stmtToRust level init
    let bodyR := stmtToRust (level + 1) body
    let stepR := stmtToRust (level + 1) step
    let pad := indentStr level
    let innerBody := joinCode bodyR stepR
    let whileBlock := pad ++ "while " ++ exprToRust cond ++ " {\n" ++
      innerBody ++ "\n" ++ pad ++ "}"
    joinCode initR whileBlock
  | .call result fname args =>
    let argsStr := ", ".intercalate (args.map exprToRust)
    indentStr level ++ varNameToStr result ++ " = " ++ fname ++ "(" ++ argsStr ++ ");"
  | .break_ => indentStr level ++ "break;"
  | .continue_ => indentStr level ++ "continue;"
  | .return_ (some e) => indentStr level ++ "return " ++ exprToRust e ++ ";"
  | .return_ none => indentStr level ++ "return;"

/-! ## Structural Properties -/

/-- stmtToRust on skip produces an empty string. -/
@[simp] theorem stmtToRust_skip (level : Nat) : stmtToRust level .skip = "" := rfl

/-- stmtToRust on break_ produces indented "break;". -/
@[simp] theorem stmtToRust_break (level : Nat) :
    stmtToRust level .break_ = indentStr level ++ "break;" := rfl

/-- stmtToRust on continue_ produces indented "continue;". -/
@[simp] theorem stmtToRust_continue (level : Nat) :
    stmtToRust level .continue_ = indentStr level ++ "continue;" := rfl

/-! ## Function Generation -/

/-- Build a comma-separated Rust parameter list.
    Each pair is (name, type), e.g., ("x", "i64") → "x: i64". -/
private def buildRustParamList (params : List (String × String)) : String :=
  ", ".intercalate (params.map fun (n, t) => n ++ ": " ++ t)

/-- Generate a complete Rust function wrapping a statement body and return expression. -/
def generateRustFunction (_cfg : RustConfig) (funcName : String)
    (params : List (String × String)) (body : Stmt) (result : LowLevelExpr) : String :=
  let signature := "fn " ++ funcName ++ "(" ++ buildRustParamList params ++ ") -> i64"
  let bodyStr := stmtToRust 1 body
  let returnStmt := "  " ++ exprToRust result
  let inner := joinCode bodyStr returnStmt
  signature ++ " {\n" ++ inner ++ "\n}"

/-- Generate Rust preamble with power helper if configured. -/
def generateRustHeader (cfg : RustConfig) : String :=
  if cfg.includePowerHelper then
    "fn power(mut base: i64, mut exp: u32) -> i64 {\n" ++
    "  let mut result: i64 = 1;\n" ++
    "  while exp > 0 {\n" ++
    "    if exp % 2 == 1 { result *= base; }\n" ++
    "    base *= base;\n" ++
    "    exp /= 2;\n" ++
    "  }\n" ++
    "  result\n" ++
    "}"
  else ""

/-! ## BackendEmitter Instance -/

/-- Rust backend implements BackendEmitter. -/
instance : BackendEmitter RustConfig where
  name := "Rust"
  emitStmt _cfg level stmt := stmtToRust level stmt
  emitFunction cfg name params body result := generateRustFunction cfg name params body result
  emitHeader cfg := generateRustHeader cfg

end TrustLean
