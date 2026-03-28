/-
  Trust-Lean — Verified Code Generation Framework
  MicroRust/Parser.lean: Total parser for MicroRust canonical form (Rust syntax)

  Adapted from MicroC/Parser.lean with Rust syntax differences:
  - if/while: no parens around condition (`if cond {` not `if (cond) {`)
  - Array access: `base[idx as usize]` with mandatory `as usize` suffix
  - Store: `base[idx as usize] = val;`
  - Load: `var = base[idx as usize];`
  - Cast: `(e as i64)` / `(e as i32)` postfix syntax inside parens
  - Booleans: `true`/`false` (same as MicroC)

  Key design: pRustExprF/pRustStmtF use Nat fuel for termination.
  parseRustStmtSeq is a separate HOF (no mutual recursion).
-/

import TrustLean.MicroRust.PrettyPrint

set_option autoImplicit false

namespace TrustLean

/-! ## Parser Type (reuse from MicroC) -/

-- We reuse ParseR, skipWs, pDigits, digitsToNat, pNat, pIdent, pBinOp
-- from MicroC/Parser.lean (imported transitively through PrettyPrint → AST).
-- However, MicroC/Parser.lean is NOT imported here to avoid circular deps.
-- We define Rust-specific parser combinators from scratch using the same
-- ParseR pattern.

abbrev ParseRR (α : Type) := List Char → Option (α × List Char)

/-! ## Basic Combinators -/

def skipWsR : List Char → List Char
  | ' ' :: rest => skipWsR rest
  | '\n' :: rest => skipWsR rest
  | '\t' :: rest => skipWsR rest
  | '\r' :: rest => skipWsR rest
  | cs => cs

def pDigitsR : ParseRR (List Char)
  | c :: rest =>
    if c.isDigit then
      match pDigitsR rest with
      | some (ds, rest') => some (c :: ds, rest')
      | none => some ([c], rest)
    else none
  | [] => none

def digitsToNatR (ds : List Char) : Nat :=
  ds.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def pNatR : ParseRR Nat := fun cs =>
  match pDigitsR cs with
  | some (ds, rest) => some (digitsToNatR ds, rest)
  | none => none

def pIdentR : ParseRR String := fun cs =>
  match cs with
  | c :: rest =>
    if c.isAlpha || c == '_' then
      let rec go (acc : List Char) : List Char → List Char × List Char
        | c' :: rest' =>
          if c'.isAlpha || c'.isDigit || c' == '_' then go (acc ++ [c']) rest'
          else (acc, c' :: rest')
        | [] => (acc, [])
      let (more, rest') := go [] rest
      some (String.ofList (c :: more), rest')
    else none
  | [] => none

/-! ## Binary Operator Parser -/

def pBinOpR : ParseRR MicroCBinOp := fun cs =>
  match cs with
  | '=' :: '=' :: rest => some (.eqOp, skipWsR rest)
  | '&' :: '&' :: rest => some (.land, skipWsR rest)
  | '|' :: '|' :: rest => some (.lor, skipWsR rest)
  | '<' :: '<' :: rest => some (.bshl, skipWsR rest)
  | '>' :: '>' :: rest => some (.bshr, skipWsR rest)
  | '+' :: rest => some (.add, skipWsR rest)
  | '-' :: rest => some (.sub, skipWsR rest)
  | '*' :: rest => some (.mul, skipWsR rest)
  | '<' :: rest => some (.ltOp, skipWsR rest)
  | '&' :: rest => some (.band, skipWsR rest)
  | '|' :: rest => some (.bor, skipWsR rest)
  | '^' :: rest => some (.bxor, skipWsR rest)
  | _ => none

/-! ## Helper: match literal string prefix -/

/-- Try to match a literal string at the start of a List Char. -/
def matchLiteral : List Char → List Char → Option (List Char)
  | [], rest => some rest
  | _ :: _, [] => none
  | c :: cs, c' :: rest =>
    if c == c' then matchLiteral cs rest
    else none

/-! ## Total Expression Parser (Rust syntax) -/

/-- Total Rust expression parser with fuel. Fuel decreases on each recursive
    pRustExprF call. At fuel 0, returns none. -/
def pRustExprF : Nat → ParseRR MicroCExpr
  | 0, _ => none
  | fuel + 1, cs =>
    let cs := skipWsR cs
    match cs with
    | '(' :: rest => pRustParenF fuel (skipWsR rest)
    | 'p' :: 'o' :: 'w' :: 'e' :: 'r' :: '(' :: rest =>
      pRustPowF fuel (skipWsR rest)
    | c :: _ =>
      if c.isDigit then
        match pNatR cs with
        | some (n, rest) => some (.litInt (Int.ofNat n), rest)
        | none => none
      else if c.isAlpha || c == '_' then pRustIdentF fuel cs
      else none
    | [] => none
where
  pRustIdentF (fuel : Nat) (cs : List Char) :
      Option (MicroCExpr × List Char) :=
    match pIdentR cs with
    | some (name, rest) =>
      if name == "true" then some (.litBool true, rest)
      else if name == "false" then some (.litBool false, rest)
      else
        let rest' := skipWsR rest
        match rest' with
        | '[' :: rest'' =>
          -- Parse array access: name[idx as usize]
          match pRustExprF fuel (skipWsR rest'') with
          | some (idx, rest''') =>
            -- Expect " as usize]"
            match matchLiteral ('a' :: 's' :: ' ' :: 'u' :: 's' :: 'i' :: 'z' :: 'e' :: ']' :: []) (skipWsR rest''') with
            | some final => some (.arrayAccess (.varRef name) idx, final)
            | none => none
          | none => none
        | _ => some (.varRef name, rest)
    | none => none
  pRustParenF (fuel : Nat) (cs : List Char) :
      Option (MicroCExpr × List Char) :=
    match cs with
    | '!' :: rest =>
      -- Logical not: (!e)
      match pRustExprF fuel rest with
      | some (e, rest') =>
        match skipWsR rest' with
        | ')' :: final => some (.unaryOp .lnot e, final)
        | _ => none
      | none => none
    | '-' :: c :: rest =>
      if c.isDigit then
        -- Negative literal: (-123)
        match pNatR (c :: rest) with
        | some (n, rest') =>
          match skipWsR rest' with
          | ')' :: final => some (.litInt (-(Int.ofNat n)), final)
          | _ => none
        | none => none
      else
        -- Unary neg: (-e)
        match pRustExprF fuel (c :: rest) with
        | some (e, rest') =>
          match skipWsR rest' with
          | ')' :: final => some (.unaryOp .neg e, final)
          | _ => none
        | none => none
    | _ =>
      -- Either binary op: (lhs op rhs) or cast: (e as i64) / (e as i32)
      match pRustExprF fuel cs with
      | some (lhs, rest) =>
        let rest := skipWsR rest
        -- Try cast: "as i64)" or "as i32)"
        match rest with
        | 'a' :: 's' :: ' ' :: 'i' :: '6' :: '4' :: ')' :: final =>
          some (.unaryOp .widen32to64 lhs, final)
        | 'a' :: 's' :: ' ' :: 'i' :: '3' :: '2' :: ')' :: final =>
          some (.unaryOp .trunc64to32 lhs, final)
        | _ =>
          -- Binary op: (lhs op rhs)
          match pBinOpR rest with
          | some (op, rest') =>
            match pRustExprF fuel rest' with
            | some (rhs, rest'') =>
              match skipWsR rest'' with
              | ')' :: final => some (.binOp op lhs rhs, final)
              | _ => none
            | none => none
          | none => none
      | none => none
  pRustPowF (fuel : Nat) (cs : List Char) :
      Option (MicroCExpr × List Char) :=
    match pRustExprF fuel cs with
    | some (base, rest) =>
      match skipWsR rest with
      | ',' :: rest' =>
        match pNatR (skipWsR rest') with
        | some (n, rest'') =>
          match skipWsR rest'' with
          | ')' :: final => some (.powCall base n, final)
          | _ => none
        | none => none
      | _ => none
    | none => none

/-! ## Statement Sequence Parser (HOF — breaks mutual recursion) -/

/-- Parse a sequence of statements using a given statement parser.
    seqFuel bounds the number of statements in the sequence. -/
def parseRustStmtSeq (parseOne : ParseRR MicroCStmt) : Nat → ParseRR MicroCStmt
  | 0, cs => parseOne cs
  | n + 1, cs =>
    match parseOne cs with
    | some (first, rest) =>
      let rest' := skipWsR rest
      match rest' with
      | '}' :: _ => some (first, rest')
      | [] => some (first, rest')
      | _ =>
        match parseRustStmtSeq parseOne n rest' with
        | some (more, final) => some (.seq first more, final)
        | none => some (first, rest')
    | none => none

/-! ## Total Statement Parser (Rust syntax) -/

/-- Total Rust statement parser with fuel. -/
def pRustStmtF : Nat → ParseRR MicroCStmt
  | 0, _ => none
  | fuel + 1, cs =>
    let cs := skipWsR cs
    match cs with
    | ';' :: rest => some (.skip, rest)
    | 'b' :: 'r' :: 'e' :: 'a' :: 'k' :: ';' :: rest =>
      some (.break_, rest)
    | 'c' :: 'o' :: 'n' :: 't' :: 'i' :: 'n' :: 'u' :: 'e' :: ';' :: rest =>
      some (.continue_, rest)
    | 'r' :: 'e' :: 't' :: 'u' :: 'r' :: 'n' :: rest =>
      pRustReturnF fuel (skipWsR rest)
    | 'i' :: 'f' :: ' ' :: rest => pRustIfF fuel (skipWsR rest)
    | 'w' :: 'h' :: 'i' :: 'l' :: 'e' :: ' ' :: rest =>
      pRustWhileF fuel (skipWsR rest)
    | _ => pRustAssignOrStoreF fuel cs
where
  pRustReturnF (fuel : Nat) (cs : List Char) :
      Option (MicroCStmt × List Char) :=
    match cs with
    | ';' :: rest => some (.return_ none, rest)
    | _ =>
      match pRustExprF (fuel + 1) cs with
      | some (e, rest) =>
        match skipWsR rest with
        | ';' :: final => some (.return_ (some e), final)
        | _ => none
      | none => none
  pRustIfF (fuel : Nat) (cs : List Char) :
      Option (MicroCStmt × List Char) :=
    -- Rust: if cond { body } else { body }  (no parens around cond)
    match pRustExprF (fuel + 1) cs with
    | some (cond, rest') =>
      match skipWsR rest' with
      | '{' :: rest'' =>
        match parseRustStmtSeq (pRustStmtF fuel) fuel (skipWsR rest'') with
        | some (thenB, rest3) =>
          match skipWsR rest3 with
          | '}' :: rest4 =>
            match skipWsR rest4 with
            | 'e' :: 'l' :: 's' :: 'e' :: rest5 =>
              match skipWsR rest5 with
              | '{' :: rest6 =>
                match parseRustStmtSeq (pRustStmtF fuel) fuel
                    (skipWsR rest6) with
                | some (elseB, rest7) =>
                  match skipWsR rest7 with
                  | '}' :: final =>
                    some (.ite cond thenB elseB, final)
                  | _ => none
                | none => none
              | _ => none
            | _ => none
          | _ => none
        | none => none
      | _ => none
    | none => none
  pRustWhileF (fuel : Nat) (cs : List Char) :
      Option (MicroCStmt × List Char) :=
    -- Rust: while cond { body }  (no parens around cond)
    match pRustExprF (fuel + 1) cs with
    | some (cond, rest') =>
      match skipWsR rest' with
      | '{' :: rest'' =>
        match parseRustStmtSeq (pRustStmtF fuel) fuel (skipWsR rest'') with
        | some (body, rest3) =>
          match skipWsR rest3 with
          | '}' :: final => some (.while_ cond body, final)
          | _ => none
        | none => none
      | _ => none
    | none => none
  pRustAssignOrStoreF (fuel : Nat) (cs : List Char) :
      Option (MicroCStmt × List Char) :=
    match pIdentR (skipWsR cs) with
    | some (name, rest) =>
      let rest := skipWsR rest
      match rest with
      | '[' :: rest' =>
        -- Array store: name[idx as usize] = val;
        match pRustExprF (fuel + 1) (skipWsR rest') with
        | some (idx, rest'') =>
          -- Expect " as usize]"
          match matchLiteral ('a' :: 's' :: ' ' :: 'u' :: 's' :: 'i' :: 'z' :: 'e' :: ']' :: []) (skipWsR rest'') with
          | some rest''' =>
            match skipWsR rest''' with
            | '=' :: rest4 =>
              match pRustExprF (fuel + 1) (skipWsR rest4) with
              | some (val, rest5) =>
                match skipWsR rest5 with
                | ';' :: final =>
                  some (.store (.varRef name) idx val, final)
                | _ => none
              | none => none
            | _ => none
          | none => none
        | none => none
      | '=' :: rest' =>
        pRustRhsF fuel name (skipWsR rest')
      | _ => none
    | none => none
  pRustRhsF (fuel : Nat) (var : String) (cs : List Char) :
      Option (MicroCStmt × List Char) :=
    match pIdentR cs with
    | some (ident, rest) =>
      let rest' := skipWsR rest
      match rest' with
      | '[' :: rest'' =>
        -- Load: var = base[idx as usize];
        match pRustExprF (fuel + 1) (skipWsR rest'') with
        | some (idx, rest''') =>
          -- Expect " as usize]"
          match matchLiteral ('a' :: 's' :: ' ' :: 'u' :: 's' :: 'i' :: 'z' :: 'e' :: ']' :: []) (skipWsR rest''') with
          | some rest4 =>
            match skipWsR rest4 with
            | ';' :: final =>
              some (.load var (.varRef ident) idx, final)
            | _ => none
          | none => none
        | none => none
      | '(' :: rest'' =>
        -- Call: var = fname(args);
        match pRustArgsF (fuel + 1) (skipWsR rest'') with
        | some (args, rest''') =>
          match skipWsR rest''' with
          | ')' :: rest4 =>
            match skipWsR rest4 with
            | ';' :: final => some (.call var ident args, final)
            | _ => none
          | _ => none
        | none => none
      | ';' :: final =>
        some (.assign var (.varRef ident), final)
      | _ => none
    | none =>
      match pRustExprF (fuel + 1) cs with
      | some (e, rest) =>
        match skipWsR rest with
        | ';' :: final => some (.assign var e, final)
        | _ => none
      | none => none
  pRustArgsF (fuel : Nat) (cs : List Char) :
      Option (List MicroCExpr × List Char) :=
    let cs := skipWsR cs
    match cs with
    | ')' :: _ => some ([], cs)
    | _ =>
      match pRustExprF fuel cs with
      | some (first, rest) => goRustArgs fuel [first] rest
      | none => none
  goRustArgs (fuel : Nat) (acc : List MicroCExpr) (cs : List Char) :
      Option (List MicroCExpr × List Char) :=
    let cs := skipWsR cs
    match fuel with
    | 0 => some (acc, cs)
    | n + 1 =>
      match cs with
      | ',' :: rest =>
        match pRustExprF (n + 1) (skipWsR rest) with
        | some (e, rest') => goRustArgs n (acc ++ [e]) rest'
        | none => none
      | _ => some (acc, cs)

/-! ## Top-Level Parse Functions -/

def parseMicroRustExpr (s : String) : Option MicroCExpr :=
  let cs := s.toList
  match pRustExprF (cs.length + 1) cs with
  | some (e, rest) => if skipWsR rest == [] then some e else none
  | none => none

def parseMicroRust (s : String) : Option MicroCStmt :=
  let cs := s.toList
  let fuel := cs.length + 1
  match pRustStmtF fuel cs with
  | some (stmt, rest) =>
    let rest' := skipWsR rest
    if rest' == [] then some stmt
    else
      match parseRustStmtSeq (pRustStmtF fuel) fuel rest' with
      | some (more, final) =>
        if skipWsR final == [] then some (.seq stmt more) else none
      | none => none
  | none => none

end TrustLean
