/-
  Trust-Lean — Verified Code Generation Framework
  MicroC/Parser.lean: Total parser for MicroC canonical form

  N12.2 (v2.0.0): PAR — total parsers with fuel for roundtrip proofs.
  Hand-rolled recursive descent on List Char.

  Key design: pExprF/pStmtF use Nat fuel for termination.
  parseStmtSeq is a separate HOF (no mutual recursion).
-/

import TrustLean.MicroC.PrettyPrint

set_option autoImplicit false

namespace TrustLean

/-! ## Parser Type -/

abbrev ParseR (α : Type) := List Char → Option (α × List Char)

/-! ## Basic Combinators -/

def skipWs : List Char → List Char
  | ' ' :: rest => skipWs rest
  | '\n' :: rest => skipWs rest
  | '\t' :: rest => skipWs rest
  | '\r' :: rest => skipWs rest
  | cs => cs

def pDigits : ParseR (List Char)
  | c :: rest =>
    if c.isDigit then
      match pDigits rest with
      | some (ds, rest') => some (c :: ds, rest')
      | none => some ([c], rest)
    else none
  | [] => none

def digitsToNat (ds : List Char) : Nat :=
  ds.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def pNat : ParseR Nat := fun cs =>
  match pDigits cs with
  | some (ds, rest) => some (digitsToNat ds, rest)
  | none => none

def pIdent : ParseR String := fun cs =>
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

def pBinOp : ParseR MicroCBinOp := fun cs =>
  match cs with
  | '=' :: '=' :: rest => some (.eqOp, skipWs rest)
  | '&' :: '&' :: rest => some (.land, skipWs rest)
  | '|' :: '|' :: rest => some (.lor, skipWs rest)
  | '+' :: rest => some (.add, skipWs rest)
  | '-' :: rest => some (.sub, skipWs rest)
  | '*' :: rest => some (.mul, skipWs rest)
  | '<' :: rest => some (.ltOp, skipWs rest)
  | _ => none

/-! ## Total Expression Parser -/

/-- Total expression parser with fuel. Fuel decreases on each recursive
    pExprF call. At fuel 0, returns none. -/
def pExprF : Nat → ParseR MicroCExpr
  | 0, _ => none
  | fuel + 1, cs =>
    let cs := skipWs cs
    match cs with
    | '(' :: rest => pParenF fuel (skipWs rest)
    | 'p' :: 'o' :: 'w' :: 'e' :: 'r' :: '(' :: rest =>
      pPowF fuel (skipWs rest)
    | c :: _ =>
      if c.isDigit then
        match pNat cs with
        | some (n, rest) => some (.litInt (Int.ofNat n), rest)
        | none => none
      else if c.isAlpha || c == '_' then pIdentF fuel cs
      else none
    | [] => none
where
  pIdentF (fuel : Nat) (cs : List Char) :
      Option (MicroCExpr × List Char) :=
    match pIdent cs with
    | some (name, rest) =>
      if name == "true" then some (.litBool true, rest)
      else if name == "false" then some (.litBool false, rest)
      else
        let rest' := skipWs rest
        match rest' with
        | '[' :: rest'' =>
          match pExprF fuel (skipWs rest'') with
          | some (idx, rest''') =>
            match skipWs rest''' with
            | ']' :: final => some (.arrayAccess (.varRef name) idx, final)
            | _ => none
          | none => none
        | _ => some (.varRef name, rest)
    | none => none
  pParenF (fuel : Nat) (cs : List Char) :
      Option (MicroCExpr × List Char) :=
    match cs with
    | '!' :: rest =>
      match pExprF fuel rest with
      | some (e, rest') =>
        match skipWs rest' with
        | ')' :: final => some (.unaryOp .lnot e, final)
        | _ => none
      | none => none
    | '-' :: c :: rest =>
      if c.isDigit then
        match pNat (c :: rest) with
        | some (n, rest') =>
          match skipWs rest' with
          | ')' :: final => some (.litInt (-(Int.ofNat n)), final)
          | _ => none
        | none => none
      else
        match pExprF fuel (c :: rest) with
        | some (e, rest') =>
          match skipWs rest' with
          | ')' :: final => some (.unaryOp .neg e, final)
          | _ => none
        | none => none
    | _ =>
      match pExprF fuel cs with
      | some (lhs, rest) =>
        match pBinOp (skipWs rest) with
        | some (op, rest') =>
          match pExprF fuel rest' with
          | some (rhs, rest'') =>
            match skipWs rest'' with
            | ')' :: final => some (.binOp op lhs rhs, final)
            | _ => none
          | none => none
        | none => none
      | none => none
  pPowF (fuel : Nat) (cs : List Char) :
      Option (MicroCExpr × List Char) :=
    match pExprF fuel cs with
    | some (base, rest) =>
      match skipWs rest with
      | ',' :: rest' =>
        match pNat (skipWs rest') with
        | some (n, rest'') =>
          match skipWs rest'' with
          | ')' :: final => some (.powCall base n, final)
          | _ => none
        | none => none
      | _ => none
    | none => none

/-! ## Statement Sequence Parser (HOF — breaks mutual recursion) -/

/-- Parse a sequence of statements using a given statement parser.
    seqFuel bounds the number of statements in the sequence. -/
def parseStmtSeq (parseOne : ParseR MicroCStmt) : Nat → ParseR MicroCStmt
  | 0, cs => parseOne cs
  | n + 1, cs =>
    match parseOne cs with
    | some (first, rest) =>
      let rest' := skipWs rest
      match rest' with
      | '}' :: _ => some (first, rest')
      | [] => some (first, rest')
      | _ =>
        match parseStmtSeq parseOne n rest' with
        | some (more, final) => some (.seq first more, final)
        | none => some (first, rest')
    | none => none

/-! ## Total Statement Parser -/

/-- Total statement parser with fuel. -/
def pStmtF : Nat → ParseR MicroCStmt
  | 0, _ => none
  | fuel + 1, cs =>
    let cs := skipWs cs
    match cs with
    | ';' :: rest => some (.skip, rest)
    | 'b' :: 'r' :: 'e' :: 'a' :: 'k' :: ';' :: rest =>
      some (.break_, rest)
    | 'c' :: 'o' :: 'n' :: 't' :: 'i' :: 'n' :: 'u' :: 'e' :: ';' :: rest =>
      some (.continue_, rest)
    | 'r' :: 'e' :: 't' :: 'u' :: 'r' :: 'n' :: rest =>
      pReturnF fuel (skipWs rest)
    | 'i' :: 'f' :: ' ' :: rest => pIfF fuel (skipWs rest)
    | 'i' :: 'f' :: '(' :: rest => pIfF fuel ('(' :: rest)
    | 'w' :: 'h' :: 'i' :: 'l' :: 'e' :: ' ' :: rest =>
      pWhileF fuel (skipWs rest)
    | 'w' :: 'h' :: 'i' :: 'l' :: 'e' :: '(' :: rest =>
      pWhileF fuel ('(' :: rest)
    | _ => pAssignOrStoreF fuel cs
where
  pReturnF (fuel : Nat) (cs : List Char) :
      Option (MicroCStmt × List Char) :=
    match cs with
    | ';' :: rest => some (.return_ none, rest)
    | _ =>
      match pExprF (fuel + 1) cs with
      | some (e, rest) =>
        match skipWs rest with
        | ';' :: final => some (.return_ (some e), final)
        | _ => none
      | none => none
  pIfF (fuel : Nat) (cs : List Char) :
      Option (MicroCStmt × List Char) :=
    match skipWs cs with
    | '(' :: rest =>
      match pExprF (fuel + 1) (skipWs rest) with
      | some (cond, rest') =>
        match skipWs rest' with
        | ')' :: rest'' =>
          match skipWs rest'' with
          | '{' :: rest''' =>
            match parseStmtSeq (pStmtF fuel) fuel (skipWs rest''') with
            | some (thenB, rest4) =>
              match skipWs rest4 with
              | '}' :: rest5 =>
                match skipWs rest5 with
                | 'e' :: 'l' :: 's' :: 'e' :: rest6 =>
                  match skipWs rest6 with
                  | '{' :: rest7 =>
                    match parseStmtSeq (pStmtF fuel) fuel
                        (skipWs rest7) with
                    | some (elseB, rest8) =>
                      match skipWs rest8 with
                      | '}' :: final =>
                        some (.ite cond thenB elseB, final)
                      | _ => none
                    | none => none
                  | _ => none
                | _ => none
              | _ => none
            | none => none
          | _ => none
        | _ => none
      | none => none
    | _ => none
  pWhileF (fuel : Nat) (cs : List Char) :
      Option (MicroCStmt × List Char) :=
    match skipWs cs with
    | '(' :: rest =>
      match pExprF (fuel + 1) (skipWs rest) with
      | some (cond, rest') =>
        match skipWs rest' with
        | ')' :: rest'' =>
          match skipWs rest'' with
          | '{' :: rest''' =>
            match parseStmtSeq (pStmtF fuel) fuel (skipWs rest''') with
            | some (body, rest4) =>
              match skipWs rest4 with
              | '}' :: final => some (.while_ cond body, final)
              | _ => none
            | none => none
          | _ => none
        | _ => none
      | none => none
    | _ => none
  pAssignOrStoreF (fuel : Nat) (cs : List Char) :
      Option (MicroCStmt × List Char) :=
    match pIdent (skipWs cs) with
    | some (name, rest) =>
      let rest := skipWs rest
      match rest with
      | '[' :: rest' =>
        match pExprF (fuel + 1) (skipWs rest') with
        | some (idx, rest'') =>
          match skipWs rest'' with
          | ']' :: rest''' =>
            match skipWs rest''' with
            | '=' :: rest4 =>
              match pExprF (fuel + 1) (skipWs rest4) with
              | some (val, rest5) =>
                match skipWs rest5 with
                | ';' :: final =>
                  some (.store (.varRef name) idx val, final)
                | _ => none
              | none => none
            | _ => none
          | _ => none
        | none => none
      | '=' :: rest' =>
        pRhsF fuel name (skipWs rest')
      | _ => none
    | none => none
  pRhsF (fuel : Nat) (var : String) (cs : List Char) :
      Option (MicroCStmt × List Char) :=
    match pIdent cs with
    | some (ident, rest) =>
      let rest' := skipWs rest
      match rest' with
      | '[' :: rest'' =>
        match pExprF (fuel + 1) (skipWs rest'') with
        | some (idx, rest''') =>
          match skipWs rest''' with
          | ']' :: rest4 =>
            match skipWs rest4 with
            | ';' :: final =>
              some (.load var (.varRef ident) idx, final)
            | _ => none
          | _ => none
        | none => none
      | '(' :: rest'' =>
        match pArgsF (fuel + 1) (skipWs rest'') with
        | some (args, rest''') =>
          match skipWs rest''' with
          | ')' :: rest4 =>
            match skipWs rest4 with
            | ';' :: final => some (.call var ident args, final)
            | _ => none
          | _ => none
        | none => none
      | ';' :: final =>
        some (.assign var (.varRef ident), final)
      | _ => none
    | none =>
      match pExprF (fuel + 1) cs with
      | some (e, rest) =>
        match skipWs rest with
        | ';' :: final => some (.assign var e, final)
        | _ => none
      | none => none
  pArgsF (fuel : Nat) (cs : List Char) :
      Option (List MicroCExpr × List Char) :=
    let cs := skipWs cs
    match cs with
    | ')' :: _ => some ([], cs)
    | _ =>
      match pExprF fuel cs with
      | some (first, rest) => goArgs fuel [first] rest
      | none => none
  goArgs (fuel : Nat) (acc : List MicroCExpr) (cs : List Char) :
      Option (List MicroCExpr × List Char) :=
    let cs := skipWs cs
    match fuel with
    | 0 => some (acc, cs)
    | n + 1 =>
      match cs with
      | ',' :: rest =>
        match pExprF (n + 1) (skipWs rest) with
        | some (e, rest') => goArgs n (acc ++ [e]) rest'
        | none => none
      | _ => some (acc, cs)

/-! ## Top-Level Parse Functions -/

def parseMicroCExpr (s : String) : Option MicroCExpr :=
  let cs := s.toList
  match pExprF (cs.length + 1) cs with
  | some (e, rest) => if skipWs rest == [] then some e else none
  | none => none

def parseMicroC (s : String) : Option MicroCStmt :=
  let cs := s.toList
  let fuel := cs.length + 1
  match pStmtF fuel cs with
  | some (stmt, rest) =>
    let rest' := skipWs rest
    if rest' == [] then some stmt
    else
      match parseStmtSeq (pStmtF fuel) fuel rest' with
      | some (more, final) =>
        if skipWs final == [] then some (.seq stmt more) else none
      | none => none
  | none => none

end TrustLean
