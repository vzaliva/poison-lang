--import System.FilePath
--import System.IO.Process
--import System.IO
import LeanPoison.Syntax
import Std.Internal.Parsec
import Lean.Data.Xml.Basic
import Lean.Data.Xml.Parser


open Std.Internal.Parsec Std.Internal.Parsec.String
open Alternative

-- Whitespace parser
def whitespace : Parser Unit := do
  dbg_trace "Parsing whitespace"
  let _ ← many (satisfy Char.isWhitespace)
  return ()

-- Parse a specific string followed by whitespace
def token (s : String) : Parser Unit := do
  whitespace
  let _ ← pstring s
  dbg_trace ("Parsed " ++ s)
  whitespace

-- Parse an identifier
def identifier : Parser String := do
  let first ← satisfy Char.isAlpha
  let rest ← manyChars (satisfy (fun c => c.isAlphanum || c == '_'))
  dbg_trace "Parsing identifier"
  return first.toString ++ rest

-- Parse a natural number (no negative numbers)
def naturalNumber : Parser Nat := do
  dbg_trace "Parsing Nat"
  let digits ← many1Chars (satisfy Char.isDigit)
  match digits.toNat? with
  | some n => return n
  | none => fail "Invalid natural number"

-- Parse expressions with proper precedence
mutual
  -- Parse atomic expressions (highest precedence)
  partial def parseAtom : Parser Expr := do
    dbg_trace "Parse atom called"
    whitespace
    (naturalNumber >>= fun n => return (Expr.num n)) <|>
    (token "true" *> return (Expr.bool true)) <|>
    (token "false" *> return (Expr.bool false)) <|>
    (token "unit" *> return Expr.unit) <|>
    (identifier >>= fun x => return Expr.var x)

  -- Parse application (left associative)
  partial def parseApp : Parser Expr := do
    dbg_trace "Parse app called"
    let first ← parseExpr
    let arg ← parseExpr
    return Expr.app first arg

  -- Parse arithmetic operations (left associative)
  --partial def parseArith : Parser Expr := attempt do
   -- dbg_trace "Parse Arith called"
   -- let lhs ← attempt parseAtom
    --let op ← attempt (token "+" *> return Op.add) <|> attempt (token ">=" *> return Op.gte)
   -- let rhs ← attempt parseArith <|> attempt parseAtom
   -- return (Expr.op lhs op rhs)

partial def parseArith : Parser Expr := attempt do
  let lhs ← parseAtom
  let op ← attempt (token "+" *> return Op.add) <|> attempt (token ">=" *> return Op.gte)
  let rhs ← attempt parseArith <|> attempt parseAtom
  parseArithRest (Expr.op lhs op rhs)

partial def parseArithRest (lhs : Expr) : Parser Expr := do
  let maybeOp ← optional <| attempt (
    (token "+" *> pure Op.add) <|>
    (token ">=" *> pure Op.gte)
  )
  match maybeOp with
  | some op =>
    let rhs ←  attempt parseAtom
    parseArithRest (Expr.op lhs op rhs)
  | none =>
    return lhs




  -- Parse assignments (right associative)
  partial def parseAssign : Parser Expr := do
    dbg_trace "Parse assign called"
    let left ← parseExpr
    token ":="
    let right ← parseExpr
    return Expr.assign left right

  -- Parse conditionals
  partial def parseConditional : Parser Expr := do
    dbg_trace "parse conditional called"
    token "if"
    let cond ← parseExpr
    token "then"
    let thenExpr ← parseExpr  -- Parse then/else at top level
    token "else"
    let elseExpr ← parseExpr
    return Expr.ite cond thenExpr elseExpr


  partial def parseLet : Parser Expr := do
    dbg_trace "Parse let called"
    token "let"
    let x ← identifier
    token "="
    let e1 ← parseExpr
    token "in"
    let e2 ← parseExpr
    return Expr.let x e1 e2

  -- Parse sequences (right associative, lowest precedence)
  partial def parseSeq : Parser Expr := do
    dbg_trace "Parse seq called"
    let e1 ← parseArith <|> parseAtom
    token ";"
    let e2 ← parseExpr
    return Expr.seq e1 e2

  -- Parse ref creation
  partial def parseRef : Parser Expr := do
    dbg_trace "Parse ref called"
    token "ref"
    let e ← parseExpr
    return Expr.newRef e

  -- Parse dereference
  partial def parseDeref : Parser Expr := do
    dbg_trace "Parse deref called"
    token "!"
    let e ← parseExpr
    return Expr.deref e

  -- Parse while loops
  partial def parseWhile : Parser Expr := do
    dbg_trace "Parse while called"
    token "while"
    let cond ← parseExpr
    token "do"
    let body ← parseExpr
    return Expr.while cond body

  -- Parse function abstractions
  partial def parseFn : Parser Expr := do
    dbg_trace "Parse func called"
    token "fn"
    let x ← identifier
    token "=>"
    let body ← parseExpr
    return Expr.fn x body

  -- Parse pure function abstractions
  partial def parsePfn : Parser Expr := do
    dbg_trace "parse pure func called"
    token "pfn"
    let x ← identifier
    token "=>"
    let body ← parseExpr
    return Expr.pfn x body

  -- Main expression parser (lowest precedence)
  partial def parseExpr : Parser Expr :=
    attempt parseSeq <|>
    attempt parseArith <|>
  --parseRef <|>
  --parseDeref <|>
  --parseWhile <|>
  --parseFn <|>
  --parsePfn <|>
  --parseLet <|>
  --parseAssign <|>
    parseAtom <|>
  --parseApp <|>

  --parseConditional <|>
  fail "parseExpr: no parser matched"

end

-- Parse a complete program
def parseProgram : Parser Expr := do
  whitespace
  let expr ← parseExpr
  whitespace
  eof
  return expr

-- Helper function to parse from string
def parseString (input : String) : Except String Expr :=
  match parseProgram.run input with
  | .ok expr => .ok expr
  | .error err => .error s!"Parse error: {err}"


------------------ XML TO Expr Functions---------------------------------------
open Lean Xml
open System

-- Run the tree-sitter parser with `-x`
def runTreeSitterXml (file : String) : IO String := do
  let cmd := "tree-sitter"
  let args := #["parse", file,"-x"]
  let output ← IO.Process.output {
    cmd := cmd,
    args := args,
    stderr := .piped,
    stdout := .piped
  }
  if output.exitCode ≠ 0 then
    throw <| IO.userError s!"Tree-sitter failed: {output.stderr}"
  return output.stdout
open Lean Xml

-- Recursively convert parsed XML to Expr

partial def xmlToExpr (x : Element) : Except String Expr :=
    match x with
  | Element.Element "expr" _ contents =>
     let elements := contents.filterMap fun
      | Content.Element el =>
        match el with
        | Element.Element "comment" _ _ => none  -- discard comment elements
        | _ => some el
      | _ => none
      match elements.toList with
      | [e] => xmlToExpr e
      | _ => .error s!"Invalid expr contents: {contents}"

  | Element.Element "identifier" _ #[Content.Character name] =>
      .ok (Expr.var name)

  | Element.Element "atom" _ contents =>
  let elems := contents.filterMap fun
    | Content.Element (Element.Element "comment" _ _) => none  -- discard comment elements
    | Content.Element el => some el

    | _ => none

  match elems.toList with
    | [Element.Element "number" _ #[Content.Character nStr]] =>
        match nStr.trim.toNat? with
        | some n => .ok (Expr.num n)
        | none => .error s!"Invalid number: {nStr}"

    | _ =>
      -- fallback: check for literal booleans or unit
      match contents.find? (fun
        | Content.Character _ => true
        | _ => false
      ) with
      | some (Content.Character s) =>
          match s.trim with
          | "true" => .ok (Expr.bool true)
          | "false" => .ok (Expr.bool false)
          | "unit" => .ok Expr.unit
          | unknown => .error s!"Unknown atom literal: {unknown}"
      | _ => .error s!"Empty atom"

  | Element.Element "binary_expr" _ contents => do
    let exprs := contents.filterMap fun

      | Content.Element (Element.Element "comment" _ _) => none  -- discard comment elements
      | Content.Element el => some el
      | _ => none
    let validOps := ["+", "-", "*", "\\", ">", ">=", "<", "<=", "=="]
    let ops := contents.filterMap fun
      | Content.Character s =>
          let trimmed := s.trim
          if trimmed ∈ validOps then some trimmed else none
      | _ => none

    --dbg_trace (exprs.toList, ops.toList)
    match (exprs.toList, ops.toList) with
      | ([lhs,
         rhs],
        [opStr]) =>
          let lhsExpr ← xmlToExpr lhs
          let rhsExpr ← xmlToExpr rhs
          match opStr with
          | "+" => return Expr.op lhsExpr Op.add rhsExpr
        --  | "-" => return Expr.op lhsExpr Op.sub rhsExpr
         -- | "*" => return Expr.op lhsExpr Op.mul rhsExpr
         -- | "\\" => return Expr.op lhsExpr Op.div rhsExpr
         -- | ">" => return Expr.op lhsExpr Op.gt rhsExpr
          | ">=" => return Expr.op lhsExpr Op.gte rhsExpr
         -- | "<" => return Expr.op lhsExpr Op.lt rhsExpr
         -- | "<=" => return Expr.op lhsExpr Op.lte rhsExpr
         -- | "==" => return Expr.op lhsExpr Op.eq rhsExpr
          | _ => .error s!"Unknown operator: {opStr}"
      | _ => .error s!"Invalid binary_expr structure: {contents}"

  | Element.Element "app_expr" _ contents =>
    do
     let exps := contents.filterMap (fun
        | Content.Element (Element.Element "comment" _ _) => none  -- discard comment elements
        | Content.Element el => some el
        | _ => none
      )
      match exps.toList with
      | [e1,e2] => return Expr.app (<- xmlToExpr e1) (<- xmlToExpr e2)
      | _ => .error s!"Invalid Apply expr contents: {contents}"



  | Element.Element "seq_expr" _ contents => do
    let elems := contents.filterMap fun
      | Content.Element (Element.Element "comment" _ _) => none  -- discard comment elements
      | Content.Element el => some el
      | _ => none
    let a:= elems.toList
    --dbg_trace a.length
    match elems.toList with
    | [leftEl, rightEl] =>
        return Expr.seq (← xmlToExpr leftEl) (← xmlToExpr rightEl)
    | _ =>
        .error s!"Invalid seq_expr structure: {contents}"


  | Element.Element "if_expr" _ contents => do
  let elems := contents.filterMap fun
    | Content.Element (Element.Element "comment" _ _) => none  -- discard comment elements
    | Content.Element el => some el
    | _ => none
    match elems.toList with
    | [if_cond_expr,
      then_expr,
      else_expr] =>
        return Expr.ite (← xmlToExpr if_cond_expr) (← xmlToExpr then_expr) (← xmlToExpr else_expr)
    | _ => .error s!"Invalid if_expr structure: {contents}"

  | Element.Element "let_expr" _ contents => do
    let elems := contents.filterMap fun
      | Content.Element (Element.Element "comment" _ _) => none  -- discard comment elements
      | Content.Element el => some el
      | _ => none

    match elems.toList with
    | [ Element.Element "identifier" _ #[Content.Character name],
        v,
        b ] =>
          return Expr.let name (← xmlToExpr v) (← xmlToExpr b)
    | _ => .error s!"Invalid let_expr structure: {contents}"

  | Element.Element "assign_expr" _ contents => do
    let elems := contents.filterMap fun
      | Content.Element (Element.Element "comment" _ _) => none  -- discard comment elements
      | Content.Element el => some el
      | _ => none

    match elems.toList with
    | [e1,e2] =>
        let lhs <- xmlToExpr e1
        let rhs ← xmlToExpr e2
        return Expr.assign lhs rhs
    | _ =>
        .error s!"Invalid assign_expr structure: {contents}"

  | Element.Element "ref_expr" _ contents =>
        let elems := contents.filterMap fun
      | Content.Element (Element.Element "comment" _ _) => none  -- discard comment elements
      | Content.Element el => some el
      | _ => none

    match elems.toList with
    | [element] =>
          return Expr.newRef (<- xmlToExpr element)
    | _ => .error s!"Invalid ref_expr structure: {contents}"

  | Element.Element "deref_expr" _ contents =>
          let elems := contents.filterMap fun
        | Content.Element (Element.Element "comment" _ _) => none  -- discard comment elements
        | Content.Element el => some el
        | _ => none

      match elems.toList with
      | [element] =>
            return Expr.deref (<- xmlToExpr element)
      | _ => .error s!"Invalid deref_expr structure: {contents}"

  | Element.Element "while_expr" _ contents => do
       let elems := contents.filterMap fun
        | Content.Element (Element.Element "comment" _ _) => none  -- discard comment elements
        | Content.Element el => some el
        | _ => none

        match elems.toList with
        | [condition,body] =>
              return Expr.while (<- xmlToExpr condition) (<- xmlToExpr body)
        | _ => .error s!"Invalid while_expr structure: {contents}"

  | Element.Element "fn_expr" _ contents => do
    let elems := contents.filterMap fun
      | Content.Element (Element.Element "comment" _ _) => none  -- discard comment elements
      | Content.Element el => some el
      | _ => none
    --dbg_trace elems.toList
    match elems.toList with
    | [Element.Element "identifier" _ #[Content.Character p],
      body] =>
        return Expr.fn p (← xmlToExpr body)
    | _ => .error s!"Invalid fn_expr structure: {contents}"

  | Element.Element "pfn_expr" _ contents => do
    let elems := contents.filterMap fun
      | Content.Element (Element.Element "comment" _ _) => none  -- discard comment elements
      | Content.Element el => some el
      | _ => none
      match elems.toList with
      | [Element.Element "identifier" _ #[Content.Character p],
        body] =>
          return Expr.pfn p (← xmlToExpr body)
      | _ => .error s!"Invalid pfn_expr structure: {contents}"

  | Element.Element "group_expr" _ contents => do
    let elements := contents.filterMap (fun
          | Content.Element (Element.Element "comment" _ _) => none  -- discard comment elements
          | Content.Element el => some el
          | _ => none
        )
        match elements.toList with
        | [e] => xmlToExpr e
        | _ => .error s!"Invalid parantheses expr contents: {contents}"

  | Element.Element "source_file" _ children => do
      let elements := children.filterMap fun
      | Content.Element el =>
        match el with
        | Element.Element "comment" _ _ => none  -- discard comment elements
        | _ => some el
      | _ => none

        match elements with
        | #[exprEl] => xmlToExpr exprEl
        | #[]       => .error "Empty source file"
        | _         => .error "Expected exactly one top-level <expr> in <source_file>"

  | _ => .error s!"Unrecognized XML element: {x}"

-- Final wrapper
def parsePoisonFile (file : String) : IO Expr := do
  let xmlStr ← runTreeSitterXml file
  match parse xmlStr with
  | .ok xml =>
      match xmlToExpr xml with
      | .ok expr => return expr
      | .error e => throw <| IO.userError s!"XML to Expr error: {e}"
  | .error err =>
      throw <| IO.userError s!"Failed to parse XML: {err}"

def myFilePath := "/home/jayc/poison-lang/parser/example.poison"

--#eval parseString " fn x => 5 "
--#eval parseString " true "
--#eval parseString " false "
--#eval parseString " 5 "
--#eval parseString " 5 ; 6"
--#eval parseString " 5 ; 6 ; 7"
--#eval parseString " 6 + 10 "
--#eval parseString " 6 >= 10 "
--aAa**#eval parseString " 6 + 10 >= 10 + 2 "
#eval (parsePoisonFile myFilePath)

--#eval " let x = 3 in x"
--#eval parseString " ref 100 "
--#eval parseString " a := 100
