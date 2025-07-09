import LeanPoison.Syntax
import Std.Internal.Parsec

open Std.Internal.Parsec Std.Internal.Parsec.String
open Alternative

-- Whitespace parser
def whitespace : Parser Unit := do
  let _ ← many (satisfy Char.isWhitespace)
  return ()

-- Parse a specific string followed by whitespace
def token (s : String) : Parser Unit := do
  let _ ← pstring s
  whitespace

-- Parse an identifier
def identifier : Parser String := do
  let first ← satisfy Char.isAlpha
  let rest ← manyChars (satisfy (fun c => c.isAlphanum || c == '_'))
  return first.toString ++ rest

-- Parse a natural number (no negative numbers)
def naturalNumber : Parser Nat := do
  let digits ← many1Chars (satisfy Char.isDigit)
  match digits.toNat? with
  | some n => return n
  | none => fail "Invalid natural number"

-- Parse expressions with proper precedence
mutual
  -- Parse atomic expressions (highest precedence)
  partial def parseAtom : Parser Expr := do
    whitespace
    (naturalNumber >>= fun n => return (Expr.num n)) <|>
    (token "true" *> return (Expr.bool true)) <|>
    (token "false" *> return (Expr.bool false)) <|>
    (token "unit" *> return Expr.unit) <|>
    (identifier >>= fun x => return Expr.var x)

  -- Parse application (left associative)
  partial def parseApp : Parser Expr := do
    let first ← parseExpr
    let arg ← parseExpr
    return Expr.app first arg

  -- Parse arithmetic operations (left associative)
  partial def parseArith : Parser Expr := do
    let left ← parseExpr
    let op ← (token "+" *> return Op.add) <|> (token ">=" *> return Op.gte)
    let right ← parseExpr
    return Expr.op left op right

  -- Parse assignments (right associative)
  partial def parseAssign : Parser Expr := do
    let left ← parseExpr
    token ":="
    let right ← parseExpr
    return Expr.assign left right

  -- Parse conditionals
  partial def parseConditional : Parser Expr := do
    token "if"
    let cond ← parseExpr
    token "then"
    let thenExpr ← parseExpr  -- Parse then/else at top level
    token "else"
    let elseExpr ← parseExpr
    return Expr.ite cond thenExpr elseExpr


  partial def parseLet : Parser Expr := do
    token "let"
    let x ← identifier
    token "="
    let e1 ← parseExpr
    token "in"
    let e2 ← parseExpr
    return Expr.let x e1 e2

  -- Parse sequences (right associative, lowest precedence)
  partial def parseSeq : Parser Expr := do
    let e1 ← parseExpr
    token ";"
    let e2 ← parseExpr
    return Expr.seq e1 e2

  -- Parse ref creation
  partial def parseRef : Parser Expr := do
    token "ref"
    let e ← parseExpr
    return Expr.newRef e

  -- Parse dereference
  partial def parseDeref : Parser Expr := do
    token "!"
    let e ← parseExpr
    return Expr.deref e

  -- Parse while loops
  partial def parseWhile : Parser Expr := do
    token "while"
    let cond ← parseExpr
    token "do"
    let body ← parseExpr
    return Expr.while cond body

  -- Parse function abstractions
  partial def parseFn : Parser Expr := do
    token "fn"
    let x ← identifier
    token "=>"
    let body ← parseExpr
    return Expr.fn x body

  -- Parse pure function abstractions
  partial def parsePfn : Parser Expr := do
    token "pfn"
    let x ← identifier
    token "=>"
    let body ← parseExpr
    return Expr.pfn x body

  -- Main expression parser (lowest precedence)
  partial def parseExpr : Parser Expr :=
  parseRef <|>
  parseDeref <|>
  parseWhile <|>
  parseFn <|>
  parsePfn <|>
  parseAtom <|>
  parseApp <|>
  parseArith <|>
  parseAssign <|>
  parseConditional <|>
  parseLet <|>
  parseSeq

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
