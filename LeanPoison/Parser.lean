import LeanPoison.Syntax
import Lean.Data.Xml.Basic
import Lean.Data.Xml.Parser
open Lean Xml
open System


-------------Helpers for XML To Expr-------------------------------------------
partial def flattenTypeExpr (fuel:Nat ) (content : Array Content) : Except String Typ := do

      -- Possible cases for contents Array ( Should have one Top Level Element only)
      -- i) Just a Base Type (int,bool..) ,
      -- ii ) Paren Type ( TypeExp ),
      -- iii ) Arrow Type tye1 -> tye2 ,
      --iv) Ref Type
      -- v ) TypeExp
   let contents := content.filterMap fun
    | Content.Element (Element.Element "base_type" attr #[Content.Character name]) => some (Content.Element (Element.Element "base_type" attr #[Content.Character name]))
    | Content.Element (Element.Element "type_expr" attr conts) => some (Content.Element (Element.Element "type_expr" attr conts))
    | Content.Element (Element.Element "arrow_type" attr conts) => some (Content.Element (Element.Element "arrow_type" attr conts))
    | Content.Element (Element.Element "ref_type" attr conts) => some (Content.Element (Element.Element "ref_type" attr conts))
    | Content.Element (Element.Element "paren_type" attr contents) => some (Content.Element (Element.Element "paren_type" attr contents))
    | _ => none

    match contents with
    -- Embedded only Base Types - int , bool , unit
    | #[Content.Element (Element.Element "base_type" _ #[Content.Character name])] =>
          let typ <- strToBasicType (name.trim)
          return typ

    -- Type expression embedded in  ()
    | #[Content.Element (Element.Element "paren_type" _ contents)] => do
         return (<- flattenTypeExpr (fuel - 1) contents)

     -- Arrow Type (tye1 -> tye2)
    | #[Content.Element (Element.Element "arrow_type" _ contents)] => do
         let contentsFiltered := contents.filterMap fun
          | Content.Element (Element.Element "type_expr" a b) => some (Content.Element (Element.Element "type_expr" a b))
          | _ => none

          match contentsFiltered with
          | #[Content.Element (Element.Element "type_expr" _ tyeExpFrom) , Content.Element (Element.Element "type_expr" _ tyeExpTo)]
            =>  let fromType <- flattenTypeExpr (fuel-1) tyeExpFrom
                let toType <- flattenTypeExpr (fuel-2) tyeExpTo
                return Typ.arrow fromType toType
          | _ => .error "Invalid arrow type expression"

      --Ref Types (ref tye)
    | #[Content.Element (Element.Element "ref_type" _ contents)] => do
         let contentsFiltered := contents.filterMap fun
          | Content.Element (Element.Element "type_expr" a b) => some (Content.Element (Element.Element "type_expr" a b))
          | _ => none
         return Typ.ref (<- flattenTypeExpr (fuel-1) contentsFiltered)

    | #[Content.Element (Element.Element "type_expr" _ contents)] => do
       return (<- flattenTypeExpr (fuel - 1) contents)

    | _ => .error s!"Invalid type_expr shape: {contents}"

--------------------------------------------------------------------------------
-- Helper Wrapper function to parse a Type Expression into a Type

def parseTypeExpr (typeExpElements : Array Content ) : Except String Typ := do
  let TypExp := flattenTypeExpr 1000 typeExpElements
  match TypExp with
   | .ok typeExpression => .ok typeExpression
   | .error e => .error e

------------------ XML TO Expr Functions---------------------------------------

-- Run the tree-sitter parser with `-x`
def runTreeSitterXml (file : String) : IO String := do
  let cwd ← IO.currentDir
  let configPath := cwd / "config.json"
  let cmd := "tree-sitter"
  let args := #["parse", "-x", file, "--config-path", toString configPath]
  let output ← IO.Process.output {
    cmd := cmd,
    args := args,
    stderr := .piped,
    stdout := .piped
  }
  if output.exitCode ≠ 0 then
    throw <| IO.userError s!"Parsing failed: {output.stderr}"
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
        match nStr.trim.toInt? with
        | some n => .ok (Expr.num n)
        | none => .error s!"Invalid number: {nStr}"

    | [Element.Element "string" _ #[Content.Character str]] =>
       .ok (Expr.str str )


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
    let validOps := ["+", "-", "*", "/", ">", ">=", "<", "<=", "=="]
    let ops := contents.filterMap fun
      | Content.Character s =>
          let trimmed := s.trim
          if trimmed ∈ validOps then some trimmed else none
      | _ => none

    match (exprs.toList, ops.toList) with
      | ([lhs,
         rhs],
        [opStr]) =>
          let lhsExpr ← xmlToExpr lhs
          let rhsExpr ← xmlToExpr rhs
          match opStr with
          | "+" => return Expr.op lhsExpr Op.add rhsExpr
          | "-" => return Expr.op lhsExpr Op.sub rhsExpr
          | "*" => return Expr.op lhsExpr Op.mul rhsExpr
          | "/" => return Expr.op lhsExpr Op.div rhsExpr
          | ">" => return Expr.op lhsExpr Op.gt rhsExpr
          | ">=" => return Expr.op lhsExpr Op.gte rhsExpr
          | "<" => return Expr.op lhsExpr Op.lt rhsExpr
          | "<=" => return Expr.op lhsExpr Op.lte rhsExpr
          | "==" => return Expr.op lhsExpr Op.eq rhsExpr
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
    | Content.Element (Element.Element "comment" _ _) => none  -- skip comments
    | Content.Element el => some el
    | _ => none


    match elems.toList with
    | [Element.Element "identifier" _ #[(Content.Character paramName)],
      Element.Element "type_expr" _ argTypeContent,
      Element.Element "expr" attr bodyContent,
      Element.Element "type_expr" _ retTypeContent] => do

    let argTypeFiltered := argTypeContent.filterMap (fun
    | Content.Element (Element.Element "comment" _ _) => none  -- skip comments

    | Content.Element e => some (Content.Element e)
    | _ => none)


    let returnTypeFiltered := retTypeContent.filterMap (fun
    | Content.Element (Element.Element "comment" _ _) => none  -- skip comments

    | Content.Element e => some (Content.Element e)
    | _ => none)

      let argType ← parseTypeExpr  argTypeFiltered
      let body ← xmlToExpr (Element.Element "expr" attr bodyContent)
      let returnType ← parseTypeExpr returnTypeFiltered

      return (Expr.fn paramName argType body returnType)


    | _ => .error s!"Invalid fn_expr structure: {contents}"

  | Element.Element "pfn_expr" _ contents => do
   let elems := contents.filterMap fun
    | Content.Element (Element.Element "comment" _ _) => none  -- skip comments
    | Content.Element el => some el
    | _ => none


    match elems.toList with
    | [Element.Element "identifier" _ #[(Content.Character paramName)],
      Element.Element "type_expr" _ argTypeContent,
      Element.Element "expr" attr bodyContent,
      Element.Element "type_expr" _ retTypeContent] => do

    let argTypeFiltered := argTypeContent.filterMap (fun
    | Content.Element (Element.Element "comment" _ _) => none  -- skip comments

    | Content.Element e => some (Content.Element e)
    | _ => none)

    let returnTypeFiltered := retTypeContent.filterMap (fun
    | Content.Element (Element.Element "comment" _ _) => none  -- skip comments

    | Content.Element e => some (Content.Element e)
    | _ => none)

      let argType ← parseTypeExpr  argTypeFiltered
      let body ← xmlToExpr (Element.Element "expr" attr bodyContent)
      let returnType ← parseTypeExpr returnTypeFiltered

      return (Expr.pfn paramName argType body returnType)


    | _ => .error s!"Invalid pfn_expr structure: {contents}"

  | Element.Element "rand_expr" _ contents => do
   let elems := contents.filterMap fun
    | Content.Element (Element.Element "comment" _ _) => none  -- skip comments
    | Content.Element el => some el
    | _ => none


    match elems.toList with
    | [e1] => return Expr.builtIn (builtInExpr.rand (<- xmlToExpr e1))
    | _ => .error "Invalid argument to rand"

  | Element.Element "frand_expr" _ contents => do
   let elems := contents.filterMap fun
    | Content.Element (Element.Element "comment" _ _) => none  -- skip comments
    | Content.Element el => some el
    | _ => none


    match elems.toList with
    | [e1] => return Expr.builtIn (builtInExpr.frand (<- xmlToExpr e1))
    | _ => .error "Invalid argument to frand"

  | Element.Element "printStr_expr" _ contents => do
   let elems := contents.filterMap fun
    | Content.Element (Element.Element "comment" _ _) => none  -- skip comments
    | Content.Element el => some el
    | _ => none


    match elems.toList with
    | [e1] => return Expr.builtIn (builtInExpr.printString (<- xmlToExpr e1))
    | _ => .error "Invalid argument to frand"

  | Element.Element "printInt_expr" _ contents => do
   let elems := contents.filterMap fun
    | Content.Element (Element.Element "comment" _ _) => none  -- skip comments
    | Content.Element el => some el
    | _ => none


    match elems.toList with
    | [e1] => return Expr.builtIn (builtInExpr.printInt (<- xmlToExpr e1))
    | _ => .error "Invalid argument to frand"

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

--------------------------------------------------------------------------------
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

--------------------------------------------------------------------------------
