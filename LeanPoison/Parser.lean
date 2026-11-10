import LeanPoison.Syntax
import LeanPoison.Xml.Basic
import LeanPoison.Xml.Parser
open Lean.Xml

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
    -- Embedded only Base Types - int , bool , unit , string
    | #[Content.Element (Element.Element "base_type" _ #[Content.Character name])] =>
          let typ <- strToBasicType (name.trimAscii.toString)
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

private def parseTypeExpr (typeExpElements : Array Content ) : Except String Typ := do
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

/-- Find the first child element with the given tag (used to locate the optional
    `effects_block` / `captures_block` sibling clauses among an extern's
    trailing children, independent of their relative order). -/
private def findExternBlock (tag : String) (els : List Element) : Option Element :=
  els.find? fun | Element.Element t _ _ => t == tag

mutual
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
          match nStr.trimAscii.toString.toInt? with
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
            match s.trimAscii.toString with
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
      let validOps := ["+", "-", "*", "/", ">", ">=", "<", "<=", "==","&","!="]
      let ops := contents.filterMap fun
        | Content.Character s =>
            let trimmed := s.trimAscii.toString
            if trimmed ∈ validOps then some trimmed else none
        | _ => none


      match (exprs.toList, ops.toList) with
        | ([lhs,
          rhs],
          [opStr]) =>
            let lhsExpr ← xmlToExpr lhs
            let rhsExpr ← xmlToExpr rhs
            match opStr with
            | "+"  => return Expr.op lhsExpr Op.add rhsExpr
            | "-"  => return Expr.op lhsExpr Op.sub rhsExpr
            | "*"  => return Expr.op lhsExpr Op.mul rhsExpr
            | "/"  => return Expr.op lhsExpr Op.div rhsExpr
            | ">"  => return Expr.op lhsExpr Op.gt rhsExpr
            | ">=" => return Expr.op lhsExpr Op.gte rhsExpr
            | "<"  => return Expr.op lhsExpr Op.lt rhsExpr
            | "<=" => return Expr.op lhsExpr Op.lte rhsExpr
            | "==" => return Expr.op lhsExpr Op.eq rhsExpr
            | "&"  => return Expr.op lhsExpr Op.bitand rhsExpr
            | "!=" => return Expr.op lhsExpr Op.neq rhsExpr
            | _ => .error s!"Unknown operator: {opStr}"
        | _ => .error s!"Invalid binary_expr structure: {contents}"

    | Element.Element "boolean_expr" _ contents => do
      let exprs := contents.filterMap fun

        | Content.Element (Element.Element "comment" _ _) => none  -- discard comment elements
        | Content.Element el => some el
        | _ => none
      let validOps := ["||","&&"]
      let ops := contents.filterMap fun
        | Content.Character s =>
            let trimmed := s.trimAscii.toString
            if trimmed ∈ validOps then some trimmed else none
        | _ => none


      match (exprs.toList, ops.toList) with
        | ([lhs,
          rhs],
          [opStr]) =>
            let lhsExpr ← xmlToExpr lhs
            let rhsExpr ← xmlToExpr rhs
            match opStr with
            | "||"  => return Expr.op lhsExpr Op.or rhsExpr
            | "&&" => return Expr.op lhsExpr Op.and rhsExpr
            | _ => .error s!"Unknown operator: {opStr}"
        | _ => .error s!"Invalid boolean_expr structure: {contents}"

    | Element.Element "unary_expr" _ contents => do
      let elems := contents.filterMap fun
        | Content.Element (Element.Element "comment" _ _) => none  -- discard comment elements
        | Content.Element el => some el
        | _ => none
      let validOps := ["not"]
      let ops := contents.filterMap fun
        | Content.Character s =>
            let trimmed := s.trimAscii.toString
            if trimmed ∈ validOps then some trimmed else none
        | _ => none
      match (elems.toList,ops.toList) with
      | ([expr],[opStr]) =>
          let expr_arg ← xmlToExpr expr
          match opStr with
          | "not" => return Expr.unaryop UnaryOp.not expr_arg
          | _ => .error s!"Unknown unary operator: {opStr}"
      | _ => .error s!"Invalid Unary expression structure: {contents}"

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
            return Expr.vlet name (← xmlToExpr v) (← xmlToExpr b)
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

    | Element.Element "group_expr" _ contents => do
      let elements := contents.filterMap (fun
            | Content.Element (Element.Element "comment" _ _) => none  -- discard comment elements
            | Content.Element el => some el
            | _ => none
          )
          match elements.toList with
          | [e] => xmlToExpr e
          | _ => .error s!"Invalid parantheses expr contents: {contents}"

    | Element.Element "extern_expr" _ contents => do
        let elems := contents.filterMap fun
        | Content.Element (Element.Element "comment" _ _) => none  -- skip comments
        | Content.Element el => some el
        | _ => none

          match elems.toList with
          | [Element.Element "extern_val" _ externValContent] =>
            let contsFiltered := externValContent.filterMap (fun
              | Content.Element (Element.Element "comment" _ _) => none  -- skip comments
              | Content.Element e => some e
              | _ => none)
            match contsFiltered.toList with
            | [Element.Element "number" _ #[Content.Character idStr], e] =>
                match idStr.trimAscii.toString.toNat? with
                | some id =>
                    let (typ, poisonStatus, pred) ← xmlToQTyp e
                    return Expr.externVal id typ poisonStatus pred
                | none => .error s!"Invalid extern_val id: {idStr}"
            | _ => .error "Invalid extern_val content"

          | [Element.Element "extern_ref" _ externRefContent] =>
            let contsFiltered := externRefContent.filterMap (fun
              | Content.Element (Element.Element "comment" _ _) => none  -- skip comments
              | Content.Element e => some e
              | _ => none)
            match contsFiltered.toList with
            | [Element.Element "number" _ #[Content.Character idStr], eRef, eCell] =>
                match idStr.trimAscii.toString.toNat? with
                | some id =>
                    let (refTyp, refPoison, refPred) ← xmlToQTyp eRef
                    let (cellTyp, cellPoison, cellPred) ← xmlToQTyp eCell
                    if refTyp != Typ.ref Typ.int then
                      .error "extern ref: the reference type must be 'ref int' (memory stores only integers)"
                    else if cellTyp != Typ.int then
                      .error "extern ref: the points_to: cell type must be 'int' (memory stores only integers)"
                    else
                      return Expr.externRef id refPoison refPred cellPoison cellPred
                | none => .error s!"Invalid extern_ref id: {idStr}"
            | _ => .error "Invalid extern_ref content"

          | [Element.Element "extern_fn" _ externFnContent] =>
              let contsFiltered := externFnContent.filterMap (fun
              | Content.Element (Element.Element "comment" _ _) => none  -- skip comments
              | Content.Element e => some e
              | _ => none)
              match contsFiltered.toList with
                | (Element.Element "number" _ #[Content.Character idStr]) :: e_name :: e_argTyp :: e_retType :: rest =>
                    let id <-
                      match idStr.trimAscii.toString.toNat? with
                      | some n => .ok n
                      | none => .error s!"Invalid extern_fn id: {idStr}"
                    let name <-
                      match e_name with
                        | Element.Element "identifier" _ #[Content.Character n] => .ok n.trimAscii.toString
                        | _ => .error "Invalid extern_fn name"
                    let (argT, argPoison, argPred) ← xmlToQTyp e_argTyp (allowCleanPred := true)
                    let retType <- xmlToRetType e_retType
                    let effects <-
                      match findExternBlock "effects_block" rest with
                      | some eb => xmlToEffects eb
                      | none => .ok []
                    let captures <-
                      match findExternBlock "captures_block" rest with
                      | some cb => xmlToCaptures cb
                      | none => .ok []
                    return Expr.externFn id name argT argPoison argPred retType effects captures

                | _ => .error "Invalid extern_fn content"

          | [Element.Element "extern_pfn" _ externPFnContent] =>
              let contsFiltered := externPFnContent.filterMap (fun
              | Content.Element (Element.Element "comment" _ _) => none  -- skip comments
              | Content.Element e => some e
              | _ => none)

              match contsFiltered.toList with
                | (Element.Element "number" _ #[Content.Character idStr]) :: e_name :: e_argTyp :: e_retType :: rest =>
                  let id <-
                    match idStr.trimAscii.toString.toNat? with
                    | some n => .ok n
                    | none => .error s!"Invalid extern_pfn id: {idStr}"
                  let name <-
                    match e_name with
                    | Element.Element "identifier" _ #[Content.Character n] => .ok n.trimAscii.toString
                    | _ => .error "Invalid extern_pfn name"
                  let (argT, argPoison, argPred) ← xmlToQTyp e_argTyp (allowCleanPred := true)
                  let retType <- xmlToRetType e_retType
                  let captures <-
                    match findExternBlock "captures_block" rest with
                    | some cb => xmlToCaptures cb
                    | none => .ok []
                  return Expr.externPfn id name argT argPoison argPred retType captures
                | _ => .error "Invalid extern_pfn content"



          | _ => .error "Invalid extern expression"


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

    -- Recent tree-sitter releases (seen with 0.27) wrap the tree as
    -- `<sources><source name="FILE"><source_file>…`, whereas 0.25 emits
    -- `<source_file>` at the top level. Unwrap either layer.
    | Element.Element "sources" _ children
    | Element.Element "source" _ children => do
        let elements := children.filterMap fun
        | Content.Element el => some el
        | _ => none
        match elements with
        | #[inner] => xmlToExpr inner
        | _ => .error "Expected exactly one element inside the tree-sitter <sources>/<source> wrapper"

    | _ => .error s!"Unrecognized XML element: {x}"

  ------------------XML To QTyp Functions---------------------------------------

  partial def parsePExpr (pexprContents : Array Content) : Except String (String × Expr) := do
    let contents := pexprContents.filterMap fun
      | Content.Element (Element.Element "identifier" attr conts) => some (Element.Element "identifier" attr conts)
      | Content.Element (Element.Element "expr" attr conts) => some (Element.Element "expr" attr conts)
      | _ => none
    match contents.toList with
    | [(Element.Element "identifier" _ #[Content.Character name]),(Element.Element "expr" attr cont)] =>
        let varName := name.trimAscii.toString
        let expr <- xmlToExpr (Element.Element "expr" attr cont)
        return (varName, expr)

    | _ => .error s!"Invalid pexpr shape: {contents.toList}"


  partial def parsePredicate (predContents : Array Content) : Except String SyntaxPredicate := do
    let contents := predContents.filterMap fun

      | Content.Element (Element.Element "number" attr cont) =>
        some (Element.Element "number" attr cont)
      | Content.Element (Element.Element "pexpr" attr cont) =>
        some (Element.Element "pexpr" attr cont)
      | _ => none

    match contents.toList with
      | [Element.Element "number" _ #[Content.Character tag], Element.Element "pexpr" _ pexprContents] =>
          let guardNumOpt := tag.trimAscii.toString.toNat?
          match guardNumOpt with
          | some n =>
              let (name,pexpr) <- parsePExpr (pexprContents)
              return SyntaxPredicate.guardClosure ⟨n⟩ name pexpr
          | none => .error s!"Invalid guard : {tag}"
      | [Element.Element "number" _ #[Content.Character tag]] =>
          let guardNumOpt := tag.trimAscii.toString.toNat?
          match guardNumOpt with
          | some n =>
              return SyntaxPredicate.guardOnly ⟨n⟩
          | none => .error s!"Invalid guard number: {tag}"
      | [] =>
          return SyntaxPredicate.noPred
      | _ => .error s!"Invalid predicate_clause shape: {predContents}"

  /-- Parse a `qtyp` XML node into the surface triple `(Typ × Bool × SyntaxPredicate)`.
      `allowCleanPred := true` lifts the "clean types cannot have predicates"
      restriction, which is required for extern ARGUMENT conditions (a clean
      precondition may carry a guard predicate, e.g. `(int :> clean { 1, v => v >= 0 })`).
      Return/value/effect positions keep the default `false`. -/
  partial def xmlToQTyp (x : Element) (allowCleanPred : Bool := false) : Except String (Typ × Bool × SyntaxPredicate) :=
    match x with
    | Element.Element "qtyp" _ contents => do
        let elems := contents.filterMap fun
          | Content.Element (Element.Element "comment" _ _) => none  -- skip comments
          | Content.Element el => some el
          | _ => none
  --   Grammar rule: "(" , $.type_expr , ":>" , field("poison", $.poison) ,
    --    $.predicate_clause , ")"
        match elems.toList with
        | [(Element.Element "type_expr" _ typeExprConts),(Element.Element "poison" _ #[Content.Character poison]),
          (Element.Element "predicate_clause" _ predContents)] =>

            let typ <- parseTypeExpr typeExprConts
            let poisonStatus := if poison.trimAscii.toString == "poisoned" then true else false
            let pred <- parsePredicate predContents
            if poisonStatus = false && pred != SyntaxPredicate.noPred && !allowCleanPred then
              .error "Clean types cannot have predicates"
            return (typ, poisonStatus, pred)
        | _ => .error s!"Invalid qtyp shape: {contents}"
    | _ => .error s!"Invalid qtyp element: {x}"

  partial def xmlToRetType (x : Element) : Except String ExternReturn :=
    match x with
    | Element.Element "qtyp" _ _ => do
        let (typ, poison, pred) <- xmlToQTyp x
        match typ with
        | Typ.ref _ => .error "Return type of extern fn cannot be a ref type"
        | _ =>  return ExternReturn.simple typ poison pred


    | Element.Element "extern_fn" _ contents => do
        let elems := contents.filterMap fun
          | Content.Element (Element.Element "comment" _ _) => none  -- skip comments
          | Content.Element el => some el
          | _ => none

        match elems.toList with
        | (Element.Element "number" _ #[Content.Character idStr]) ::
          (Element.Element "identifier" _ #[Content.Character name]) ::
          (e_argQt@(Element.Element "qtyp" _ _)) ::
          e_retType :: rest =>
            let id <-
              match idStr.trimAscii.toString.toNat? with
              | some n => .ok n
              | none => .error s!"Invalid nested extern_fn id: {idStr}"
            let (argType, argPoison, argPred) <- xmlToQTyp e_argQt (allowCleanPred := true)
            let retType <- xmlToRetType e_retType
            let effects <-
              match findExternBlock "effects_block" rest with
              | some eb => xmlToEffects eb
              | none => .ok []
            let captures <-
              match findExternBlock "captures_block" rest with
              | some cb => xmlToCaptures cb
              | none => .ok []
            return ExternReturn.nestedFn id name.trimAscii.toString argType argPoison argPred retType effects captures

        | _ => .error s!"Invalid extern_fn shape in RetType: {elems.toList}"

    | Element.Element "extern_pfn" _ contents => do
        let elems := contents.filterMap fun
          | Content.Element (Element.Element "comment" _ _) => none  -- skip comments
          | Content.Element el => some el
          | _ => none
        match elems.toList with
        | (Element.Element "number" _ #[Content.Character idStr]) ::
          (Element.Element "identifier" _ #[Content.Character name]) ::
          (e_argQt@(Element.Element "qtyp" _ _)) ::
          e_retType :: rest =>
            let id <-
              match idStr.trimAscii.toString.toNat? with
              | some n => .ok n
              | none => .error s!"Invalid nested extern_pfn id: {idStr}"
            let (argType, argPoison, argPred) <- xmlToQTyp e_argQt (allowCleanPred := true)
            let retType <- xmlToRetType e_retType
            let captures <-
              match findExternBlock "captures_block" rest with
              | some cb => xmlToCaptures cb
              | none => .ok []
            return ExternReturn.nestedPfn id name.trimAscii.toString argType argPoison argPred retType captures
        | _ => .error s!"Invalid extern_pfn shape in RetType: {contents}"

    | _ => .error s!"Invalid RetType element: {x}"

/-inductive EffectTarget where
  | namedVar : Name → EffectTarget      -- !varname
  deriving Repr, BEq

  structure Effect where
  target : EffectTarget
  poison : Bool  -- true for "poisoned", false for "clean"
  pred : SyntaxPredicate
 -/
  partial def xmlToEffects (x : Element) : Except String (List Effect) := do
    match x with
    | Element.Element "effects_block" _ effectblock =>
      let elems := effectblock.filterMap fun
        | Content.Element (Element.Element "comment" _ _) => none
        | Content.Element (Element.Element "effect" attr cont) => some (Element.Element "effect" attr cont)
        | _ => none
      -- filter only non-comment elements



      let mut acc : List Effect := []
      for el in elems do

        match el with
        | Element.Element "effect" _ effectContents =>
          let effectElems := effectContents.filterMap fun
            | Content.Element (Element.Element "comment" _ _) => none
            | Content.Element e => some e
            | _ => none

          match effectElems.toList with

          | [Element.Element "identifier" _ #[Content.Character name],
            Element.Element "qtyp" attr qtypContents] =>

            match xmlToQTyp (Element.Element "qtyp" attr qtypContents) with
            | .ok (_,poison,pred) => acc := acc.append [Effect.mk (EffectTarget.namedVar name.trimAscii.toString) poison pred]
            | .error e => throw e

          | _ => throw "Invalid effect"
        | _ => throw "Invalid effect"
      return acc
    | _ => throw s!"Invalid effects_block element: {x}"

  -- Convert a `<captures_block>` element to `List Capture`.  A capture target is
  -- either a bare environment variable (`<identifier field="env_name">` →
  -- `CaptureTarget.bareVar`) or a bang memory target (`<identifier
  -- field="mem_name">` → `CaptureTarget.memVar`); the trailing `<qtyp>` carries
  -- the qualified-type contract `(typ :> poison pred)`.
  partial def xmlToCaptures (x : Element) : Except String (List Capture) := do
    match x with
    | Element.Element "captures_block" _ captureblock =>
      let elems := captureblock.filterMap fun
        | Content.Element (Element.Element "comment" _ _) => none
        | Content.Element (Element.Element "capture" attr cont) => some (Element.Element "capture" attr cont)
        | _ => none
      let mut acc : List Capture := []
      for el in elems do
        match el with
        | Element.Element "capture" _ captureContents =>
          let capElems := captureContents.filterMap fun
            | Content.Element (Element.Element "comment" _ _) => none
            | Content.Element e => some e
            | _ => none
          match capElems.toList with
          | [Element.Element "identifier" idAttr #[Content.Character name],
            Element.Element "qtyp" attr qtypContents] =>
            let target ←
              match idAttr.get? "field" with
              | some "env_name" => .ok (CaptureTarget.bareVar name.trimAscii.toString)
              | some "mem_name" => .ok (CaptureTarget.memVar name.trimAscii.toString)
              | _ => .error s!"Invalid capture target (missing env_name/mem_name field)"
            -- `allowCleanPred := true`: a `captures:` requirement may be a guarded
            -- dependency `(int :> clean { k, v => p })` — a clean requirement that
            -- additionally constrains the guard shape — exactly as extern argument
            -- conditions allow (`doc/ffi-proposal.md`, `captures:` section).
            match xmlToQTyp (Element.Element "qtyp" attr qtypContents) (allowCleanPred := true) with
            | .ok (typ, poison, pred) =>
              acc := acc.append [Capture.mk target typ poison pred]
            | .error e => throw e
          | _ => throw "Invalid capture"
        | _ => throw "Invalid capture"
      return acc
    | _ => throw s!"Invalid captures_block element: {x}"

end
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
