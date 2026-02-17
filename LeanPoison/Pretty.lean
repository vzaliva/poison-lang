import LeanPoison.Syntax
import LeanPoison.Runtime

open Std

instance : Repr LocSet where
  reprPrec s prec :=
    reprPrec (ExtTreeSet.toList s) prec

partial def reprTyp : Typ → Nat → Std.Format
  | Typ.int, _ => "int"
  | Typ.bool, _ => "bool"
  | Typ.unit, _ => "unit"
  | Typ.ref t, _ => Std.Format.text "ref " ++ reprTyp t 0
  | Typ.arrow t1 t2, _ => Std.Format.text "(" ++ reprTyp t1 0 ++ Std.Format.text " -> " ++ reprTyp t2 0 ++ Std.Format.text ")"
  | Typ.string, _ => "string"

private def formatTypSurface : Typ → Std.Format
  | Typ.int => "int"
  | Typ.bool => "bool"
  | Typ.unit => "unit"
  | Typ.string => "string"
  | Typ.ref t => Std.Format.text "ref " ++ formatTypSurface t
  | Typ.arrow t1 t2 => Std.Format.text "(" ++ formatTypSurface t1 ++ Std.Format.text " -> " ++ formatTypSurface t2 ++ Std.Format.text ")"

private def formatOpSymbol : Op → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "/"
  | .gte => ">="
  | .lte => "<="
  | .gt => ">"
  | .lt => "<"
  | .eq => "=="
  | .neq => "!="
  | .and => "&&"
  | .or => "||"
  | .bitand => "&"

mutual

private partial def exprInline (e : Expr) : String :=
  Std.Format.pretty (reprExpr e 0)

private partial def syntaxPredCore : SyntaxPredicate → String
  | .guardClosure tag arg body => s!"{tag}, pfn {arg} -> {exprInline body}"
  | .guardOnly tag => s!"{tag}"
  | .noPred => ""

private partial def syntaxPredInline (pred : SyntaxPredicate) : String :=
  "{" ++ syntaxPredCore pred ++ "}"

private partial def effectInline : Effect → String
  | ⟨target, poison, pred⟩ =>
      let targetFmt :=
        match target with
        | .namedVar x => s!"!{x}"
        | .returnValue => "return"
      targetFmt ++
      " :> (int :> " ++
      (if poison then "poisoned" else "clean") ++
      " " ++ syntaxPredInline pred ++ ")"

private partial def externReturnInline : ExternReturn → String
  | .simple typ poison pred =>
      "(" ++ Std.Format.pretty (reprTyp typ 0) ++
      " :> " ++ (if poison then "poisoned" else "clean") ++
      " " ++ syntaxPredInline pred ++ ")"
  | .nestedFn x typ ret eff =>
      "extern fn " ++ x ++
      " : (" ++ Std.Format.pretty (reprTyp typ 0) ++
      ") -> (" ++ externReturnInline ret ++
      "), effects: {" ++ String.intercalate ", " (eff.map effectInline) ++ "}"
  | .nestedPfn x typ ret =>
      "extern pfn " ++ x ++
      " : (" ++ Std.Format.pretty (reprTyp typ 0) ++
      ") -> (" ++ externReturnInline ret ++ ")"

partial def reprValue : Value → Nat → Std.Format
  | Value.num n, _ => repr n
  | Value.bool b, _ => repr b
  | Value.unit, _ => "unit"
  | Value.str s, _ => repr s
  | Value.loc l, _ => s!"loc {repr l}"
  | Value.closure x _ _, _ => s!"closure {x} <expr> <env>"
  | Value.peClosure x _ _, _ => s!"peClosure {x} <expr> <env>"

partial def reprExpr : Expr → Nat → Std.Format
  | e, _ =>
    let atom : Expr → Std.Format := fun e' =>
      match e' with
      | Expr.unit | Expr.str _ | Expr.num _ | Expr.bool _ | Expr.var _ => reprExpr e' 0
      | _ => Std.Format.text "(" ++ reprExpr e' 0 ++ Std.Format.text ")"
    match e with
    | Expr.unit => "unit"
    | Expr.str s => repr s
    | Expr.num n => repr n
    | Expr.bool b => repr b
    | Expr.var x => Std.Format.text x
    | Expr.op e1 op e2 =>
        atom e1 ++ Std.Format.text s!" {formatOpSymbol op} " ++ atom e2
    | Expr.unaryop .not e =>
        Std.Format.text "not " ++ atom e
    | Expr.ite e1 e2 e3 =>
        Std.Format.group (
          Std.Format.text "if " ++ reprExpr e1 0 ++
          Std.Format.text " then " ++ reprExpr e2 0 ++
          Std.Format.text " else " ++ reprExpr e3 0
        )
    | Expr.newRef e => Std.Format.text "ref " ++ atom e
    | Expr.assign e1 e2 => atom e1 ++ Std.Format.text " := " ++ atom e2
    | Expr.deref e => Std.Format.text "!" ++ atom e
    | Expr.seq e1 e2 => atom e1 ++ Std.Format.text "; " ++ atom e2
    | Expr.kwhile e1 e2 =>
        Std.Format.text "while " ++ reprExpr e1 0 ++ Std.Format.text " do " ++ reprExpr e2 0
    | Expr.vlet x e1 e2 =>
        Std.Format.text "let " ++ Std.Format.text x ++ Std.Format.text " = " ++ reprExpr e1 0 ++
        Std.Format.text " in " ++ reprExpr e2 0
    | Expr.fn x t1 e t2 =>
        Std.Format.text "fn " ++ Std.Format.text x ++ Std.Format.text " : " ++ formatTypSurface t1 ++
        Std.Format.text " => " ++ reprExpr e 0 ++ Std.Format.text " : " ++ formatTypSurface t2
    | Expr.pfn x t1 e t2 =>
        Std.Format.text "pfn " ++ Std.Format.text x ++ Std.Format.text " : " ++ formatTypSurface t1 ++
        Std.Format.text " => " ++ reprExpr e 0 ++ Std.Format.text " : " ++ formatTypSurface t2
    | Expr.app e1 e2 => atom e1 ++ Std.Format.text " " ++ atom e2
    | Expr.rand e => Std.Format.text "rand " ++ atom e
    | Expr.frand e => Std.Format.text "frand " ++ atom e
    | Expr.printString e => Std.Format.text "printString " ++ atom e
    | Expr.printInt e => Std.Format.text "printInt " ++ atom e
    | Expr.externVal t p pred =>
        Std.Format.text "extern val (" ++
        reprTyp t 0 ++
        Std.Format.text " :> " ++
        Std.Format.text (if p then "poisoned" else "clean") ++
        Std.Format.text " " ++
        Std.Format.text (syntaxPredInline pred) ++
        Std.Format.text ")"
    | Expr.externFn x t ret eff =>
        Std.Format.text "extern fn " ++
        Std.Format.text x ++
        Std.Format.text " : (" ++
        reprTyp t 0 ++
        Std.Format.text ") -> (" ++
        Std.Format.text (externReturnInline ret) ++
        Std.Format.text "), effects: {" ++
        Std.Format.text (String.intercalate ", " (eff.map effectInline)) ++
        Std.Format.text "}"
    | Expr.externPfn x t ret =>
        Std.Format.text "extern pfn " ++
        Std.Format.text x ++
        Std.Format.text " : (" ++
        reprTyp t 0 ++
        Std.Format.text ") -> (" ++
        Std.Format.text (externReturnInline ret) ++
        Std.Format.text ")"

end

partial def reprSyntaxPredicate : SyntaxPredicate → Nat → Std.Format
  | pred, _ => Std.Format.text (syntaxPredInline pred)

partial def reprEffect : Effect → Nat → Std.Format
  | eff, _ => Std.Format.text (effectInline eff)

partial def reprExternReturn : ExternReturn → Nat → Std.Format
  | ret, _ => Std.Format.text (externReturnInline ret)

instance : Repr Value where
  reprPrec := reprValue

instance : Repr Expr where
  reprPrec := reprExpr

instance : Repr SyntaxPredicate where
  reprPrec := reprSyntaxPredicate

instance : Repr Effect where
  reprPrec := reprEffect

instance : Repr ExternReturn where
  reprPrec := reprExternReturn

instance : ToString Typ where
  toString t := Std.Format.pretty (repr t)

instance : ToString Value where
  toString v := Std.Format.pretty (repr v)

instance : ToString Op where
  toString op := Std.Format.pretty (repr op)

instance : ToString UnaryOp where
  toString opname := Std.Format.pretty (repr opname)

instance : ToString Expr where
  toString e := Std.Format.pretty (repr e)

mutual

partial def reprPExpr : PExpr → Nat → Std.Format
  | e, _ =>
    let atom : PExpr → Std.Format := fun e' =>
      match e' with
      | PExpr.unit | PExpr.num _ | PExpr.bool _ | PExpr.str _ | PExpr.var _ => reprPExpr e' 0
      | _ => Std.Format.text "(" ++ reprPExpr e' 0 ++ Std.Format.text ")"
    match e with
    | PExpr.unit => "unit"
    | PExpr.num n => repr n
    | PExpr.bool b => repr b
    | PExpr.str s => repr s
    | PExpr.var x => Std.Format.text x
    | PExpr.op e1 op e2 =>
        atom e1 ++ Std.Format.text s!" {formatOpSymbol op} " ++ atom e2
    | PExpr.unaryop .not e =>
        Std.Format.text "not " ++ atom e
    | PExpr.ite e1 e2 e3 =>
        Std.Format.group (
          Std.Format.text "if " ++ reprPExpr e1 0 ++
          Std.Format.text " then " ++ reprPExpr e2 0 ++
          Std.Format.text " else " ++ reprPExpr e3 0
        )
    | PExpr.deref e =>
        Std.Format.text "!" ++ atom e
    | PExpr.vlet x e1 e2 =>
        Std.Format.text "let " ++ Std.Format.text x ++ Std.Format.text " = " ++ reprPExpr e1 0 ++
        Std.Format.text " in " ++ reprPExpr e2 0
    | PExpr.app e1 e2 =>
        atom e1 ++ Std.Format.text " " ++ atom e2

partial def reprFnTClosure : FnTClosure → Nat → Std.Format
  | FnTClosure.regular x _ _, _ => s!"regular {x} <expr>"
  | FnTClosure.extern x ret eff _, _ =>
      Std.Format.text s!"extern {x} (" ++
      Std.Format.text (externReturnInline ret) ++
      Std.Format.text ") effects: {" ++
      Std.Format.text (String.intercalate ", " (eff.map effectInline)) ++
      Std.Format.text "}"

partial def reprPFnTClosure : PFnTClosure → Nat → Std.Format
  | PFnTClosure.regular x _ _, _ => s!"regular {x} <pexpr>"
  | PFnTClosure.extern x ret _, _ =>
      Std.Format.text s!"extern {x} (" ++ Std.Format.text (externReturnInline ret) ++ Std.Format.text ")"

partial def reprETyp : ETyp → Nat → Std.Format
  | ETyp.int, _ => "int"
  | ETyp.bool, _ => "bool"
  | ETyp.unit, _ => "unit"
  | ETyp.string, _ => "string"
  | ETyp.ref t ls, _ => s!"ref {reprETyp t 0} {repr ls}"
  | ETyp.arrow st1 st2 p tcls, _ =>
      let closureReprs := tcls.map (fun tcl => reprFnTClosure tcl 0)
      s!"arrow {reprTyp st1 0} {reprTyp st2 0} {repr p} [{Std.Format.joinSep closureReprs (Std.Format.text ", ")}]"
  | ETyp.parrow st1 st2 p tcls, _ =>
      let closureReprs := tcls.map (fun tcl => reprPFnTClosure tcl 0)
      s!"parrow {reprTyp st1 0} {reprTyp st2 0} {repr p} [{Std.Format.joinSep closureReprs (Std.Format.text ", ")}]"

partial def reprVarEnv (env : CapturedVarEnv) (_ : Nat) : Std.Format :=
  let entries : List Std.Format := env.map (fun (x, qt) => s!"{x} : {reprQTyp qt 0}")
  match entries with
  | [] => Std.Format.text "[]"
  | _ =>
      let sep := Std.Format.text "," ++ Std.Format.line
      Std.Format.group (
        Std.Format.text "[" ++
        Std.Format.nest 2 (Std.Format.joinSep entries sep) ++
        Std.Format.text "]"
      )

partial def reprPredicate : Predicate → Nat → Std.Format
  | Predicate.guardClosure tag arg_name pred_body var_env, _ =>
      let base :=
        Std.Format.text s!"{tag}, pfn {arg_name} -> " ++
        reprPExpr pred_body 0
      let withDeps :=
        match var_env with
        | [] => base
        | _ => base ++ Std.Format.text ", deps: " ++ reprVarEnv var_env 0
      Std.Format.text "{" ++ withDeps ++ Std.Format.text "}"
  | Predicate.guardOnly tag, _ =>
      Std.Format.text "{" ++ repr tag ++ Std.Format.text "}"
  | Predicate.noPred, _ =>
      "{}"

partial def reprQTyp : QTyp → Nat → Std.Format
  | QTyp.mk etyp poison pred, _ =>
      Std.Format.text "{type=" ++
      reprETyp etyp 0 ++
      Std.Format.text ", poison=" ++
      repr poison ++
      Std.Format.text ", pred=" ++
      reprPredicate pred 0 ++
      Std.Format.text "}"

end

instance : Repr PExpr where
  reprPrec := reprPExpr

instance : Repr FnTClosure where
  reprPrec := reprFnTClosure

instance : Repr PFnTClosure where
  reprPrec := reprPFnTClosure

instance : Repr ETyp where
  reprPrec := reprETyp

instance : Repr QTyp where
  reprPrec := reprQTyp

instance : Repr Predicate where
  reprPrec := reprPredicate

instance : ToString ETyp where
  toString e := Std.Format.pretty (repr e)

instance : ToString QTyp where
  toString e := Std.Format.pretty (repr e)

namespace Memory

private def formatEntries (m : Memory) : Std.Format :=
  let sorted := (ExtTreeMap.toList m : List (Address × Int)).mergeSort (fun a b => a.fst < b.fst)
  let entries : List Std.Format := sorted.map (fun (addr, value) => s!"({repr addr}, {repr value})")
  match entries with
  | [] => Std.Format.text "[]"
  | _ =>
      let sep := Std.Format.text "," ++ Std.Format.line
      Std.Format.group (
        Std.Format.text "[" ++
        Std.Format.nest 2 (Std.Format.joinSep entries sep) ++
        Std.Format.text "]"
      )

instance : Repr Memory where
  reprPrec m _ := formatEntries m

end Memory

private def formatVarEnvEntries (venv : VarEnv) : Std.Format :=
  let entries : List Std.Format := venv.map (fun (name, value) => Std.Format.text name ++ Std.Format.text " := " ++ repr value)
  match entries with
  | [] => Std.Format.text "[]"
  | _ =>
      let sep := Std.Format.text "," ++ Std.Format.line
      Std.Format.group (
        Std.Format.text "[" ++
        Std.Format.nest 2 (Std.Format.joinSep entries sep) ++
        Std.Format.text "]"
      )

instance : Repr VarEnv where
  reprPrec venv _ := formatVarEnvEntries venv

instance : ToString VarEnv where
  toString env := Std.Format.pretty (repr env)

instance : Repr Config where
  reprPrec c _ :=
    Std.Format.group (
      Std.Format.text "Config {" ++
      Std.Format.nest 2 (
        Std.Format.line ++ Std.Format.text "memory := " ++ repr c.memory ++ Std.Format.text "," ++
        Std.Format.line ++ Std.Format.text "varEnv := " ++ repr c.varEnv ++ Std.Format.text "," ++
        Std.Format.line ++ Std.Format.text "nextAddr := " ++ repr c.nextAddr ++ Std.Format.text "," ++
        Std.Format.line ++ Std.Format.text "pureMode := " ++ repr c.pureMode
      ) ++
      Std.Format.line ++
      Std.Format.text "}"
    )

instance : ToString Memory where
  toString m := Std.Format.pretty (repr m)

instance : ToString Config where
  toString config := Std.Format.pretty (repr config)
