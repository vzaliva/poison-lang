import LeanPoison.Syntax
import LeanPoison.Runtime

open Std

private def commaLine : Std.Format := Std.Format.text "," ++ Std.Format.line

private def formatDelimited (l : String) (entries : List Std.Format) (r : String) : Std.Format :=
  Std.Format.bracket l (Std.Format.joinSep entries commaLine) r

private def formatBracketedList (entries : List Std.Format) : Std.Format :=
  formatDelimited "[" entries "]"

private def formatBracedEntries (entries : List Std.Format) : Std.Format :=
  formatDelimited "{" entries "}"

private def formatKV (k v : Std.Format) : Std.Format :=
  k ++ Std.Format.text " := " ++ v

private def formatKVMap (entries : List (Std.Format × Std.Format)) : Std.Format :=
  formatBracedEntries (entries.map (fun (k, v) => formatKV k v))

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

private partial def syntaxPredCore : SyntaxPredicate → Std.Format
  | .guardClosure tag arg body =>
      repr tag ++
      Std.Format.text ", pfn " ++
      Std.Format.text arg ++
      Std.Format.text " -> " ++
      reprExpr body 0
  | .guardOnly tag => repr tag
  | .noPred => Std.Format.nil

private partial def syntaxPredInline (pred : SyntaxPredicate) : Std.Format :=
  Std.Format.bracket "{" (syntaxPredCore pred) "}"

private partial def effectInline : Effect → Std.Format
  | ⟨target, poison, pred⟩ =>
      let targetFmt :=
        match target with
        | .namedVar x => Std.Format.text "!" ++ Std.Format.text x
        | .returnValue => Std.Format.text "return"
      targetFmt ++
      Std.Format.text " :> " ++
      Std.Format.paren (
        Std.Format.text "int :> " ++
        Std.Format.text (if poison then "poisoned" else "clean") ++
        Std.Format.text " " ++
        syntaxPredInline pred
      )

private partial def externReturnInline : ExternReturn → Std.Format
  | .simple typ poison pred =>
      Std.Format.paren (
        reprTyp typ 0 ++
        Std.Format.text " :> " ++
        Std.Format.text (if poison then "poisoned" else "clean") ++
        Std.Format.text " " ++
        syntaxPredInline pred
      )
  | .nestedFn x typ ret eff =>
      Std.Format.text "extern fn " ++
      Std.Format.text x ++
      Std.Format.text " : " ++
      Std.Format.paren (reprTyp typ 0) ++
      Std.Format.text " -> " ++
      Std.Format.paren (externReturnInline ret) ++
      Std.Format.text ", effects: " ++
      formatBracedEntries (eff.map effectInline)
  | .nestedPfn x typ ret =>
      Std.Format.text "extern pfn " ++
      Std.Format.text x ++
      Std.Format.text " : " ++
      Std.Format.paren (reprTyp typ 0) ++
      Std.Format.text " -> " ++
      Std.Format.paren (externReturnInline ret)

partial def reprValue : Value → Nat → Std.Format
  | Value.num n, _ => repr n
  | Value.bool b, _ => repr b
  | Value.unit, _ => "unit"
  | Value.str s, _ => repr s
  | Value.loc l, _ => Std.Format.text "loc " ++ repr l
  | Value.closure x body env, _ =>
      Std.Format.text "closure " ++
      Std.Format.text x ++
      Std.Format.text " (" ++ reprExpr body 0 ++ Std.Format.text ")" ++
      Std.Format.text " " ++ reprRuntimeVarEnv env 0
  | Value.peClosure x body env, _ =>
      Std.Format.text "peClosure " ++
      Std.Format.text x ++
      Std.Format.text " (" ++ reprExpr body 0 ++ Std.Format.text ")" ++
      Std.Format.text " " ++ reprRuntimeVarEnv env 0

partial def reprRuntimeVarEnv (env : VarEnv) (_ : Nat) : Std.Format :=
  let entries : List Std.Format := env.map (fun (x, v) => Std.Format.text x ++ Std.Format.text " := " ++ reprValue v 0)
  formatBracketedList entries

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
      syntaxPredInline pred ++
      Std.Format.text ")"
    | Expr.externFn x t ret eff =>
      Std.Format.text "extern fn " ++
      Std.Format.text x ++
      Std.Format.text " : " ++
      Std.Format.paren (reprTyp t 0) ++
      Std.Format.text " -> " ++
      Std.Format.paren (externReturnInline ret) ++
      Std.Format.text ", effects: " ++
      formatBracedEntries (eff.map effectInline)
    | Expr.externPfn x t ret =>
      Std.Format.text "extern pfn " ++
      Std.Format.text x ++
      Std.Format.text " : " ++
      Std.Format.paren (reprTyp t 0) ++
      Std.Format.text " -> " ++
      Std.Format.paren (externReturnInline ret)

end

partial def reprSyntaxPredicate : SyntaxPredicate → Nat → Std.Format
  | pred, _ => syntaxPredInline pred

partial def reprEffect : Effect → Nat → Std.Format
  | eff, _ => effectInline eff

partial def reprExternReturn : ExternReturn → Nat → Std.Format
  | ret, _ => externReturnInline ret

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
  | FnTClosure.regular x body env, _ =>
      Std.Format.text "regular " ++
      Std.Format.text x ++
      Std.Format.text " " ++
      Std.Format.paren (reprExpr body 0) ++
      Std.Format.text " " ++ reprVarEnv env 0
  | FnTClosure.extern x ret eff env, _ =>
      Std.Format.text "extern " ++
      Std.Format.text x ++
      Std.Format.text " " ++
      Std.Format.paren (externReturnInline ret) ++
      Std.Format.text " effects: " ++
      formatBracedEntries (eff.map effectInline) ++
      Std.Format.text ", deps: " ++
      reprVarEnv env 0

partial def reprPFnTClosure : PFnTClosure → Nat → Std.Format
  | PFnTClosure.regular x body env, _ =>
      Std.Format.text "regular " ++
      Std.Format.text x ++
      Std.Format.text " " ++
      Std.Format.paren (reprPExpr body 0) ++
      Std.Format.text " " ++ reprVarEnv env 0
  | PFnTClosure.extern x ret env, _ =>
      Std.Format.text "extern " ++
      Std.Format.text x ++
      Std.Format.text " " ++
      Std.Format.paren (externReturnInline ret) ++
      Std.Format.text ", deps: " ++
      reprVarEnv env 0

partial def reprETyp : ETyp → Nat → Std.Format
  | ETyp.int, _ => "int"
  | ETyp.bool, _ => "bool"
  | ETyp.unit, _ => "unit"
  | ETyp.string, _ => "string"
  | ETyp.ref ls, _ =>
      Std.Format.text "ref @ " ++
      repr ls
  | ETyp.arrow st1 st2 p tcls, _ =>
      let closureReprs := tcls.map (fun tcl => reprFnTClosure tcl 0)
      Std.Format.text "arrow " ++
      reprTyp st1 0 ++
      Std.Format.text " " ++
      reprTyp st2 0 ++
      Std.Format.text " " ++
      repr p ++
      Std.Format.text " " ++
      formatBracketedList closureReprs
  | ETyp.parrow st1 st2 p tcls, _ =>
      let closureReprs := tcls.map (fun tcl => reprPFnTClosure tcl 0)
      Std.Format.text "parrow " ++
      reprTyp st1 0 ++
      Std.Format.text " " ++
      reprTyp st2 0 ++
      Std.Format.text " " ++
      repr p ++
      Std.Format.text " " ++
      formatBracketedList closureReprs

partial def reprVarEnv (env : CapturedVarEnv) (_ : Nat) : Std.Format :=
  let entries : List Std.Format := env.map (fun (x, qt) => Std.Format.text x ++ Std.Format.text " : " ++ reprQTyp qt 0)
  formatBracketedList entries

partial def reprPredicate : Predicate → Nat → Std.Format
  | Predicate.guardClosure tag arg_name pred_body var_env, _ =>
      let base :=
        repr tag ++
        Std.Format.text ", pfn " ++
        Std.Format.text arg_name ++
        Std.Format.text " -> " ++
        reprPExpr pred_body 0
      let withDeps :=
        match var_env with
        | [] => base
        | _ => base ++ Std.Format.text ", deps: " ++ reprVarEnv var_env 0
      Std.Format.bracket "{" withDeps "}"
  | Predicate.guardOnly tag, _ =>
      Std.Format.bracket "{" (repr tag) "}"
  | Predicate.noPred, _ =>
      Std.Format.bracket "{" Std.Format.nil "}"

partial def reprQTyp : QTyp → Nat → Std.Format
  | QTyp.mk etyp poison pred, _ =>
      formatBracedEntries [
        Std.Format.text "type=" ++ reprETyp etyp 0,
        Std.Format.text "poison=" ++ repr poison,
        Std.Format.text "pred=" ++ reprPredicate pred 0
      ]

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
  let entries : List Std.Format :=
    (ExtTreeMap.toList m).map (fun (addr, value) =>
      Std.Format.text "(" ++ repr addr ++ Std.Format.text ", " ++ repr value ++ Std.Format.text ")")
  formatBracketedList entries

instance : Repr Memory where
  reprPrec m _ := formatEntries m

end Memory

private def formatVarEnvEntries (venv : VarEnv) : Std.Format :=
  let entries : List Std.Format := venv.map (fun (name, value) => Std.Format.text name ++ Std.Format.text " := " ++ repr value)
  formatBracketedList entries

instance : Repr VarEnv where
  reprPrec venv _ := formatVarEnvEntries venv

instance : ToString VarEnv where
  toString env := Std.Format.pretty (repr env)

instance : Repr Config where
  reprPrec c _ :=
    Std.Format.text "Config " ++
    formatKVMap [
      (Std.Format.text "memory", repr c.memory),
      (Std.Format.text "varEnv", repr c.varEnv),
      (Std.Format.text "nextAddr", repr c.nextAddr),
      (Std.Format.text "pureMode", repr c.pureMode)
    ]

instance : ToString Memory where
  toString m := Std.Format.pretty (repr m)

instance : ToString Config where
  toString config := Std.Format.pretty (repr config)
