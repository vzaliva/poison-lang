import LeanPoison.Syntax

-- Predicate tags
abbrev Tag := Nat

-- Poison flag
abbrev Poison := Bool

-- Use mutual block to define interdependent types
mutual

-- Predicate expressions (subset of expressions that can appear in predicates)
inductive PExpr : Type where
  | value : Value → PExpr                          -- Values embedded in expressions
  | var : Name → PExpr                             -- x
  | op : PExpr → Op → PExpr → PExpr                -- e1 op e2
  | ite : PExpr → PExpr → PExpr → PExpr            -- if e1 then e2 else e3
  | deref : PExpr → PExpr                          -- ! e
  | seq : PExpr → PExpr → PExpr                    -- e1 ; e2
  | let : Name → PTyp → PExpr → PExpr → PExpr      -- let x : T = e1 in e2
  | app : PExpr → PExpr → PExpr                    -- e1 e2

-- Type closures for function types
inductive TClosure : Type where
  | fn_tclosure : Name → Expr → VarEnv → TClosure
  | pfn_tclosure: Name → PExpr → VarEnv → TClosure

-- Poison type (full type)
inductive PTyp : Type where
  | int : PTyp
  | bool : PTyp
  | unit : PTyp
  | ref : PTyp → Address → PTyp
  | arrow : PTyp → PTyp → Poison → TClosure → PTyp

end

-- Tagged predicate: (tag, predicate closure)
def TPred : Type := Tag × TClosure

-- Qualified type: (poison flag, optional tagged predicate)
def QTyp : Type := PTyp × Poison × Option TPred

-- Manual Repr instances for mutual types
mutual

def reprPExpr : PExpr → Nat → Std.Format
  | PExpr.value v, _ => s!"PExpr.value {repr v}"
  | PExpr.var x, _ => s!"PExpr.var {repr x}"
  | PExpr.op e1 op e2, _ => s!"PExpr.op ({reprPExpr e1 0}) {repr op} ({reprPExpr e2 0})"
  | PExpr.ite e1 e2 e3, _ => s!"PExpr.ite ({reprPExpr e1 0}) ({reprPExpr e2 0}) ({reprPExpr e3 0})"
  | PExpr.deref e, _ => s!"PExpr.deref ({reprPExpr e 0})"
  | PExpr.seq e1 e2, _ => s!"PExpr.seq ({reprPExpr e1 0}) ({reprPExpr e2 0})"
  | PExpr.let x t e1 e2, _ => s!"PExpr.let {repr x} {reprPTyp t 0} ({reprPExpr e1 0}) ({reprPExpr e2 0})"
  | PExpr.app e1 e2, _ => s!"PExpr.app ({reprPExpr e1 0}) ({reprPExpr e2 0})"

def reprTClosure : TClosure → Nat → Std.Format
  | TClosure.fn_tclosure x _ _ , _ => s!"TClosure.fn_tclosure {repr x} <expr>"
  | TClosure.pfn_tclosure x _ _ , _ => s!"TClosure.pfn_tclosure {repr x} <pexpr>"

def reprPTyp : PTyp → Nat → Std.Format
  | PTyp.int, _ => "PTyp.int"
  | PTyp.bool, _ => "PTyp.bool"
  | PTyp.unit, _ => "PTyp.unit"
  | PTyp.ref t l, _ => s!"PTyp.ref {reprPTyp t 0} {repr l}"
  | PTyp.arrow t1 t2 p tcl, _ => s!"PTyp.arrow {reprPTyp t1 0} {reprPTyp t2 0} {repr p} {reprTClosure tcl 0}"

def reprQTyp : QTyp → Nat → Std.Format
  | (ptyp, poison, tpred), _ =>
    let tpredRepr := match tpred with
      | none => "none"
      | some (tag, tcl) => s!"some ({repr tag}, {reprTClosure tcl 0})"
    s!"QTyp {reprPTyp ptyp 0} {repr poison} {tpredRepr}"

end

instance : Repr PExpr where
  reprPrec := reprPExpr

instance : Repr TClosure where
  reprPrec := reprTClosure

instance : Repr PTyp where
  reprPrec := reprPTyp

instance : Repr QTyp where
  reprPrec := reprQTyp

instance : Repr TPred where
  reprPrec := fun (tag, tcl) _ => s!"({repr tag}, {repr tcl})"
