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
  | let : Name → PExpr → PExpr → PExpr      -- let x : T = e1 in e2
  | app : PExpr → PExpr → PExpr                    -- e1 e2

-- Tagged predicate structure
structure TPred where
  tag : Tag
  arg_name: Name
  pred_body: PExpr
  var_env: List (Name × QTyp)

-- Qualified type structure
structure QTyp where
  ptyp : PTyp
  poison : Poison
  pred : Option TPred

-- Type closures for function types
inductive TClosure : Type where
  | fn_tclosure : Name → Expr → List (Name × QTyp) → TClosure
  | pfn_tclosure: Name → PExpr → List (Name × QTyp) → TClosure

-- Poison type (full type)
inductive PTyp : Type where
  | int : PTyp
  | bool : PTyp
  | unit : PTyp
  | ref : PTyp → Address → PTyp
  | arrow : PTyp → PTyp → Poison → TClosure → PTyp

end

-- Variable typing environment (σ in the Ott spec) Because we use it in a
-- mutually inductive type above which requires types you’re defining must be
-- strictly positive and may only appear in constructors you’re declaring in
-- that same mutual block we could not use Std.HashMap. Instead we use an assoc
-- list of key-value pairs.
abbrev VarTypeEnv := List (Name × QTyp)

-- helper function to lookup a variable in the variable typing environment
def lookupVarEnv : VarTypeEnv → Name → Option QTyp
  | [], _ => none
  | (x, qt) :: env, y => if x == y then some qt else lookupVarEnv env y

-- helper function to update a variable in the variable typing environment the
-- implementation is not very efficient as mappings with existing keys are just
-- added to the front of the list. However this is sound, as lookupVarEnv always
-- returns the first mapping with a given key.
def updateVarEnv : VarTypeEnv → Name → QTyp → VarTypeEnv
  | env, x, qt => (x, qt) :: env

-- Manual Repr instances for mutual types

mutual

partial def reprPExpr : PExpr → Nat → Std.Format
  | PExpr.value v, _ => s!"PExpr.value {repr v}"
  | PExpr.var x, _ => s!"PExpr.var {repr x}"
  | PExpr.op e1 op e2, _ => s!"PExpr.op ({reprPExpr e1 0}) {repr op} ({reprPExpr e2 0})"
  | PExpr.ite e1 e2 e3, _ => s!"PExpr.ite ({reprPExpr e1 0}) ({reprPExpr e2 0}) ({reprPExpr e3 0})"
  | PExpr.deref e, _ => s!"PExpr.deref ({reprPExpr e 0})"
  | PExpr.seq e1 e2, _ => s!"PExpr.seq ({reprPExpr e1 0}) ({reprPExpr e2 0})"
  | PExpr.let x e1 e2, _ => s!"PExpr.let {repr x} ({reprPExpr e1 0}) ({reprPExpr e2 0})"
  | PExpr.app e1 e2, _ => s!"PExpr.app ({reprPExpr e1 0}) ({reprPExpr e2 0})"

partial def reprTClosure : TClosure → Nat → Std.Format
  | TClosure.fn_tclosure x _ _ , _ => s!"TClosure.fn_tclosure {repr x} <expr>"
  | TClosure.pfn_tclosure x _ _ , _ => s!"TClosure.pfn_tclosure {repr x} <pexpr>"

partial def reprPTyp : PTyp → Nat → Std.Format
  | PTyp.int, _ => "PTyp.int"
  | PTyp.bool, _ => "PTyp.bool"
  | PTyp.unit, _ => "PTyp.unit"
  | PTyp.ref t l, _ => s!"PTyp.ref {reprPTyp t 0} {repr l}"
  | PTyp.arrow t1 t2 p tcl, _ => s!"PTyp.arrow {reprPTyp t1 0} {reprPTyp t2 0} {repr p} {reprTClosure tcl 0}"

partial def reprQTyp : QTyp → Nat → Std.Format
  | QTyp.mk ptyp poison tpred, _ =>
    let tpredRepr := match tpred with
      | none => "none"
      | some tp => s!"{reprTPred tp 0}"
    s!"QTyp.mk {reprPTyp ptyp 0} {repr poison} {tpredRepr}"

partial def reprVarEnv (env: VarTypeEnv) (_:Nat): Std.Format :=
    Std.Format.text "[" ++
    Std.Format.joinSep (env.map (fun (x, qt) => s!"({repr x}, {reprQTyp qt 0})")) (Std.Format.text ", ") ++
    Std.Format.text "]"

partial def reprTPred : TPred → Nat → Std.Format
  | TPred.mk tag arg_name pred_body var_env, _ => s!"TPred.mk {repr tag} {repr arg_name} {reprPExpr pred_body 0} {reprVarEnv var_env 0}"

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
  reprPrec := reprTPred
