-- Core definitions for Poison language (aligned with poison-lang.ott)

import Std.Data.HashMap
import Mathlib.Tactic
open Std

abbrev Address := Nat
abbrev Name := String

-- Surface types (corresponds to typ, ST in Ott)
inductive Typ : Type where
  | int : Typ
  | bool : Typ
  | unit : Typ
  | ref : Typ → Typ
  | arrow : Typ → Typ → Typ
  | string : Typ
  deriving Repr, DecidableEq

-- Manual BEq instance for Typ (for better control over proofs)
def Typ.beq : Typ → Typ → Bool
  | int, int => true
  | bool, bool => true
  | unit, unit => true
  | string, string => true
  | ref t1, ref t2 => beq t1 t2
  | arrow t1 t2, arrow t1' t2' => beq t1 t1' && beq t2 t2'
  | _, _ => false

instance : BEq Typ where
  beq := Typ.beq

-- Operations (corresponds to binary operations, op in Ott)
inductive Op : Type where
  | add : Op      -- +
  | sub : Op
  | mul : Op
  | div : Op
  | gte : Op      -- >=
  | lte : Op
  | gt  : Op
  | lt  : Op
  | eq  : Op
  | and : Op
  | bitand : Op
  | or  : Op
  | neq : Op
  deriving Repr, BEq, DecidableEq

inductive UnaryOp : Type where
  | not : UnaryOp   -- unary boolean negation
  deriving Repr, BEq, DecidableEq

-- Predicate tags (moved here for use in SyntaxPredicate)
abbrev Tag := Nat

-- Effect target: either a named variable or the return value
inductive EffectTarget where
  | namedVar : Name → EffectTarget      -- !varname
  | returnValue : EffectTarget           -- return (special keyword)
  deriving Repr, BEq



mutual

-- Syntax-level predicate (simplified, no captured environment)
-- Parser creates these, typechecker converts to full Predicate
inductive SyntaxPredicate : Type where
  | guardClosure: Tag → Name → Expr → SyntaxPredicate  -- tag, arg name, predicate body (as Expr)
  | guardOnly : Tag → SyntaxPredicate
  | noPred : SyntaxPredicate

-- Effect specification for impure externs (uses SyntaxPredicate)
structure Effect where
  target : EffectTarget
  poison : Bool  -- true for "poisoned", false for "clean"
  pred : SyntaxPredicate

-- Return specification for extern functions (simple or nested)
inductive ExternReturn where
  | simple : Typ → Bool → SyntaxPredicate → ExternReturn
  | nestedFn : Name → Typ → ExternReturn → List Effect → ExternReturn
  | nestedPfn : Name → Typ → ExternReturn → ExternReturn

-- Expressions (corresponds to e in Ott)
inductive Expr : Type where
  /- literals -/
  | unit : Expr                                 -- unit
  | num : Int → Expr                            -- n
  | bool : Bool → Expr                          -- b
  | str : String -> Expr
  /- expressions -/
  | var : Name → Expr                           -- x
  | op : Expr → Op → Expr → Expr                -- e1 op e2
  | unaryop :  UnaryOp → Expr → Expr             -- e op
  | ite : Expr → Expr → Expr → Expr             -- if e1 then e2 else e3
  | newRef : Expr → Expr                        -- ref e
  | assign : Expr → Expr → Expr                 -- e1 := e2
  | deref : Expr → Expr                         -- ! e
  | seq : Expr → Expr → Expr                    -- e1 ; e2
  | kwhile : Expr → Expr → Expr                  -- while e1 do e2
  | vlet : Name → Expr → Expr → Expr             -- let x = e1 in e2
  | fn : Name → Typ → Expr → Typ → Expr         -- fn x : ST1 => e : ST2
  | pfn : Name → Typ → Expr → Typ → Expr        -- pfn x : ST1 => pe : ST2
  | app : Expr → Expr → Expr                    -- e1 e2
  /- built-in expressions -/
  | rand  : Expr -> Expr
  | frand : Expr -> Expr
  | printString  : Expr -> Expr
  | printInt  : Expr -> Expr
  /- extern placeholders -/
  | externVal : Typ → Bool → SyntaxPredicate → Expr
  | externFn : Name → Typ → ExternReturn → List Effect → Expr
  | externPfn : Name → Typ → ExternReturn → Expr

end

-- Values (corresponds to v in Ott)
-- Note: In Ott, values are: n | b | unit | closure(x,e,r) | pe_closure(x,pe,r)
inductive Value : Type where
  | num : Int → Value           -- n
  | bool : Bool → Value         -- b
  | unit : Value                -- unit
  | str : String -> Value       -- str
  | loc : Address → Value           -- l (locations are values in the operational semantics)
  | closure : Name → Expr → List (Name × Value) → Value      -- closure(x,e,r)
  | peClosure : Name → Expr → List (Name × Value) → Value    -- pe_closure(x,pe,r)


-- Variable environment: List (name × value) . We do not use a
-- HashMap here, as we do for Memory, because of the Lean restriction of
-- inductive type definitions (insude pe_closure)
abbrev VarEnv := List (Name × Value)

-- Note: No helper functions needed for literals since they are now direct constructors
-- Locations cannot be created as expressions - they only exist at runtime

-- Extract value from expression if it's a literal
def Expr.toValue? : Expr → Option Value
  | Expr.num n => some (Value.num n)
  | Expr.bool b => some (Value.bool b)
  | Expr.unit => some Value.unit
  | Expr.str s => some (Value.str s)
  | _ => none

-- BEq instances

-- First define beqExpr (used by Value closures)
-- For extern constructors, we avoid circular dependencies by directly comparing
-- Tag/Name/Bool fields instead of calling helper beq functions
mutual

def beqExpr : Expr → Expr → Bool
  | Expr.unit, Expr.unit => true
  | Expr.num n1, Expr.num n2 => n1 == n2
  | Expr.bool b1, Expr.bool b2 => b1 == b2
  | Expr.str s1 , Expr.str s2 => s1 == s2
  | Expr.var x1, Expr.var x2 => x1 == x2
  | Expr.op e1 op1 e2, Expr.op e1' op2 e2' => beqExpr e1 e1' && op1 == op2 && beqExpr e2 e2'
  | Expr.unaryop op1 e1, Expr.unaryop op2 e2 => op1 == op2 && beqExpr e1 e2
  | Expr.ite e1 e2 e3, Expr.ite e1' e2' e3' => beqExpr e1 e1' && beqExpr e2 e2' && beqExpr e3 e3'
  | Expr.newRef e1, Expr.newRef e2 => beqExpr e1 e2
  | Expr.assign e1 e2, Expr.assign e1' e2' => beqExpr e1 e1' && beqExpr e2 e2'
  | Expr.deref e1, Expr.deref e2 => beqExpr e1 e2
  | Expr.seq e1 e2, Expr.seq e1' e2' => beqExpr e1 e1' && beqExpr e2 e2'
  | Expr.kwhile e1 e2, Expr.kwhile e1' e2' => beqExpr e1 e1' && beqExpr e2 e2'
  | Expr.vlet x1 e1 e2, Expr.vlet x2 e1' e2' => x1 == x2 && beqExpr e1 e1' && beqExpr e2 e2'
  | Expr.fn x1 t1 e1 t1', Expr.fn x2 t2 e2 t2' => x1 == x2 && t1 == t2 && beqExpr e1 e2 && t1' == t2'
  | Expr.pfn x1 t1 e1 t1', Expr.pfn x2 t2 e2 t2' => x1 == x2 && t1 == t2 && beqExpr e1 e2 && t1' == t2'
  | Expr.app e1 e2, Expr.app e1' e2' => beqExpr e1 e1' && beqExpr e2 e2'
  | Expr.rand e1, Expr.rand e2 => beqExpr e1 e2
  | Expr.frand e1, Expr.frand e2 => beqExpr e1 e2
  | Expr.printString e1, Expr.printString e2 => beqExpr e1 e2
  | Expr.printInt e1, Expr.printInt e2 => beqExpr e1 e2
  | Expr.externVal t1 p1 pred1, Expr.externVal t2 p2 pred2 =>
      t1 == t2 && p1 == p2 && beqSyntaxPredicate pred1 pred2
  | Expr.externFn x1 t1 ret1 eff1, Expr.externFn x2 t2 ret2 eff2 =>
      x1 == x2 && t1 == t2 && beqExternReturn ret1 ret2 && beqEffectList eff1 eff2
  | Expr.externPfn x1 t1 ret1, Expr.externPfn x2 t2 ret2 =>
      x1 == x2 && t1 == t2 && beqExternReturn ret1 ret2
  | _, _ => false
termination_by structural e1 _ => e1

def beqSyntaxPredicate : SyntaxPredicate → SyntaxPredicate → Bool
  | SyntaxPredicate.guardClosure k1 arg1 body1, SyntaxPredicate.guardClosure k2 arg2 body2 =>
      k1 == k2 && arg1 == arg2 && beqExpr body1 body2
  | SyntaxPredicate.guardOnly k1, SyntaxPredicate.guardOnly k2 => k1 == k2
  | SyntaxPredicate.noPred, SyntaxPredicate.noPred => true
  | _, _ => false
termination_by structural p1 _ => p1

def beqEffect : Effect → Effect → Bool
  | ⟨t1, p1, pred1⟩, ⟨t2, p2, pred2⟩ =>
      t1 == t2 && p1 == p2 && beqSyntaxPredicate pred1 pred2
termination_by structural ef1 _ => ef1

def beqEffectList : List Effect → List Effect → Bool
  | [], [] => true
  | e1 :: es1, e2 :: es2 => beqEffect e1 e2 && beqEffectList es1 es2
  | _, _ => false
termination_by structural efs1 _=> efs1

def beqExternReturn : ExternReturn → ExternReturn → Bool
  | ExternReturn.simple t1 p1 pred1, ExternReturn.simple t2 p2 pred2 =>
      t1 == t2 && p1 == p2 && beqSyntaxPredicate pred1 pred2
  | ExternReturn.nestedFn x1 t1 ret1 eff1, ExternReturn.nestedFn x2 t2 ret2 eff2 =>
      x1 == x2 && t1 == t2 && beqExternReturn ret1 ret2 && beqEffectList eff1 eff2
  | ExternReturn.nestedPfn x1 t1 ret1, ExternReturn.nestedPfn x2 t2 ret2 =>
      x1 == x2 && t1 == t2 && beqExternReturn ret1 ret2
  | _, _ => false
termination_by structural r1 _ => r1

end


-- Now define beqValue and beqValueVarEnv (which use beqExpr)
mutual
def beqValue : Value → Value → Bool
  | Value.num n1, Value.num n2 => n1 == n2
  | Value.bool b1, Value.bool b2 => b1 == b2
  | Value.unit, Value.unit => true
  | Value.loc l1, Value.loc l2 => l1 == l2
  | Value.str s1, Value.str s2 => s1 == s2
  | Value.closure x1 e1 env1, Value.closure x2 e2 env2 =>
      x1 == x2 && beqExpr e1 e2 && beqValueVarEnv env1 env2
  | Value.peClosure x1 e1 env1, Value.peClosure x2 e2 env2 =>
      x1 == x2 && beqExpr e1 e2 && beqValueVarEnv env1 env2
  | _, _ => false

def beqValueVarEnv : VarEnv → VarEnv → Bool
  | [], [] => true
  | (x1, v1) :: env1, (x2, v2) :: env2 =>
      x1 == x2 && beqValue v1 v2 && beqValueVarEnv env1 env2
  | _, _ => false

end


@[instance]
instance : BEq Value where
  beq := beqValue

@[instance]
instance : BEq Expr where
  beq := beqExpr

@[instance]
instance : BEq SyntaxPredicate where
  beq := beqSyntaxPredicate

@[instance]
instance : BEq Effect where
  beq := beqEffect

@[instance]
instance : BEq ExternReturn where
  beq := beqExternReturn

-- Repr instances

def reprTyp : Typ → Nat → Std.Format
  | Typ.int, _ => "Typ.int"
  | Typ.bool, _ => "Typ.bool"
  | Typ.unit, _ => "Typ.unit"
  | Typ.ref t, _ => s!"Typ.ref {reprTyp t 0}"
  | Typ.arrow t1 t2, _ => s!"Typ.arrow {reprTyp t1 0} {reprTyp t2 0}"
  | Typ.string , _ => s!"Typ.string"

-- Manual Repr instances (mutual recursion needed)
mutual

def reprValue : Value → Nat → Std.Format
  | Value.num n, _ => s!"Value.num {repr n}"
  | Value.bool b, _ => s!"Value.bool {repr b}"
  | Value.unit, _ => "Value.unit"
  | Value.str s , _ => s!"Value.str " ++ s
  | Value.loc l, _ => s!"Value.loc {repr l}"
  | Value.closure x _ _, _ => s!"Value.closure {repr x} <expr> <env>"
  | Value.peClosure x _ _, _ => s!"Value.peClosure {repr x} <expr> <env>"

def reprExpr : Expr → Nat → Std.Format
  | Expr.unit, _ => "Expr.unit"
  | Expr.str s , _ => s!"Expr.string {s} "
  | Expr.num n, _ => s!"Expr.num {repr n}"
  | Expr.bool b, _ => s!"Expr.bool {repr b}"
  | Expr.var x, _ => s!"Expr.var {repr x}"
  | Expr.op e1 op e2, _ => s!"Expr.op ({reprExpr e1 0}) {repr op} ({reprExpr e2 0})"
  | Expr.unaryop opname e, _ => s!"Expr.unaryop {repr opname} ({reprExpr e 0})"
  | Expr.ite e1 e2 e3, _ => s!"Expr.ite ({reprExpr e1 0}) ({reprExpr e2 0}) ({reprExpr e3 0})"
  | Expr.newRef e, _ => s!"Expr.newRef ({reprExpr e 0})"
  | Expr.assign e1 e2, _ => s!"Expr.assign ({reprExpr e1 0}) ({reprExpr e2 0})"
  | Expr.deref e, _ => s!"Expr.deref ({reprExpr e 0})"
  | Expr.seq e1 e2, _ => s!"Expr.seq ({reprExpr e1 0}) ({reprExpr e2 0})"
  | Expr.kwhile e1 e2, _ => s!"Expr.kwhile ({reprExpr e1 0}) ({reprExpr e2 0})"
  | Expr.vlet x e1 e2, _ => s!"Expr.vlet {repr x} ({reprExpr e1 0}) ({reprExpr e2 0})"
  | Expr.fn x t1 e t2, _ => s!"Expr.fn {repr x} : {repr t1} => ({reprExpr e 0}) : {repr t2}"
  | Expr.pfn x t1 e t2, _ => s!"Expr.pfn {repr x} : {repr t1} => ({reprExpr e 0}) : {repr t2}"
  | Expr.app e1 e2, _ => s!"Expr.app ({reprExpr e1 0}) ({reprExpr e2 0})"
  | Expr.rand e, _ => s!"Expr.rand ({reprExpr e 0})"
  | Expr.frand e, _ => s!"Expr.frand ({reprExpr e 0})"
  | Expr.printString e, _ => s!"Expr.printString ({reprExpr e 0})"
  | Expr.printInt e, _  => s!"Expr.printInt ({reprExpr e 0})"
  | Expr.externVal t p _pred, _ => s!"Expr.externVal {repr t} {repr p} <pred>"
  | Expr.externFn x t _ret _eff, _ => s!"Expr.externFn {repr x} : {repr t} <retspec> <effects>"
  | Expr.externPfn x t _ret, _ => s!"Expr.externPfn {repr x} : {repr t} <retspec>"

end

-- Repr functions for extern types (defined separately after reprExpr)
def reprSyntaxPredicate : SyntaxPredicate → Nat → Std.Format
  | SyntaxPredicate.guardClosure tag arg _body, _ =>
      s!"SyntaxPredicate.guardClosure {repr tag} {repr arg} <body>"
  | SyntaxPredicate.guardOnly tag, _ =>
      s!"SyntaxPredicate.guardOnly {repr tag}"
  | SyntaxPredicate.noPred, _ =>
      "SyntaxPredicate.noPred"

def reprEffect : Effect → Nat → Std.Format
  | ⟨target, poison, pred⟩, _ =>
      s!"Effect {repr target} {repr poison} {reprSyntaxPredicate pred 0}"

def reprExternReturn : ExternReturn → Nat → Std.Format
  | ExternReturn.simple typ poison pred, _ =>
      s!"ExternReturn.simple {repr typ} {repr poison} {reprSyntaxPredicate pred 0}"
  | ExternReturn.nestedFn x typ ret _eff, _ =>
      s!"ExternReturn.nestedFn {repr x} {repr typ} {reprExternReturn ret 0} <effects>"
  | ExternReturn.nestedPfn x typ ret, _ =>
      s!"ExternReturn.nestedPfn {repr x} {repr typ} {reprExternReturn ret 0}"

@[instance]
instance : Repr Value where
  reprPrec := reprValue

@[instance]
instance : Repr Expr where
  reprPrec := reprExpr

@[instance]
instance : Repr SyntaxPredicate where
  reprPrec := reprSyntaxPredicate

@[instance]
instance : Repr Effect where
  reprPrec := reprEffect

@[instance]
instance : Repr ExternReturn where
  reprPrec := reprExternReturn

-- Note: We cannot convert arbitrary values to expressions
-- Only literals (num, bool, unit) can appear in both
-- Locations and closures are runtime-only

-- Helper function to convert string to type
def strToBasicType (str : String) : Except String Typ :=
 match str with
 | "int" => .ok Typ.int
 | "bool" => .ok Typ.bool
 | "unit" => .ok Typ.unit
 | "string" => .ok Typ.string
 | _ => .error ("Invalid type annotation : " ++ str)


@[instance]
instance : ToString Typ where
  toString t := Std.Format.pretty (repr t)

@[instance]
instance : ToString Value where
  toString v := Std.Format.pretty (repr v)


@[instance]
instance : ToString Op where
  toString op := Std.Format.pretty (repr op)

@[instance]
instance : ToString UnaryOp where
  toString opname := Std.Format.pretty (repr opname)

@[instance]
instance : ToString Expr where
  toString e := Std.Format.pretty (repr e)


 -- Helper function to print the type of Value
def ValueToTypeString (val : Value) : String :=
  match val with
    | Value.num _  => "number"
    | Value.bool _ => "boolean"
    | Value.unit   => "unit"
    | Value.loc _  => "location"
    | Value.closure _ _ _   => "function"
    | Value.peClosure _ _ _ => "pure function"
    | Value.str _  => "string"

-- Poison flag
abbrev Poison := Bool

-- Predicate expressions (subset of expressions that can appear in predicates)
inductive PExpr : Type where
  | unit : PExpr                                   -- unit
  | num : Int → PExpr                              -- n
  | bool : Bool → PExpr                            -- b
  | str : String → PExpr                           -- string
  | var : Name → PExpr                             -- x
  | op : PExpr → Op → PExpr → PExpr                -- e1 op e2
  | unaryop :  UnaryOp → PExpr → PExpr             -- e op
  | ite : PExpr → PExpr → PExpr → PExpr            -- if e1 then e2 else e3
  | deref : PExpr → PExpr                          -- ! e
  | vlet : Name → PExpr → PExpr → PExpr            -- let x : T = e1 in e2
  | app : PExpr → PExpr → PExpr                    -- e1 e2

-- Use mutual block to define interdependent types
mutual

-- Predicate type matching OTT specification exactly
-- Corresponds to predicate, P in OTT:
--   | guard k pred_closure pcl  -- guardClosure
--   | guard k                   -- guardOnly
--   | no_pred                   -- noPred
inductive Predicate : Type where
  | guardClosure : Tag → Name → PExpr → List (Name × QTyp) → Predicate
  | guardOnly : Tag → Predicate
  | noPred : Predicate

-- Qualified type structure
structure QTyp where
  etyp : ETyp
  poison : Poison
  pred : Predicate

-- Separate typing closures for impure and pure functions
inductive FnTClosure : Type where
  | regular : Name → Expr → List (Name × QTyp) → FnTClosure
  | extern : Name → ExternReturn → List Effect → List (Name × QTyp) → FnTClosure

inductive PFnTClosure : Type where
  | regular : Name → PExpr → List (Name × QTyp) → PFnTClosure
  | extern : Name → ExternReturn → List (Name × QTyp) → PFnTClosure

-- Enriched type (full type)
inductive ETyp : Type where
  | int : ETyp
  | bool : ETyp
  | unit : ETyp
  | string : ETyp
  | ref : ETyp → Address → ETyp
  | arrow : Typ → Typ → Poison → FnTClosure → ETyp
  | parrow : Typ → Typ → Poison → PFnTClosure → ETyp

end

-- Variable typing environment (σ in the Ott spec) Because we use it in a
-- mutually inductive type above which requires types you're defining must be
-- strictly positive and may only appear in constructors you're declaring in
-- that same mutual block we could not use Std.HashMap. Instead we use an assoc
-- list of key-value pairs.
abbrev VarTypeEnv := List (Name × QTyp)

namespace VarTypeEnv

-- helper function to lookup a variable in the variable typing environment
@[inline] def lookup (env : VarTypeEnv) (x : Name) : Option QTyp :=
  List.lookup x env

-- helper function to update a variable in the variable typing environment the
-- implementation is not very efficient as mappings with existing keys are just
-- added to the front of the list. However this is sound, as lookupVarEnv always
-- returns the first mapping with a given key.
@[inline] def update (env : VarTypeEnv) (x : Name) (qt : QTyp) : VarTypeEnv :=
  (x, qt) :: env

/-- `env` contains a binding for `x`. -/
def hasKey (env : VarTypeEnv) (x : Name) : Prop :=
  env.lookup x ≠ none

end VarTypeEnv

-- Manual Repr instances for mutual types

mutual

partial def reprPExpr : PExpr → Nat → Std.Format
  | PExpr.unit, _ => "PExpr.unit"
  | PExpr.num n, _ => s!"PExpr.num {repr n}"
  | PExpr.bool b, _ => s!"PExpr.bool {repr b}"
  | PExpr.str s, _ => s!"PExpr.str " ++ s
  | PExpr.var x, _ => s!"PExpr.var {repr x}"
  | PExpr.op e1 op e2, _ => s!"PExpr.op ({reprPExpr e1 0}) {repr op} ({reprPExpr e2 0})"
  | PExpr.unaryop opname e, _ => s!"PExpr.unaryop {repr opname} ({reprPExpr e 0})"
  | PExpr.ite e1 e2 e3, _ => s!"PExpr.ite ({reprPExpr e1 0}) ({reprPExpr e2 0}) ({reprPExpr e3 0})"
  | PExpr.deref e, _ => s!"PExpr.deref ({reprPExpr e 0})"
  | PExpr.vlet x e1 e2, _ => s!"PExpr.vlet {repr x} ({reprPExpr e1 0}) ({reprPExpr e2 0})"
  | PExpr.app e1 e2, _ => s!"PExpr.app ({reprPExpr e1 0}) ({reprPExpr e2 0})"

partial def reprFnTClosure : FnTClosure → Nat → Std.Format
  | FnTClosure.regular x _ _ , _ => s!"FnTClosure.regular {repr x} <expr>"
  | FnTClosure.extern x _ _ _, _ => s!"FnTClosure.extern {repr x} <retspec> <effects>"

partial def reprPFnTClosure : PFnTClosure → Nat → Std.Format
  | PFnTClosure.regular x _ _ , _ => s!"PFnTClosure.regular {repr x} <pexpr>"
  | PFnTClosure.extern x _ _, _ => s!"PFnTClosure.extern {repr x} <retspec>"

partial def reprETyp : ETyp → Nat → Std.Format
  | ETyp.int, _ => "ETyp.int"
  | ETyp.bool, _ => "ETyp.bool"
  | ETyp.unit, _ => "ETyp.unit"
  | ETyp.string , _ => "ETyp.string"
  | ETyp.ref t l, _ => s!"ETyp.ref {reprETyp t 0} {repr l}"
  | ETyp.arrow st1 st2 p tcl, _ => s!"ETyp.arrow {reprTyp st1 0} {reprTyp st2 0} {repr p} {reprFnTClosure tcl 0}"
  | ETyp.parrow st1 st2 p tcl, _ => s!"ETyp.parrow {reprTyp st1 0} {reprTyp st2 0} {repr p} {reprPFnTClosure tcl 0}"

partial def reprVarEnv (env: VarTypeEnv) (_:Nat): Std.Format :=
    Std.Format.text "[" ++
    Std.Format.joinSep (env.map (fun (x, qt) => s!"({repr x}, {reprQTyp qt 0})")) (Std.Format.text ", ") ++
    Std.Format.text "]"

partial def reprPredicate : Predicate → Nat → Std.Format
  | Predicate.guardClosure tag arg_name pred_body var_env, _ =>
    s!"Predicate.guardClosure {repr tag} {repr arg_name} {reprPExpr pred_body 0} {reprVarEnv var_env 0}"
  | Predicate.guardOnly tag, _ =>
    s!"Predicate.guardOnly {repr tag}"
  | Predicate.noPred, _ =>
    "Predicate.noPred"

partial def reprQTyp : QTyp → Nat → Std.Format
  | QTyp.mk etyp poison pred, _ =>
    s!"QTyp.mk {reprETyp etyp 0} {repr poison} {reprPredicate pred 0}"

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


-- Manual BEq instance for PExpr (must be defined first as it's used in the mutual block)
def beqPExpr : PExpr → PExpr → Bool
  | .unit, .unit => true
  | .num n1, .num n2 => n1 == n2
  | .bool b1, .bool b2 => b1 == b2
  | .str s1, .str s2 => s1 == s2
  | .var x1, .var x2 => x1 == x2
  | .op e1 op1 e2, .op e1' op2 e2' => op1 == op2 && beqPExpr e1 e1' && beqPExpr e2 e2'
  | .unaryop op1 e1, .unaryop op2 e2 => op1 == op2 && beqPExpr e1 e2
  | .ite e1 e2 e3, .ite e1' e2' e3' => beqPExpr e1 e1' && beqPExpr e2 e2' && beqPExpr e3 e3'
  | .deref e1, .deref e2 => beqPExpr e1 e2
  | .vlet x1 e1 e2, .vlet x2 e1' e2' => x1 == x2 && beqPExpr e1 e1' && beqPExpr e2 e2'
  | .app e1 e2, .app e1' e2' => beqPExpr e1 e1' && beqPExpr e2 e2'
  | _, _ => false

instance : BEq PExpr where
  beq := beqPExpr

-- Manual BEq instances for ETyp and related types (updated to do full structural comparison)
mutual
def beqETyp : ETyp → ETyp → Bool
  | ETyp.int, ETyp.int => true
  | ETyp.bool, ETyp.bool => true
  | ETyp.unit, ETyp.unit => true
  | ETyp.string , ETyp.string => true
  | ETyp.ref t1 l1, ETyp.ref t2 l2 => beqETyp t1 t2 && l1 == l2
  | ETyp.arrow st1 st2 p1 tcl1, ETyp.arrow st1' st2' p2 tcl2 =>
    st1 == st1' && st2 == st2' && p1 == p2 && beqFnTClosure tcl1 tcl2
  | ETyp.parrow st1 st2 p1 tcl1, ETyp.parrow st1' st2' p2 tcl2 =>
    st1 == st1' && st2 == st2' && p1 == p2 && beqPFnTClosure tcl1 tcl2
  | _, _ => false

def beqFnTClosure : FnTClosure → FnTClosure → Bool
  | FnTClosure.regular x1 e1 env1, FnTClosure.regular x2 e2 env2 =>
    x1 == x2 && e1 == e2 && beqVarEnv env1 env2
  | FnTClosure.extern x1 ret1 eff1 env1, FnTClosure.extern x2 ret2 eff2 env2 =>
    x1 == x2 && beqExternReturn ret1 ret2 && beqEffectList eff1 eff2 && beqVarEnv env1 env2
  | _, _ => false

def beqPFnTClosure : PFnTClosure → PFnTClosure → Bool
  | PFnTClosure.regular x1 e1 env1, PFnTClosure.regular x2 e2 env2 =>
    x1 == x2 && e1 == e2 && beqVarEnv env1 env2
  | PFnTClosure.extern x1 ret1 env1, PFnTClosure.extern x2 ret2 env2 =>
    x1 == x2 && beqExternReturn ret1 ret2 && beqVarEnv env1 env2
  | _, _ => false

def beqVarEnv : List (Name × QTyp) → List (Name × QTyp) → Bool
  | [], [] => true
  | (x1, qt1) :: env1, (x2, qt2) :: env2 => x1 == x2 && beqQTyp qt1 qt2 && beqVarEnv env1 env2
  | _, _ => false

def beqPredicate : Predicate → Predicate → Bool
  | Predicate.guardClosure tag1 arg1 body1 env1, Predicate.guardClosure tag2 arg2 body2 env2 =>
    tag1 == tag2 && arg1 == arg2 && body1 == body2 && beqVarEnv env1 env2
  | Predicate.guardOnly tag1, Predicate.guardOnly tag2 =>
    tag1 == tag2
  | Predicate.noPred, Predicate.noPred => true
  | _, _ => false

def beqQTyp : QTyp → QTyp → Bool
  | QTyp.mk etyp1 poison1 pred1, QTyp.mk etyp2 poison2 pred2 =>
    beqETyp etyp1 etyp2 && poison1 == poison2 && beqPredicate pred1 pred2

end

instance : BEq ETyp where
  beq := beqETyp

instance : BEq FnTClosure where
  beq := beqFnTClosure

instance : BEq PFnTClosure where
  beq := beqPFnTClosure

instance : BEq Predicate where
  beq := beqPredicate

instance : BEq QTyp where
  beq := beqQTyp

-- Signature-based equality for function types (for type checking)
-- Compares only parameter type, return type, and poison flag, ignoring closure contents
-- Corresponds to the ≈ operator in the Ott specification (sig_comp)
def beqETypSignature : ETyp → ETyp → Bool
  | ETyp.int, ETyp.int => true
  | ETyp.bool, ETyp.bool => true
  | ETyp.unit, ETyp.unit => true
  | ETyp.string, ETyp.string => true
  | ETyp.ref t1 l1, ETyp.ref t2 l2 => beqETypSignature t1 t2 && l1 == l2
  | ETyp.arrow st1 st2 p1 _, ETyp.arrow st1' st2' p2 _ =>
    st1 == st1' && st2 == st2' && p1 == p2
  | ETyp.parrow st1 st2 p1 _, ETyp.parrow st1' st2' p2 _ =>
    st1 == st1' && st2 == st2' && p1 == p2
  | _, _ => false

@[instance]
instance : ToString ETyp where
  toString e := Std.Format.pretty (repr e)


@[instance]
instance : ToString QTyp where
  toString e := Std.Format.pretty (repr e)
