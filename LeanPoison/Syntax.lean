-- Core definitions for Poison language (aligned with poison-lang.ott)

import Std.Data.HashMap
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
  deriving Repr, BEq

-- Operations (corresponds to operations, op in Ott)
inductive Op : Type where
  | add : Op      -- +
  | gte : Op      -- >=
  deriving Repr, BEq

-- Mutual inductive definitions for Value and Expr
mutual

-- Values (corresponds to v in Ott)
-- Note: In Ott, values are: n | b | unit | closure(x,e,r) | pe_closure(x,pe,r)
inductive Value : Type where
  | num : Nat → Value           -- n
  | bool : Bool → Value         -- b
  | unit : Value                -- unit
  | loc : Address → Value           -- l (locations are values in the operational semantics)
  | closure : Name → Expr → (Name → Option Value) → Value      -- closure(x,e,r)
  | peClosure : Name → Expr → (Name → Option Value) → Value    -- pe_closure(x,pe,r)

-- Expressions (corresponds to e in Ott)
inductive Expr : Type where
  | value : Value → Expr                          -- Values embedded in expressions
  | var : Name → Expr                           -- x
  | op : Expr → Op → Expr → Expr                  -- e1 op e2
  | ite : Expr → Expr → Expr → Expr               -- if e1 then e2 else e3
  | newRef : Expr → Expr                          -- ref e
  | assign : Expr → Expr → Expr                   -- e1 := e2
  | deref : Expr → Expr                           -- ! e
  | seq : Expr → Expr → Expr                      -- e1 ; e2
  | while : Expr → Expr → Expr                    -- while e1 do e2
  | let : Name → Expr → Expr → Expr               -- let x = e1 in e2 (no type annotation)
  | fn : Name → Typ → Expr → Typ → Expr           -- fn x : ST1 => e : ST2
  | pfn : Name → Typ → Expr → Typ → Expr          -- pfn x : ST1 => pe : ST2
  | app : Expr → Expr → Expr                       -- e1 e2

end

-- Variable environment: variable name → value (function type) We do not use a
-- HashMap here, as we do for Memory, because of the Lean restriction of
-- inductive type definitions (insude pe_closure)
abbrev VarEnv := Name → Option Value

-- Helper pattern synonyms for common value expressions
def Expr.num (n : Nat) : Expr := Expr.value (Value.num n)
def Expr.bool (b : Bool) : Expr := Expr.value (Value.bool b)
def Expr.unit : Expr := Expr.value Value.unit
def Expr.loc (l : Address) : Expr := Expr.value (Value.loc l)

-- Extract value from expression if possible
def Expr.toValue? : Expr → Option Value
  | Expr.value v => some v
  | _ => none

-- BEq instances
mutual

def beqValue : Value → Value → Bool
  | Value.num n1, Value.num n2 => n1 == n2
  | Value.bool b1, Value.bool b2 => b1 == b2
  | Value.unit, Value.unit => true
  | Value.loc l1, Value.loc l2 => l1 == l2
  | _, _ => false  -- Closures are compared by reference, not structurally

def beqExpr : Expr → Expr → Bool
  | Expr.value v1, Expr.value v2 => beqValue v1 v2
  | Expr.var x1, Expr.var x2 => x1 == x2
  | Expr.op e1 op1 e2, Expr.op e1' op2 e2' => beqExpr e1 e1' && op1 == op2 && beqExpr e2 e2'
  | Expr.ite e1 e2 e3, Expr.ite e1' e2' e3' => beqExpr e1 e1' && beqExpr e2 e2' && beqExpr e3 e3'
  | Expr.newRef e1, Expr.newRef e2 => beqExpr e1 e2
  | Expr.assign e1 e2, Expr.assign e1' e2' => beqExpr e1 e1' && beqExpr e2 e2'
  | Expr.deref e1, Expr.deref e2 => beqExpr e1 e2
  | Expr.seq e1 e2, Expr.seq e1' e2' => beqExpr e1 e1' && beqExpr e2 e2'
  | Expr.while e1 e2, Expr.while e1' e2' => beqExpr e1 e1' && beqExpr e2 e2'
  | Expr.let x1 e1 e2, Expr.let x2 e1' e2' => x1 == x2 && beqExpr e1 e1' && beqExpr e2 e2'
  | Expr.fn x1 t1 e1 t1', Expr.fn x2 t2 e2 t2' => x1 == x2 && t1 == t2 && beqExpr e1 e2 && t1' == t2'
  | Expr.pfn x1 t1 e1 t1', Expr.pfn x2 t2 e2 t2' => x1 == x2 && t1 == t2 && beqExpr e1 e2 && t1' == t2'
  | Expr.app e1 e2, Expr.app e1' e2' => beqExpr e1 e1' && beqExpr e2 e2'
  | _, _ => false

end

@[instance]
instance : BEq Value where
  beq := beqValue

@[instance]
instance : BEq Expr where
  beq := beqExpr

-- Repr instances

def reprTyp : Typ → Nat → Std.Format
  | Typ.int, _ => "Typ.int"
  | Typ.bool, _ => "Typ.bool"
  | Typ.unit, _ => "Typ.unit"
  | Typ.ref t, _ => s!"Typ.ref {reprTyp t 0}"
  | Typ.arrow t1 t2, _ => s!"Typ.arrow {reprTyp t1 0} {reprTyp t2 0}"

-- Manual Repr instance for Value (since closures contain functions)
def reprValue : Value → Nat → Std.Format
  | Value.num n, _ => s!"Value.num {repr n}"
  | Value.bool b, _ => s!"Value.bool {repr b}"
  | Value.unit, _ => "Value.unit"
  | Value.loc l, _ => s!"Value.loc {repr l}"
  | Value.closure x _ _, _ => s!"Value.closure {repr x} <expr> <env>"
  | Value.peClosure x _ _, _ => s!"Value.peClosure {repr x} <expr> <env>"

def reprExpr : Expr → Nat → Std.Format
  | Expr.value v, prec => reprValue v prec
  | Expr.var x, _ => s!"Expr.var {repr x}"
  | Expr.op e1 op e2, _ => s!"Expr.op ({reprExpr e1 0}) {repr op} ({reprExpr e2 0})"
  | Expr.ite e1 e2 e3, _ => s!"Expr.ite ({reprExpr e1 0}) ({reprExpr e2 0}) ({reprExpr e3 0})"
  | Expr.newRef e, _ => s!"Expr.newRef ({reprExpr e 0})"
  | Expr.assign e1 e2, _ => s!"Expr.assign ({reprExpr e1 0}) ({reprExpr e2 0})"
  | Expr.deref e, _ => s!"Expr.deref ({reprExpr e 0})"
  | Expr.seq e1 e2, _ => s!"Expr.seq ({reprExpr e1 0}) ({reprExpr e2 0})"
  | Expr.while e1 e2, _ => s!"Expr.while ({reprExpr e1 0}) ({reprExpr e2 0})"
  | Expr.let x e1 e2, _ => s!"Expr.let {repr x} ({reprExpr e1 0}) ({reprExpr e2 0})"
  | Expr.fn x t1 e t2, _ => s!"Expr.fn {repr x} : {repr t1} => ({reprExpr e 0}) : {repr t2}"
  | Expr.pfn x t1 e t2, _ => s!"Expr.pfn {repr x} : {repr t1} => ({reprExpr e 0}) : {repr t2}"
  | Expr.app e1 e2, _ => s!"Expr.app ({reprExpr e1 0}) ({reprExpr e2 0})"

@[instance]
instance : Repr Value where
  reprPrec := reprValue

@[instance]
instance : Repr Expr where
  reprPrec := reprExpr

-- Helper functions to convert values to expressions
def Value.toExpr : Value → Expr
  | v => Expr.value v

@[instance]
instance : ToString Value where
  toString v :=
    match v with
    | Value.num n => s!"{n}"
    | Value.bool b => s!"{b}"
    | Value.unit => "()"
    | Value.loc l => s!"@{l}"
    | Value.closure x _ _ => s!"(closure {x} <expr> <env>)"
    | Value.peClosure x _ _ => s!"(peClosure {x} <expr> <env>)"
