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
  | string : Typ
  deriving Repr, BEq

-- Operations (corresponds to operations, op in Ott)
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
  | or  : Op

  deriving Repr, BEq


mutual
-- Expressions (corresponds to e in Ott)
inductive Expr : Type where
  | unit : Expr                                 -- unit
  | num : Int → Expr                            -- n
  | bool : Bool → Expr                          -- b
  | str : String -> Expr
  | var : Name → Expr                           -- x
  | op : Expr → Op → Expr → Expr                -- e1 op e2
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
  | builtIn : builtInExpr -> Expr

-- Values (corresponds to v in Ott)
-- Note: In Ott, values are: n | b | unit | closure(x,e,r) | pe_closure(x,pe,r)
inductive Value : Type where
  | num : Int → Value           -- n
  | bool : Bool → Value         -- b
  | unit : Value                -- unit
  | str : String -> Value       -- str
  | loc : Address → Value           -- l (locations are values in the operational semantics)
  | closure : Name → Expr → (Name → Option Value) → Value      -- closure(x,e,r)
  | peClosure : Name → Expr → (Name → Option Value) → Value    -- pe_closure(x,pe,r)

-- Expression or Value type matching Ott specification
-- This is used only in the operational semantics for step results
inductive ExprOrValue : Type where
  | expr : Expr → ExprOrValue     -- expr e
  | value : Value → ExprOrValue   -- value v

-- builtInExpr (Type to represent built in expressions in poison lang)
inductive builtInExpr : Type where
  | rand  : Expr -> builtInExpr
  | frand : Expr -> builtInExpr
  | printString  : Expr -> builtInExpr
  | printInt  : Expr -> builtInExpr
end
-- Variable environment: variable name → value (function type) We do not use a
-- HashMap here, as we do for Memory, because of the Lean restriction of
-- inductive type definitions (insude pe_closure)
abbrev VarEnv := Name → Option Value

-- Note: No helper functions needed for literals since they are now direct constructors
-- Locations cannot be created as expressions - they only exist at runtime

-- Extract value from expression if it's a literal
def Expr.toValue? : Expr → Option Value
  | Expr.num n => some (Value.num n)
  | Expr.bool b => some (Value.bool b)
  | Expr.unit => some Value.unit
  | _ => none

-- Extract value from ExprOrValue if possible
def ExprOrValue.toValue? : ExprOrValue → Option Value
  | ExprOrValue.value v => some v
  | _ => none

-- Extract expression from ExprOrValue if possible
def ExprOrValue.toExpr? : ExprOrValue → Option Expr
  | ExprOrValue.expr e => some e
  | _ => none

-- BEq instances

def beqValue : Value → Value → Bool
  | Value.num n1, Value.num n2 => n1 == n2
  | Value.bool b1, Value.bool b2 => b1 == b2
  | Value.unit, Value.unit => true
  | Value.loc l1, Value.loc l2 => l1 == l2
  | Value.str s1 , Value.str s2 => s1 == s2
  | _, _ => false  -- Closures are compared by reference, not structurally

mutual

def beqExpr : Expr → Expr → Bool
  | Expr.unit, Expr.unit => true
  | Expr.num n1, Expr.num n2 => n1 == n2
  | Expr.bool b1, Expr.bool b2 => b1 == b2
  | Expr.var x1, Expr.var x2 => x1 == x2
  | Expr.op e1 op1 e2, Expr.op e1' op2 e2' => beqExpr e1 e1' && op1 == op2 && beqExpr e2 e2'
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
  | _, _ => false

def beqExprOrValue : ExprOrValue → ExprOrValue → Bool
  | ExprOrValue.expr e1, ExprOrValue.expr e2 => beqExpr e1 e2
  | ExprOrValue.value v1, ExprOrValue.value v2 => beqValue v1 v2
  | _, _ => false

end


@[instance]
instance : BEq Value where
  beq := beqValue

@[instance]
instance : BEq Expr where
  beq := beqExpr

@[instance]
instance : BEq ExprOrValue where
  beq := beqExprOrValue

-- Repr instances

def reprTyp : Typ → Nat → Std.Format
  | Typ.int, _ => "Typ.int"
  | Typ.bool, _ => "Typ.bool"
  | Typ.unit, _ => "Typ.unit"
  | Typ.ref t, _ => s!"Typ.ref {reprTyp t 0}"
  | Typ.arrow t1 t2, _ => s!"Typ.arrow {reprTyp t1 0} {reprTyp t2 0}"
  | Typ.string , _ => s!"Typ.string"

-- Manual Repr instances (mutual recursion needed due to ExprOrValue)
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
  | Expr.str s , _ => "Expr.string " ++ s
  | Expr.num n, _ => s!"Expr.num {repr n}"
  | Expr.bool b, _ => s!"Expr.bool {repr b}"
  | Expr.var x, _ => s!"Expr.var {repr x}"
  | Expr.op e1 op e2, _ => s!"Expr.op ({reprExpr e1 0}) {repr op} ({reprExpr e2 0})"
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
  | Expr.builtIn (builtInExpr.rand e),_ => s!"Expr.builtin.rand ({reprExpr e 0})"
  | Expr.builtIn (builtInExpr.frand e),_ => s!"Expr.builtin.frand ({reprExpr e 0})"
  | Expr.builtIn (builtInExpr.printString e),_ => s!"Expr.builtin.printString ({reprExpr e 0})"
  | Expr.builtIn (builtInExpr.printInt e),_  => s!"Expr.builtin.printString ({reprExpr e 0})"

def reprExprOrValue : ExprOrValue → Nat → Std.Format
  | ExprOrValue.expr e, prec => reprExpr e prec
  | ExprOrValue.value v, prec => reprValue v prec

end

@[instance]
instance : Repr Value where
  reprPrec := reprValue

@[instance]
instance : Repr Expr where
  reprPrec := reprExpr

@[instance]
instance : Repr ExprOrValue where
  reprPrec := reprExprOrValue

-- Note: We cannot convert arbitrary values to expressions
-- Only literals (num, bool, unit) can appear in both
-- Locations and closures are runtime-only

-- Helper functions to convert between types for ExprOrValue
def Value.toExprOrValue : Value → ExprOrValue
  | v => ExprOrValue.value v

def Expr.toExprOrValue : Expr → ExprOrValue
  | e => ExprOrValue.expr e

-- Helper function to convert string to type
def strToBasicType (str : String) : Except String Typ :=
 match str with
 | "int" => .ok Typ.int
 | "bool" => .ok Typ.bool
 | "unit" => .ok Typ.unit
 | "string" => .ok Typ.string
 | _ => .error ("Invalid type annotation : " ++ str)

@[instance]
instance : ToString Value where
  toString v :=
    match v with
    | Value.num n => s!"{n}"
    | Value.bool b => s!"{b}"
    | Value.unit => "()"
    | Value.str s => s!"{s}"
    | Value.loc l => s!"@{l}"
    | Value.closure x _ _ => s!"(closure {x} <expr> <env>)"
    | Value.peClosure x _ _ => s!"(peClosure {x} <expr> <env>)"


@[instance]
instance : ToString Op where
  toString op :=
    match op with
    | .add => s!"+"     -- +
    | .sub => s!"-"
    | .mul => s!"*"
    | .div => s!"-"
    | .gte => s!">="     -- >=
    | .lte => s!"<="
    | .gt  => s!">"
    | .lt  => s!"<"
    | .eq  => s!"=="
    | .or  => s!"|"
    | .and => s!"&"


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
