-- Core definitions for Poison language (aligned with poison-lang.ott)

import Std.Data.ExtTreeSet
import Std.Data.ExtTreeMap
import Mathlib.Tactic

open Std

abbrev Address := Nat
abbrev Loc := Nat
abbrev LocSet := ExtTreeSet Loc

namespace LocSet

@[inline] def empty : LocSet := ExtTreeSet.empty

@[inline] def singleton (l : Loc) : LocSet :=
  (∅ : LocSet).insert l

@[inline] def union (s₁ s₂ : LocSet) : LocSet :=
  ExtTreeSet.union s₁ s₂

@[inline] def fromList (ls : List Loc) : LocSet :=
  ExtTreeSet.ofList ls

@[inline] def fold (s : LocSet) (init : β) (f : β → Loc → β) : β :=
  ExtTreeSet.foldl (f := fun acc l => f acc l) (init := init) s

@[inline] def foldM [Monad m] [LawfulMonad m] (s : LocSet) (init : β) (f : β → Loc → m β) : m β :=
  ExtTreeSet.foldlM (f := fun acc l => f acc l) (init := init) s

@[inline] def any (s : LocSet) (p : Loc → Bool) : Bool :=
  ExtTreeSet.any s p

@[inline] def anyM [Monad m] [LawfulMonad m] (s : LocSet) (p : Loc → m Bool) : m Bool :=
  foldM s false (fun acc l => do
    if acc then
      pure true
    else
      p l)

end LocSet

instance : BEq LocSet where
  beq s t := (ExtTreeSet.toList s) == (ExtTreeSet.toList t)

abbrev Name := String

namespace LeanPoison

end LeanPoison

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


-- TagIndex definitions and instaces requiered for ExtTreeMap TagIndex Tag

/-- Symbolic tag index used in extern specifications.
    At each extern use site, `TagIndex` values are collected and mapped to fresh
    concrete `Tag`s, ensuring that distinct calls get independent tags. -/
structure TagIndex where
  val : Nat
  deriving Repr, DecidableEq, Hashable

-- BEq via DecidableEq so that of_decide_eq_true works in proofs
instance : BEq TagIndex where
  beq a b := decide (a = b)

instance : LawfulBEq TagIndex where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl

/-- Ord instance for TagIndex delegating to Nat's comparison. -/
@[reducible] instance : Ord TagIndex where
  compare a b := compare a.val b.val

instance : OrientedCmp (compare : TagIndex → TagIndex → Ordering) where
  eq_swap {a b} := by
    show compare a.val b.val = (compare b.val a.val).swap
    exact OrientedCmp.eq_swap (α := Nat)

instance : ReflCmp (compare : TagIndex → TagIndex → Ordering) where
  compare_self {a} := by
    show compare a.val a.val = Ordering.eq
    exact ReflCmp.compare_self

instance : LawfulEqCmp (compare : TagIndex → TagIndex → Ordering) where
  eq_of_compare {a b} h := by
    have hval : a.val = b.val := by
      have hcmp : compare a.val b.val = Ordering.eq := h
      exact LawfulEqCmp.eq_of_compare hcmp
    cases a with
    | mk aval =>
      cases b with
      | mk bval =>
        simp at hval
        subst bval
        rfl

instance : TransCmp (compare : TagIndex → TagIndex → Ordering) where
  isLE_trans {a b c} (h1 : (compare a.val b.val).isLE = true)
      (h2 : (compare b.val c.val).isLE = true) := by
    show (compare a.val c.val).isLE = true
    exact TransCmp.isLE_trans (α := Nat) h1 h2


/-- Map from symbolic `TagIndex` to fresh concrete `Tag`s allocated at an
    extern use site. Used by `collectAndAllocExternTags` / `resolveSyntaxPred`
    and by the FR contract surface for externs. -/
abbrev TagMapping := ExtTreeMap TagIndex Tag compare

-- Effect target: a named variable whose memory location is affected
inductive EffectTarget where
  | namedVar : Name → EffectTarget      -- !varname
  deriving Repr, BEq

/-- Extern identifier: author-chosen runtime handle assigned at each extern
    declaration site (both top-level and nested). See
    `doc/ffi-proposal.md`. -/
abbrev ExternId := Nat

mutual

-- Syntax-level predicate (simplified, no captured environment)
-- Parser creates these with symbolic TagIndex values.
-- At each extern use site, the typechecker allocates fresh concrete Tags
-- and resolves TagIndex → Tag, ensuring independent tags per call.
inductive SyntaxPredicate : Type where
  | guardClosure: TagIndex → Name → Expr → SyntaxPredicate  -- symbolic tag index, arg name, predicate body (as Expr)
  | guardOnly : TagIndex → SyntaxPredicate
  | noPred : SyntaxPredicate

-- Effect specification for impure externs (uses SyntaxPredicate)
structure Effect where
  target : EffectTarget
  poison : Bool  -- true for "poisoned", false for "clean"
  pred : SyntaxPredicate

-- Return specification for extern functions (simple or nested)
-- Nested variants carry their own `ExternId`; `simple` does not (the id lives
-- on the enclosing top-level extern AST node).
inductive ExternReturn where
  | simple : Typ → Bool → SyntaxPredicate → ExternReturn
  | nestedFn : ExternId → Name → Typ → ExternReturn → List Effect → ExternReturn
  | nestedPfn : ExternId → Name → Typ → ExternReturn → ExternReturn

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
  | vlet : Name → Expr → Expr → Expr             -- let x = e1 in e2
  | fn : Name → Typ → Expr → Typ → Expr         -- fn x : ST1 => e : ST2
  | pfn : Name → Typ → Expr → Typ → Expr        -- pfn x : ST1 => pe : ST2
  | app : Expr → Expr → Expr                    -- e1 e2
  /- extern declarations: each carries a mandatory `ExternId` identifier -/
  | externVal : ExternId → Typ → Bool → SyntaxPredicate → Expr
  | externFn : ExternId → Name → Typ → ExternReturn → List Effect → Expr
  | externPfn : ExternId → Name → Typ → ExternReturn → Expr

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


-- Variable environment: List (name × value). We do not use ExtTreeMap
-- here, as we do for Memory, because of the Lean restriction of
-- inductive type definitions (inside pe_closure)
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
  | Expr.vlet x1 e1 e2, Expr.vlet x2 e1' e2' => x1 == x2 && beqExpr e1 e1' && beqExpr e2 e2'
  | Expr.fn x1 t1 e1 t1', Expr.fn x2 t2 e2 t2' => x1 == x2 && t1 == t2 && beqExpr e1 e2 && t1' == t2'
  | Expr.pfn x1 t1 e1 t1', Expr.pfn x2 t2 e2 t2' => x1 == x2 && t1 == t2 && beqExpr e1 e2 && t1' == t2'
  | Expr.app e1 e2, Expr.app e1' e2' => beqExpr e1 e1' && beqExpr e2 e2'
  | Expr.externVal id1 t1 p1 pred1, Expr.externVal id2 t2 p2 pred2 =>
      id1 == id2 && t1 == t2 && p1 == p2 && beqSyntaxPredicate pred1 pred2
  | Expr.externFn id1 x1 t1 ret1 eff1, Expr.externFn id2 x2 t2 ret2 eff2 =>
      id1 == id2 && x1 == x2 && t1 == t2 && beqExternReturn ret1 ret2 && beqEffectList eff1 eff2
  | Expr.externPfn id1 x1 t1 ret1, Expr.externPfn id2 x2 t2 ret2 =>
      id1 == id2 && x1 == x2 && t1 == t2 && beqExternReturn ret1 ret2
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
  | ExternReturn.nestedFn id1 x1 t1 ret1 eff1, ExternReturn.nestedFn id2 x2 t2 ret2 eff2 =>
      id1 == id2 && x1 == x2 && t1 == t2 && beqExternReturn ret1 ret2 && beqEffectList eff1 eff2
  | ExternReturn.nestedPfn id1 x1 t1 ret1, ExternReturn.nestedPfn id2 x2 t2 ret2 =>
      id1 == id2 && x1 == x2 && t1 == t2 && beqExternReturn ret1 ret2
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

def PExpr.usesArg (x : Name) : PExpr → Bool
  | .var y        => x == y
  | .op p _ q     => usesArg x p || usesArg x q
  | .unaryop _ p  => usesArg x p
  | .ite p q r    => usesArg x p || usesArg x q || usesArg x r
  | .deref p      => usesArg x p
  | .vlet y p q   => usesArg x p || (if y == x then false else usesArg x q)
  | .app p q      => usesArg x p || usesArg x q
  | _             => false

-- Pure conversion: returns none if the expression is not a pure expression.
def Expr.toPExpr? : Expr → Option PExpr
  | Expr.unit => some .unit
  | Expr.num n => some (.num n)
  | Expr.bool b => some (.bool b)
  | Expr.str s => some (.str s)
  | Expr.var x => some (.var x)
  | Expr.op e1 opName e2 => do
      let pe1 ← Expr.toPExpr? e1
      let pe2 ← Expr.toPExpr? e2
      some (.op pe1 opName pe2)
  | Expr.unaryop opName e => do
      let pe ← Expr.toPExpr? e
      some (.unaryop opName pe)
  | Expr.ite e1 e2 e3 => do
      let pe1 ← Expr.toPExpr? e1
      let pe2 ← Expr.toPExpr? e2
      let pe3 ← Expr.toPExpr? e3
      some (.ite pe1 pe2 pe3)
  | Expr.deref e => do
      let pe ← Expr.toPExpr? e
      some (.deref pe)
  | Expr.vlet x e1 e2 => do
      let pe1 ← Expr.toPExpr? e1
      let pe2 ← Expr.toPExpr? e2
      some (.vlet x pe1 pe2)
  | Expr.app e1 e2 => do
      let pe1 ← Expr.toPExpr? e1
      let pe2 ← Expr.toPExpr? e2
      some (.app pe1 pe2)
  | _ => none

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
-- Arrow types now carry non-empty lists of closures (merged typing closures)
-- to support flow-insensitive joins at conditionals
inductive ETyp : Type where
  | int : ETyp
  | bool : ETyp
  | unit : ETyp
  | string : ETyp
  | ref : LocSet → ETyp
  | arrow : Typ → Typ → Poison → List FnTClosure → ETyp
  | parrow : Typ → Typ → Poison → List PFnTClosure → ETyp

end

namespace ETyp

/-- Check if an enriched type is an arrow type. -/
def isArrow : ETyp → Bool
  | .arrow _ _ _ _ => true
  | _ => false

/-- Check if an enriched type is a parrow (pure arrow) type. -/
def isParrow : ETyp → Bool
  | .parrow _ _ _ _ => true
  | _ => false

/-- Check if an enriched type is a function type (either arrow or parrow). -/
def isFunctionType (t : ETyp) : Bool :=
  t.isArrow || t.isParrow

end ETyp

-- Captured variable environments are association lists.
abbrev CapturedVarEnv := List (Name × QTyp)

namespace CapturedVarEnv

-- helper function to lookup a variable in a captured environment
@[inline] def lookup (env : CapturedVarEnv) (x : Name) : Option QTyp :=
  List.lookup x env

-- helper function to update a captured environment; newest mapping wins
@[inline] def update (env : CapturedVarEnv) (x : Name) (qt : QTyp) : CapturedVarEnv :=
  (x, qt) :: env

/-- `env` contains a binding for `x`. -/
def hasKey (env : CapturedVarEnv) (x : Name) : Prop :=
  env.lookup x ≠ none

end CapturedVarEnv

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
--
-- IMPORTANT NOTE on closure list equality:
-- Closure lists semantically represent SETS (order-independent, no duplicates).
-- However, implementing true set equality in this mutual recursion would require
-- partial functions, which is not acceptable for core type system operations.
--
-- Our solution:
-- 1. Closure lists use ORDERED comparison in BEq (for termination)
-- 2. Merge functions (mergeFnTClosures/mergePFnTClosures) maintain CONSISTENT ordering
--    by deduplicating and preserving first-occurrence order
-- 3. The type checker uses beqETypSignature which IGNORES closures entirely
--
-- This means [a,b] ≠ [b,a] in BEq, but this is acceptable because:
-- - Type checking (the critical path) ignores closure order via beqETypSignature
-- - Merge operations produce consistent ordering
-- - The semantic meaning (sets) is preserved through deduplication
--
mutual

def beqFnTClosureList : List FnTClosure → List FnTClosure → Bool
  | [], [] => true
  | tcl1 :: tcls1, tcl2 :: tcls2 => beqFnTClosure tcl1 tcl2 && beqFnTClosureList tcls1 tcls2
  | _, _ => false

def beqPFnTClosureList : List PFnTClosure → List PFnTClosure → Bool
  | [], [] => true
  | tcl1 :: tcls1, tcl2 :: tcls2 => beqPFnTClosure tcl1 tcl2 && beqPFnTClosureList tcls1 tcls2
  | _, _ => false

def beqETyp : ETyp → ETyp → Bool
  | ETyp.int, ETyp.int => true
  | ETyp.bool, ETyp.bool => true
  | ETyp.unit, ETyp.unit => true
  | ETyp.string , ETyp.string => true
  | ETyp.ref ls1, ETyp.ref ls2 => ls1 == ls2
  | ETyp.arrow st1 st2 p1 tcls1, ETyp.arrow st1' st2' p2 tcls2 =>
    st1 == st1' && st2 == st2' && p1 == p2 && beqFnTClosureList tcls1 tcls2
  | ETyp.parrow st1 st2 p1 tcls1, ETyp.parrow st1' st2' p2 tcls2 =>
    st1 == st1' && st2 == st2' && p1 == p2 && beqPFnTClosureList tcls1 tcls2
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

def beqVarEnv : CapturedVarEnv → CapturedVarEnv → Bool
  | [], [] => true
  | (x1, qt1) :: env1, (x2, qt2) :: env2 =>
      x1 == x2 && beqQTyp qt1 qt2 && beqVarEnv env1 env2
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
-- Signature compatibility check for ETyp.
-- Corresponds to the ≈ operator in the Ott specification (sig_comp).
-- This checks if two enriched types are signature-compatible:
-- same shape, ignoring closure sets and arrow-internal poison.
def beqETypSignature : ETyp → ETyp → Bool
  | ETyp.int, ETyp.int => true
  | ETyp.bool, ETyp.bool => true
  | ETyp.unit, ETyp.unit => true
  | ETyp.string, ETyp.string => true
  | ETyp.ref _, ETyp.ref _ => true
  | ETyp.arrow st1 st2 _ _, ETyp.arrow st1' st2' _ _ =>
    st1 == st1' && st2 == st2'
  | ETyp.parrow st1 st2 _ _, ETyp.parrow st1' st2' _ _ =>
    st1 == st1' && st2 == st2'
  | _, _ => false

-- Helper functions for merged typing closures
-- Closure lists semantically represent SETS: order-independent, no duplicates
--
-- Implementation approach:
-- 1. Merge functions (mergeFnTClosures, mergePFnTClosures) deduplicate and maintain
--    consistent first-occurrence ordering
-- 2. BEq uses ordered comparison (not true set equality) to avoid partial functions
-- 3. Type checking uses beqETypSignature which ignores closures entirely
--
-- Trade-off: [a,b] ≠ [b,a] in BEq, but this doesn't affect correctness because:
-- - The critical type checking operations use beqETypSignature (ignores closures)
-- - Merge operations produce consistent ordering
-- - Deduplication ensures no duplicates

/-- Merge two lists of FnTClosure as sets, removing duplicates.
    The result is the union of tcls1 and tcls2, with duplicates removed.
    Order follows the input lists but is semantically irrelevant (sets). -/
def mergeFnTClosures (tcls1 tcls2 : List FnTClosure) : List FnTClosure :=
  -- Start with tcls1 (deduplicated), then add elements from tcls2 that aren't already present
  let withTcls1 := tcls1.foldl (fun acc tcl => if acc.contains tcl then acc else acc ++ [tcl]) []
  tcls2.foldl (fun acc tcl => if acc.contains tcl then acc else acc ++ [tcl]) withTcls1

/-- Merge two lists of PFnTClosure as sets, removing duplicates.
    The result is the union of tcls1 and tcls2, with duplicates removed.
    Order follows the input lists but is semantically irrelevant (sets). -/
def mergePFnTClosures (tcls1 tcls2 : List PFnTClosure) : List PFnTClosure :=
  -- Start with tcls1 (deduplicated), then add elements from tcls2 that aren't already present
  let withTcls1 := tcls1.foldl (fun acc tcl => if acc.contains tcl then acc else acc ++ [tcl]) []
  tcls2.foldl (fun acc tcl => if acc.contains tcl then acc else acc ++ [tcl]) withTcls1
