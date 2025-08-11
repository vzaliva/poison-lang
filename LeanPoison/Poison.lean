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
  etyp : ETyp
  poison : Poison
  pred : Option TPred

-- Type closures for function types
inductive TClosure : Type where
  | fn_tclosure : Name → Expr → List (Name × QTyp) → TClosure
  | pfn_tclosure: Name → PExpr → List (Name × QTyp) → TClosure

-- Enriched type (full type)
inductive ETyp : Type where
  | int : ETyp
  | bool : ETyp
  | unit : ETyp
  | string : ETyp
  | ref : ETyp → Address → ETyp
  | arrow : Typ → Typ → Poison → TClosure → ETyp  -- Now stores surface type ST, not T1 -> T2

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
  | PExpr.let x e1 e2, _ => s!"PExpr.let {repr x} ({reprPExpr e1 0}) ({reprPExpr e2 0})"
  | PExpr.app e1 e2, _ => s!"PExpr.app ({reprPExpr e1 0}) ({reprPExpr e2 0})"

partial def reprTClosure : TClosure → Nat → Std.Format
  | TClosure.fn_tclosure x _ _ , _ => s!"TClosure.fn_tclosure {repr x} <expr>"
  | TClosure.pfn_tclosure x _ _ , _ => s!"TClosure.pfn_tclosure {repr x} <pexpr>"

partial def reprETyp : ETyp → Nat → Std.Format
  | ETyp.int, _ => "ETyp.int"
  | ETyp.bool, _ => "ETyp.bool"
  | ETyp.unit, _ => "ETyp.unit"
  | ETyp.string , _ => "ETyp.string"
  | ETyp.ref t l, _ => s!"ETyp.ref {reprETyp t 0} {repr l}"
  | ETyp.arrow st1 st2 p tcl, _ => s!"ETyp.arrow {reprTyp st1 0} {reprTyp st2 0} {repr p} {reprTClosure tcl 0}"

partial def reprQTyp : QTyp → Nat → Std.Format
  | QTyp.mk etyp poison tpred, _ =>
    let tpredRepr := match tpred with
      | none => "none"
      | some tp => s!"{reprTPred tp 0}"
    s!"QTyp.mk {reprETyp etyp 0} {repr poison} {tpredRepr}"

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

instance : Repr ETyp where
  reprPrec := reprETyp

instance : Repr QTyp where
  reprPrec := reprQTyp

instance : Repr TPred where
  reprPrec := reprTPred


-- Manual BEq instance for ETyp (needed for type checking)
mutual
def beqETyp : ETyp → ETyp → Bool
  | ETyp.int, ETyp.int => true
  | ETyp.bool, ETyp.bool => true
  | ETyp.unit, ETyp.unit => true
  | ETyp.ref t1 l1, ETyp.ref t2 l2 => beqETyp t1 t2 && l1 == l2
  | ETyp.arrow st1 st2 p1 tcl1, ETyp.arrow st1' st2' p2 tcl2 =>
    st1 == st1' && st2 == st2' && p1 == p2 && beqTClosure tcl1 tcl2
  | _, _ => false

def beqTClosure : TClosure → TClosure → Bool
  | TClosure.fn_tclosure x1 _ _, TClosure.fn_tclosure x2 _ _ => x1 == x2
  | TClosure.pfn_tclosure x1 _ _, TClosure.pfn_tclosure x2 _ _ => x1 == x2
  | _, _ => false
end

instance : BEq ETyp where
  beq := beqETyp

instance : BEq TClosure where
  beq := beqTClosure


-- Manual BEq instance for PExpr
def beqPExpr : PExpr → PExpr → Bool
  | PExpr.value v1, PExpr.value v2 => v1 == v2
  | PExpr.var x1, PExpr.var x2 => x1 == x2
  | PExpr.op e1 op1 e2, PExpr.op e1' op2 e2' => op1 == op2 && beqPExpr e1 e1' && beqPExpr e2 e2'
  | PExpr.ite e1 e2 e3, PExpr.ite e1' e2' e3' => beqPExpr e1 e1' && beqPExpr e2 e2' && beqPExpr e3 e3'
  | PExpr.deref e1, PExpr.deref e2 => beqPExpr e1 e2
  | PExpr.let x1 e1 e2, PExpr.let x2 e1' e2' => x1 == x2 && beqPExpr e1 e1' && beqPExpr e2 e2'
  | PExpr.app e1 e2, PExpr.app e1' e2' => beqPExpr e1 e1' && beqPExpr e2 e2'
  | _, _ => false

instance : BEq PExpr where
  beq := beqPExpr


mutual

def beqVarEnv : List (Name × QTyp) → List (Name × QTyp) → Bool
  | [], [] => true
  | (x1, qt1) :: env1, (x2, qt2) :: env2 => x1 == x2 && beqQTyp qt1 qt2 && beqVarEnv env1 env2
  | _, _ => false

-- Manual BEq instance for TPred
def beqTPred : TPred → TPred → Bool
  | TPred.mk tag1 arg_name1 pred_body1 var_env1, TPred.mk tag2 arg_name2 pred_body2 var_env2 =>
    tag1 == tag2 && arg_name1 == arg_name2 && pred_body1 == pred_body2 && beqVarEnv var_env1 var_env2

-- Manual BEq instance for Option TPred
def beqOptionTPred : Option TPred → Option TPred → Bool
  | none, none => true
  | some tp1, some tp2 => beqTPred tp1 tp2
  | _, _ => false

-- Manual BEq instance for QTyp
def beqQTyp : QTyp → QTyp → Bool
  | QTyp.mk etyp1 poison1 pred1, QTyp.mk etyp2 poison2 pred2 =>
    etyp1 == etyp2 && poison1 == poison2 && beqOptionTPred pred1 pred2

end

instance : BEq TPred where
  beq := beqTPred

instance : BEq QTyp where
  beq := beqQTyp
