import LeanPoison.Syntax

-- Predicate tags
abbrev Tag := Nat

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

-- Separate typing closures for impure and pure functions
inductive FnTClosure : Type where
  | mk : Name → Expr → List (Name × QTyp) → FnTClosure

inductive PFnTClosure : Type where
  | mk : Name → PExpr → List (Name × QTyp) → PFnTClosure

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
-- mutually inductive type above which requires types you’re defining must be
-- strictly positive and may only appear in constructors you’re declaring in
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
  | FnTClosure.mk x _ _ , _ => s!"FnTClosure {repr x} <expr>"

partial def reprPFnTClosure : PFnTClosure → Nat → Std.Format
  | PFnTClosure.mk x _ _ , _ => s!"PFnTClosure {repr x} <pexpr>"

partial def reprETyp : ETyp → Nat → Std.Format
  | ETyp.int, _ => "ETyp.int"
  | ETyp.bool, _ => "ETyp.bool"
  | ETyp.unit, _ => "ETyp.unit"
  | ETyp.string , _ => "ETyp.string"
  | ETyp.ref t l, _ => s!"ETyp.ref {reprETyp t 0} {repr l}"
  | ETyp.arrow st1 st2 p tcl, _ => s!"ETyp.arrow {reprTyp st1 0} {reprTyp st2 0} {repr p} {reprFnTClosure tcl 0}"
  | ETyp.parrow st1 st2 p tcl, _ => s!"ETyp.parrow {reprTyp st1 0} {reprTyp st2 0} {repr p} {reprPFnTClosure tcl 0}"

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

instance : Repr FnTClosure where
  reprPrec := reprFnTClosure

instance : Repr PFnTClosure where
  reprPrec := reprPFnTClosure

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
  | ETyp.string , ETyp.string => true
  | ETyp.ref t1 l1, ETyp.ref t2 l2 => beqETyp t1 t2 && l1 == l2
  | ETyp.arrow st1 st2 p1 tcl1, ETyp.arrow st1' st2' p2 tcl2 =>
    st1 == st1' && st2 == st2' && p1 == p2 && beqFnTClosure tcl1 tcl2
  | ETyp.parrow st1 st2 p1 tcl1, ETyp.parrow st1' st2' p2 tcl2 =>
    st1 == st1' && st2 == st2' && p1 == p2 && beqPFnTClosure tcl1 tcl2
  | _, _ => false

def beqFnTClosure : FnTClosure → FnTClosure → Bool
  | FnTClosure.mk x1 _ _, FnTClosure.mk x2 _ _ => x1 == x2

def beqPFnTClosure : PFnTClosure → PFnTClosure → Bool
  | PFnTClosure.mk x1 _ _, PFnTClosure.mk x2 _ _ => x1 == x2
end

instance : BEq ETyp where
  beq := beqETyp

instance : BEq FnTClosure where
  beq := beqFnTClosure

instance : BEq PFnTClosure where
  beq := beqPFnTClosure

theorem rfl_ETyp {t : ETyp} : (beqETyp t t) = true := by
  sorry

theorem eq_of_beq_ETyp {t1 t2 : ETyp} : (beqETyp t1 t2) = true → t1 = t2 := by
  sorry

instance : LawfulBEq ETyp where
  rfl := rfl_ETyp
  eq_of_beq := eq_of_beq_ETyp

-- Manual BEq instance for PExpr
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

@[instance]
instance : ToString ETyp where
  toString e := Std.Format.pretty (repr e)


@[instance]
instance : ToString QTyp where
  toString e := Std.Format.pretty (repr e)
