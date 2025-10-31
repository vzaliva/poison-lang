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

-- Reflexivity lemmas for BEq instances on mutually recursive types
mutual
-- Prove reflexivity of beqETyp using mutual induction
theorem beqETyp_refl (t : ETyp) : beqETyp t t = true := by
  cases t with
  | int | bool | unit | string => simp [beqETyp]
  | ref t' l =>
    simp [beqETyp]
    -- For ref type: (beqETyp t' t' && l == l) = true
    -- Show both parts are true
    have h_t' : beqETyp t' t' = true := beqETyp_refl t'
    have h_l : (l == l) = true := by simp [BEq.beq]
    simp [h_t']
  | arrow st1 st2 p' tcl =>
    simp [beqETyp]
    -- Need: (st1 == st1 && st2 == st2 && p' == p' && beqFnTClosure tcl tcl) = true
    -- Typ has BEq instance, use Typ_beq_refl from Syntax.lean
    have h_st1 : (st1 == st1) = true := Typ_beq_refl st1
    have h_st2 : (st2 == st2) = true := Typ_beq_refl st2
    have h_p' : (p' == p') = true := by cases p' <;> simp [BEq.beq]
    have h_tcl : beqFnTClosure tcl tcl = true := beqFnTClosure_refl tcl
    simp [h_st1, h_st2, h_tcl]
  | parrow st1 st2 p' tcl =>
    simp [beqETyp]
    have h_st1 : (st1 == st1) = true := Typ_beq_refl st1
    have h_st2 : (st2 == st2) = true := Typ_beq_refl st2
    have h_p' : (p' == p') = true := by cases p' <;> simp [BEq.beq]
    have h_tcl : beqPFnTClosure tcl tcl = true := beqPFnTClosure_refl tcl
    simp [h_st1, h_st2, h_tcl]

-- Prove reflexivity of beqFnTClosure
theorem beqFnTClosure_refl (tcl : FnTClosure) : beqFnTClosure tcl tcl = true := by
  cases tcl with
  | mk x _ _ =>
    simp [beqFnTClosure, BEq.beq]
    -- x == x reduces to true by BEq reflexivity for Name (String)

-- Prove reflexivity of beqPFnTClosure
theorem beqPFnTClosure_refl (tcl : PFnTClosure) : beqPFnTClosure tcl tcl = true := by
  cases tcl with
  | mk x _ _ =>
    simp [beqPFnTClosure, BEq.beq]
    -- x == x reduces to true by BEq reflexivity for Name (String)
end


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

-- Manual BEq instance for Predicate
def beqPredicate : Predicate → Predicate → Bool
  | Predicate.guardClosure tag1 arg1 body1 env1, Predicate.guardClosure tag2 arg2 body2 env2 =>
    tag1 == tag2 && arg1 == arg2 && body1 == body2 && beqVarEnv env1 env2
  | Predicate.guardOnly tag1, Predicate.guardOnly tag2 =>
    tag1 == tag2
  | Predicate.noPred, Predicate.noPred => true
  | _, _ => false

-- Manual BEq instance for QTyp
def beqQTyp : QTyp → QTyp → Bool
  | QTyp.mk etyp1 poison1 pred1, QTyp.mk etyp2 poison2 pred2 =>
    etyp1 == etyp2 && poison1 == poison2 && beqPredicate pred1 pred2

end

instance : BEq Predicate where
  beq := beqPredicate

instance : BEq QTyp where
  beq := beqQTyp

@[instance]
instance : ToString ETyp where
  toString e := Std.Format.pretty (repr e)


@[instance]
instance : ToString QTyp where
  toString e := Std.Format.pretty (repr e)
