import LeanPoison.Syntax
import LeanPoison.Misc

import Std.Data.HashMap
open Std

-- Type checking environment definitions

/-- Default fuel for type checking -/
private def defaultFuel : Nat := 1000

/-- Memory typing environment (Γ in the Ott spec) -/
abbrev MemoryTypeEnv := HashMap Address QTyp

namespace MemoryTypeEnv

  @[inline] def lookup (m : MemoryTypeEnv) (a : Address) : Option QTyp :=
    m.get? a

  @[inline] def update (m : MemoryTypeEnv) (a : Address) (qt : QTyp) : MemoryTypeEnv :=
    m.insert a qt

  /-- `m` contains a binding for `a`. -/
  def hasKey (m : MemoryTypeEnv) (a : Address) : Prop :=
    m.contains a

  /-- Extensional equality of memory typing environments. All keys and values must be equal. -/
  def equiv (m₁ m₂ : MemoryTypeEnv) : Prop := HashMap.Equiv m₁ m₂

end MemoryTypeEnv

/-- Dependency set for tracking heap locations read by predicates -/
abbrev Deps := List Address

/-- Tag valuation with dependency information -/
structure TagVal where
  value : Bool
  deps : Deps
  deriving Repr, BEq

/-- Tag valuation environment (ℒ in the Ott spec) -/
abbrev TagEnv := HashMap Tag TagVal

/-- Remove from tag environment all entries whose dependency sets contain location l -/
def invalidateTagDeps (env : TagEnv) (l : Address) : TagEnv :=
  Std.HashMap.fold (fun acc k tv =>
    if tv.deps.contains l then acc else acc.insert k tv) (∅ : TagEnv) env

/-- Type checking context containing all environments -/
structure TypeContext where
  pc : Poison            -- Poison context
  memEnv : MemoryTypeEnv -- Γ
  varEnv : VarTypeEnv    -- σ
  tagEnv : TagEnv        -- ℒ
  nextLoc : Address  -- for fresh location generation
  nextTag : Tag  -- for fresh location generation
  pureCtx : Bool -- whether we are inside a pure function body typing

/-- Type checking result: qualified type and updated memory environment -/
structure TypeResult where
  qualType : QTyp -- Qualified type of the expression
  memEnv' : MemoryTypeEnv -- Updated memory typing environment
  tagEnv' : TagEnv  -- Updated logical environment
  nextLoc' : Address -- Updated next location
  nextTag' : Tag -- Updated next location

/-- Type checking monad for error handling -/
abbrev TypecheckM := Except String


/-- Extract dependencies from a predicate by analyzing free variables in the predicate body -/
def extractDepsFromPred (pred : Predicate) : TypecheckM Deps :=
  match pred with
  | Predicate.guardClosure _tag arg_name pred_body var_env =>
    let rec extractDepsFromPExpr (pe : PExpr) (boundVars : List Name) (env : VarTypeEnv) (fuel : Nat) : TypecheckM Deps :=
      match fuel with
      | 0 => throw "Out of fuel while extracting dependencies"
      | fuel + 1 =>
        match pe with
        | PExpr.var x =>
          if boundVars.contains x then return []  -- Bound variable, not free
          else
            match env.find? (fun (name, _) => name == x) with
            | some (_, qt) =>
              match qt.etyp with
              | ETyp.ref _t l => return [l]  -- Reference type, add location
              | ETyp.parrow _argTy _retTy _poison (PFnTClosure.regular argName body varEnv') =>
                -- Pure function, recurse into its closure
                extractDepsFromPExpr body (argName :: boundVars) varEnv' fuel
              | _ => return []  -- Other types don't read from heap
            | none => throw s!"Variable {x} not found in environment while extracting dependencies"
        | PExpr.deref pe' => extractDepsFromPExpr pe' boundVars env fuel
        | PExpr.op pe1 _ pe2 => do
          let deps1 ← extractDepsFromPExpr pe1 boundVars env fuel
          let deps2 ← extractDepsFromPExpr pe2 boundVars env fuel
          return concat_noDups deps1 deps2
        | PExpr.unaryop _ pe' => extractDepsFromPExpr pe' boundVars env fuel
        | PExpr.ite pe1 pe2 pe3 => do
          let deps1 ← extractDepsFromPExpr pe1 boundVars env fuel
          let deps2 ← extractDepsFromPExpr pe2 boundVars env fuel
          let deps3 ← extractDepsFromPExpr pe3 boundVars env fuel
          return concat_noDups (concat_noDups deps1 deps2) deps3
        | PExpr.app pe1 pe2 => do
          let deps1 ← extractDepsFromPExpr pe1 boundVars env fuel
          let deps2 ← extractDepsFromPExpr pe2 boundVars env fuel
          return concat_noDups deps1 deps2
        | PExpr.vlet x pe1 pe2 => do
          let deps1 ← extractDepsFromPExpr pe1 boundVars env fuel
          let deps2 ← extractDepsFromPExpr pe2 (x :: boundVars) env fuel
          return concat_noDups deps1 deps2
        | _ => return []  -- literals, unit, etc. don't read from heap

    -- Start with the bound parameter in the bound variables list
    extractDepsFromPExpr pred_body [arg_name] var_env defaultFuel
  | Predicate.guardOnly _tag =>
    -- Guard-only predicate with no body, no dependencies
    return []
  | Predicate.noPred =>
    -- No predicate, no dependencies
    return []

-- Allocate a fresh location and return it along with updated typing context
def freshTLoc (ctx : TypeContext): (Address × TypeContext) :=
  (ctx.nextLoc, { ctx with nextLoc := ctx.nextLoc + 1 })

-- Allocate a fresh location and return it along with updated typing context
def freshTLocRes (result : TypeResult): (Address × TypeResult) :=
  (result.nextLoc', { result with nextLoc' := result.nextLoc' + 1 })

-- Function to get a fresh Tag Value From the environment
def generateFreshTag (ctx : TypeContext) : (Tag × TypeContext) :=
  (ctx.nextTag, { ctx with nextTag := ctx.nextTag + 1 })

-- Allocate a fresh Tag Value and return it along with updated typing result
def generateFreshTagRes (result : TypeResult): (Tag × TypeResult) :=
  (result.nextTag', { result with nextTag' := result.nextTag' + 1 })


-- Helper functions

/-- Join two poison flags -/
def joinPoison (p1 p2 : Poison) : Poison :=
  p1 || p2

/-- Join multiple poison flags -/
def joinPoisons (ps : List Poison) : Poison :=
  ps.foldl joinPoison false

/-- Update memory environment at a location -/
def updateMemEnv (env : MemoryTypeEnv) (l : Address) (qt : QTyp) : MemoryTypeEnv :=
  env.insert l qt

/-- Join two memory environments (branch join). See JoinG in the Ott spec. -/
def joinMemEnvs (env1 env2 : MemoryTypeEnv) : MemoryTypeEnv :=
  combineMaps env1 env2 (fun _ oq1 oq2 =>
    match oq1, oq2 with
    | some qt1, none => some qt1
    | none, some qt2 => some qt2
    | some qt1, some qt2 =>
      let ⟨t1, p1, pred1⟩ := qt1
      let ⟨t2, p2, pred2⟩ := qt2
      if t1 == t2 then
        let p := joinPoison p1 p2
        let pred :=
          match pred1, pred2 with
          -- Both branches have guard closure with same tag: keep the closure
          | Predicate.guardClosure k1 an1 pb1 ve1, Predicate.guardClosure k2 _ _ _ =>
              if k1 == k2 then Predicate.guardClosure k1 an1 pb1 ve1 else Predicate.noPred
          -- Both branches have guard only with same tag: keep guard only
          | Predicate.guardOnly k1, Predicate.guardOnly k2 =>
              if k1 == k2 then Predicate.guardOnly k1 else Predicate.noPred
          -- Mixed: guardClosure and guardOnly with same tag: keep the more general guardOnly
          | Predicate.guardClosure k1 _ _ _, Predicate.guardOnly k2 =>
              if k1 == k2 then Predicate.guardOnly k1 else Predicate.noPred
          | Predicate.guardOnly k1, Predicate.guardClosure k2 _ _ _ =>
              if k1 == k2 then Predicate.guardOnly k1 else Predicate.noPred
          -- One or both branches have noPred: conservative choice is noPred
          | Predicate.noPred, _ => Predicate.noPred
          | _, Predicate.noPred => Predicate.noPred
        some ⟨t1, p, pred⟩
      else
        -- Unreachable under well-typedness: location types are immutable.
        -- Symmetric, conservative fallback: drop the conflicting binding.
        -- TODO: consider running this in Exception monad to report an error.
        none
    | none, none => none)

/-- Join two logical environments (agreement-only meet used in while fixpoint) -/
def joinTagEnvs (env1 env2 : TagEnv) : TagEnv :=
  combineMaps env1 env2 (fun _ otv1 otv2 =>
    match otv1, otv2 with
    | some ⟨b1, deps1⟩, some ⟨b2, deps2⟩ =>
      if b1 == b2 then
        -- Agreement: keep the tag with union of dependencies
        some ⟨b1, concat_noDups deps1 deps2⟩
      else
        -- Disagreement: drop the tag (unknown)
        none
    | some _, none => none  -- Single-sided: drop (unknown)
    | none, some _ => none  -- Single-sided: drop (unknown)
    | none, none => none)

-- Helper function to convert Expr to PExpr
def Expr.toPExpr (e : Expr) : TypecheckM PExpr :=
  match e with
  | Expr.unit => return .unit
  | Expr.num n => return .num n
  | Expr.bool b => return .bool b
  | Expr.str s => return .str s
  | Expr.var x => return .var x
  | Expr.op e1 opname e2 => (fun pe1 pe2 => PExpr.op pe1 opname pe2) <$> e1.toPExpr <*> e2.toPExpr
  | Expr.unaryop opname e => PExpr.unaryop opname <$> e.toPExpr
  | Expr.ite e1 e2 e3 => PExpr.ite <$> e1.toPExpr <*> e2.toPExpr <*> e3.toPExpr
  | Expr.deref e => .deref <$> e.toPExpr
  | Expr.vlet x e1 e2 => (fun pe1 pe2 => .vlet x pe1 pe2) <$> e1.toPExpr <*> e2.toPExpr
  | Expr.app e1 e2 => .app <$> e1.toPExpr <*> e2.toPExpr
  | _ => throw "Cannot convert expression to PExpr"

-- Helper function to project ETyp to Typ By stripping poison and closure
-- information from arrows and locations from references.
def ETyp.toTyp (pt : ETyp) : Typ :=
  match pt with
  | ETyp.int => Typ.int
  | ETyp.bool => Typ.bool
  | ETyp.unit => Typ.unit
  | ETyp.string => Typ.string
  | ETyp.ref t _ => Typ.ref (t.toTyp)
  | ETyp.arrow st1 st2 _p _tcl => Typ.arrow st1 st2
  | ETyp.parrow st1 st2 _p _tcl => Typ.arrow st1 st2

-- Helper function to convert PExpr to Expr
def PExpr.toExpr (pe : PExpr) : Expr :=
  match pe with
  | .unit => Expr.unit
  | .num n => Expr.num n
  | .bool b => Expr.bool b
  | .str s => Expr.str s
  | .var x => Expr.var x
  | .op e1 o e2 => Expr.op (e1.toExpr) o (e2.toExpr)
  | .unaryop opname e => Expr.unaryop opname (e.toExpr)
  | .ite e1 e2 e3 => Expr.ite (e1.toExpr) (e2.toExpr) (e3.toExpr)
  | .deref e => Expr.deref (e.toExpr)
  | .vlet x e1 e2 => Expr.vlet x (e1.toExpr) (e2.toExpr)
  | .app e1 e2 => Expr.app (e1.toExpr) (e2.toExpr)

/-- Convert qualified type to surface type by stripping poison and preducate info -/
def QTyp.toTyp (qt : QTyp) : Typ :=
  qt.etyp.toTyp

/-- Check if a surface type is a subtype of a qualified type. This implements ST
      <: T by comparing surface types.

    This is as strict comparsion by discarding poison and closure information.
    We can consider implementing proper subtyping relation with contravariance
    for the parameter type and covariance for the return type in the future.
-/
def isSubtype (st : Typ) (qt : QTyp) : Bool :=
  qt.toTyp == st

-- Typing judgement for operations
inductive OpEType : Op → ETyp → ETyp → ETyp → Prop where
  | add_int : OpEType Op.add ETyp.int ETyp.int ETyp.int
  | sub_int : OpEType Op.sub ETyp.int ETyp.int ETyp.int
  | mul_int : OpEType Op.mul ETyp.int ETyp.int ETyp.int
  | div_int : OpEType Op.div ETyp.int ETyp.int ETyp.int

  | gte_int : OpEType Op.gte ETyp.int ETyp.int ETyp.bool
  | lte_int : OpEType Op.lte ETyp.int ETyp.int ETyp.bool
  | gt_int  : OpEType Op.gt  ETyp.int ETyp.int ETyp.bool
  | lt_int  : OpEType Op.lt  ETyp.int ETyp.int ETyp.bool
  | eq_int  : OpEType Op.eq  ETyp.int ETyp.int ETyp.bool
  | neq_int : OpEType Op.neq ETyp.int ETyp.int ETyp.bool
  | and_bool : OpEType Op.and ETyp.bool ETyp.bool ETyp.bool
  | or_bool  : OpEType Op.or  ETyp.bool ETyp.bool ETyp.bool
  | bitand_int  : OpEType Op.bitand  ETyp.int  ETyp.int  ETyp.int

def opEType? : Op → ETyp → ETyp → Option ETyp
  | .add, .int,  .int  => some .int
  | .sub, .int,  .int  => some .int
  | .mul, .int,  .int  => some .int
  | .div, .int,  .int  => some .int
  | .gte, .int,  .int  => some .bool
  | .lte, .int,  .int  => some .bool
  | .gt,  .int,  .int  => some .bool
  | .lt,  .int,  .int  => some .bool
  | .eq,  .int,  .int  => some .bool
  | .and, .bool, .bool => some .bool
  | .or,  .bool, .bool => some .bool
  | .bitand, .int,.int  => some .int
  | .neq,  .int,   .int  => some .bool
  | _,    _,     _     => none

inductive OpUnaryEType : UnaryOp → ETyp → ETyp → Prop where
  | not_bool : OpUnaryEType UnaryOp.not ETyp.bool ETyp.bool

def opUnaryEType? : UnaryOp → ETyp → Option ETyp
  | .not, .bool  => some .bool
  | _,    _     => none

/--
 Helper function to check if two PExprs are syntactically equal modulo
 environment differences. This handles variable substitution and type
 compatibility checking during structural comparison. Variables are substituted
 in the first argument only.

 The `fuel` parameter is used to prove termination. Normally we should be able
 should be able to prove termination on structure of pe1 and pe2 arguments but
 this is does not work in case of substitution. In fact, unless isValidSubstitution
 is ensured in matchGuard, we will get infinite recursion.

 The `substitution` parameter is an optional (variable, value) pair for
 substitution.
--/
def PExpr.equalWithEnvs (pe1 : PExpr) (env1 : VarTypeEnv) (pe2 : PExpr) (env2 : VarTypeEnv) (substitution : Option (Name × PExpr)) (fuel : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    match pe1, pe2 with
    | .unit, .unit => true
    | .num n1, .num n2 => n1 == n2
    | .bool b1, .bool b2 => b1 == b2
    | .str s1, .str s2 => s1 == s2
    | .var x1, pe2 =>
        match substitution with
        | some (arg1, val1) =>
          if x1 == arg1 then
            -- If we're substituting x with x, just compare syntactically
            if val1 == PExpr.var x1 then
              match pe2 with
              | PExpr.var x2 => x1 == x2
              | _ => false
            else
              -- Normal substitution
              PExpr.equalWithEnvs val1 env1 pe2 env2 substitution fuel
          else
            -- Some other variable, compare it syntactically with the target variable
            match pe2 with
            | .var x2 => x1 == x2
            | _ => false
        | none =>
          -- No substitution active, just compare variables syntactically
          match pe2 with
          | .var x2 => x1 == x2
          | _ => false
    | .op e1 op1 e2, .op e1' op2 e2' =>
      op1 == op2 && equalWithEnvs e1 env1 e1' env2 substitution fuel && equalWithEnvs e2 env1 e2' env2 substitution fuel
    | .ite e1 e2 e3, .ite e1' e2' e3' =>
      equalWithEnvs e1 env1 e1' env2 substitution fuel && equalWithEnvs e2 env1 e2' env2 substitution fuel && equalWithEnvs e3 env1 e3' env2 substitution fuel
    | .deref e1, .deref e2 => equalWithEnvs e1 env1 e2 env2 substitution fuel
    | .vlet x1 e1 e2, .vlet x2 e1' e2' =>
      x1 == x2 &&
      equalWithEnvs e1 env1 e1' env2 substitution fuel &&
      -- For the body, disable substitution if the bound variable shadows the substitution variable
      equalWithEnvs e2 env1 e2' env2 (if substitution.map (·.1) == some x1 then none else substitution) fuel
    | .app e1 e2, .app e1' e2' =>
      equalWithEnvs e1 env1 e1' env2 substitution fuel && equalWithEnvs e2 env1 e2' env2 substitution fuel
    | _, _ => false


/--
  Scans the predicates attached to every variable in S and every memory location
  in G which has a variable in S referencing it; if it finds exactly one guard k
  whose test expression, when applied to its owning value (variable or deref of
  variable), is syntactically identical to the condition e, it returns that k -
  otherwise it throws an error.

  We perform variable substitution in the predicate body before comparing it to
  the condition using PExpr.equalWithEnvs for proper environment-aware
  comparison.
--/
def matchGuard (e : Expr) (G : MemoryTypeEnv) (S : VarTypeEnv) : TypecheckM (Tag × Deps) := do
  -- Try to convert the condition e to a PExpr
  let conditionPExpr ← e.toPExpr

  -- Helper function to check if a predicate's test expression matches the condition
  let checkPredicate (arg : PExpr) (qt : QTyp) : TypecheckM (Option (Tag × Deps)) :=
    match qt.pred with
    | Predicate.noPred => return none
    | Predicate.guardOnly _tag => return none  -- Guard-only cannot be matched syntactically
    | Predicate.guardClosure tag arg_name pred_body var_env =>
        -- Compare the predicate body with the condition using environment-aware equality
        if PExpr.equalWithEnvs pred_body var_env conditionPExpr S (some (arg_name, arg)) defaultFuel then do
          let deps ← extractDepsFromPred qt.pred
          return some (tag, deps)
        else return none

  -- Collect all matching tags from variable environment
    let varMatches := S.foldl (init := []) fun acc ⟨name, qt⟩ =>
    let arg := PExpr.var name
    match checkPredicate arg qt with
    | .ok (some (tag, deps)) => (tag, deps) :: acc
    | .ok none => acc
    | .error _ => acc

  -- For references, we need to check the memory environment
  let refMatches := S.foldl (init := []) fun acc ⟨name, qt⟩ =>
    -- Check if the variable has a reference type
      match qt.etyp with
  | ETyp.ref _t l =>
      if qt.poison then
        -- Poisoned reference: it could never be de-poisoned, so we don't need to check the predicate
        acc
      else
        -- Look up the type of the memory location in G
        match G.get? l with
        | some memQt =>
          -- Use the dereferenced value as the substitution value
          let arg := PExpr.deref (PExpr.var name)
          -- Use checkPredicate to check if the memory location's predicate matches
          match checkPredicate arg memQt with
          | .ok (some (tag, deps)) => (tag, l :: deps) :: acc  -- Add the memory location l that arg refers to
          | .ok none => acc
          | .error _ => acc
        | none => acc
    | _ => acc

  let allMatches := varMatches ++ refMatches
  -- Return the tag and dependencies if exactly one match is found, otherwise throw an error
  match allMatches with
  | [(tag, deps)] => return (tag, deps)
  | [] => throw "No matching guard found for condition"
  | _ => throw s!"Multiple matching guards found for condition: {allMatches}"



-- Type checking rules implementation

/-- Rule: int (Ott rule: int)
-- pc ; G ; S ; L |- n : int :> clean { no_pred } -| G ; L
-/
def typecheckInt (ctx : TypeContext) (_n : Int) : TypecheckM TypeResult := do
  let qt : QTyp := ⟨ETyp.int, false, Predicate.noPred⟩  -- clean, no predicate
  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag }

/-- Rule: bool (Ott rule: bool)
-- pc ; G ; S ; L |- b : bool :> clean { no_pred } -| G ; L
-/
def typecheckBool (ctx : TypeContext) (_b : Bool) : TypecheckM TypeResult := do
  let qt : QTyp := ⟨ETyp.bool, false, Predicate.noPred⟩  -- clean, no predicate
  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag }


/-- Rules: var_guard_true, var_guard_false, var_guard_unknown, var_no_pred (Ott rules)
-- Variable typing with predicate handling:
-- - var_guard_true: S(x) = T :> p { guard k pred_closure pcl }, L(k) = true
-- - var_guard_only_true: S(x) = T :> p { guard k }, L(k) = true
-- - var_guard_false: S(x) = T :> p { guard k pred_closure pcl }, L(k) = false
-- - var_guard_only_false: S(x) = T :> p { guard k }, L(k) = false
-- - var_guard_unknown: S(x) = T :> p { guard k pred_closure pcl }, k not in L
-- - var_guard_only_unknown: S(x) = T :> p { guard k }, k not in L
-- - var_no_pred: S(x) = T :> p { no_pred }
--/
def typecheckVar (ctx : TypeContext) (x : Name) : TypecheckM TypeResult := do
  --dbg_trace ("Typechecking var " ++ x)
  --dbg_trace s!"ctx.pc is {ctx.pc}"
   match ctx.varEnv.lookup x with
  | some qt =>
    let ⟨etyp, poison, pred⟩ := qt
    match pred with
    | Predicate.noPred =>  -- no_pred case
      let poison := joinPoison ctx.pc poison
      let qt' : QTyp := ⟨etyp, poison, Predicate.noPred⟩
      return { qualType := qt', memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag }
    | Predicate.guardOnly k | Predicate.guardClosure k _ _ _ =>
      -- Both guard types behave the same: check tag in L and de-poison/poison/preserve accordingly
      --dbg_trace s!"Guard predicate found with tag {k}"
      match ctx.tagEnv.get? k with
      | some ⟨true, _deps⟩ =>  -- guard_true / guard_only_true case
        -- dbg_trace "Guard True case"
        let qt' : QTyp := ⟨etyp, ctx.pc, Predicate.noPred⟩
        return { qualType := qt', memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag }
      | some ⟨false, _deps⟩ =>  -- guard_false / guard_only_false case
        -- dbg_trace "Guard False case"
        let qt' : QTyp := ⟨etyp, true, Predicate.noPred⟩  -- poisoned
        return { qualType := qt', memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag }
      | none =>  -- guard_unknown / guard_only_unknown case
        -- dbg_trace "Guard Unknown case"
        let poison := joinPoison ctx.pc poison
        -- Preserve the original predicate (either guardOnly or guardClosure)
        let qt' : QTyp := ⟨etyp, poison, pred⟩
        return { qualType := qt', memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag }
  | none => throw s!"Variable {x} not found in environment"


/-- Rule: location (Ott rule: location)
-- G(l) = T :> p { P }
-- ------------------
-- pc ; G ; S ; L |- l : ref T @ l :> clean { no_pred } -| G ; L
-/
def typecheckLocation (ctx : TypeContext) (l : Address) : TypecheckM TypeResult := do
  match ctx.memEnv.get? l with
  | some qt =>
    let ⟨etyp, _p, pred ⟩ := qt
    let refTyp := ETyp.ref etyp l
    let qt' : QTyp := ⟨refTyp, false, pred⟩  -- clean, preserve predicate
    return { qualType := qt', memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag }
  | none => throw s!"Location {l} not found in memory environment"

/-- Rule: unit (Ott rule: unit)
-- pc ; G ; S ; L |- unit : unit :> clean { no_pred } -| G ; L
-/
def typecheckUnit (ctx : TypeContext) : TypecheckM TypeResult := do
  let qt : QTyp := ⟨ETyp.unit, false, Predicate.noPred⟩  -- clean, no predicate
  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag }

/--  Rule: string (Ott rule: string)
-- pc ; G ; S ; L |- string : string :> clean { no_pred } -| G ; L
-/
def typecheckString (ctx : TypeContext) (_s : String) : TypecheckM TypeResult := do
  let qt : QTyp := ⟨ETyp.string, false, Predicate.noPred⟩  -- clean, no predicate
  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag }

-- The following option is needed in increasing the maximum number of heartbeats
-- to avoid the termination checker failure on the following mutual block.
set_option maxHeartbeats 800000


/-- Rule: fn_abs (Ott rule: fn_abs)
----------------------------------------------------------------------  :: fn_abs
  pc ; G ; S ; L |- fn x : ST1 => e : ST1 -> ST2 # pc typing_closure ( x , e , S ) :> pc { no_pred } -| G ; L
-/
def typecheckFn (ctx : TypeContext) (x : Name) (st1 : Typ) (body : Expr) (st2 : Typ) : TypecheckM TypeResult :=
  -- Simply record the body and return type without typechecking the body
  -- Body typechecking is deferred until application time

  -- Create arrow type ST1 -> ST2
  let arrowTyp : ETyp := ETyp.arrow st1 st2 false (FnTClosure.regular x body ctx.varEnv)
  -- Create qualified type ST1 -> ST2 # pc { no_pred }
  let qt : QTyp := ⟨arrowTyp, ctx.pc, Predicate.noPred⟩
   return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag }

/-- Rule: pfn_abs (Ott rule: pfn_abs)
----------------------------------------------------------------------  :: pfn_abs
  pc ; G ; S ; L |- pfn x : ST1 => pe : ST1 -> ST2 # pc typing_closure ( x , pe , S ) :> pc { no_pred } -| G ; L
-/
def typecheckPfn (ctx : TypeContext) (x : Name) (st1 : Typ) (body : Expr) (st2 : Typ) : TypecheckM TypeResult := do
  -- Simply record the body and return type without typechecking the body
  -- Body typechecking is deferred until application time

   -- Convert body to PExpr
  let pbody ← body.toPExpr
  -- Create arrow type ST1 -> ST2
  let arrowTyp : ETyp := ETyp.parrow st1 st2 false (PFnTClosure.regular x pbody ctx.varEnv)
  -- Create qualified type ST1 -> ST2 # pc { no_pred }
  let qt : QTyp := ⟨arrowTyp, ctx.pc, Predicate.noPred⟩

  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag }

-- Helper functions for extern type conversion

/-- Convert SyntaxPredicate to Predicate with late environment capture.
    Parser creates predicates with Expr bodies and no captured env.
    During typechecking, we convert Expr to PExpr and attach current varEnv.
-/
def attachVarEnvToPredicate (pred : SyntaxPredicate) (varEnv : VarTypeEnv) : TypecheckM Predicate := do
  -- Temporary simplified implementation - TODO: implement proper conversion
  match pred with
  | SyntaxPredicate.guardClosure k arg body => pure (Predicate.guardClosure k arg (← body.toPExpr ) varEnv)
  | SyntaxPredicate.guardOnly k => pure (Predicate.guardOnly k)
  | SyntaxPredicate.noPred => pure Predicate.noPred

/-- Convert (Typ, Bool, SyntaxPredicate) to QTyp for EXTERN VALUES.
    Used only for extern val declarations at definition time.
    May allocate fresh locations for reference types and update Γ.
-/
def surfaceSpecToQTyp (typ : Typ) (poison : Bool) (pred : SyntaxPredicate)
    (varEnv : VarTypeEnv) (ctx : TypeContext) : TypecheckM (QTyp × TypeContext) := do
  -- Convert Typ to ETyp, allocating locations for references
  let (etyp, ctx') ← (match typ with
    | Typ.int => pure (ETyp.int, ctx)
    | Typ.bool => pure (ETyp.bool, ctx)
    | Typ.unit => pure (ETyp.unit, ctx)
    | Typ.string => pure (ETyp.string, ctx)
    | Typ.ref t => do
        let (l, ctx') := freshTLoc ctx
        let (innerQt, ctx'') ← surfaceSpecToQTyp t false SyntaxPredicate.noPred varEnv ctx'
        return (ETyp.ref innerQt.etyp l, ctx'')
    | Typ.arrow _ _ => throw "Arrow types not expected in extern specs" : TypecheckM (ETyp × TypeContext))

  let pred' ← attachVarEnvToPredicate pred varEnv
  return (⟨etyp, poison, pred'⟩, ctx')

/-- Convert (Bool, SyntaxPredicate) to QTyp for EFFECT SPECIFICATIONS.
    Used when processing effects during extern function application.
    IMPORTANT: Memory currently stores only integers, so typ is always int.
    Effects specify the type stored AT a memory location (the contents type).
    No location allocation, no ctx updates.
-/
def effectSpecToQTyp (poison : Bool) (pred : SyntaxPredicate)
    (varEnv : VarTypeEnv) : TypecheckM QTyp := do
  let pred' ← attachVarEnvToPredicate pred varEnv
  return ⟨ETyp.int, poison, pred'⟩

/-- Convert (Typ, Bool, SyntaxPredicate) to QTyp for RETURN SPECIFICATIONS.
    Used when processing return specs during extern function application.
    MUST NOT allocate locations for reference types - extern functions cannot return references.

    RESTRICTION: Extern functions are forbidden from returning reference types.
    This function will reject any attempt to create a return spec with type `ref T`.
    See issue #72: Extern Functions Returning Reference Types - Location Tracking Problem
-/
def returnSpecToQTyp (typ : Typ) (poison : Bool) (pred : SyntaxPredicate)
    (varEnv : VarTypeEnv) (nextLoc : Address) : TypecheckM (QTyp × Address) := do
  -- Convert Typ to ETyp, rejecting reference types
  let (etyp, nextLoc') ← (match typ with
    | Typ.int => pure (ETyp.int, nextLoc)
    | Typ.bool => pure (ETyp.bool, nextLoc)
    | Typ.unit => pure (ETyp.unit, nextLoc)
    | Typ.string => pure (ETyp.string, nextLoc)
    | Typ.ref _ => throw "Extern functions cannot return reference types (see issue #72)"
    | Typ.arrow _ _ => throw "Arrow types not expected in extern specs" : TypecheckM (ETyp × Address))

  let pred' ← attachVarEnvToPredicate pred varEnv
  return (⟨etyp, poison, pred'⟩, nextLoc')

-- Type checking functions for extern expressions

/-- Typecheck extern value: let x = extern val : (T :> p { P }) -/
def typecheckExternVal (ctx : TypeContext) (typ : Typ) (poison : Bool) (pred : SyntaxPredicate)
    : TypecheckM TypeResult :=
    match (poison,pred) with
    | (false, SyntaxPredicate.guardOnly _) =>
        throw "Extern values cannot have guard-only predicates without closures"
    | (false, SyntaxPredicate.guardClosure _ _ _) =>
        throw "Clean types cannot have predicates"
    | _ => do 

  -- Convert to QTyp with current varEnv
  let (qt, ctx') ← surfaceSpecToQTyp typ poison pred ctx.varEnv ctx

  -- Return the qualified type
  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv,
           nextLoc' := ctx'.nextLoc, nextTag' := ctx.nextTag }

def parseReturnType (retType : ExternReturn):Typ :=
 match retType with
 | ExternReturn.simple typ _ _ => typ
 | ExternReturn.nestedFn _ typ extReturn _ => Typ.arrow typ (parseReturnType extReturn)
 | ExternReturn.nestedPfn _ typ extReturn => Typ.arrow typ (parseReturnType extReturn)

/-- Typecheck extern impure function -/
def typecheckExternFn (ctx : TypeContext) (arg : Name) (argTyp : Typ)
    (retSpec : ExternReturn) (effects : List Effect) : TypecheckM TypeResult := do
  -- Create extern closure with captured varEnv
  let tcl := FnTClosure.extern arg retSpec effects ctx.varEnv


  let retTyp := parseReturnType retSpec
  let arrowTyp := ETyp.arrow argTyp retTyp ctx.pc tcl  -- placeholder for st2

  -- Return qualified type with poison = pc
  let qt : QTyp := ⟨arrowTyp, ctx.pc, Predicate.noPred⟩
  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv,
           nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag }

/-- Typecheck extern pure function -/
def typecheckExternPfn (ctx : TypeContext) (arg : Name) (argTyp : Typ)
    (retSpec : ExternReturn) : TypecheckM TypeResult := do
  -- Create extern closure with captured varEnv
  let tcl := PFnTClosure.extern arg retSpec ctx.varEnv

  let retTyp := parseReturnType retSpec
  -- Create arrow type with ambient pc
  let arrowTyp := ETyp.parrow argTyp retTyp ctx.pc tcl

  -- Return qualified type with poison = pc
  let qt : QTyp := ⟨arrowTyp, ctx.pc, Predicate.noPred⟩
  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv,
           nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag }


def generateFreshVar (ctx : TypeContext) (pref : Name) (suffix : Nat) (fuel : Nat) : Name :=
  match fuel with
  | 0 => s!"{pref}{suffix}"
  | fuel + 1 =>
      let candidate := if suffix = 0 then pref else s!"{pref}{suffix}"
      if candidate ∈ ctx.varEnv.map (·.fst) then
       generateFreshVar ctx pref (suffix + 1) fuel
      else
       candidate
termination_by fuel

mutual

-- Helper function to type check an expression with context
def typecheckExpr (ctx : TypeContext) (e : Expr) (fuel : Nat) : TypecheckM TypeResult :=

  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    match e with
    | Expr.num n => typecheckInt ctx n
    | Expr.bool b => typecheckBool ctx b
    | Expr.unit => typecheckUnit ctx
    | Expr.str s => typecheckString ctx s
    | Expr.var x => typecheckVar ctx x
    | Expr.op e1 op e2 => typecheckOp ctx e1 e2 fuel op
    | Expr.newRef e => typecheckNewRef ctx e fuel
    | Expr.assign e1 e2 => typecheckAssign ctx e1 e2 fuel
    | Expr.deref e1 => typecheckDeref ctx e1 fuel
    | Expr.seq e1 e2 => typecheckSeq ctx e1 e2 fuel
    | Expr.kwhile e1 e2 => typecheckWhile ctx e1 e2 fuel
    | Expr.vlet x e1 e2 => typecheckVlet ctx x e1 e2 fuel
    | Expr.fn x paramType body returnType => typecheckFn ctx x paramType body returnType
    | Expr.pfn x paramType body returnType => typecheckPfn ctx x paramType body returnType
    | Expr.app e1 e2 => typecheckApp ctx e1 e2 fuel
    | Expr.ite e1 e2 e3 => typecheckIf ctx e1 e2 e3 fuel
    | Expr.rand e => typecheckRand ctx  e fuel
    | Expr.frand e => typecheckFrand ctx e fuel
    | Expr.printString e => typecheckPrintString ctx e fuel
    | Expr.printInt e => typecheckPrintInt ctx e fuel
    | Expr.unaryop op e => typecheckUnaryOp ctx op e fuel
    | Expr.externVal typ poison pred => typecheckExternVal ctx typ poison pred
    | Expr.externFn arg argTyp retSpec effects => typecheckExternFn ctx arg argTyp retSpec effects
    | Expr.externPfn arg argTyp retSpec => typecheckExternPfn ctx arg argTyp retSpec
termination_by fuel

/-- Helper function to run proper fixpoint computation for while loops.
    Re-types the guard each iteration, threads pc := pc ⊔ poison(guard),
    and joins Γ/ℒ from the body as in the Ott recurrences.
    Also tracks fresh location and tag counters through the fixpoint. -/
def runWhileFixpoint (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (pureGuard : Bool) (guardOpt : Option (Tag × Deps)) : TypecheckM (Poison × MemoryTypeEnv × TagEnv × Address × Tag) :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    -- (1) Typecheck the guard for this iteration
    let ctxForGuard := if pureGuard then { ctx with pureCtx := true } else ctx
    let guardRes ← typecheckExpr ctxForGuard e1 fuel
    let ⟨etyp1, p1, _⟩ := guardRes.qualType
    if etyp1 != ETyp.bool then throw "Condition of while must be bool"

    -- (2) Build body context: pc includes guard poison; take Γ from guard
    -- For pure guards (while_depoison): use Γ from guard but preserve ℒ (per Ott spec line 806)
    -- For impure guards (while_std): use both Γ and ℒ from guard (per Ott spec line 821)
    let bodyPcCtx : TypeContext := { ctx with pc := joinPoison ctx.pc p1 }
    -- strictly speaking this is not necessary because pure expressions do not modify envs,
    -- but we add it as extra precasion and to exactly match the Ott spec.
    let bodyTagEnv := if pureGuard then ctx.tagEnv else guardRes.tagEnv'
    let bodyEnvCtx : TypeContext := { bodyPcCtx with memEnv := guardRes.memEnv', tagEnv := bodyTagEnv }
    -- Body is typed in mode pm from outer context (per Ott spec)
    -- In practice, while loops can't appear in pure contexts, but we preserve ctx.pureCtx for correctness
    let bodyCtxBase : TypeContext := { bodyEnvCtx with nextLoc := guardRes.nextLoc', nextTag := guardRes.nextTag', pureCtx := ctx.pureCtx }
    let bodyCtx := match guardOpt with
      | some (k, deps) => { bodyCtxBase with tagEnv := bodyCtxBase.tagEnv.insert k (TagVal.mk true deps) }
      | none => bodyCtxBase

    -- (3) Typecheck the body
    let bodyRes ← typecheckExpr bodyCtx e2 fuel
    let ⟨etyp2, p2, _⟩ := bodyRes.qualType
    if etyp2 != ETyp.unit then throw "Body of while must have unit type"

    -- (4) Recurrences: pc_{i+1} = pc_i ⊔ p_{2,i}; Γ/ℒ joins with the body results
    let newPc := joinPoison ctx.pc p2
    let newMemEnv := joinMemEnvs ctx.memEnv bodyRes.memEnv'
    let newTagEnv := joinTagEnvs ctx.tagEnv bodyRes.tagEnv'

    -- (5) Fixpoint check
    if newMemEnv == ctx.memEnv && newPc == ctx.pc && newTagEnv == ctx.tagEnv then
      return (newPc, newMemEnv, newTagEnv, bodyRes.nextLoc', bodyRes.nextTag')
    else
      let nextCtx := { ctx with pc := newPc, memEnv := newMemEnv, tagEnv := newTagEnv, nextLoc := bodyRes.nextLoc', nextTag := bodyRes.nextTag' }
      runWhileFixpoint nextCtx e1 e2 fuel pureGuard guardOpt
termination_by fuel

/-- Rule: while_depoison (Ott rule: while_depoison when matchGuard succeeds)
-- Implements flow-sensitive analysis with predicate-based de-poisoning
-- Condition e1 is pure (doesn't modify G or L)
--/
def typecheckWhileDepoison (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (k : Tag) (deps : Deps) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    -- Run fixpoint computation with predicate-based de-poisoning (pure guard).
    -- Guard is typed under L (without k); body under L[k↦true] handled inside runWhileFixpoint.
    let (finalPc, finalMemEnv, finalTagEnv, finalNextLoc, finalNextTag) ← runWhileFixpoint ctx e1 e2 fuel true (some (k, deps))

    -- After loop termination, set k to false in the output environment
    let tagEnv' := finalTagEnv.insert k ⟨false, deps⟩

    let qt : QTyp := ⟨ETyp.unit, finalPc, Predicate.noPred⟩
    return { qualType := qt, memEnv' := finalMemEnv, tagEnv' := tagEnv', nextLoc' := finalNextLoc, nextTag' := finalNextTag }
termination_by fuel

/-- Rule: while_std (Ott rule: while_std when matchGuard fails)
-- Implements flow-sensitive analysis without predicate-based de-poisoning
-- Unlike while_depoison, e1 is not pure and can modify G and L
--/
def typecheckWhileStd (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    -- Run fixpoint computation (impure guard; re-types guard each iteration)
    let (finalPc, finalMemEnv, finalTagEnv, finalNextLoc, finalNextTag) ← runWhileFixpoint ctx e1 e2 fuel false none

    let qt : QTyp := ⟨ETyp.unit, finalPc, Predicate.noPred⟩
    return { qualType := qt, memEnv' := finalMemEnv, tagEnv' := finalTagEnv, nextLoc' := finalNextLoc, nextTag' := finalNextTag }
termination_by fuel



/- Rule : Ty rand typing
                pc; Γ; σ; L ⊢ e : int ▷ p {P} ⊣ Γ′; L′
                ---------------------------------------------------
                pc; Γ; σ; L ⊢ rand e : int ▷ pc ⊔ p {} ⊣ Γ′; L′
-/
def typecheckRand (ctx : TypeContext) (e : Expr) (fuel : Nat):TypecheckM TypeResult :=
  match fuel with
    | 0        => throw "Out of fuel"
    | fuel + 1 =>
            do
              let result ← typecheckExpr ctx e fuel
              let ⟨etyp, poison, _  ⟩ := result.qualType
              if etyp != ETyp.int then throw ("Argument Expression to rand must have type int")
              else
                let qt' : QTyp := ⟨ETyp.int , joinPoison ctx.pc poison, Predicate.noPred⟩
                return {result with qualType := qt' }
termination_by fuel

/- Rule: Ty frand typing
                  pc; Γ; σ; L ⊢ pe : int ▷ p {P} ⊣ Γ; L
                  fresh k
                  fresh x σ
                  pcl = (0 ≤ x ≤ pe, σ)
                  ------------------------------------------------------------------
                  pc; Γ; σ; L ⊢ frand pe : int ▷ poisoned {guard k pred closure pcl} ⊣ Γ; L

-/
def typecheckFrand (ctx : TypeContext) (e : Expr) (fuel : Nat):TypecheckM TypeResult :=
  match fuel with
  | 0        => throw "Out of fuel"
  | fuel + 1 =>
    do
      let result ← typecheckExpr ctx e fuel
      let ⟨etyp, _, _  ⟩ := result.qualType
      if etyp != ETyp.int then throw ("Argument Expression to frand must have type int")
      else
        let (newTag,result') := generateFreshTagRes result
        let varName := generateFreshVar ctx "limit" 0 fuel
        let predBody : PExpr <- Expr.toPExpr (Expr.op (Expr.op (Expr.var varName) Op.gte (Expr.num 0)) Op.and
                                 (Expr.op (Expr.var varName) Op.lte ( e)) )

        let depoisoningPred : Predicate := Predicate.guardClosure newTag varName predBody ctx.varEnv

        let qt' : QTyp := ⟨ETyp.int , true, depoisoningPred⟩
        return {result' with qualType := qt'}
termination_by fuel

/-
      pc ; G ; S ; L |- e : string :> p { P } -| G' ; L'
    ----------------------------------------------------------------------  :: printString_typing
      pc ; G ; S ; L |- printString e : unit :> join pc p { no_pred } -| G' ; L'
 -/
def typecheckPrintString (ctx : TypeContext) (e : Expr) (fuel : Nat):TypecheckM TypeResult :=
  match fuel with
    | 0        => throw "Out of fuel"
    | fuel + 1 =>
            do

              let result ← typecheckExpr ctx e fuel
              let ⟨etyp, poison, _  ⟩ := result.qualType
              if etyp != ETyp.string then throw ("Argument Expression to printString must have type string")
              else
                let qt' : QTyp := ⟨ETyp.unit , joinPoison ctx.pc poison, Predicate.noPred⟩
                return {result with qualType := qt' }
termination_by fuel

/-
              pc ; G ; S ; L |- e : int :> p { P } -| G' ; L'
    ----------------------------------------------------------------------  :: printInt_typing
      pc ; G ; S ; L |- printInt e : unit :> join pc p { no_pred } -| G' ; L'

 -/
def typecheckPrintInt (ctx : TypeContext) (e : Expr) (fuel : Nat):TypecheckM TypeResult :=
  match fuel with
    | 0        => throw "Out of fuel"
    | fuel + 1 =>
            do
              let result ← typecheckExpr ctx e fuel
              let ⟨etyp, poison, _  ⟩ := result.qualType
              if etyp != ETyp.int then throw ("Argument Expression to printInt must have type int")
              else
                let qt' : QTyp := ⟨ETyp.unit , joinPoison ctx.pc poison, Predicate.noPred⟩
                return {result with qualType := qt' }
termination_by fuel

/- Function to typecheck expressions in a binary-operation Expression, ensuring
   both expressions in a binary-op expression must be Integers .
-/
/-- Rule: op
-- pc ; G ; S ; L |- e1 : int :> p' { P1 } -| G' ; L'
-- pc ; G' ; S ; L' |- e2 : int :> p'' { P2 } -| G'' ; L''
-- op ∈ {+,-,*,/,>,>=,<,<=,==}
-- --------------------------------
-- pc ; G ; S ; L |- e1 op e2 : int :> join pc join p' p'' { no_pred } -| G'' ; L''
-/
def typecheckOp (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (op : Op) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    let result1 ← typecheckExpr ctx e1 fuel
    let ⟨etyp1, p1, _  ⟩ := result1.qualType

    -- Propagate fresh-name supplies from the condition into branch contexts
    let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag' }
    let result2 ← typecheckExpr ctx' e2 fuel
    let ⟨etyp2, p2, _  ⟩ := result2.qualType

    match opEType? op etyp1 etyp2 with
    | some r =>
        let poison := joinPoison ctx.pc (joinPoison p1 p2)
        let qt : QTyp := ⟨r, poison, Predicate.noPred⟩
        return { result2 with qualType := qt }
    | none => throw s!"Operation argument types do not match.\n  Left: {etyp1}\n  Op:   {op}\n  Right: {etyp2}"
termination_by fuel

/-- Rule: ref (Ott rule: ref)
-- pc ; G ; S ; L |- e : T :> p { P } -| G' ; L'
-- fresh l
-- -----------------------
-- pc ; G ; S ; L |- ref e : ref T @ l :> pc { no_pred } -| G'[l |-> T :> join pc p { P }] ; L'
-/
def typecheckNewRef (ctx : TypeContext) (e : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    let result ← typecheckExpr ctx e fuel
    let ⟨etyp, poison, pred ⟩ := result.qualType

    -- Generate fresh location (simplified)
    let (l, result') := freshTLocRes result
    let storedPoison := joinPoison ctx.pc poison
    let storedQt : QTyp := ⟨etyp, storedPoison, pred⟩
    let memEnv' := updateMemEnv result'.memEnv' l storedQt

    let qt : QTyp := ⟨ETyp.ref etyp l, ctx.pc, Predicate.noPred⟩
    return { qualType := qt, memEnv' := memEnv', tagEnv' := result'.tagEnv', nextLoc' := result'.nextLoc', nextTag' := result'.nextTag' }
termination_by fuel

/-- Rule: assign (Ott rule: assign)
-- pc ; G ; S ; L |- e1 : ref T @ l :> p' { P' } -| G' ; L'
-- pc ; G' ; S ; L' |- e2 : T :> p'' { P'' } -| G'' ; L''
-- -----------------------
-- pc ; G ; S ; L |- e1 := e2 : unit :> join pc p' { no_pred } -| G''[l |-> T :> join pc join p' p'' { P'' }] ; L''
-/
def typecheckAssign (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    let result1 ← typecheckExpr ctx e1 fuel
    let ⟨etyp1, p1, _  ⟩ := result1.qualType
    match etyp1 with
    | ETyp.ref t l =>
      let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag' }
      let result2 ← typecheckExpr ctx' e2 fuel
      let ⟨etyp2, p2, pred2  ⟩ := result2.qualType
      if etyp2 != t then throw "Type mismatch in assignment"

      let storedPoison := joinPoison ctx.pc (joinPoison p1 p2)
      let storedQt : QTyp := ⟨t, storedPoison, pred2⟩
      let memEnv' := updateMemEnv result2.memEnv' l storedQt

      let resultPoison := joinPoison ctx.pc p1
      let qt : QTyp := ⟨ETyp.unit, resultPoison, Predicate.noPred⟩
      -- Invalidate dependencies on write (Ott rule: assign)
      let tagEnv' := invalidateTagDeps result2.tagEnv' l
      return { qualType := qt, memEnv' := memEnv', tagEnv' := tagEnv', nextLoc' := result2.nextLoc', nextTag' := result2.nextTag'  }
    | _ => throw "Left operand of assignment must be a reference"
termination_by fuel

/-- Rules: deref_* (Ott rules: deref_poisoned, deref_no_pred, deref_guard_true, deref_guard_false, deref_guard_unknown)
--/
def typecheckDeref (ctx : TypeContext) (e : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    let result ← typecheckExpr ctx e fuel
    let ⟨etyp, poison, _pred ⟩ := result.qualType
    match etyp with
    | ETyp.ref t l =>
      match result.memEnv'.get? l with
      | some ⟨etyp', p2, pred⟩ =>
        -- Check type equality first, before any poison or predicate handling
        if etyp' != t then throw s!"Type mismatch in dereference: {repr etyp'} != {repr t}"
        -- Check if reference itself is poisoned
        if poison then
          -- Reference is poisoned: always return poisoned with no predicate
          -- Ott rule: deref_poisoned
          let qt : QTyp := ⟨t, true, Predicate.noPred⟩  -- poisoned, no_pred
          return { qualType := qt, memEnv' := result.memEnv', tagEnv' := result.tagEnv', nextLoc' := result.nextLoc', nextTag' := result.nextTag' }
        else
          -- Reference is clean: proceed with normal predicate handling
          match pred with
          | Predicate.noPred =>  -- Ott rule: deref_no_pred
            let poison := joinPoison ctx.pc p2
            let qt : QTyp := ⟨t, poison, Predicate.noPred⟩
            return { qualType := qt, memEnv' := result.memEnv', tagEnv' := result.tagEnv', nextLoc' := result.nextLoc', nextTag' := result.nextTag' }
          | Predicate.guardOnly k | Predicate.guardClosure k _ _ _ =>
            -- Both guard types behave the same for dereference
            match result.tagEnv'.get? k with
            | some ⟨true, _deps⟩ =>
              -- Ott rule: deref_guard_true / deref_guard_only_true
              let poison := ctx.pc
              let qt : QTyp := ⟨t, poison, Predicate.noPred⟩
              return { qualType := qt, memEnv' := result.memEnv', tagEnv' := result.tagEnv', nextLoc' := result.nextLoc', nextTag' := result.nextTag' }
            | some ⟨false, _deps⟩ =>
              -- Ott rule: deref_guard_false / deref_guard_only_false
              let qt : QTyp := ⟨t, true, Predicate.noPred⟩  -- poisoned
              return { qualType := qt, memEnv' := result.memEnv', tagEnv' := result.tagEnv', nextLoc' := result.nextLoc', nextTag' := result.nextTag' }
            | none =>
              -- Ott rule: deref_guard_unknown / deref_guard_only_unknown
              let poison := joinPoison ctx.pc p2
              -- Preserve the original predicate (either guardOnly or guardClosure)
              let qt : QTyp := ⟨t, poison, pred⟩
              return { qualType := qt, memEnv' := result.memEnv', tagEnv' := result.tagEnv', nextLoc' := result.nextLoc', nextTag' := result.nextTag' }
      | none => throw s!"Location {l} not found in memory environment"
    | _ => throw "Operand of dereference must be a reference"
termination_by fuel

/-- Rule: seq (Ott rule: seq)
-- pc ; G ; S ; L |- e1 : T1 :> p' { P' } -| G' ; L'
-- pc ; G' ; S ; L' |- e2 : T2 :> p'' { P'' } -| G'' ; L''
-- --------------------------------
-- pc ; G ; S ; L |- e1 ; e2 : T2 :> join p' p'' { P'' } -| G'' ; L''
-/
def typecheckSeq (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    let result1 ← typecheckExpr ctx e1 fuel
    let ⟨_etyp1, p1, _  ⟩ := result1.qualType

    let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag' }
    let result2 ← typecheckExpr ctx' e2 fuel
    let ⟨etyp2, p2, pred2  ⟩ := result2.qualType

    let poison := joinPoison p1 p2
    let qt : QTyp := ⟨etyp2, poison, pred2⟩
    return { qualType := qt, memEnv' := result2.memEnv', tagEnv' := result2.tagEnv', nextLoc' := result2.nextLoc', nextTag' := result2.nextTag' }
termination_by fuel


/-- Rule: app_fn (Ott rules: app_fn, app_pfn)
  pc ; G ; S ; L |- e1 : ST1 -> ST2 # p typing_closure ( x , e , S' ) :> p1 { P1 } -| G' ; L'
  pc ; G' ; S ; L' |- e2 : T1 :> p2 { P2 } -| G'' ; L''
  ST1 <: T1
  pc ; G'' ; S'[x |-> T1 :> join pc p2 { P2 }] ; L'' |- e : T2 :> p3 { P3 } -| G''' ; L'''
  ST2 <: T2
----------------------------------------------------------------------  :: app_fn
  pc ; G ; S ; L |- e1 e2 : T2 :> join pc p3 { P3 } -| G''' ; L'''


  pc ; G ; S ; L |- e1 : ST1 -> ST2 # p typing_closure ( x , pe , S' ) :> p1 { P1 } -| G' ; L'
  pc ; G' ; S ; L' |- e2 : T1 :> p2 { P2 } -| G'' ; L''
  ST1 <: T1
  pc ; G'' ; S'[x |-> T1 :> join pc p2 { P2 }] ; L'' |- pe : T2 :> p3 { P3 } -| G''' ; L'''
  ST2 <: T2
----------------------------------------------------------------------  :: app_pfn
  pc ; G ; S ; L |- e1 e2 : T2 :> join pc p3 { P3 } -| G''' ; L'''

-/
def typecheckApp (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    -- Premise 1: pc ; G ; S ; L |- e1 : ST1 -> ST2 # p typing_closure ( x , e , S' ) :> p1 { P1 } -| G' ; L'
    let result1 ← typecheckExpr ctx e1 fuel
    let ⟨etyp1, p1, _pred1⟩ := result1.qualType
    match etyp1 with
    | ETyp.arrow st1 st2 p tcl =>
      -- In pure context, disallow applying impure arrow
      if ctx.pureCtx then
        throw "Pure context disallows application of impure function"
      -- Premise 2: pc ; G' ; S ; L' |- e2 : T1 :> p2 { P2 } -| G'' ; L''
      let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag' }
      let result2 ← typecheckExpr ctx' e2 fuel
      let ⟨etyp2, p2, pred2⟩ := result2.qualType

      -- Premise 3: ST1 <: T1 (check subtyping)
      if not (isSubtype st1 result2.qualType) then
        throw s!"Type mismatch in function application: parameter type {repr st1} is not compatible with argument type {repr (QTyp.toTyp result2.qualType)}"

      match tcl with
      | FnTClosure.regular x body env =>
        -- Premise 4: pc ; G'' ; S'[x |-> T1 :> join pc p2 { P2 }] ; L'' |- e : T2 :> p3 { P3 } -| G''' ; L'''
        let argQt : QTyp := ⟨etyp2, joinPoison ctx.pc p2, pred2⟩
        let env' := VarTypeEnv.update env x argQt
        let ctx'' := { ctx with pc := joinPoison p (joinPoison ctx.pc p1), memEnv := result2.memEnv', varEnv := env', tagEnv := result2.tagEnv' ,nextTag := result2.nextTag', nextLoc := result2.nextLoc' }

        let result3 ← typecheckExpr ctx'' body fuel
        let ⟨etyp3, p3, pred3⟩ := result3.qualType

        -- Premise 5: ST2 <: T2 (check subtyping)
        if not (isSubtype st2 result3.qualType) then
          throw s!"Type mismatch in function application: return type {repr st2} is not compatible with body type {repr (QTyp.toTyp result3.qualType)}"

        -- Conclusion: pc ; G ; S ; L |- e1 e2 : T2 :> join pc p3 { P3 } -| G''' ; L'''
        let poison := joinPoison ctx.pc p3
        let qt : QTyp := ⟨etyp3, poison, pred3⟩
        return { qualType := qt, memEnv' := result3.memEnv', tagEnv' := result3.tagEnv', nextLoc' := result3.nextLoc', nextTag' := result3.nextTag' }
      | FnTClosure.extern x retSpec effects capturedEnv =>
        -- Extern function application logic
        -- 1. Build unified environment: extend capturedEnv with argument
        let argQt := ⟨etyp2, joinPoison ctx.pc p2, pred2⟩
        let unifiedEnv := VarTypeEnv.update capturedEnv x argQt

        -- 2. Process effects: update Γ for each effect target
        let mut memEnv := result2.memEnv'
        let mut nextLoc := result2.nextLoc'
        for effect in effects do
          match effect.target with
          | EffectTarget.namedVar v =>
              -- Resolve v in unifiedEnv to get ref location
              match unifiedEnv.lookup v with
              | some qt =>
                  match qt.etyp with
                  | ETyp.ref _t l =>
                      -- Convert effect spec to QTyp and update Γ(l)
                      let effectQt ← effectSpecToQTyp effect.poison effect.pred unifiedEnv
                      let storedQt := ⟨effectQt.etyp, joinPoison ctx.pc effectQt.poison, effectQt.pred⟩
                      memEnv := memEnv.insert l storedQt
                  | _ => throw s!"Effect target {v} must be a reference type"
              | none => throw s!"Effect target {v} not found in environment"
          | EffectTarget.returnValue =>
              -- Will be handled when processing return spec if it's a ref type
              pure ()

        -- 3. Handle return spec (simple or nested)
        match retSpec with
        | ExternReturn.simple typ poison pred =>
            -- Simple return type
            let (retQt, nextLoc') ← returnSpecToQTyp typ poison pred unifiedEnv nextLoc

            -- If return type is ref and there's a "return" effect, update Γ at that location
            match retQt.etyp with
            | ETyp.ref _t l =>
                -- Check for "return" effect
                let returnEffect := effects.find? (fun eff =>
                  match eff.target with
                  | EffectTarget.returnValue => true
                  | _ => false)
                match returnEffect with
                | some eff =>
                    let effectQt ← effectSpecToQTyp eff.poison eff.pred unifiedEnv
                    let storedQt := ⟨effectQt.etyp, joinPoison ctx.pc effectQt.poison, effectQt.pred⟩
                    memEnv := memEnv.insert l storedQt
                | none => pure ()
            | _ =>
                -- Non-ref return: verify no "return" effect exists
                let hasReturnEffect := effects.any (fun eff =>
                  match eff.target with
                  | EffectTarget.returnValue => true
                  | _ => false)
                if hasReturnEffect then
                  throw "Effect on 'return' is only valid when return type is a reference"

            let poison' := joinPoison ctx.pc retQt.poison
            let qt := ⟨retQt.etyp, poison', retQt.pred⟩
            return { qualType := qt, memEnv' := memEnv, tagEnv' := result2.tagEnv',
                     nextLoc' := nextLoc', nextTag' := result2.nextTag' }

        | ExternReturn.nestedFn innerArg innerArgTyp innerRet innerEffects =>
            -- Nested extern function: return a closure
            let innerTcl := FnTClosure.extern innerArg innerRet innerEffects unifiedEnv
            let innerArrowTyp := ETyp.arrow innerArgTyp (parseReturnType innerRet) ctx.pc innerTcl
            let qt := ⟨innerArrowTyp, ctx.pc, Predicate.noPred⟩
            return { qualType := qt, memEnv' := memEnv, tagEnv' := result2.tagEnv',
                     nextLoc' := nextLoc, nextTag' := result2.nextTag' }

        | ExternReturn.nestedPfn innerArg innerArgTyp innerRet =>
            -- Nested extern pure function: return a closure
            let innerTcl := PFnTClosure.extern innerArg innerRet unifiedEnv
            let innerArrowTyp := ETyp.parrow innerArgTyp (parseReturnType innerRet) ctx.pc innerTcl
            let qt := ⟨innerArrowTyp, ctx.pc, Predicate.noPred⟩
            return { qualType := qt, memEnv' := memEnv, tagEnv' := result2.tagEnv',
                     nextLoc' := nextLoc, nextTag' := result2.nextTag' }
    | ETyp.parrow st1 st2 p tcl =>
      -- Premise 2: pc ; G' ; S ; L' |- e2 : T1 :> p2 { P2 } -| G'' ; L''
      let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag' }
      let result2 ← typecheckExpr ctx' e2 fuel
      let ⟨etyp2, p2, pred2⟩ := result2.qualType

      -- Premise 3: ST1 <: T1 (check subtyping)
      if not (isSubtype st1 result2.qualType) then
        throw s!"Type mismatch in function application: parameter type {repr st1} is not compatible with argument type {repr (QTyp.toTyp result2.qualType)}"

      match tcl with
      | PFnTClosure.regular x body env =>
        -- Premise 4: pc ; G'' ; S'[x |-> T1 :> join pc p2 { P2 }] ; L'' |- pe : T2 :> p3 { P3 } -| G''' ; L'''
        let argQt : QTyp := ⟨etyp2, joinPoison ctx.pc p2, pred2⟩
        let env' := VarTypeEnv.update env x argQt
        -- Set pure context for the body re-typechecking
        let ctx'' := { ctx with memEnv := result2.memEnv',pc := joinPoison p (joinPoison ctx.pc p1), varEnv := env', tagEnv := result2.tagEnv', pureCtx := true, nextLoc := result2.nextLoc', nextTag := result2.nextTag' }
        let result3 ← typecheckExpr ctx'' (PExpr.toExpr body) fuel
        let ⟨etyp3, p3, pred3⟩ := result3.qualType

        -- Premise 5: ST2 <: T2 (check subtyping)
        if not (isSubtype st2 result3.qualType) then
          throw s!"Type mismatch in function application: return type {repr st2} is not compatible with body type {repr (QTyp.toTyp result3.qualType)}"

        -- Conclusion: pc ; G ; S ; L |- e1 e2 : T2 :> join pc p3 { P3 } -| G''' ; L'''
        let poison := joinPoison ctx.pc p3
        let qt : QTyp := ⟨etyp3, poison, pred3⟩
        return { qualType := qt, memEnv' := result3.memEnv', tagEnv' := result3.tagEnv', nextLoc' := result3.nextLoc', nextTag' := result3.nextTag' }
      | PFnTClosure.extern x retSpec capturedEnv =>
        -- Extern pure function application (no effects)
        let argQt := ⟨etyp2, joinPoison ctx.pc p2, pred2⟩
        let unifiedEnv := VarTypeEnv.update capturedEnv x argQt

        let mut nextLoc := result2.nextLoc'

        -- Handle return spec (simple or nested)
        match retSpec with
        | ExternReturn.simple typ poison pred =>
            -- Simple return type
            let (retQt, nextLoc') ← returnSpecToQTyp typ poison pred unifiedEnv nextLoc

            let poison' := joinPoison ctx.pc retQt.poison
            let qt := ⟨retQt.etyp, poison', retQt.pred⟩
            return { qualType := qt, memEnv' := result2.memEnv', tagEnv' := result2.tagEnv',
                     nextLoc' := nextLoc', nextTag' := result2.nextTag' }

        | ExternReturn.nestedFn innerArg innerArgTyp innerRet innerEffects =>
            -- Nested extern impure function: return a closure
            let innerTcl := FnTClosure.extern innerArg innerRet innerEffects unifiedEnv
            let innerArrowTyp := ETyp.arrow innerArgTyp (parseReturnType innerRet) ctx.pc innerTcl
            let qt := ⟨innerArrowTyp, ctx.pc, Predicate.noPred⟩
            return { qualType := qt, memEnv' := result2.memEnv', tagEnv' := result2.tagEnv',
                     nextLoc' := nextLoc, nextTag' := result2.nextTag' }

        | ExternReturn.nestedPfn innerArg innerArgTyp innerRet =>
            -- Nested extern pure function: return a closure
            let innerTcl := PFnTClosure.extern innerArg innerRet unifiedEnv
            let innerArrowTyp := ETyp.parrow innerArgTyp (parseReturnType innerRet) ctx.pc innerTcl
            let qt := ⟨innerArrowTyp, ctx.pc, Predicate.noPred⟩
            return { qualType := qt, memEnv' := result2.memEnv', tagEnv' := result2.tagEnv',
                     nextLoc' := nextLoc, nextTag' := result2.nextTag' }

    | _ => throw "Left operand of application must be a function"
termination_by fuel


/-- Rule: let (Ott rule: let)
      --  pc ; G ; S ; L |- e1 : T :> p1 { P1 } -| G' ; L'
      --  pc ; G' ; S[x |-> T :> p1  { P1 }] ; L' |- e2 : T2 :> p2 { P2 } -| G'' ; L''
          ----------------------------------------------------------------------  :: let
      --  pc ; G ; S ; L |- let x = e1 in e2 : T2 :> join pc p2 { P2 } -| G'' ; L''
  -/
def typecheckVlet (ctx : TypeContext) (x : Name) (e1 : Expr) (e2 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    let result1 ← typecheckExpr ctx e1 fuel
    let varEnv' := ctx.varEnv.update x result1.qualType
    let ctx' := { ctx with memEnv := result1.memEnv', varEnv := varEnv', tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag' }

    let result2 ← typecheckExpr ctx' e2 fuel
    let ⟨etyp2, p2, pred2⟩ := result2.qualType
   --dbg_trace s!" In typecheck Let ,Poison val for exp {e1} is {p1}"
   -- dbg_trace s!"In typecheck Let ,Poison val for exp {e2} is {p2}"

    let poison := joinPoison ctx.pc p2
    let qt : QTyp := ⟨etyp2, poison, pred2⟩
    return { qualType := qt, memEnv' := result2.memEnv', tagEnv' := result2.tagEnv', nextLoc' := result2.nextLoc', nextTag' := result2.nextTag' }
termination_by fuel


/-- Rule: if_depoison and if_std (Ott rules: if_depoison when matchGuard succeeds, if_std when it fails)
-- First tries predicate-based de-poisoning, falls back to standard conditional typing
--/
def typecheckIf (ctx : TypeContext) (e1 e2 e3 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    -- Step 1: Try matchGuard first (before typechecking e1)
    match matchGuard e1 ctx.memEnv ctx.varEnv with
    | .ok (k, deps) => do
      -- Predicate-based case (if_depoison)

      -- Step 2: Typecheck e1 in pure mode
      let pureCtx := { ctx with pureCtx := true }
      let result1 ← typecheckExpr pureCtx e1 fuel
      let ⟨etyp1, p', _  ⟩ := result1.qualType
      if etyp1 != ETyp.bool then throw "Condition of if must be bool"

      -- Step 3: Use original memEnv and tagEnv for both branches, with tagEnv modified by guard
      let ctxTrue := { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ }
      let ctxFalse := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩ }

      let result2 ← typecheckExpr ctxTrue e2 fuel
      let ⟨etyp2, p'', _  ⟩ := result2.qualType
      --dbg_trace s!" Poison val for {e2} is {p''}"

      -- Ensure disjoint fresh supplies across branches by advancing the false-branch supply
      let ctxFalse' := { ctxFalse with nextLoc := result2.nextLoc', nextTag := result2.nextTag' }
      let result3 ← typecheckExpr ctxFalse' e3 fuel
      let ⟨etyp3, p''', _  ⟩ := result3.qualType
      --dbg_trace s!" Poison val for {e3} is {p'''}"

      -- Use signature-based equality for type checking (not structural equality of closures)
      -- Structural equality compares closures including their bodies, which is too strict for type checking
      -- We only need to check that function signatures match (parameter type, return type, poison flag)
      if not (beqETypSignature etyp2 etyp3) then throw s!"Branches of if must have same type (etyp2: {etyp2}, etyp3: {etyp3})"

      let poison := joinPoison ctx.pc (joinPoison p'' p''')
     -- dbg_trace s!" Result Poison val for if is {poison}"
      let qt : QTyp := ⟨etyp2, poison, Predicate.noPred⟩
      let memEnv' := joinMemEnvs result2.memEnv' result3.memEnv'
      let nextLoc' := max result2.nextLoc' result3.nextLoc'
      let nextTag' := max result2.nextTag' result3.nextTag'
      -- Step 4: Return original tag environment (k becomes unknown after conditional)
      return { qualType := qt, memEnv' := memEnv', tagEnv' := ctx.tagEnv, nextLoc' := nextLoc', nextTag' := nextTag' }

    | .error _ => do
      -- Standard case (if_std) - no matching predicate found
      -- Typecheck e1 first
      let result1 ← typecheckExpr ctx e1 fuel
      let ⟨etyp1, p', _  ⟩ := result1.qualType
      if etyp1 != ETyp.bool then throw "Condition of if must be bool"

      let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag' }

      --dbg_trace "No tag found"
      let branchPc := joinPoison ctx.pc p'
      --dbg_trace s!" Branch pc for Typecheck if with condition {e1} is {branchPc}"
      let ctx'' := { ctx' with pc := branchPc }

      let result2 ← typecheckExpr ctx'' e2 fuel
      let ⟨etyp2, p'', _  ⟩ := result2.qualType

      -- Ensure disjoint fresh supplies across branches by advancing the second branch supply
      let ctxForE3 := { ctx'' with nextLoc := result2.nextLoc', nextTag := result2.nextTag' }
      let result3 ← typecheckExpr ctxForE3 e3 fuel
      let ⟨etyp3, p''', _  ⟩ := result3.qualType

      -- Use signature-based equality for type checking (not structural equality of closures)
      -- Structural equality compares closures including their bodies, which is too strict for type checking
      -- We only need to check that function signatures match (parameter type, return type, poison flag)
      if not (beqETypSignature etyp2 etyp3) then throw s!"Branches of if must have same type (etyp2: {etyp2}, etyp3: {etyp3})"

      let poison := joinPoison ctx.pc (joinPoison p' (joinPoison p'' p'''))
      let qt : QTyp := ⟨etyp2, poison, Predicate.noPred⟩
      let memEnv' := joinMemEnvs result2.memEnv' result3.memEnv'
      let nextLoc' := max result2.nextLoc' result3.nextLoc'
      let nextTag' := max result2.nextTag' result3.nextTag'
      return { qualType := qt, memEnv' := memEnv', tagEnv' := ctx'.tagEnv, nextLoc' := nextLoc', nextTag' := nextTag' }
termination_by fuel



/- Rule: not_expr_typing (Ott rule: not_expr_typing)

pm ; pc ; G ; S ; L |- e : bool :> p { P } -| G' ; L'
----------------------------------------------------------------------  :: not_expr_typing
pm ; pc ; G ; S ; L |- not_expr e : bool :> join pc p { no_pred } -| G' ; L'

-/

def typecheckUnaryOp (ctx : TypeContext) (op : UnaryOp) (e : Expr) (fuel : Nat):TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    let result ← typecheckExpr ctx e fuel
    let ⟨etyp, p, _  ⟩ := result.qualType

    match opUnaryEType? op etyp with
    | some r =>
        let poison := joinPoison ctx.pc p
        let qt : QTyp := ⟨r, poison, Predicate.noPred⟩
        return { result with qualType := qt }
    | none => throw s!"Operation argument types do not match.\n  Expression Type: {etyp}\n  UnaryOp: {op}"
termination_by fuel



/-- Rule: while_depoison and while_std (Ott rules: while_depoison when matchGuard succeeds, while_std when it fails)
-- Implements flow-sensitive analysis based on Hunt & Sands 2006
--/
def typecheckWhile (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    -- Step 1: Try matchGuard first (as in typecheckIf)
    match matchGuard e1 ctx.memEnv ctx.varEnv with
    | .ok (k, deps) => do
      -- Predicate-based case (while_depoison) - condition is pure
      typecheckWhileDepoison ctx e1 e2 fuel k deps
    | .error _ => do
      -- Standard case (while_std) - condition can modify G and L
      typecheckWhileStd ctx e1 e2 fuel
termination_by fuel

end

-- Main type checking function
def typecheck (ctx : TypeContext) (e : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  typecheckExpr ctx e fuel



/-- Type check an expression in an initial empty context -/
def typecheckExprSimple (e : Expr) : TypecheckM QTyp := do
  let initialCtx : TypeContext := {
    pc := false  -- clean
    memEnv := {}
    varEnv := []
    tagEnv := {}
    nextLoc := 0
    nextTag := 1
    pureCtx := false
  }
  let result ← typecheck initialCtx e defaultFuel
  return result.qualType

def typecheckExprVerbose (e : Expr) : TypecheckM TypeResult := do
  let initialCtx : TypeContext := {
    pc := false  -- clean
    memEnv := {}
    varEnv := []
    tagEnv := {}
    nextLoc := 0
    nextTag := 1
    pureCtx := false
  }
  typecheck initialCtx e defaultFuel


/-- Type check a program (expression) and return a human-readable result -/
def typecheckProgram (e : Expr) (verbose : Bool) : String :=
  if verbose then
    match typecheckExprVerbose e with
    | .ok result => s!"Type: {repr result.qualType} , MemoryTypeEnv : {repr result.memEnv'} , tagEnv : {repr result.tagEnv'} , nextLoc : {repr result.nextLoc'} "
    | .error msg => s!"Type error: {msg}"
  else
    match typecheckExprSimple e   with
    | .ok qualType  => s!"Type: {repr qualType}"
    | .error msg => s!"Type error: {msg}"
