import LeanPoison.Syntax
import LeanPoison.Misc

import Std.Data.ExtTreeMap
open Std
open LeanPoison

-- Type checking environment definitions

/-- Comparison for variable names (Name is String in this project). -/
abbrev varTypeEnvCmp : Name → Name → Ordering := compare

instance : ReflCmp varTypeEnvCmp := by
  infer_instance

instance : LawfulEqCmp varTypeEnvCmp := by
  infer_instance

instance : OrientedCmp varTypeEnvCmp := by
  infer_instance

instance : TransCmp varTypeEnvCmp := by
  infer_instance

/-- Default fuel for type checking -/
private def defaultFuel : Nat := 1000

/-- Memory typing environment (Γ in the Ott spec), keyed by logical locations. -/
abbrev MemoryTypeEnv := ExtTreeMap Loc QTyp

/-- Variable typing environment (σ in the Ott spec), keyed by names. -/
abbrev VarTypeEnv := ExtTreeMap Name QTyp varTypeEnvCmp

namespace VarTypeEnv

  @[inline] def lookup (env : VarTypeEnv) (x : Name) : Option QTyp :=
    env.get? x

  @[inline] def update (env : VarTypeEnv) (x : Name) (qt : QTyp) : VarTypeEnv :=
    env.insert x qt

  /-- `env` contains a binding for `x`. -/
  def hasKey (env : VarTypeEnv) (x : Name) : Prop :=
    env.contains x

  @[inline] def toCaptured (env : VarTypeEnv) : CapturedVarEnv :=
    ExtTreeMap.toList env

  @[inline] def ofCaptured (env : CapturedVarEnv) : VarTypeEnv :=
    env.foldr (fun (entry : Name × QTyp) acc => acc.insert entry.1 entry.2) ({} : VarTypeEnv)

  @[inline] def foldl (init : δ) (f : δ → Name → QTyp → δ) (env : VarTypeEnv) : δ :=
    ExtTreeMap.foldl (f := f) (init := init) env

  @[inline] def foldlM [Monad m] [LawfulMonad m] (init : δ) (f : δ → Name → QTyp → m δ) (env : VarTypeEnv) : m δ :=
    ExtTreeMap.foldlM (f := f) (init := init) env

end VarTypeEnv

namespace MemoryTypeEnv

  @[inline] def lookup (m : MemoryTypeEnv) (l : Loc) : Option QTyp :=
    m.get? l

  @[inline] def update (m : MemoryTypeEnv) (l : Loc) (qt : QTyp) : MemoryTypeEnv :=
    m.insert l qt

  /-- `m` contains a binding for `a`. -/
  def hasKey (m : MemoryTypeEnv) (l : Loc) : Prop :=
    m.contains l

  /-- Sub-environment: every binding in `m₁` appears in `m₂`. -/
  def subset (m₁ m₂ : MemoryTypeEnv) : Prop :=
    ∀ {l qt}, m₁.lookup l = some qt → m₂.lookup l = some qt

  scoped infix:50 " ⊆ " => MemoryTypeEnv.subset

  /-- Extensional equality of memory typing environments. All keys and values must be equal. -/
  def equiv (m₁ m₂ : MemoryTypeEnv) : Prop :=
    (ExtTreeMap.toList m₁) == (ExtTreeMap.toList m₂)

  instance : BEq MemoryTypeEnv where
    beq m₁ m₂ := (ExtTreeMap.toList m₁) == (ExtTreeMap.toList m₂)

  instance : Repr MemoryTypeEnv where
    reprPrec m _ := s!"ofList {repr (ExtTreeMap.toList m)}"

end MemoryTypeEnv

/-- Dependency set for tracking logical locations read by predicates -/
abbrev Deps := LocSet

/-- Tag valuation with dependency information -/
structure TagVal where
  value : Bool
  deps : LocSet
  deriving Repr, BEq

/-- Tag valuation environment (ℒ in the Ott spec) -/
abbrev TagEnv := ExtTreeMap Tag TagVal

namespace TagEnv

instance : BEq TagEnv where
  beq m₁ m₂ := (ExtTreeMap.toList m₁) == (ExtTreeMap.toList m₂)

instance : Repr TagEnv where
  reprPrec m _ := s!"ofList {repr (ExtTreeMap.toList m)}"

end TagEnv

/-- Remove from tag environment all entries whose dependency sets intersect the given locset. -/
def invalidateTagDeps (env : TagEnv) (ls : LocSet) : TagEnv :=
  env.filter (fun _ tv =>
    not <| tv.deps.any ls.contains)

/-- Regime: bounded partial mapping from guard tags to their truth values.
    The `bound` field ensures regimes only interpret input/spec tags (tags < bound),
    excluding fresh internal tags introduced during typing (tags ≥ bound). -/
structure Regime where
  bound : Tag
  map : ExtTreeMap Tag Bool

namespace Regime

/-- Lookup a tag in the regime map, respecting the bound. -/
def lookup? (R : Regime) (k : Tag) : Option Bool :=
  if k < R.bound then R.map.get? k else none

end Regime

/-- Empty regime: all tags return none (regime-agnostic typing) -/
def emptyRegime : Regime := {
  bound := 0
  map := {}
}

/-- Invalidate regime entries for tags whose dependencies intersect written locations
    (mirrors invalidateTagDeps behaviour) -/
def invalidateRegimeDeps (R : Regime) (env : TagEnv) (ls : LocSet) : Regime :=
  let invalidated := env.filter (fun _ tv => not <| tv.deps.any ls.contains)
  let invalidatedMap := R.map.filter (fun k _ => invalidated.contains k)
  { bound := R.bound, map := invalidatedMap }

/-- Join two regimes (conservative intersection: keep only entries that agree) -/
def joinRegimes (R1 R2 : Regime) : Regime :=
  let joinedMap :=
    combineExtTreeMaps R1.map R2.map (fun _ ob1 ob2 =>
      match ob1, ob2 with
      | some b1, some b2 => if b1 == b2 then some b1 else none
      | _, _ => none)
  { bound := min R1.bound R2.bound, map := joinedMap }

namespace Regime

-- Regime monotonicity: R' can only drop entries (never change values or add new entries)
-- Three constraints:
--   1. bounds are equal
--   2. preserved entries keep their values
--   3. R' can't have entries that R doesn't have (no new entries)
def monotoneStep (R R' : Regime) : Prop :=
  R'.bound = R.bound ∧
  (∀ k b, R.lookup? k = some b → (R'.lookup? k = some b ∨ R'.lookup? k = none)) ∧
  (∀ k, R'.lookup? k ≠ none → R.lookup? k ≠ none)

end Regime

/-- Type checking context containing all environments -/
structure TypeContext where
  pc : Poison            -- Poison context
  regime : Regime        -- R (regime for FR reasoning)
  memEnv : MemoryTypeEnv -- Γ
  varEnv : VarTypeEnv    -- σ
  tagEnv : TagEnv        -- ℒ
  nextLoc : Loc  -- for fresh logical location generation
  nextTag : Tag  -- for fresh location generation
  pureCtx : Bool -- whether we are inside a pure function body typing

/-- Type checking result: qualified type and updated memory environment -/
structure TypeResult where
  qualType : QTyp -- Qualified type of the expression
  memEnv' : MemoryTypeEnv -- Updated memory typing environment
  tagEnv' : TagEnv  -- Updated logical environment
  nextLoc' : Loc -- Updated next logical location
  nextTag' : Tag -- Updated next location
  regime' : Regime -- Updated regime after typing step

/-- Type checking monad for error handling -/
abbrev TypecheckM := Except String

/-- Update the context with the result of a type checking operation -/
def updateCtxFromResult (ctx : TypeContext) (result : TypeResult) : TypeContext :=
  { ctx with memEnv := result.memEnv', tagEnv := result.tagEnv', nextLoc := result.nextLoc', nextTag := result.nextTag', regime := result.regime' }

/-- Extract dependencies from a predicate by analyzing free variables in the predicate body -/
def extractDepsFromPred (pred : Predicate) : TypecheckM Deps :=
  match pred with
  | Predicate.guardClosure _tag arg_name pred_body var_env =>
    let varEnvMap := VarTypeEnv.ofCaptured var_env
    let rec extractDepsFromPExpr (pe : PExpr) (boundVars : List Name) (env : VarTypeEnv) (fuel : Nat) : TypecheckM Deps :=
      match fuel with
      | 0 => throw "Out of fuel while extracting dependencies"
      | fuel + 1 =>
        match pe with
        | PExpr.var x =>
          if boundVars.contains x then return LocSet.empty  -- Bound variable, not free
          else
            match env.get? x with
            | some qt =>
              match qt.etyp with
              | ETyp.ref _t ls => return ls  -- Reference type, add referenced locset
              | ETyp.parrow _argTy _retTy _poison tcls =>
                -- Pure function, recurse into all closures' bodies
                match tcls with
                | [PFnTClosure.regular argName body varEnv'] =>
                    -- Single closure, recurse into its body
                    extractDepsFromPExpr body (argName :: boundVars) (VarTypeEnv.ofCaptured varEnv') fuel
                | _ => return LocSet.empty  -- Multiple or extern closures: conservative fallback
              | _ => return LocSet.empty  -- Other types don't read from heap
            | none => throw s!"Variable {x} not found in environment while extracting dependencies"
        | PExpr.deref pe' => extractDepsFromPExpr pe' boundVars env fuel
        | PExpr.op pe1 _ pe2 => do
          let deps1 ← extractDepsFromPExpr pe1 boundVars env fuel
          let deps2 ← extractDepsFromPExpr pe2 boundVars env fuel
          return LocSet.union deps1 deps2
        | PExpr.unaryop _ pe' => extractDepsFromPExpr pe' boundVars env fuel
        | PExpr.ite pe1 pe2 pe3 => do
          let deps1 ← extractDepsFromPExpr pe1 boundVars env fuel
          let deps2 ← extractDepsFromPExpr pe2 boundVars env fuel
          let deps3 ← extractDepsFromPExpr pe3 boundVars env fuel
          return LocSet.union (LocSet.union deps1 deps2) deps3
        | PExpr.app pe1 pe2 => do
          let deps1 ← extractDepsFromPExpr pe1 boundVars env fuel
          let deps2 ← extractDepsFromPExpr pe2 boundVars env fuel
          return LocSet.union deps1 deps2
        | PExpr.vlet x pe1 pe2 => do
          let deps1 ← extractDepsFromPExpr pe1 boundVars env fuel
          let deps2 ← extractDepsFromPExpr pe2 (x :: boundVars) env fuel
          return LocSet.union deps1 deps2
        | _ => return LocSet.empty  -- literals, unit, etc. don't read from heap

    -- Start with the bound parameter in the bound variables list
    extractDepsFromPExpr pred_body [arg_name] varEnvMap defaultFuel
  | Predicate.guardOnly _tag =>
    -- Guard-only predicate with no body, no dependencies
    return LocSet.empty
  | Predicate.noPred =>
    -- No predicate, no dependencies
    return LocSet.empty

-- Allocate a fresh location and return it along with updated typing context
def freshTLoc (ctx : TypeContext): (Loc × TypeContext) :=
  (ctx.nextLoc, { ctx with nextLoc := ctx.nextLoc + 1 })

-- Allocate a fresh location and return it along with updated typing context
def freshTLocRes (result : TypeResult): (Loc × TypeResult) :=
  (result.nextLoc', { result with nextLoc' := result.nextLoc' + 1 })

-- Function to get a fresh Tag Value From the environment
def generateFreshTag (ctx : TypeContext) : (Tag × TypeContext) :=
  (ctx.nextTag, { ctx with nextTag := ctx.nextTag + 1 })

-- Allocate a fresh Tag Value and return it along with updated typing result
def generateFreshTagRes (result : TypeResult): (Tag × TypeResult) :=
  (result.nextTag', { result with nextTag' := result.nextTag' + 1 })

/-- Advance nextTag past any tag introduced by a Predicate. -/
def advanceNextTagForPred (pred : Predicate) (nextTag : Tag) : Tag :=
  match pred with
  | Predicate.guardClosure k _ _ _ => max nextTag (k + 1)
  | Predicate.guardOnly k          => max nextTag (k + 1)
  | Predicate.noPred               => nextTag

/-- Advance nextTag past any tag introduced by a SyntaxPredicate. -/
def advanceNextTagForSyntaxPred (pred : SyntaxPredicate) (nextTag : Tag) : Tag :=
  match pred with
  | SyntaxPredicate.guardClosure k _ _ => max nextTag (k + 1)
  | SyntaxPredicate.guardOnly k        => max nextTag (k + 1)
  | SyntaxPredicate.noPred             => nextTag

/-- Advance nextTag past all tags introduced by an effects list. -/
def advanceNextTagForEffects (effects : List Effect) (nextTag : Tag) : Tag :=
  effects.foldl (fun acc eff => advanceNextTagForSyntaxPred eff.pred acc) nextTag

-- Helper functions

/-- Join two poison flags -/
def joinPoison (p1 p2 : Poison) : Poison :=
  p1 || p2

/-- Join multiple poison flags -/
def joinPoisons (ps : List Poison) : Poison :=
  ps.foldl joinPoison false

/-- Join two predicates using agreement-only policy.
    Merge rule:
    1. Exact match: If P₁ = P₂ (same tag and closure), preserve the predicate.
    2. Tag match: If both have the same tag k but different closures, use guard k (losing the closure).
    3. Otherwise: Use no_pred.

    This policy ensures predicates are only preserved when identical or when they share
    the same guard tag (using the more general guardOnly form).
-/
def joinPredicates (pred1 pred2 : Predicate) : Predicate :=
  -- Agreement-only policy for predicates:
  -- 1. Exact match: If P₁ = P₂ (same tag and closure), preserve the predicate.
  -- 2. Tag match: If both have the same tag k but different closures, use guard k (losing the closure).
  -- 3. Otherwise: Use no_pred.
  if beqPredicate pred1 pred2 then
    -- Exact match: preserve the predicate
    pred1
  else
    match pred1, pred2 with
    -- Both branches have guard closure with same tag but different closures: downgrade to guardOnly
    | Predicate.guardClosure k1 _ _ _, Predicate.guardClosure k2 _ _ _ =>
        if k1 == k2 then Predicate.guardOnly k1 else Predicate.noPred
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

/-- Update memory environment at a location -/
def updateMemEnv (env : MemoryTypeEnv) (l : Loc) (qt : QTyp) : MemoryTypeEnv :=
env.insert l qt

/-- Weak update for non-singleton locsets: join stored int QTyp with existing entries.
    Computes max poison and merged predicate across all locations, then updates uniformly.
    This implements the weak update semantics for assign_locset in the Ott spec. -/
def updateLocsetWeak (env : MemoryTypeEnv) (ls : LocSet) (storedPoison : Poison) (storedPred : Predicate) : MemoryTypeEnv :=
  -- First pass: compute joined poison and predicate from existing entries
  let (joinedPoison, joinedPred) := LocSet.fold ls (storedPoison, storedPred) (fun (accP, accPred) l =>
    match env.get? l with
    | some qt => (joinPoison accP qt.poison, joinPredicates accPred qt.pred)
    | none => (accP, accPred))
  -- Second pass: update all locations with the joined type
  let finalQt : QTyp := ⟨ETyp.int, joinedPoison, joinedPred⟩
  LocSet.fold ls env (fun env l => updateMemEnv env l finalQt)

/-- Join two memory environments (branch join). See JoinG in the Ott spec. -/
def joinMemEnvs (env1 env2 : MemoryTypeEnv) : MemoryTypeEnv :=
  combineExtTreeMaps env1 env2 (fun _ oq1 oq2 =>
    match oq1, oq2 with
    | some qt1, none => some qt1
    | none, some qt2 => some qt2
    | some qt1, some qt2 =>
      let ⟨t1, p1, pred1⟩ := qt1
      let ⟨t2, p2, pred2⟩ := qt2
      if t1 == t2 then
        let p := joinPoison p1 p2
        let pred := joinPredicates pred1 pred2
        some ⟨t1, p, pred⟩
      else
        -- Unreachable under well-typedness: location types are immutable.
        -- Symmetric, conservative fallback: drop the conflicting binding.
        -- TODO: consider running this in Exception monad to report an error.
        none
    | none, none => none)

/-- Strong join: like joinMemEnvs but drops predicates for single-sided entries.
    Used for unknown-branch if joins (if_std, if_depoison_*_R_unknown) so that
    guardClosure from an untaken branch does not survive into the post-context. -/
def joinMemEnvsStrong (env1 env2 : MemoryTypeEnv) : MemoryTypeEnv :=
  combineExtTreeMaps env1 env2 (fun _ oq1 oq2 =>
    match oq1, oq2 with
    | some qt1, none =>
      -- Single-sided: keep type and poison, drop predicate
      some ⟨qt1.etyp, qt1.poison, Predicate.noPred⟩
    | none, some qt2 =>
      -- Single-sided: keep type and poison, drop predicate
      some ⟨qt2.etyp, qt2.poison, Predicate.noPred⟩
    | some qt1, some qt2 =>
      -- Both-sided: same as joinMemEnvs
      let ⟨t1, p1, pred1⟩ := qt1
      let ⟨t2, p2, pred2⟩ := qt2
      if t1 == t2 then
        let p := joinPoison p1 p2
        let pred := joinPredicates pred1 pred2
        some ⟨t1, p, pred⟩
      else
        none
    | none, none => none)

/-- Restrict `envToRestrict` to the domain of `base`. -/
def restrictMemEnv (envToRestrict base : MemoryTypeEnv) : MemoryTypeEnv :=
  envToRestrict.filter (fun k _ => base.contains k)

/-- Join two ETyps at conditional joins, merging closures for arrow types.
    This implements the closure merging logic from the if-typing rules in the Ott spec.
    For arrow types: merge closure sets and join arrow-internal poisons.
    For other types: types must be equal (checked earlier via beqETypSignature).
    Note: p1 and p2 are the outer qualified-type poisons (joined separately by callers).
-/
def joinETyps (t1 t2 : ETyp) (_p1 _p2 : Poison) : ETyp :=
  match t1, t2 with
  | ETyp.ref inner1 ls1, ETyp.ref inner2 ls2 =>
      if beqETypSignature inner1 inner2 then
        ETyp.ref inner1 (LocSet.union ls1 ls2)
      else
        t1
  | ETyp.arrow st1 st2 p1' tcls1, ETyp.arrow st1' st2' p2' tcls2 =>
      -- Signature compatibility already checked; merge closures and join arrow-internal poisons
      if st1 == st1' && st2 == st2' then
        let mergedClosures := mergeFnTClosures tcls1 tcls2
        -- Join arrow-internal poisons: p = join p' p'' (Ott spec lines 908, 956)
        ETyp.arrow st1 st2 (joinPoison p1' p2') mergedClosures
      else
        t1  -- Fallback (should not happen if beqETypSignature passed)
  | ETyp.parrow st1 st2 p1' tcls1, ETyp.parrow st1' st2' p2' tcls2 =>
      -- Signature compatibility already checked; merge closures and join arrow-internal poisons
      if st1 == st1' && st2 == st2' then
        let mergedClosures := mergePFnTClosures tcls1 tcls2
        -- Join arrow-internal poisons: p = join p' p'' (Ott spec lines 926, 975)
        ETyp.parrow st1 st2 (joinPoison p1' p2') mergedClosures
      else
        t1  -- Fallback (should not happen if beqETypSignature passed)
  | _, _ =>
      -- For non-arrow types, types must be equal (checked via beqETypSignature)
      t1

/-- Join two logical environments (agreement-only meet used in while fixpoint) -/
def joinTagEnvs (env1 env2 : TagEnv) : TagEnv :=
  combineExtTreeMaps env1 env2 (fun _ otv1 otv2 =>
    match otv1, otv2 with
    | some ⟨b1, deps1⟩, some ⟨b2, deps2⟩ =>
      if b1 == b2 then
        -- Agreement: keep the tag with union of dependencies
        some ⟨b1, LocSet.union deps1 deps2⟩
      else
        -- Disagreement: drop the tag (unknown)
        none
    | some _, none => none  -- Single-sided: drop (unknown)
    | none, some _ => none  -- Single-sided: drop (unknown)
    | none, none => none)

-- Helper function to convert Expr to PExpr
def Expr.toPExpr (e : Expr) : TypecheckM PExpr :=
  match Expr.toPExpr? e with
  | some pe => return pe
  | none => throw "Cannot convert expression to PExpr"

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
def PExpr.equalWithEnvs (pe1 : PExpr) (env1 : CapturedVarEnv) (pe2 : PExpr) (env2 : CapturedVarEnv)
    (substitution : Option (Name × PExpr)) (fuel : Nat) : Bool :=
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
  let sCaptured := VarTypeEnv.toCaptured S
  let checkNoPredOnArrow (qt : QTyp) : TypecheckM Unit := do
    match qt.etyp with
    | ETyp.arrow _ _ _ _ | ETyp.parrow _ _ _ _ =>
        match qt.pred with
        | Predicate.noPred => pure ()
        | _ => throw "Function types cannot carry predicates in matchGuard"
    | _ => pure ()

  -- Helper function to check if a predicate's test expression matches the condition
  let checkPredicate (arg : PExpr) (qt : QTyp) : TypecheckM (Option (Tag × Deps)) :=
    do
    checkNoPredOnArrow qt
    match qt.pred with
    | Predicate.noPred => return none
    | Predicate.guardOnly _tag => return none  -- Guard-only cannot be matched syntactically
    | Predicate.guardClosure tag arg_name pred_body var_env =>
        if PExpr.usesArg arg_name pred_body then
          -- Parameterised: proceed with substitution + equality as today
          if PExpr.equalWithEnvs pred_body var_env conditionPExpr sCaptured (some (arg_name, arg)) defaultFuel then do
            let deps ← extractDepsFromPred qt.pred
            return some (tag, deps)
          else return none
        else
          -- Argument-ignoring: skip, not eligible for matching
          return none

  -- Collect all matching tags from variable environment
  let varMatches := VarTypeEnv.foldl [] (fun acc name qt =>
    let arg := PExpr.var name
    match checkPredicate arg qt with
    | .ok (some (tag, deps)) => (tag, deps) :: acc
    | .ok none => acc
    | .error _ => acc) S

  -- For references, merge predicates across the locset before matching
  let refMatches ← VarTypeEnv.foldlM (init := ([] : List (Tag × Deps))) (fun acc name qt => do
    match qt.etyp with
    | ETyp.ref _t ls =>
        if qt.poison then
          pure acc
        else
          if ls.isEmpty then throw "Reference locset is empty in matchGuard" else
          let arg := PExpr.deref (PExpr.var name)
          -- Merge predicates across locset, error if a referenced location is missing
          let merged? ←
            LocSet.foldM ls (init := (none : Option Predicate)) (fun accPred? l => do
              match G.get? l with
              | some memQt =>
                  checkNoPredOnArrow memQt
                  let nextPred :=
                    match accPred? with
                    | none => memQt.pred
                    | some p => joinPredicates p memQt.pred
                  pure (some nextPred)
              | none => throw s!"Location {l} not found in memory environment during matchGuard")
          -- Collect deps across locset
          let depsMerged ← LocSet.foldM ls (init := LocSet.empty) (fun dacc l => do
            match G.get? l with
            | some memQt =>
                checkNoPredOnArrow memQt
                let deps ← extractDepsFromPred memQt.pred
                pure (LocSet.union dacc (LocSet.union (LocSet.singleton l) deps))
            | none => throw s!"Location {l} not found in memory environment during matchGuard")
          let merged := merged?.getD Predicate.noPred
          match merged with
          | Predicate.guardClosure tag arg_name pred_body var_env =>
              if PExpr.usesArg arg_name pred_body then
                if PExpr.equalWithEnvs pred_body var_env conditionPExpr sCaptured (some (arg_name, arg)) defaultFuel then
                  pure ((tag, depsMerged) :: acc)
                else pure acc
              else pure acc
          | Predicate.guardOnly _tag => pure acc
          | Predicate.noPred => pure acc
    | _ => pure acc
    ) S

  let allMatches := varMatches ++ refMatches
  -- Return the tag and dependencies if exactly one match is found, otherwise throw an error
  match allMatches with
  | [(tag, deps)] => return (tag, deps)
  | [] => throw "No matching guard found for condition"
  | _ => throw s!"Multiple matching guards found for condition: {repr allMatches}"



-- Type checking rules implementation

/-- Rule: int (Ott rule: int)
-- pc ; G ; S ; L |- n : int :> clean { no_pred } -| G ; L
-/
def typecheckInt (ctx : TypeContext) (_n : Int) : TypecheckM TypeResult := do
  let qt : QTyp := ⟨ETyp.int, false, Predicate.noPred⟩  -- clean, no predicate
  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag, regime' := ctx.regime }

/-- Rule: bool (Ott rule: bool)
-- pc ; G ; S ; L |- b : bool :> clean { no_pred } -| G ; L
-/
def typecheckBool (ctx : TypeContext) (_b : Bool) : TypecheckM TypeResult := do
  let qt : QTyp := ⟨ETyp.bool, false, Predicate.noPred⟩  -- clean, no predicate
  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag, regime' := ctx.regime }


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
      return { qualType := qt', memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag, regime' := ctx.regime }
    | Predicate.guardOnly k | Predicate.guardClosure k _ _ _ =>
      -- Both guard types behave the same: check tag in L and de-poison/poison/preserve accordingly
      --dbg_trace s!"Guard predicate found with tag {k}"
      if etyp.isFunctionType then
        throw s!"Function types cannot carry guard predicates (variable {x})"
      match ctx.tagEnv.get? k with
      | some ⟨true, _deps⟩ =>  -- guard_true / guard_only_true case
        -- dbg_trace "Guard True case"
        let qt' : QTyp := ⟨etyp, ctx.pc, Predicate.noPred⟩
        return { qualType := qt', memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag, regime' := ctx.regime }
      | some ⟨false, _deps⟩ =>  -- guard_false / guard_only_false case
        -- dbg_trace "Guard False case"
        let qt' : QTyp := ⟨etyp, true, Predicate.noPred⟩  -- poisoned
        return { qualType := qt', memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag, regime' := ctx.regime }
      | none =>  -- guard_unknown / guard_only_unknown case
        -- dbg_trace "Guard Unknown case"
        let poison := joinPoison ctx.pc poison
        -- Preserve the original predicate (either guardOnly or guardClosure)
        let qt' : QTyp := ⟨etyp, poison, pred⟩
        return { qualType := qt', memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag, regime' := ctx.regime }
  | none => throw s!"Variable {x} not found in environment"


/-- Rule: location (Ott rule: location)
-- G(l) = T :> p { P }
-- ------------------
-- pc ; G ; S ; L |- l : ref T @ {l} :> clean { no_pred } -| G ; L
-/
def typecheckLocation (ctx : TypeContext) (l : Loc) : TypecheckM TypeResult := do
  match ctx.memEnv.get? l with
  | some qt =>
    let ⟨etyp, _p, pred ⟩ := qt
    let refTyp := ETyp.ref etyp (LocSet.singleton l)
    let qt' : QTyp := ⟨refTyp, false, pred⟩  -- clean, preserve predicate
    return { qualType := qt', memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag, regime' := ctx.regime }
  | none => throw s!"Location {l} not found in memory environment"

/-- Rule: unit (Ott rule: unit)
-- pc ; G ; S ; L |- unit : unit :> clean { no_pred } -| G ; L
-/
def typecheckUnit (ctx : TypeContext) : TypecheckM TypeResult := do
  let qt : QTyp := ⟨ETyp.unit, false, Predicate.noPred⟩  -- clean, no predicate
  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag, regime' := ctx.regime }

/--  Rule: string (Ott rule: string)
-- pc ; G ; S ; L |- string : string :> clean { no_pred } -| G ; L
-/
def typecheckString (ctx : TypeContext) (_s : String) : TypecheckM TypeResult := do
  let qt : QTyp := ⟨ETyp.string, false, Predicate.noPred⟩  -- clean, no predicate
  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag, regime' := ctx.regime }

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

  -- Create arrow type ST1 -> ST2 with singleton closure list
  let arrowTyp : ETyp := ETyp.arrow st1 st2 ctx.pc [FnTClosure.regular x body (VarTypeEnv.toCaptured ctx.varEnv)]
  -- Create qualified type ST1 -> ST2 # pc { no_pred }
  let qt : QTyp := ⟨arrowTyp, ctx.pc, Predicate.noPred⟩
   return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag, regime' := ctx.regime }

/-- Rule: pfn_abs (Ott rule: pfn_abs)
----------------------------------------------------------------------  :: pfn_abs
  pc ; G ; S ; L |- pfn x : ST1 => pe : ST1 -> ST2 # pc typing_closure ( x , pe , S ) :> pc { no_pred } -| G ; L
-/
def typecheckPfn (ctx : TypeContext) (x : Name) (st1 : Typ) (body : Expr) (st2 : Typ) : TypecheckM TypeResult := do
  -- Simply record the body and return type without typechecking the body
  -- Body typechecking is deferred until application time

   -- Convert body to PExpr
  let pbody ← body.toPExpr
  -- Create arrow type ST1 -> ST2 with singleton closure list
  let arrowTyp : ETyp := ETyp.parrow st1 st2 ctx.pc [PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctx.varEnv)]
  -- Create qualified type ST1 -> ST2 # pc { no_pred }
  let qt : QTyp := ⟨arrowTyp, ctx.pc, Predicate.noPred⟩

  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag, regime' := ctx.regime }

-- Helper functions for extern type conversion

/-- Convert SyntaxPredicate to Predicate with late environment capture.
    Parser creates predicates with Expr bodies and no captured env.
    During typechecking, we convert Expr to PExpr and attach current varEnv.
-/
def attachVarEnvToPredicate (pred : SyntaxPredicate) (varEnv : VarTypeEnv) : TypecheckM Predicate := do
  -- Temporary simplified implementation - TODO: implement proper conversion
  match pred with
  | SyntaxPredicate.guardClosure k arg body =>
      pure (Predicate.guardClosure k arg (← body.toPExpr ) (VarTypeEnv.toCaptured varEnv))
  | SyntaxPredicate.guardOnly k => pure (Predicate.guardOnly k)
  | SyntaxPredicate.noPred => pure Predicate.noPred

/-- Convert (Typ, Bool, SyntaxPredicate) to QTyp for EXTERN VALUES.
    Used only for extern val declarations at definition time.
    May allocate fresh locations for reference types and update Γ.
    NOTE: Memory can only store integers - reject ref T unless T = int.
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
        -- Memory can only store integers - reject ref T unless T = int
        if t != Typ.int then
          throw s!"Type error: extern val can only use ref int, but got ref {repr t} (memory stores only integers)"
        let (l, ctx') := freshTLoc ctx
        let (innerQt, ctx'') ← surfaceSpecToQTyp t false SyntaxPredicate.noPred varEnv ctx'
        let memEnv' := updateMemEnv ctx''.memEnv l innerQt
        let ctx''' := { ctx'' with memEnv := memEnv' }
        return (ETyp.ref innerQt.etyp (LocSet.singleton l), ctx''')
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
    (varEnv : VarTypeEnv) (nextLoc : Loc) : TypecheckM (QTyp × Loc) := do
  -- Convert Typ to ETyp, rejecting reference types
  let (etyp, nextLoc') ← (match typ with
    | Typ.int => pure (ETyp.int, nextLoc)
    | Typ.bool => pure (ETyp.bool, nextLoc)
    | Typ.unit => pure (ETyp.unit, nextLoc)
    | Typ.string => pure (ETyp.string, nextLoc)
    | Typ.ref _ => throw "Extern functions cannot return reference types"
    | Typ.arrow _ _ => throw "Arrow types not expected in extern specs" : TypecheckM (ETyp × Loc))

  let pred' ← attachVarEnvToPredicate pred varEnv
  return (⟨etyp, poison, pred'⟩, nextLoc')

-- Type checking functions for extern expressions

/-- Typecheck extern value: let x = extern val : (T :> p { P }) -/
def typecheckExternVal (mode : EvalMode) (ctx : TypeContext) (typ : Typ) (poison : Bool) (pred : SyntaxPredicate)
    : TypecheckM TypeResult := do
    if mode == .ioFree then throw "IO operation (externVal) forbidden in ioFree mode"
    match (poison,pred) with
    | (false, SyntaxPredicate.guardOnly _)
    | (false, SyntaxPredicate.guardClosure _ _ _) =>
        throw "Clean types cannot have predicates"
    | _ => do
      -- Convert to QTyp with current varEnv
      let (qt, ctx') ← surfaceSpecToQTyp typ poison pred ctx.varEnv ctx
      -- Return the qualified type
      return { qualType := qt, memEnv' := ctx'.memEnv, tagEnv' := ctx.tagEnv,
               nextLoc' := ctx'.nextLoc, nextTag' := advanceNextTagForPred qt.pred ctx.nextTag, regime' := ctx.regime }

def parseReturnType (retType : ExternReturn):Typ :=
 match retType with
 | ExternReturn.simple typ _ _ => typ
 | ExternReturn.nestedFn _ typ extReturn _ => Typ.arrow typ (parseReturnType extReturn)
 | ExternReturn.nestedPfn _ typ extReturn => Typ.arrow typ (parseReturnType extReturn)

/-- Typecheck extern impure function -/
def typecheckExternFn (mode : EvalMode) (ctx : TypeContext) (arg : Name) (argTyp : Typ)
    (retSpec : ExternReturn) (effects : List Effect) : TypecheckM TypeResult := do
  if mode == .ioFree then throw "IO operation (externFn) forbidden in ioFree mode"
  -- Create extern closure with captured varEnv (singleton list)
  let tcl := FnTClosure.extern arg retSpec effects (VarTypeEnv.toCaptured ctx.varEnv)


  let retTyp := parseReturnType retSpec
  let arrowTyp := ETyp.arrow argTyp retTyp ctx.pc [tcl]

  -- Return qualified type with poison = pc
  let qt : QTyp := ⟨arrowTyp, ctx.pc, Predicate.noPred⟩
  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv,
           nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag, regime' := ctx.regime }

/-- Typecheck extern pure function -/
def typecheckExternPfn (mode : EvalMode) (ctx : TypeContext) (arg : Name) (argTyp : Typ)
    (retSpec : ExternReturn) : TypecheckM TypeResult := do
  if mode == .ioFree then throw "IO operation (externPfn) forbidden in ioFree mode"
  -- Create extern closure with captured varEnv (singleton list)
  let tcl := PFnTClosure.extern arg retSpec (VarTypeEnv.toCaptured ctx.varEnv)

  let retTyp := parseReturnType retSpec
  -- Create arrow type with ambient pc
  let arrowTyp := ETyp.parrow argTyp retTyp ctx.pc [tcl]

  -- Return qualified type with poison = pc
  let qt : QTyp := ⟨arrowTyp, ctx.pc, Predicate.noPred⟩
  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv,
           nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag, regime' := ctx.regime }


def generateFreshVar (ctx : TypeContext) (pref : Name) (suffix : Nat) (fuel : Nat) : Name :=
  match fuel with
  | 0 => s!"{pref}{suffix}"
  | fuel + 1 =>
      let candidate := if suffix = 0 then pref else s!"{pref}{suffix}"
      if ctx.varEnv.contains candidate then
        generateFreshVar ctx pref (suffix + 1) fuel
      else
        candidate
termination_by fuel

/-- Helper: Join a list of TypeResults into a single TypeResult -/
def joinTypeResults (ctx : TypeContext) (firstResult : TypeResult) (restResults : List TypeResult) : TypecheckM TypeResult := do
  let ⟨firstEtyp, _firstP, _firstPred⟩ := firstResult.qualType

  -- Check that all results have signature-compatible types (Section 5.3) using foldlM
  let _ ← List.foldlM (fun () result => do
    let ⟨resEtyp, _resP, _resPred⟩ := result.qualType
    if not (beqETypSignature firstEtyp resEtyp) then
      throw s!"Closure alternatives produced incompatible result types: {repr firstEtyp} vs {repr resEtyp}"
    else
      pure ()) () restResults

  -- Join all results (Section 5.4) using foldlM
    let joinAccumulator := (firstEtyp, firstResult.memEnv', firstResult.qualType.poison,
                            firstResult.qualType.pred, firstResult.tagEnv', firstResult.regime',
                            firstResult.nextLoc', firstResult.nextTag')

    let joined ← List.foldlM (fun acc result => do
      let ⟨resEtyp, resPoison, resPred⟩ := result.qualType
      let (joinedEtyp, joinedMemEnv, joinedPoison, joinedPred, joinedTagEnv, joinedRegime, maxNextLoc, maxNextTag) := acc
      pure (joinETyps joinedEtyp resEtyp joinedPoison resPoison,
            joinMemEnvs joinedMemEnv result.memEnv',
            joinPoison joinedPoison resPoison,
            joinPredicates joinedPred resPred,
            joinTagEnvs joinedTagEnv result.tagEnv',
            joinRegimes joinedRegime result.regime',
            max maxNextLoc result.nextLoc',
            max maxNextTag result.nextTag')) joinAccumulator restResults

    let (joinedEtyp, joinedMemEnv, joinedPoison, joinedPred, joinedTagEnv, joinedRegime, maxNextLoc, maxNextTag) := joined

    -- Final result with joined poison from all alternatives and caller pc
    -- If result is a function type, clear predicate to no_pred (predicates are only meaningful for basic types)
    let finalPred := match joinedEtyp with
      | ETyp.arrow _ _ _ _ => Predicate.noPred
      | ETyp.parrow _ _ _ _ => Predicate.noPred
      | _ => joinedPred
    let finalPoison := joinPoison ctx.pc joinedPoison
    let qt : QTyp := ⟨joinedEtyp, finalPoison, finalPred⟩
    return { qualType := qt, memEnv' := joinedMemEnv, tagEnv' := joinedTagEnv,
             nextLoc' := maxNextLoc, nextTag' := maxNextTag, regime' := joinedRegime }

mutual

-- Helper function to type check an expression with context
def typecheckExpr (mode : EvalMode) (ctx : TypeContext) (e : Expr) (fuel : Nat) : TypecheckM TypeResult :=

  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    match e with
    | Expr.num n => typecheckInt ctx n
    | Expr.bool b => typecheckBool ctx b
    | Expr.unit => typecheckUnit ctx
    | Expr.str s => typecheckString ctx s
    | Expr.var x => typecheckVar ctx x
    | Expr.op e1 op e2 => typecheckOp mode ctx e1 e2 fuel op
    | Expr.newRef e => typecheckNewRef mode ctx e fuel
    | Expr.assign e1 e2 => typecheckAssign mode ctx e1 e2 fuel
    | Expr.deref e1 => typecheckDeref mode ctx e1 fuel
    | Expr.seq e1 e2 => typecheckSeq mode ctx e1 e2 fuel
    | Expr.kwhile e1 e2 => typecheckWhile mode ctx e1 e2 fuel
    | Expr.vlet x e1 e2 => typecheckVlet mode ctx x e1 e2 fuel
    | Expr.fn x paramType body returnType => typecheckFn ctx x paramType body returnType
    | Expr.pfn x paramType body returnType => typecheckPfn ctx x paramType body returnType
    | Expr.app e1 e2 => typecheckApp mode ctx e1 e2 fuel
    | Expr.ite e1 e2 e3 => typecheckIf mode ctx e1 e2 e3 fuel
    | Expr.rand e => typecheckRand mode ctx e fuel
    | Expr.frand e => typecheckFrand mode ctx e fuel
    | Expr.printString e => typecheckPrintString mode ctx e fuel
    | Expr.printInt e => typecheckPrintInt mode ctx e fuel
    | Expr.unaryop op e => typecheckUnaryOp mode ctx op e fuel
    | Expr.externVal typ poison pred => typecheckExternVal mode ctx typ poison pred
    | Expr.externFn arg argTyp retSpec effects => typecheckExternFn mode ctx arg argTyp retSpec effects
    | Expr.externPfn arg argTyp retSpec => typecheckExternPfn mode ctx arg argTyp retSpec
termination_by fuel

/-- Helper function to run proper fixpoint computation for while loops.
    Re-types the guard each iteration, threads pc := pc ⊔ poison(guard),
    and joins Γ/ℒ from the body as in the Ott recurrences.
    Also tracks fresh location and tag counters through the fixpoint. -/
def runWhileFixpoint (mode : EvalMode) (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (pureGuard : Bool) (guardOpt : Option (Tag × Deps)) : TypecheckM (Poison × MemoryTypeEnv × TagEnv × Regime × Loc × Tag) :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    -- (1) Typecheck the guard for this iteration
    let ctxForGuard := if pureGuard then { ctx with pureCtx := true } else ctx
    let guardRes ← typecheckExpr mode ctxForGuard e1 fuel
    let ⟨etyp1, p1, _⟩ := guardRes.qualType
    if etyp1 != ETyp.bool then throw "Condition of while must be bool"

    -- (2) Build body context: pc includes guard poison; take Γ from guard
    -- For pure guards (while_depoison): use Γ from guard but preserve ℒ (per Ott spec line 806)
    -- For impure guards (while_std): use both Γ and ℒ from guard (per Ott spec line 821)
    let bodyPcCtx : TypeContext := { ctx with pc := joinPoison ctx.pc p1 }
    -- strictly speaking this is not necessary because pure expressions do not modify envs,
    -- but we add it as extra precasion and to exactly match the Ott spec.
    let bodyTagEnv := if pureGuard then ctx.tagEnv else guardRes.tagEnv'
    let bodyRegime := if pureGuard then ctx.regime else guardRes.regime'
    let bodyEnvCtx : TypeContext := { bodyPcCtx with memEnv := guardRes.memEnv', tagEnv := bodyTagEnv, regime := bodyRegime }
    -- Body is typed in mode pm from outer context (per Ott spec)
    -- In practice, while loops can't appear in pure contexts, but we preserve ctx.pureCtx for correctness
    let bodyCtxBase : TypeContext := { bodyEnvCtx with nextLoc := guardRes.nextLoc', nextTag := guardRes.nextTag', pureCtx := ctx.pureCtx }
    let bodyCtx := match guardOpt with
      | some (k, deps) => { bodyCtxBase with tagEnv := bodyCtxBase.tagEnv.insert k (TagVal.mk true deps) }
      | none => bodyCtxBase

    -- (3) Typecheck the body
    let bodyRes ← typecheckExpr mode bodyCtx e2 fuel
    let ⟨etyp2, p2, _⟩ := bodyRes.qualType
    if etyp2 != ETyp.unit then throw "Body of while must have unit type"

    -- (4) Recurrences: pc_{i+1} = pc_i ⊔ p_{2,i}; Γ/ℒ/R joins with the body results
    let newPc := joinPoison ctx.pc p2
    let restrictedBodyEnv := restrictMemEnv bodyRes.memEnv' ctx.memEnv
    let newMemEnv := joinMemEnvs ctx.memEnv restrictedBodyEnv
    let newTagEnv := joinTagEnvs ctx.tagEnv bodyRes.tagEnv'
    let newRegime := joinRegimes ctx.regime bodyRes.regime'

    -- (5) Fixpoint check
    if newMemEnv == ctx.memEnv && newPc == ctx.pc && newTagEnv == ctx.tagEnv && newRegime.bound == ctx.regime.bound then
      return (newPc, newMemEnv, newTagEnv, newRegime, bodyRes.nextLoc', bodyRes.nextTag')
    else
      let nextCtx := { ctx with pc := newPc, memEnv := newMemEnv, tagEnv := newTagEnv, regime := newRegime, nextLoc := bodyRes.nextLoc', nextTag := bodyRes.nextTag' }
      runWhileFixpoint mode nextCtx e1 e2 fuel pureGuard guardOpt
termination_by fuel

/-- Rule: while_depoison (Ott rule: while_depoison when matchGuard succeeds)
-- Implements flow-sensitive analysis with predicate-based de-poisoning
-- Condition e1 is pure (doesn't modify G or L)
--/
def typecheckWhileDepoison (mode : EvalMode) (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (k : Tag) (deps : Deps) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    -- Run fixpoint computation with predicate-based de-poisoning (pure guard).
    -- Guard is typed under L (without k); body under L[k↦true] handled inside runWhileFixpoint.
    let (finalPc, finalMemEnv, finalTagEnv, finalRegime, finalNextLoc, finalNextTag) ← runWhileFixpoint mode ctx e1 e2 fuel true (some (k, deps))

    -- After loop termination, set k to false in the output environment
    let tagEnv' := finalTagEnv.insert k ⟨false, deps⟩

    let qt : QTyp := ⟨ETyp.unit, finalPc, Predicate.noPred⟩
    return { qualType := qt, memEnv' := finalMemEnv, tagEnv' := tagEnv', nextLoc' := finalNextLoc, nextTag' := finalNextTag, regime' := finalRegime }
termination_by fuel

/-- Rule: while_std (Ott rule: while_std when matchGuard fails)
-- Implements flow-sensitive analysis without predicate-based de-poisoning
-- Unlike while_depoison, e1 is not pure and can modify G and L
--/
def typecheckWhileStd (mode : EvalMode) (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    -- Run fixpoint computation (impure guard; re-types guard each iteration)
    let (finalPc, finalMemEnv, finalTagEnv, finalRegime, finalNextLoc, finalNextTag) ← runWhileFixpoint mode ctx e1 e2 fuel false none

    let qt : QTyp := ⟨ETyp.unit, finalPc, Predicate.noPred⟩
    return { qualType := qt, memEnv' := finalMemEnv, tagEnv' := finalTagEnv, nextLoc' := finalNextLoc, nextTag' := finalNextTag, regime' := finalRegime }
termination_by fuel



/- Rule : Ty rand typing
                pc; Γ; σ; L ⊢ e : int ▷ p {P} ⊣ Γ′; L′
                ---------------------------------------------------
                pc; Γ; σ; L ⊢ rand e : int ▷ pc ⊔ p {} ⊣ Γ′; L′
-/
def typecheckRand (mode : EvalMode) (ctx : TypeContext) (e : Expr) (fuel : Nat):TypecheckM TypeResult :=
  match fuel with
    | 0        => throw "Out of fuel"
    | fuel + 1 =>
            do
              if mode == .ioFree then throw "IO operation (rand) forbidden in ioFree mode"
              let result ← typecheckExpr mode ctx e fuel
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
def typecheckFrand (mode : EvalMode) (ctx : TypeContext) (e : Expr) (fuel : Nat):TypecheckM TypeResult :=
  match fuel with
  | 0        => throw "Out of fuel"
  | fuel + 1 =>
    do
      if mode == .ioFree then throw "IO operation (frand) forbidden in ioFree mode"
      let result ← typecheckExpr mode ctx e fuel
      let ⟨etyp, _, _  ⟩ := result.qualType
      if etyp != ETyp.int then throw ("Argument Expression to frand must have type int")
      else
        let (newTag,result') := generateFreshTagRes result
        let varName := generateFreshVar ctx "limit" 0 fuel
        let predBody : PExpr <- Expr.toPExpr (Expr.op (Expr.op (Expr.var varName) Op.gte (Expr.num 0)) Op.and
                                 (Expr.op (Expr.var varName) Op.lte ( e)) )

        let depoisoningPred : Predicate :=
          Predicate.guardClosure newTag varName predBody (VarTypeEnv.toCaptured ctx.varEnv)

        let qt' : QTyp := ⟨ETyp.int , true, depoisoningPred⟩
        return {result' with qualType := qt'}
termination_by fuel

/-
      pc ; G ; S ; L |- e : string :> p { P } -| G' ; L'
    ----------------------------------------------------------------------  :: printString_typing
      pc ; G ; S ; L |- printString e : unit :> join pc p { no_pred } -| G' ; L'
 -/
def typecheckPrintString (mode : EvalMode) (ctx : TypeContext) (e : Expr) (fuel : Nat):TypecheckM TypeResult :=
  match fuel with
    | 0        => throw "Out of fuel"
    | fuel + 1 =>
            do
              if mode == .ioFree then throw "IO operation (printString) forbidden in ioFree mode"
              let result ← typecheckExpr mode ctx e fuel
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
def typecheckPrintInt (mode : EvalMode) (ctx : TypeContext) (e : Expr) (fuel : Nat):TypecheckM TypeResult :=
  match fuel with
    | 0        => throw "Out of fuel"
    | fuel + 1 =>
            do
              if mode == .ioFree then throw "IO operation (printInt) forbidden in ioFree mode"
              let result ← typecheckExpr mode ctx e fuel
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
def typecheckOp (mode : EvalMode) (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (op : Op) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    let result1 ← typecheckExpr mode ctx e1 fuel
    let ⟨etyp1, p1, _  ⟩ := result1.qualType

    -- Propagate fresh-name supplies and regime from first operand into second operand context
    let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime' }
    let result2 ← typecheckExpr mode ctx' e2 fuel
    let ⟨etyp2, p2, _  ⟩ := result2.qualType

    match opEType? op etyp1 etyp2 with
    | some r =>
        let poison := joinPoison ctx.pc (joinPoison p1 p2)
        let qt : QTyp := ⟨r, poison, Predicate.noPred⟩
        return { result2 with qualType := qt }
    | none => throw s!"Operation argument types do not match.\n  Left: {etyp1}\n  Op:   {op}\n  Right: {etyp2}"
termination_by fuel

/-- Rule: ref (Ott rule: ref)
-- pc ; G ; S ; L |- e : int :> p { P } -| G' ; L'
-- fresh l
-- -----------------------
-- pc ; G ; S ; L |- ref e : ref int @ l :> pc { no_pred } -| G'[l |-> int :> join pc p { P }] ; L'
-- NOTE: Memory can only store integers (matching runtime semantics)
-/
def typecheckNewRef (mode : EvalMode) (ctx : TypeContext) (e : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    let result ← typecheckExpr mode ctx e fuel
    let ⟨etyp, poison, pred ⟩ := result.qualType

    -- Require that the allocated value has type int (heap stores only integers)
    if etyp != ETyp.int then
      throw s!"Type error: ref can only allocate integers, but got {repr etyp}"

    -- Generate fresh location (simplified)
    let (l, result') := freshTLocRes result
    let storedPoison := joinPoison ctx.pc poison
    let storedQt : QTyp := ⟨ETyp.int, storedPoison, pred⟩
    let memEnv' := updateMemEnv result'.memEnv' l storedQt

    let qt : QTyp := ⟨ETyp.ref ETyp.int (LocSet.singleton l), ctx.pc, Predicate.noPred⟩
    return { qualType := qt, memEnv' := memEnv', tagEnv' := result'.tagEnv', nextLoc' := result'.nextLoc', nextTag' := result'.nextTag', regime' := result'.regime' }
termination_by fuel

/-- Rule: assign (Ott rules: assign_singleton, assign_locset, assign_singleton_poisoned_ref, assign_locset_poisoned_ref) -/
def typecheckAssign (mode : EvalMode) (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    let result1 ← typecheckExpr mode ctx e1 fuel
    let ⟨etyp1, p1, _  ⟩ := result1.qualType
    match etyp1 with
    | ETyp.ref t ls =>
      -- Require that the reference stores integers (heap stores only integers)
      if t != ETyp.int then
        throw s!"Type error: can only assign to ref int, but got ref {repr t}"

      let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime' }
      let result2 ← typecheckExpr mode ctx' e2 fuel
      let ⟨etyp2, p2, pred2  ⟩ := result2.qualType

      -- Require that the RHS has type int
      if etyp2 != ETyp.int then
        throw s!"Type error: can only assign int values, but got {repr etyp2}"

      let storedPoison := joinPoison ctx.pc (joinPoison p1 p2)
      -- If reference is poisoned, erase predicates (store no_pred), mirroring deref_poisoned
      let storedPred := if p1 then Predicate.noPred else pred2
      let memEnv' := match ExtTreeSet.toList ls with
        | [l] =>
          -- Singleton: strong update (assign_singleton / assign_singleton_poisoned_ref)
          let storedQt : QTyp := ⟨ETyp.int, storedPoison, storedPred⟩
          updateMemEnv result2.memEnv' l storedQt
        | _ =>
          -- Non-singleton: weak update (assign_locset / assign_locset_poisoned_ref)
          updateLocsetWeak result2.memEnv' ls storedPoison storedPred

      let resultPoison := joinPoison ctx.pc p1
      let qt : QTyp := ⟨ETyp.unit, resultPoison, Predicate.noPred⟩
      -- Invalidate dependencies on write (Ott rule: assign)
      let tagEnv' := invalidateTagDeps result2.tagEnv' ls
      let regime' := invalidateRegimeDeps ctx.regime result2.tagEnv' ls
      -- Bump nextLoc' past all locations in ls to ensure wfTypeResult holds
      -- (locations may not be in memEnv due to conservative if/while typing)
      let nextLoc' := LocSet.fold ls result2.nextLoc' (fun acc l => max acc (l + 1))
      return { qualType := qt, memEnv' := memEnv', tagEnv' := tagEnv', nextLoc' := nextLoc', nextTag' := result2.nextTag', regime' := regime' }
    | _ => throw "Left operand of assignment must be a reference"
termination_by fuel

/-- Rules: deref_* (Ott rules: deref_poisoned, deref_no_pred, deref_guard_true, deref_guard_false, deref_guard_unknown)
-- NOTE: Memory can only store integers (matching runtime semantics)
--/
def typecheckDeref (mode : EvalMode) (ctx : TypeContext) (e : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    let result ← typecheckExpr mode ctx e fuel
    let ⟨etyp, poisonRef, _predRef ⟩ := result.qualType
    match etyp with
    | ETyp.ref t ls =>
      -- Require that the reference stores integers (heap stores only integers)
      if t != ETyp.int then
        throw s!"Type error: can only dereference ref int, but got ref {repr t}"

      if ls.isEmpty then
        throw "Reference locset is empty"
      -- Fetch all referenced memory cells and ensure their types are compatible
      let (joinedCellPoison, mergedPred?) ←
        LocSet.foldM ls (init := (false, (none : Option Predicate))) (fun (accPoison, accPred?) l => do
          match result.memEnv'.get? l with
          | some qt =>
              if qt.etyp == ETyp.int then
                let nextPoison := joinPoison accPoison qt.poison
                let nextPred? :=
                  match accPred? with
                  | none => some qt.pred
                  | some p => some (joinPredicates p qt.pred)
                pure (nextPoison, nextPred?)
              else
                throw s!"Type mismatch in dereference at {l}: {repr qt.etyp} ≠ int"
          | none => throw s!"Location {l} not found in memory environment")

      let mergedPred := mergedPred?.getD Predicate.noPred

      if poisonRef then
        -- Reference itself poisoned: ignore predicates, return poisoned
        let qt : QTyp := ⟨ETyp.int, true, Predicate.noPred⟩
        return { qualType := qt, memEnv' := result.memEnv', tagEnv' := result.tagEnv', nextLoc' := result.nextLoc', nextTag' := result.nextTag', regime' := result.regime' }
      else
        match mergedPred with
        | Predicate.noPred =>
            let poison := joinPoison ctx.pc joinedCellPoison
            let qt : QTyp := ⟨ETyp.int, poison, Predicate.noPred⟩
            return { qualType := qt, memEnv' := result.memEnv', tagEnv' := result.tagEnv', nextLoc' := result.nextLoc', nextTag' := result.nextTag', regime' := result.regime' }
        | Predicate.guardOnly k | Predicate.guardClosure k _ _ _ =>
            match result.tagEnv'.get? k with
            | some ⟨true, _deps⟩ =>
              let qt : QTyp := ⟨ETyp.int, ctx.pc, Predicate.noPred⟩
              return { qualType := qt, memEnv' := result.memEnv', tagEnv' := result.tagEnv', nextLoc' := result.nextLoc', nextTag' := result.nextTag', regime' := result.regime' }
            | some ⟨false, _deps⟩ =>
              let qt : QTyp := ⟨ETyp.int, true, Predicate.noPred⟩
              return { qualType := qt, memEnv' := result.memEnv', tagEnv' := result.tagEnv', nextLoc' := result.nextLoc', nextTag' := result.nextTag', regime' := result.regime' }
            | none =>
              let poison := joinPoison ctx.pc joinedCellPoison
              let qt : QTyp := ⟨ETyp.int, poison, mergedPred⟩
              return { qualType := qt, memEnv' := result.memEnv', tagEnv' := result.tagEnv', nextLoc' := result.nextLoc', nextTag' := result.nextTag', regime' := result.regime' }
    | _ => throw "Operand of dereference must be a reference"
termination_by fuel

/-- Rule: seq (Ott rule: seq)
-- pc ; G ; S ; L |- e1 : T1 :> p' { P' } -| G' ; L'
-- pc ; G' ; S ; L' |- e2 : T2 :> p'' { P'' } -| G'' ; L''
-- --------------------------------
-- pc ; G ; S ; L |- e1 ; e2 : T2 :> join p' p'' { P'' } -| G'' ; L''
-/
def typecheckSeq (mode : EvalMode) (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    let result1 ← typecheckExpr mode ctx e1 fuel
    let ctx' := updateCtxFromResult ctx result1
    let result2 ← typecheckExpr mode ctx' e2 fuel
    return result2
termination_by fuel


/-- Issue #113: when p1 (function outer poison) is true, the application result
    is irrecoverably poisoned with no predicate. -/
def normalizeAppResultByProvenance (p1 : Poison) (qt : QTyp) : QTyp :=
  if p1 then { qt with poison := true, pred := Predicate.noPred } else qt

/-- Helper: Apply a single FnTClosure and return the result type and updated environments.
    This encapsulates the body typing logic for a single closure alternative.
-/
def applyFnTClosure (mode : EvalMode) (tcl : FnTClosure) (_st1 st2 : Typ) (p : Poison) (p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (ctx : TypeContext) (result2 : TypeResult) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel in applyFnTClosure"
  | fuel + 1 => do
    match tcl with
    | FnTClosure.regular x body env =>
        -- Type the body with the closure's captured environment
        -- pc = join p join p1 pc (Ott spec line 733: app_fn_singleton)
        let argQt : QTyp := ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        let envMap := VarTypeEnv.ofCaptured env
        let env' := VarTypeEnv.update envMap x argQt
        let ctx'' := { ctx with pc := joinPoison p (joinPoison p1 ctx.pc),
                                memEnv := result2.memEnv', varEnv := env', tagEnv := result2.tagEnv',
                                nextTag := result2.nextTag', nextLoc := result2.nextLoc', regime := result2.regime' }
        let result3 ← typecheckExpr mode ctx'' body fuel
        let ⟨_etyp3, _p3, _pred3⟩ := result3.qualType

        -- Check subtyping
        if not (isSubtype st2 result3.qualType) then
          throw s!"Type mismatch in function application: return type {repr st2} is not compatible with body type {repr (QTyp.toTyp result3.qualType)}"

        -- Issue #111: taint app result by function poison (p, p1)
        -- Issue #113: provenance gate - if p1, force irrecoverable poison and no_pred
        let taintedPoison := joinPoison p1 (joinPoison p result3.qualType.poison)
        let taintedQt := { result3.qualType with poison := taintedPoison }
        return { result3 with qualType := normalizeAppResultByProvenance p1 taintedQt }

    | FnTClosure.extern x retSpec effects capturedEnv =>
        if mode == .ioFree then throw "Extern function application forbidden in ioFree mode"
        -- Extern function application (simplified - returns immediately)
        let argQt := ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        let unifiedEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured capturedEnv) x argQt

        -- Process effects
        let mut memEnv := result2.memEnv'
        let mut nextLoc := result2.nextLoc'
        for effect in effects do
          match effect.target with
          | EffectTarget.namedVar v =>
              match unifiedEnv.lookup v with
              | some qt =>
                  match qt.etyp with
                  | ETyp.ref _t ls =>
                      let effectQt ← effectSpecToQTyp effect.poison effect.pred unifiedEnv
                      let storedQt := ⟨effectQt.etyp, joinPoison ctx.pc effectQt.poison, effectQt.pred⟩
                      memEnv := LocSet.fold ls memEnv (fun acc l => acc.insert l storedQt)
                  | _ => throw s!"Effect target {v} must be a reference type"
              | none => throw s!"Effect target {v} not found in environment"
          | EffectTarget.returnValue => pure ()

        -- Handle return spec
        match retSpec with
        | ExternReturn.simple typ poison pred =>
            let (retQt, nextLoc') ← returnSpecToQTyp typ poison pred unifiedEnv nextLoc

            match retQt.etyp with
            | ETyp.ref _t ls =>
                let returnEffect := effects.find? (fun eff =>
                  match eff.target with
                  | EffectTarget.returnValue => true
                  | _ => false)
                match returnEffect with
                | some eff =>
                    let effectQt ← effectSpecToQTyp eff.poison eff.pred unifiedEnv
                    let storedQt := ⟨effectQt.etyp, joinPoison ctx.pc effectQt.poison, effectQt.pred⟩
                    memEnv := LocSet.fold ls memEnv (fun acc l => acc.insert l storedQt)
                | none => pure ()
            | _ =>
                let hasReturnEffect := effects.any (fun eff =>
                  match eff.target with
                  | EffectTarget.returnValue => true
                  | _ => false)
                if hasReturnEffect then
                  throw "Effect on 'return' is only valid when return type is a reference"

            -- Issue #111: taint app result by function poison (p, p1)
            -- Issue #113: provenance gate
            let poison' := joinPoison p1 (joinPoison p (joinPoison ctx.pc retQt.poison))
            let qt := ⟨retQt.etyp, poison', retQt.pred⟩
            let normalizedQt := normalizeAppResultByProvenance p1 qt
            return { qualType := normalizedQt, memEnv' := memEnv, tagEnv' := result2.tagEnv',
                     nextLoc' := nextLoc', nextTag' := advanceNextTagForSyntaxPred pred (advanceNextTagForEffects effects result2.nextTag'), regime' := result2.regime' }

        | ExternReturn.nestedFn innerArg innerArgTyp innerRet innerEffects =>
            let innerTcl := FnTClosure.extern innerArg innerRet innerEffects (VarTypeEnv.toCaptured unifiedEnv)
            let innerArrowTyp := ETyp.arrow innerArgTyp (parseReturnType innerRet) ctx.pc [innerTcl]
            -- Issue #111: taint app result by function poison (p, p1)
            -- Issue #113: provenance gate
            let poison' := joinPoison p1 (joinPoison p ctx.pc)
            let qt := ⟨innerArrowTyp, poison', Predicate.noPred⟩
            let normalizedQt := normalizeAppResultByProvenance p1 qt
            return { qualType := normalizedQt, memEnv' := memEnv, tagEnv' := result2.tagEnv',
                     nextLoc' := nextLoc, nextTag' := advanceNextTagForEffects effects result2.nextTag', regime' := result2.regime' }

        | ExternReturn.nestedPfn innerArg innerArgTyp innerRet =>
            let innerTcl := PFnTClosure.extern innerArg innerRet (VarTypeEnv.toCaptured unifiedEnv)
            let innerArrowTyp := ETyp.parrow innerArgTyp (parseReturnType innerRet) ctx.pc [innerTcl]
            -- Issue #111: taint app result by function poison (p, p1)
            -- Issue #113: provenance gate
            let poison' := joinPoison p1 (joinPoison p ctx.pc)
            let qt := ⟨innerArrowTyp, poison', Predicate.noPred⟩
            let normalizedQt := normalizeAppResultByProvenance p1 qt
            return { qualType := normalizedQt, memEnv' := memEnv, tagEnv' := result2.tagEnv',
                     nextLoc' := nextLoc, nextTag' := advanceNextTagForEffects effects result2.nextTag', regime' := result2.regime' }
termination_by fuel

/-- Helper: Apply a single PFnTClosure and return the result type and updated environments.
    This encapsulates the body typing logic for a single pure closure alternative.
-/
def applyPFnTClosure (mode : EvalMode) (tcl : PFnTClosure) (_st1 st2 : Typ) (p : Poison) (p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (ctx : TypeContext) (result2 : TypeResult) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel in applyPFnTClosure"
  | fuel + 1 => do
    match tcl with
    | PFnTClosure.regular x body env =>
        -- Type the body with the closure's captured environment in pure context
        let argQt : QTyp := ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        let envMap := VarTypeEnv.ofCaptured env
        let env' := VarTypeEnv.update envMap x argQt
        let ctx'' := { ctx with pc := joinPoison p (joinPoison ctx.pc p1),
                                memEnv := result2.memEnv', varEnv := env', tagEnv := result2.tagEnv',
                                pureCtx := true, nextLoc := result2.nextLoc', nextTag := result2.nextTag', regime := result2.regime' }
        let result3 ← typecheckExpr mode ctx'' (PExpr.toExpr body) fuel
        let ⟨_etyp3, _p3, _pred3⟩ := result3.qualType

        -- Check subtyping
        if not (isSubtype st2 result3.qualType) then
          throw s!"Type mismatch in function application: return type {repr st2} is not compatible with body type {repr (QTyp.toTyp result3.qualType)}"

        -- Issue #111: taint app result by function poison (p, p1)
        -- Issue #113: provenance gate - if p1, force irrecoverable poison and no_pred
        let taintedPoison := joinPoison p1 (joinPoison p result3.qualType.poison)
        let taintedQt := { result3.qualType with poison := taintedPoison }
        return { result3 with qualType := normalizeAppResultByProvenance p1 taintedQt }

    | PFnTClosure.extern x retSpec capturedEnv =>
        if mode == .ioFree then throw "Extern function application forbidden in ioFree mode"
        -- Extern pure function application (no effects)
        let argQt := ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        let unifiedEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured capturedEnv) x argQt

        let mut nextLoc := result2.nextLoc'

        -- Handle return spec (simple or nested)
        match retSpec with
        | ExternReturn.simple typ poison pred =>
            let (retQt, nextLoc') ← returnSpecToQTyp typ poison pred unifiedEnv nextLoc

            -- Issue #111: taint app result by function poison (p, p1)
            -- Issue #113: provenance gate
            let poison' := joinPoison p1 (joinPoison p (joinPoison ctx.pc retQt.poison))
            let qt := ⟨retQt.etyp, poison', retQt.pred⟩
            let normalizedQt := normalizeAppResultByProvenance p1 qt
            return { qualType := normalizedQt, memEnv' := result2.memEnv', tagEnv' := result2.tagEnv',
                     nextLoc' := nextLoc', nextTag' := advanceNextTagForSyntaxPred pred result2.nextTag', regime' := result2.regime' }

        | ExternReturn.nestedFn innerArg innerArgTyp innerRet innerEffects =>
            let innerTcl := FnTClosure.extern innerArg innerRet innerEffects (VarTypeEnv.toCaptured unifiedEnv)
            let innerArrowTyp := ETyp.arrow innerArgTyp (parseReturnType innerRet) ctx.pc [innerTcl]
            -- Issue #111: taint app result by function poison (p, p1)
            -- Issue #113: provenance gate
            let poison' := joinPoison p1 (joinPoison p ctx.pc)
            let qt := ⟨innerArrowTyp, poison', Predicate.noPred⟩
            let normalizedQt := normalizeAppResultByProvenance p1 qt
            return { qualType := normalizedQt, memEnv' := result2.memEnv', tagEnv' := result2.tagEnv',
                     nextLoc' := nextLoc, nextTag' := result2.nextTag', regime' := result2.regime' }

        | ExternReturn.nestedPfn innerArg innerArgTyp innerRet =>
            let innerTcl := PFnTClosure.extern innerArg innerRet (VarTypeEnv.toCaptured unifiedEnv)
            let innerArrowTyp := ETyp.parrow innerArgTyp (parseReturnType innerRet) ctx.pc [innerTcl]
            -- Issue #111: taint app result by function poison (p, p1)
            -- Issue #113: provenance gate
            let poison' := joinPoison p1 (joinPoison p ctx.pc)
            let qt := ⟨innerArrowTyp, poison', Predicate.noPred⟩
            let normalizedQt := normalizeAppResultByProvenance p1 qt
            return { qualType := normalizedQt, memEnv' := result2.memEnv', tagEnv' := result2.tagEnv',
                     nextLoc' := nextLoc, nextTag' := result2.nextTag', regime' := result2.regime' }
termination_by fuel

def typecheckApp (mode : EvalMode) (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    -- NOTE: The operational semantics evaluates application argument-first (see `beval`),
    -- so we typecheck the argument before the function to mirror the evaluation order.
    --
    let result2 ← typecheckExpr mode ctx e2 fuel
    let ⟨etyp2, p2, pred2⟩ := result2.qualType

    let ctx' := { ctx with memEnv := result2.memEnv', tagEnv := result2.tagEnv', nextLoc := result2.nextLoc', nextTag := result2.nextTag', regime := result2.regime' }
    let result1 ← typecheckExpr mode ctx' e1 fuel
    let ⟨etyp1, p1, _pred1⟩ := result1.qualType
    match etyp1 with
    | ETyp.arrow st1 st2 p tcls =>
      -- In pure context, disallow applying impure arrow
      if ctx.pureCtx then
        throw "Pure context disallows application of impure function"

      -- Check for empty closure list (should never happen in well-formed programs)
      if tcls.isEmpty then
        throw "Function type has empty closure set"

      -- Premise 3: ST1 <: T1 (check subtyping)
      if not (isSubtype st1 result2.qualType) then
        throw s!"Type mismatch in function application: parameter type {repr st1} is not compatible with argument type {repr (QTyp.toTyp result2.qualType)}"

      -- Apply each closure in the list using List.mapM
      let results ← List.mapM (fun tcl => applyFnTClosure mode tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 fuel) tcls

      -- Check that we have at least one result and join them
      match results with
      | [] => throw "Internal error: no results from closure application"
      | firstResult :: restResults => joinTypeResults ctx firstResult restResults
    | ETyp.parrow st1 st2 p tcls =>
      -- Check for empty closure list (should never happen in well-formed programs)
      if tcls.isEmpty then
        throw "Function type has empty closure set"

      -- Premise 3: ST1 <: T1 (check subtyping)
      if not (isSubtype st1 result2.qualType) then
        throw s!"Type mismatch in function application: parameter type {repr st1} is not compatible with argument type {repr (QTyp.toTyp result2.qualType)}"

      -- Apply each closure in the list using List.mapM
      let results ← List.mapM (fun tcl => applyPFnTClosure mode tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 fuel) tcls

      -- Check that we have at least one result and join them
      match results with
      | [] => throw "Internal error: no results from closure application"
      | firstResult :: restResults => joinTypeResults ctx firstResult restResults

    | _ => throw "Left operand of application must be a function"
termination_by fuel


/-- Rule: let (Ott rule: let)
      --  pc ; G ; S ; L |- e1 : T :> p1 { P1 } -| G' ; L'
      --  pc ; G' ; S[x |-> T :> p1  { P1 }] ; L' |- e2 : T2 :> p2 { P2 } -| G'' ; L''
          ----------------------------------------------------------------------  :: let
      --  pc ; G ; S ; L |- let x = e1 in e2 : T2 :> join pc p2 { P2 } -| G'' ; L''
  -/
def typecheckVlet (mode : EvalMode) (ctx : TypeContext) (x : Name) (e1 : Expr) (e2 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    -- Check for harmful shadowing (Option B): reject if outer binding has guardClosure with interpreted tag
    match ctx.varEnv.lookup x with
    | none => pure ()
    | some qt_outer =>
      match qt_outer.pred with
      | Predicate.guardClosure k _ _ _ =>
        if ctx.regime.lookup? k |>.isSome then
          throw s!"Cannot shadow variable '{x}': outer binding has an active guard predicate"
      | _ => pure ()

    let result1 ← typecheckExpr mode ctx e1 fuel
    let varEnv' := ctx.varEnv.update x result1.qualType
    let ctx' := { ctx with memEnv := result1.memEnv', varEnv := varEnv', tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime' }

    let result2 ← typecheckExpr mode ctx' e2 fuel
    let ⟨etyp2, p2, pred2⟩ := result2.qualType
   --dbg_trace s!" In typecheck Let ,Poison val for exp {e1} is {p1}"
   -- dbg_trace s!"In typecheck Let ,Poison val for exp {e2} is {p2}"

    let poison := joinPoison ctx.pc p2
    let qt : QTyp := ⟨etyp2, poison, pred2⟩
    return { qualType := qt, memEnv' := result2.memEnv', tagEnv' := result2.tagEnv', nextLoc' := result2.nextLoc', nextTag' := result2.nextTag', regime' := result2.regime' }
termination_by fuel


/-- Rule: if_depoison_* and if_std_* (Ott rules with regime awareness)
-- When matchGuard succeeds: consult R(k) for regime-aware typing
-- When matchGuard fails: use standard conservative typing
-- In ioFree mode with known regime, skip typechecking the untaken branch
-- Implements all if_* rules from poison-lang.ott faithfully
--/
def typecheckIf (mode : EvalMode) (ctx : TypeContext) (e1 e2 e3 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    -- Step 1: Try matchGuard first
    match matchGuard e1 ctx.memEnv ctx.varEnv with
    | .ok (k, deps) => do
      -- Predicate-based case: consult R(k)

      -- Typecheck e1 in pure mode (all if_depoison_* rules require this)
      let pureCtx := { ctx with pureCtx := true }
      let result1 ← typecheckExpr mode pureCtx e1 fuel
      let ⟨etyp1, p1, _⟩ := result1.qualType
      if etyp1 != ETyp.bool then throw "Condition of if must be bool"

      -- Setup branch contexts with tag knowledge
      let ctxTrue := { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ }
      let ctxFalse := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩ }

      -- Consult R(k) for branch selection
      match ctx.regime.lookup? k with
      | some true => do
        -- R(k) = true: then-branch effective (if_depoison_*_R_true rules)
        let result2 ← typecheckExpr mode ctxTrue e2 fuel
        let ⟨etyp2, p2, _pred2⟩ := result2.qualType

        -- In ioFree mode, skip else-branch (untaken at runtime)
        if mode == .ioFree then
          let poison := joinPoison ctx.pc p2
          let qt : QTyp := ⟨etyp2, poison, Predicate.noPred⟩
          return { qualType := qt, memEnv' := result2.memEnv', tagEnv' := result2.tagEnv',
                   nextLoc' := result2.nextLoc', nextTag' := result2.nextTag', regime' := result2.regime' }
        -- Normal mode: typecheck else-branch for well-formedness
        let ctxFalse' := { ctxFalse with nextLoc := result2.nextLoc', nextTag := result2.nextTag' }
        let result3 ← typecheckExpr mode ctxFalse' e3 fuel
        let ⟨etyp3, _p3, _pred3⟩ := result3.qualType
        if not (beqETypSignature etyp2 etyp3) then throw s!"Branches of if must have same type (etyp2: {etyp2}, etyp3: {etyp3})"
        let poison := joinPoison ctx.pc p2
        let qt : QTyp := ⟨etyp2, poison, Predicate.noPred⟩
        return { qualType := qt, memEnv' := result2.memEnv', tagEnv' := result2.tagEnv',
                 nextLoc' := max result2.nextLoc' result3.nextLoc', nextTag' := max result2.nextTag' result3.nextTag', regime' := result2.regime' }

      | some false => do
        -- R(k) = false: else-branch effective (if_depoison_*_R_false rules)
        -- In ioFree mode, skip then-branch (untaken at runtime)
        if mode == .ioFree then do
          let ctxFalse' := ctxFalse
          let result3 ← typecheckExpr mode ctxFalse' e3 fuel
          let ⟨etyp3, p3, _pred3⟩ := result3.qualType
          let poison := joinPoison ctx.pc p3
          let qt : QTyp := ⟨etyp3, poison, Predicate.noPred⟩
          return { qualType := qt, memEnv' := result3.memEnv', tagEnv' := result3.tagEnv',
                   nextLoc' := result3.nextLoc', nextTag' := result3.nextTag', regime' := result3.regime' }
        -- Normal mode: typecheck both branches
        let result2 ← typecheckExpr mode ctxTrue e2 fuel
        let ⟨etyp2, _p2, _pred2⟩ := result2.qualType
        let ctxFalse' := { ctxFalse with nextLoc := result2.nextLoc', nextTag := result2.nextTag' }
        let result3 ← typecheckExpr mode ctxFalse' e3 fuel
        let ⟨etyp3, p3, _pred3⟩ := result3.qualType
        if not (beqETypSignature etyp2 etyp3) then throw s!"Branches of if must have same type (etyp2: {etyp2}, etyp3: {etyp3})"
        let poison := joinPoison ctx.pc p3
        let qt : QTyp := ⟨etyp3, poison, Predicate.noPred⟩
        return { qualType := qt, memEnv' := result3.memEnv', tagEnv' := result3.tagEnv',
                 nextLoc' := max result2.nextLoc' result3.nextLoc', nextTag' := max result2.nextTag' result3.nextTag', regime' := result3.regime' }

      | none => do
        -- R(k) = none: conservative fallback (if_depoison_*_R_unknown rules)
        -- Branch pc is poisoned by guard poison
        let branchPc := joinPoison ctx.pc p1
        let ctxTruePoisoned := { ctxTrue with pc := branchPc }
        let ctxFalsePoisoned := { ctxFalse with pc := branchPc }

        let result2 ← typecheckExpr mode ctxTruePoisoned e2 fuel
        let ⟨etyp2, p2, _pred2⟩ := result2.qualType

        let ctxFalse' := { ctxFalsePoisoned with nextLoc := result2.nextLoc', nextTag := result2.nextTag' }
        let result3 ← typecheckExpr mode ctxFalse' e3 fuel
        let ⟨etyp3, p3, _pred3⟩ := result3.qualType

        -- Check type compatibility
        if not (beqETypSignature etyp2 etyp3) then throw s!"Branches of if must have same type (etyp2: {etyp2}, etyp3: {etyp3})"

        -- Join both branches (conservative)
        let joinedEtyp := joinETyps etyp2 etyp3 p2 p3
        let poison := joinPoison ctx.pc (joinPoison p1 (joinPoison p2 p3))
        let qt : QTyp := ⟨joinedEtyp, poison, Predicate.noPred⟩
        let memEnv' := joinMemEnvsStrong result2.memEnv' result3.memEnv'
        let tagEnv' := joinTagEnvs result2.tagEnv' result3.tagEnv'
        let regime' := joinRegimes result2.regime' result3.regime'
        let nextLoc' := max result2.nextLoc' result3.nextLoc'
        let nextTag' := max result2.nextTag' result3.nextTag'
        return { qualType := qt, memEnv' := memEnv', tagEnv' := tagEnv', nextLoc' := nextLoc', nextTag' := nextTag', regime' := regime' }

    | .error _ => do
      -- Standard case (if_std_*) - no matching predicate found
      let result1 ← typecheckExpr mode ctx e1 fuel
      let ⟨etyp1, p1, _⟩ := result1.qualType
      if etyp1 != ETyp.bool then throw "Condition of if must be bool"

      let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv',
                             nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime' }

      -- Branch pc is poisoned by guard poison
      let branchPc := joinPoison ctx.pc p1
      let ctx'' := { ctx' with pc := branchPc }

      let result2 ← typecheckExpr mode ctx'' e2 fuel
      let ⟨etyp2, p2, _⟩ := result2.qualType

      -- Ensure disjoint fresh supplies across branches
      -- Note: regime stays as ctx''.regime (= result1.regime') since branches are parallel, not sequential
      let ctxForE3 := { ctx'' with nextLoc := result2.nextLoc', nextTag := result2.nextTag' }
      let result3 ← typecheckExpr mode ctxForE3 e3 fuel
      let ⟨etyp3, p3, _⟩ := result3.qualType

      -- Check type compatibility
      if not (beqETypSignature etyp2 etyp3) then throw s!"Branches of if must have same type"

      -- Join both branches (if_std_* rules)
      let joinedEtyp := joinETyps etyp2 etyp3 p2 p3
      let poison := joinPoison ctx.pc (joinPoison p1 (joinPoison p2 p3))
      let qt : QTyp := ⟨joinedEtyp, poison, Predicate.noPred⟩
      let memEnv' := joinMemEnvsStrong result2.memEnv' result3.memEnv'
      let tagEnv' := joinTagEnvs result2.tagEnv' result3.tagEnv'
      let regime' := joinRegimes result2.regime' result3.regime'
      let nextLoc' := max result2.nextLoc' result3.nextLoc'
      let nextTag' := max result2.nextTag' result3.nextTag'
      return { qualType := qt, memEnv' := memEnv', tagEnv' := tagEnv', nextLoc' := nextLoc', nextTag' := nextTag', regime' := regime' }
termination_by fuel



/- Rule: not_expr_typing (Ott rule: not_expr_typing)

pm ; pc ; G ; S ; L |- e : bool :> p { P } -| G' ; L'
----------------------------------------------------------------------  :: not_expr_typing
pm ; pc ; G ; S ; L |- not_expr e : bool :> join pc p { no_pred } -| G' ; L'

-/

def typecheckUnaryOp (mode : EvalMode) (ctx : TypeContext) (op : UnaryOp) (e : Expr) (fuel : Nat):TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    let result ← typecheckExpr mode ctx e fuel
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
def typecheckWhile (mode : EvalMode) (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    -- Step 1: Try matchGuard first (as in typecheckIf)
    match matchGuard e1 ctx.memEnv ctx.varEnv with
    | .ok (k, deps) => do
      -- Predicate-based case (while_depoison) - condition is pure
      typecheckWhileDepoison mode ctx e1 e2 fuel k deps
    | .error _ => do
      -- Standard case (while_std) - condition can modify G and L
      typecheckWhileStd mode ctx e1 e2 fuel
termination_by fuel

end

-- Main type checking function
def typecheck (mode : EvalMode) (ctx : TypeContext) (e : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  typecheckExpr mode ctx e fuel



/-- Type check an expression in an initial empty context -/
def typecheckExprSimple (e : Expr) (regime : Regime := emptyRegime) (mode : EvalMode := .normal) : TypecheckM QTyp := do
  let initialCtx : TypeContext := {
    pc := false  -- clean
    regime := regime
    memEnv := {}
    varEnv := ({} : VarTypeEnv)
    tagEnv := {}
    nextLoc := 0
    nextTag := 1
    pureCtx := false
  }
  let result ← typecheck mode initialCtx e defaultFuel
  return result.qualType

def typecheckExprVerbose (e : Expr) (regime : Regime := emptyRegime) (mode : EvalMode := .normal) : TypecheckM TypeResult := do
  let initialCtx : TypeContext := {
    pc := false  -- clean
    regime := regime
    memEnv := {}
    varEnv := ({} : VarTypeEnv)
    tagEnv := {}
    nextLoc := 0
    nextTag := 1
    pureCtx := false
  }
  typecheck mode initialCtx e defaultFuel


/-- Type check a program (expression) and return a human-readable result -/
def typecheckProgram (e : Expr) (verbose : Bool) (regime : Regime := emptyRegime) (mode : EvalMode := .normal) : String :=
  if verbose then
    match typecheckExprVerbose e regime mode with
    | .ok result => s!"Type: {repr result.qualType} , MemoryTypeEnv : {repr result.memEnv'} , tagEnv : {repr result.tagEnv'} , nextLoc : {repr result.nextLoc'} "
    | .error msg => s!"Type error: {msg}"
  else
    match typecheckExprSimple e regime mode with
    | .ok qualType  => s!"Type: {repr qualType}"
    | .error msg => s!"Type error: {msg}"
