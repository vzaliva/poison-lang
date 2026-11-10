import LeanPoison.Syntax
import LeanPoison.Misc
import LeanPoison.Pretty

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

/-- Memory entry: poison and predicate only (stored type is always int). -/
structure MemEntry where
  poison : Poison
  pred : Predicate
  deriving Repr, BEq

/-- Memory typing environment (Γ in the Ott spec), keyed by logical locations. -/
abbrev MemoryTypeEnv := ExtTreeMap Loc MemEntry

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

  /-- Lookup returns QTyp with etyp = ETyp.int (memory stores only integers). -/
  @[inline] def lookup (m : MemoryTypeEnv) (l : Loc) : Option QTyp :=
    (m.get? l).map (fun e => ⟨ETyp.int, e.poison, e.pred⟩)

  @[inline] def update (m : MemoryTypeEnv) (l : Loc) (qt : QTyp) : MemoryTypeEnv :=
    m.insert l ⟨qt.poison, qt.pred⟩

  /-- `m` contains a binding for `l`. -/
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
    reprPrec m _ :=
      let entries := ExtTreeMap.toList m
      match entries with
      | [] => "{}"
      | _ =>
          let docs : List Std.Format := entries.map (fun (l, e) => Std.Format.text s!"{l} := ({e.poison}, {repr e.pred})")
          Std.Format.group (
            Std.Format.text "{" ++
            Std.Format.nest 2 (Std.Format.line ++ Std.Format.joinSep docs (Std.Format.text "," ++ Std.Format.line)) ++
            Std.Format.line ++
            Std.Format.text "}"
          )

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
  reprPrec m _ :=
    let entries := ExtTreeMap.toList m
    match entries with
    | [] => "{}"
    | _ =>
        let docs : List Std.Format := entries.map (fun (k, tv) => Std.Format.text s!"{k} := {repr tv}")
        Std.Format.group (
          Std.Format.text "{" ++
          Std.Format.nest 2 (Std.Format.line ++ Std.Format.joinSep docs (Std.Format.text "," ++ Std.Format.line)) ++
          Std.Format.line ++
          Std.Format.text "}"
        )

end TagEnv

/-- Remove from tag environment all entries whose dependency sets intersect the given locset. -/
def invalidateTagDeps (env : TagEnv) (ls : LocSet) : TagEnv :=
  env.filter (fun _ tv =>
    not <| tv.deps.any ls.contains)

/-- Regime: partial mapping from guard tags to their truth values. -/
abbrev Regime := ExtTreeMap Tag Bool

namespace Regime

/-- Lookup a tag in the regime map. -/
def lookup? (R : Regime) (k : Tag) : Option Bool :=
  R.get? k

end Regime

/-- Empty regime: all tags return none (regime-agnostic typing) -/
def emptyRegime : Regime := {}

/-- Invalidate regime entries for tags whose dependencies intersect written locations
    (mirrors invalidateTagDeps behaviour) -/
def invalidateRegimeDeps (R : Regime) (env : TagEnv) (ls : LocSet) : Regime :=
  let invalidated := env.filter (fun _ tv => not <| tv.deps.any ls.contains)
  R.filter (fun k _ => invalidated.contains k)

/-- Effect-path regime invalidation.  Unlike
    `invalidateRegimeDeps` (used by assignment), this removes a regime entry ONLY
    when its tag is a *materialised* guard in `env` whose dependencies intersect the
    written locations.  Driver-asserted regime tags that are not (yet) in `env` —
    e.g. an extern's shared return guard supplied via `--regime`, before it enters
    the tag environment at a later `if`/deref — are KEPT, and a guard the effect's
    own predicate re-establishes is not spuriously dropped (it survives via its
    cell type).  In short: a materialised guard whose predicate reads a written
    effect target is invalidated, while legitimate driver assertions persist
    (see `examples/lp55xx-read.poison`). -/
def invalidateRegimeDepsEffect (R : Regime) (env : TagEnv) (ls : LocSet) : Regime :=
  R.filter (fun k _ =>
    match env.get? k with
    | some tv => not (tv.deps.any ls.contains)
    | none => true)

/-- Join two regimes (conservative intersection: keep only entries that agree) -/
def joinRegimes (R1 R2 : Regime) : Regime :=
  combineExtTreeMaps R1 R2 (fun _ ob1 ob2 =>
    match ob1, ob2 with
    | some b1, some b2 => if b1 == b2 then some b1 else none
    | _, _ => none)

namespace Regime

-- Regime monotonicity: R' can only drop entries (never change values or add new entries)
-- Two constraints:
--   1. preserved entries keep their values
--   2. R' can't have entries that R doesn't have (no new entries)
def monotoneStep (R R' : Regime) : Prop :=
  (∀ k b, R.lookup? k = some b → (R'.lookup? k = some b ∨ R'.lookup? k = none)) ∧
  (∀ k, R'.lookup? k ≠ none → R.lookup? k ≠ none)

/-- Regime evolution that is monotone for old tags but may add fresh tags
    satisfying `newTags` ("monotone modulo fresh selected extern outputs").  The first conjunct (old-entry preservation) is IDENTICAL to
    `monotoneStep`; the second conjunct is weakened to allow result entries whose tag
    is in `newTags`.  Instantiated with `newTags = fun k => bound ≤ k` for the
    freshly-allocated selected extern-output tags of a typing step. -/
def monotoneStepExt (R R' : Regime) (newTags : Tag → Prop) : Prop :=
  (∀ k b, ¬ newTags k → R.lookup? k = some b → (R'.lookup? k = some b ∨ R'.lookup? k = none)) ∧
  (∀ k, R'.lookup? k ≠ none → R.lookup? k ≠ none ∨ newTags k)

/-- `monotoneStep` is the `newTags = ∅` special case of `monotoneStepExt`; the strong
    relation can always be weakened to the extended one for any `newTags`. -/
theorem monotoneStep_toExt {R R' : Regime} (h : monotoneStep R R')
    (newTags : Tag → Prop) : monotoneStepExt R R' newTags :=
  ⟨fun k b _ hR => h.1 k b hR, fun k hk => Or.inl (h.2 k hk)⟩

/-- Backward transport for an old tag: if `k` is not a fresh tag, a result entry for
    `k` was already present in `R` with the same value. -/
theorem monotoneStepExt_lookup_back {R R' : Regime} {newTags : Tag → Prop}
    (h : monotoneStepExt R R' newTags) {k : Tag} {b : Bool}
    (hknew : ¬ newTags k) (hkR' : R'.lookup? k = some b) :
    R.lookup? k = some b := by
  have hRdef : R.lookup? k ≠ none := by
    rcases h.2 k (by simp [hkR']) with hne | hnew
    · exact hne
    · exact absurd hnew hknew
  cases hkR : R.lookup? k with
  | none => exact absurd hkR hRdef
  | some b0 =>
      rcases h.1 k b0 hknew hkR with hkR'' | hkR''
      · have : b0 = b := Option.some.inj (hkR''.symm.trans hkR'); subst this; rfl
      · simp [hkR''] at hkR'

/-- Reflexivity of the extended-regime relation. -/
theorem monotoneStepExt_refl (R : Regime) (newTags : Tag → Prop) :
    monotoneStepExt R R newTags :=
  ⟨fun _ _ _ h => Or.inl h, fun _ h => Or.inl h⟩

/-- Weaken the fresh-tag set of an extended-regime step.  (Larger `newTags` ⇒ weaker relation:
    the forward part is restricted to fewer tags, the backward part allows more.) -/
theorem monotoneStepExt_weaken {R R' : Regime} {nt nt' : Tag → Prop}
    (h : monotoneStepExt R R' nt) (hsub : ∀ k, nt k → nt' k) :
    monotoneStepExt R R' nt' :=
  ⟨fun k b hnt' hR => h.1 k b (fun hnt => hnt' (hsub k hnt)) hR,
   fun k hk => (h.2 k hk).imp id (hsub k)⟩

/-- Transitivity of the extended-regime relation.  With the forward conjunct restricted to
    non-fresh tags, NO disjointness side condition is needed. -/
theorem monotoneStepExt_trans {R1 R2 R3 : Regime} {nt1 nt2 : Tag → Prop}
    (h12 : monotoneStepExt R1 R2 nt1) (h23 : monotoneStepExt R2 R3 nt2) :
    monotoneStepExt R1 R3 (fun k => nt1 k ∨ nt2 k) := by
  refine ⟨?_, ?_⟩
  · intro k b hnt hR1
    have hn1 : ¬ nt1 k := fun h => hnt (Or.inl h)
    have hn2 : ¬ nt2 k := fun h => hnt (Or.inr h)
    rcases h12.1 k b hn1 hR1 with hR2 | hR2
    · rcases h23.1 k b hn2 hR2 with hR3 | hR3
      · exact Or.inl hR3
      · exact Or.inr hR3
    · refine Or.inr ?_
      by_contra hR3ne
      rcases h23.2 k hR3ne with hR2ne | hnt2
      · exact hR2ne hR2
      · exact hn2 hnt2
  · intro k hR3
    rcases h23.2 k hR3 with hR2ne | hnt2
    · rcases h12.2 k hR2ne with hR1ne | hnt1
      · exact Or.inl hR1ne
      · exact Or.inr (Or.inl hnt1)
    · exact Or.inr (Or.inr hnt2)

/-- Packaged transitivity for the `≥`-bound fresh-tag sets used by the typechecker regime chain:
    compose `R1→R2` (fresh `≥ b1`) with `R2→R3` (fresh `≥ b2`), where `b1 ≤ b2` (nextTag-mono),
    and weaken back to `≥ b1`. -/
theorem monotoneStepExt_trans_le {R1 R2 R3 : Regime} {b1 b2 : Tag}
    (h12 : monotoneStepExt R1 R2 (fun k => b1 ≤ k))
    (h23 : monotoneStepExt R2 R3 (fun k => b2 ≤ k)) (hb : b1 ≤ b2) :
    monotoneStepExt R1 R3 (fun k => b1 ≤ k) :=
  monotoneStepExt_weaken (monotoneStepExt_trans h12 h23)
    (fun _ hk => hk.elim id (fun h => _root_.le_trans hb h))

/-- Compose an extended-regime step with a following strong (`monotoneStep`) step: the strong
    step adds no tags, so the fresh-tag set is unchanged.  Used where a typing step ends with a
    regime invalidation (e.g. assignment). -/
theorem monotoneStepExt_trans_monotoneStep {R1 R2 R3 : Regime} {nt : Tag → Prop}
    (h12 : monotoneStepExt R1 R2 nt) (h23 : monotoneStep R2 R3) :
    monotoneStepExt R1 R3 nt := by
  refine ⟨?_, ?_⟩
  · intro k b hknt hR1
    rcases h12.1 k b hknt hR1 with hR2 | hR2
    · exact h23.1 k b hR2
    · refine Or.inr ?_
      by_contra hR3
      exact (h23.2 k hR3) hR2
  · intro k hR3
    exact h12.2 k (h23.2 k hR3)

end Regime

/-- Type checking context containing all environments -/
structure TypeContext where
  pc : Poison            -- Poison context
  regime : Regime        -- R (regime for FR reasoning)
  memEnv : MemoryTypeEnv -- Γ
  varEnv : VarTypeEnv    -- σ
  tagEnv : TagEnv        -- ℒ
  nextLoc : Loc  -- for fresh logical location generation
  nextTag : Tag  -- for fresh tag generation
  pureCtx : Bool -- whether we are inside a pure function body typing
  -- Extern-regime policy: for a selected extern id and
  -- a freshly-allocated output guard tag, the scenario chooses `some b` (insert
  -- `tag ↦ b` into `regime'`) or `none` (leave the tag out → conservative path).
  -- The default `fun _ _ => none` selects no extern (the policy then inserts
  -- nothing into the regime) and threads unchanged through every
  -- `{ ctx with … }` update.
  externRegime : ExternId → Tag → Option Bool := fun _ _ => none
  -- Reference-valued extern discipline (doc/externs.md, `@21`): `extern
  -- ref` may only appear in evaluate-at-most-once positions.  The flag is
  -- cleared when descending into fn/pfn bodies at application time; it flows
  -- downward only (results never restore it).
  externRefAllowed : Bool := true
  -- Extern ids already declared by an `extern ref` on this typing path.  Each
  -- id may be declared at most once per program (the fault-robustness proof
  -- realizes each registry-reserved address at most once).  Threaded serially
  -- through subexpressions — including across `if` arms — via
  -- `TypeResult.declared'`.
  declaredExternRefs : List ExternId := []

/-- Type checking result: qualified type and updated memory environment -/
structure TypeResult where
  qualType : QTyp -- Qualified type of the expression
  memEnv' : MemoryTypeEnv -- Updated memory typing environment
  tagEnv' : TagEnv  -- Updated logical environment
  nextLoc' : Loc -- Updated next logical location
  nextTag' : Tag -- Updated next tag
  regime' : Regime -- Updated regime after typing step
  declared' : List ExternId -- Updated declared `extern ref` ids (no default: every result must thread it)

/-- Type checking monad for error handling -/
abbrev TypecheckM := Except String

/-- Update the context with the result of a type checking operation -/
def updateCtxFromResult (ctx : TypeContext) (result : TypeResult) : TypeContext :=
  { ctx with memEnv := result.memEnv', tagEnv := result.tagEnv', nextLoc := result.nextLoc', nextTag := result.nextTag', regime := result.regime', declaredExternRefs := result.declared' }

/-- Extract dependencies from a predicate by analyzing free variables in the predicate body -/
def extractDepsFromPred (pred : Predicate) (fuel : Nat) : TypecheckM Deps :=
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
              | ETyp.ref ls => return ls  -- Reference type, add referenced locset
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
    extractDepsFromPExpr pred_body [arg_name] varEnvMap fuel
  | Predicate.guardOnly _tag =>
    -- Guard-only predicate with no body, no dependencies
    return LocSet.empty
  | Predicate.noPred =>
    -- No predicate, no dependencies
    return LocSet.empty

-- Allocate a fresh location and return it along with updated typing context
def freshTLoc (ctx : TypeContext): (Loc × TypeContext) :=
  (ctx.nextLoc, { ctx with nextLoc := ctx.nextLoc + 1 })

-- Allocate a fresh location and return it along with updated typing result
def freshTLocRes (result : TypeResult): (Loc × TypeResult) :=
  (result.nextLoc', { result with nextLoc' := result.nextLoc' + 1 })

-- Function to get a fresh Tag Value From the environment
private def generateFreshTag (ctx : TypeContext) : (Tag × TypeContext) :=
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

/-- Advance `nextTag` past any literal tag index mentioned by a
    `SyntaxPredicate`. The extern typechecking path allocates fresh tags via
    `collectAndAllocExternTags`; this helper is the direct cursor arithmetic for
    already-indexed syntax predicates. -/
def advanceNextTagForSyntaxPred (pred : SyntaxPredicate) (nextTag : Tag) : Tag :=
  match pred with
  | SyntaxPredicate.guardClosure k _ _ => max nextTag (k.val + 1)
  | SyntaxPredicate.guardOnly k        => max nextTag (k.val + 1)
  | SyntaxPredicate.noPred             => nextTag

/-- Advance nextTag past all tags introduced by an effects list. -/
def advanceNextTagForEffects (effects : List Effect) (nextTag : Tag) : Tag :=
  effects.foldl (fun acc eff => advanceNextTagForSyntaxPred eff.pred acc) nextTag

-- Helper functions

/-- Join two poison flags -/
def joinPoison (p1 p2 : Poison) : Poison :=
  p1 || p2

/-- Join multiple poison flags -/
private def joinPoisons (ps : List Poison) : Poison :=
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
  env.insert l ⟨qt.poison, qt.pred⟩

/-- Weak update for non-singleton locsets: join stored poison/pred with existing entries.
    Computes max poison and merged predicate across all locations, then updates uniformly.
    This implements the weak update semantics for assign_locset in the Ott spec.

    A locset member that is NOT tracked by the memory environment (possible after
    conservative `if` typing) degrades the joined predicate to `noPred`: a
    symbolic guard claim is only kept when every written cell is tracked, since an
    untracked cell has no prior type (and, in a well-formed run, no realization)
    against which the claim could be justified.  The poison join is unaffected by
    untracked members (still conservative). -/
def updateLocsetWeak (env : MemoryTypeEnv) (ls : LocSet) (storedPoison : Poison) (storedPred : Predicate) : MemoryTypeEnv :=
  -- First pass: compute joined poison and predicate from existing entries
  let (joinedPoison, joinedPred) := LocSet.fold ls (storedPoison, storedPred) (fun (accP, accPred) l =>
    match env.get? l with
    | some e => (joinPoison accP e.poison, joinPredicates accPred e.pred)
    | none => (accP, Predicate.noPred))
  -- Second pass: update all locations with the joined entry
  let entry : MemEntry := ⟨joinedPoison, joinedPred⟩
  LocSet.fold ls env (fun acc l => acc.insert l entry)

/-- Join two memory environments (branch join). See JoinG in the Ott spec. -/
def joinMemEnvs (env1 env2 : MemoryTypeEnv) : MemoryTypeEnv :=
  combineExtTreeMaps env1 env2 (fun _ oe1 oe2 =>
    match oe1, oe2 with
    | some e1, none => some e1
    | none, some e2 => some e2
    | some e1, some e2 =>
      let p := joinPoison e1.poison e2.poison
      let pred := joinPredicates e1.pred e2.pred
      some ⟨p, pred⟩
    | none, none => none)

/-- Strong join: like joinMemEnvs but drops predicates for single-sided entries.
    Used for standard-case if joins (if_std_*) so that
    guardClosure from an untaken branch does not survive into the post-context. -/
def joinMemEnvsStrong (env1 env2 : MemoryTypeEnv) : MemoryTypeEnv :=
  combineExtTreeMaps env1 env2 (fun _ oe1 oe2 =>
    match oe1, oe2 with
    | some e1, none =>
      -- Single-sided: keep poison, drop predicate
      some ⟨e1.poison, Predicate.noPred⟩
    | none, some e2 =>
      -- Single-sided: keep poison, drop predicate
      some ⟨e2.poison, Predicate.noPred⟩
    | some e1, some e2 =>
      -- Both-sided: same as joinMemEnvs
      let p := joinPoison e1.poison e2.poison
      let pred := joinPredicates e1.pred e2.pred
      some ⟨p, pred⟩
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
  | ETyp.ref ls1, ETyp.ref ls2 =>
      ETyp.ref (LocSet.union ls1 ls2)
  | ETyp.arrow st1 st2 p1' tcls1, ETyp.arrow st1' st2' p2' tcls2 =>
      -- Signature compatibility already checked; merge closures and join arrow-internal poisons
      if st1 == st1' && st2 == st2' then
        let mergedClosures := mergeFnTClosures tcls1 tcls2
        -- Join arrow-internal poisons: p = join p' p'' (Ott rules: if_std_fn, app_fn_cons_arrow)
        ETyp.arrow st1 st2 (joinPoison p1' p2') mergedClosures
      else
        t1  -- Fallback (should not happen if beqETypSignature passed)
  | ETyp.parrow st1 st2 p1' tcls1, ETyp.parrow st1' st2' p2' tcls2 =>
      -- Signature compatibility already checked; merge closures and join arrow-internal poisons
      if st1 == st1' && st2 == st2' then
        let mergedClosures := mergePFnTClosures tcls1 tcls2
        -- Join arrow-internal poisons: p = join p' p'' (Ott rules: if_std_pfn, app_pfn_cons_arrow)
        ETyp.parrow st1 st2 (joinPoison p1' p2') mergedClosures
      else
        t1  -- Fallback (should not happen if beqETypSignature passed)
  | _, _ =>
      -- For non-arrow types, types must be equal (checked via beqETypSignature)
      t1

/-- Join two logical environments (agreement-only meet used in if-then-else) -/
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
private def ETyp.toTyp (pt : ETyp) : Typ :=
  match pt with
  | ETyp.int => Typ.int
  | ETyp.bool => Typ.bool
  | ETyp.unit => Typ.unit
  | ETyp.string => Typ.string
  | ETyp.ref _ => Typ.ref Typ.int
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

/-- Erase a qualified type to its surface type: drop the poison and predicate,
    then erase the enriched type (`ETyp.toTyp`). -/
private def QTyp.toTyp (qt : QTyp) : Typ :=
  qt.etyp.toTyp

/-- Check that the surface type `st` is the erasure of the qualified type `qt`:
    `qt`'s enriched type with its location sets and the poison and closure
    sets of arrows dropped must equal `st`. Pure and impure arrows both erase
    to `Typ.arrow`, and a reference erases to `ref int`, since `ETyp.ref`
    carries no referent type. This implements the side condition
    `erase T = ST` (rendered ⌊T⌋ = ST) of the application rules. The
    comparison is syntactic equality after erasure.
-/
def isErasureOf (st : Typ) (qt : QTyp) : Bool :=
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

private inductive OpUnaryEType : UnaryOp → ETyp → ETyp → Prop where
  | not_bool : OpUnaryEType UnaryOp.not ETyp.bool ETyp.bool

def opUnaryEType? : UnaryOp → ETyp → Option ETyp
  | .not, .bool  => some .bool
  | _,    _     => none

/--
 Helper function to check if two PExprs are syntactically equal modulo
 environment differences. This handles variable substitution during structural
 comparison. Variables are substituted in the first argument only.

 The `fuel` parameter is used to prove termination. Structural recursion on the
 pe1 and pe2 arguments does not work in case of substitution: the substituted
 value is compared again under the same substitution, so recursion is bounded
 by fuel instead.

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
def matchGuard (e : Expr) (G : MemoryTypeEnv) (S : VarTypeEnv) (fuel : Nat) : TypecheckM (Tag × Deps) := do
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
          -- Parameterised: proceed with substitution + equality
          if PExpr.equalWithEnvs pred_body var_env conditionPExpr sCaptured (some (arg_name, arg)) fuel then do
            let deps ← extractDepsFromPred qt.pred fuel
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
    | ETyp.ref ls =>
        if qt.poison then
          pure acc
        else
          if ls.isEmpty then throw "Reference locset is empty in matchGuard" else
          let arg := PExpr.deref (PExpr.var name)
          -- Merge predicates across locset, error if a referenced location is missing
          let merged? ←
            LocSet.foldM ls (init := (none : Option Predicate)) (fun accPred? l => do
              match G.lookup l with
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
            match G.lookup l with
            | some memQt =>
                checkNoPredOnArrow memQt
                let deps ← extractDepsFromPred memQt.pred fuel
                pure (LocSet.union dacc (LocSet.union (LocSet.singleton l) deps))
            | none => throw s!"Location {l} not found in memory environment during matchGuard")
          let merged := merged?.getD Predicate.noPred
          match merged with
          | Predicate.guardClosure tag arg_name pred_body var_env =>
              if PExpr.usesArg arg_name pred_body then
                if PExpr.equalWithEnvs pred_body var_env conditionPExpr sCaptured (some (arg_name, arg)) fuel then
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

section TypecheckPrimitives
variable (ctx : TypeContext)

/-- Rule: int (Ott rule: int)
-- pc ; G ; S ; L |- n : int :> clean { no_pred } -| G ; L
-/
def typecheckInt (_n : Int) : TypecheckM TypeResult := do
  let qt : QTyp := ⟨ETyp.int, false, Predicate.noPred⟩  -- clean, no predicate
  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag, regime' := ctx.regime, declared' := ctx.declaredExternRefs }

/-- Rule: bool (Ott rule: bool)
-- pc ; G ; S ; L |- b : bool :> clean { no_pred } -| G ; L
-/
def typecheckBool (_b : Bool) : TypecheckM TypeResult := do
  let qt : QTyp := ⟨ETyp.bool, false, Predicate.noPred⟩  -- clean, no predicate
  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag, regime' := ctx.regime, declared' := ctx.declaredExternRefs }


def typecheckVar (x : Name) : TypecheckM TypeResult := do
  --dbg_trace ("Typechecking var " ++ x)
  --dbg_trace s!"ctx.pc is {ctx.pc}"
  match ctx.varEnv.lookup x with
  | some qt =>
    let ⟨etyp, poison, pred⟩ := qt
    match pred with
    | Predicate.noPred =>  -- no_pred case
      let poison := joinPoison ctx.pc poison
      let qt' : QTyp := ⟨etyp, poison, Predicate.noPred⟩
      return { qualType := qt', memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag, regime' := ctx.regime, declared' := ctx.declaredExternRefs }
    | Predicate.guardOnly k | Predicate.guardClosure k _ _ _ =>
      -- Both guard types behave the same: check tag in L and de-poison/poison/preserve accordingly
      --dbg_trace s!"Guard predicate found with tag {k}"
      if etyp.isFunctionType then
        throw s!"Function types cannot carry guard predicates (variable {x})"
      match ctx.tagEnv.get? k with
      | some ⟨true, _deps⟩ =>  -- guard_true / guard_only_true case
        -- dbg_trace "Guard True case"
        let qt' : QTyp := ⟨etyp, ctx.pc, Predicate.noPred⟩
        return { qualType := qt', memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag, regime' := ctx.regime, declared' := ctx.declaredExternRefs }
      | some ⟨false, _deps⟩ =>  -- guard_false / guard_only_false case
        -- dbg_trace "Guard False case"
        let qt' : QTyp := ⟨etyp, true, Predicate.noPred⟩  -- poisoned
        return { qualType := qt', memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag, regime' := ctx.regime, declared' := ctx.declaredExternRefs }
      | none =>  -- guard_unknown / guard_only_unknown case
        -- dbg_trace "Guard Unknown case"
        let poison := joinPoison ctx.pc poison
        -- Preserve the original predicate (either guardOnly or guardClosure)
        let qt' : QTyp := ⟨etyp, poison, pred⟩
        return { qualType := qt', memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag, regime' := ctx.regime, declared' := ctx.declaredExternRefs }
  | none => throw s!"Variable {x} not found in environment"


/-- Rule: location (no corresponding Ott rule: locations are not surface expressions)
-- G(l) = p { P }
-- ------------------
-- pc ; G ; S ; L |- l : ref @ {l} :> clean { no_pred } -| G ; L
-/
private def typecheckLocation (l : Loc) : TypecheckM TypeResult := do
  match ctx.memEnv.lookup l with
  | some qt =>
    let refTyp := ETyp.ref (LocSet.singleton l)
    let qt' : QTyp := ⟨refTyp, false, qt.pred⟩  -- clean, preserve predicate from stored entry
    return { qualType := qt', memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag, regime' := ctx.regime, declared' := ctx.declaredExternRefs }
  | none => throw s!"Location {l} not found in memory environment"

/-- Rule: unit (Ott rule: unit)
-- pc ; G ; S ; L |- unit : unit :> clean { no_pred } -| G ; L
-/
def typecheckUnit : TypecheckM TypeResult := do
  let qt : QTyp := ⟨ETyp.unit, false, Predicate.noPred⟩  -- clean, no predicate
  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag, regime' := ctx.regime, declared' := ctx.declaredExternRefs }

/--  Rule: string (Ott rule: string)
-- pc ; G ; S ; L |- string : string :> clean { no_pred } -| G ; L
-/
def typecheckString (_s : String) : TypecheckM TypeResult := do
  let qt : QTyp := ⟨ETyp.string, false, Predicate.noPred⟩  -- clean, no predicate
  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag, regime' := ctx.regime, declared' := ctx.declaredExternRefs }

end TypecheckPrimitives

/-- Rule: fn_abs (Ott rule: fn_abs)
  not_extern_fn e
----------------------------------------------------------------------  :: fn_abs
  pc ; G ; S ; L |- fn x : ST1 => e : ST2 : ST1 -> ST2 # pc tclosures ( x , e , S ) :> pc { no_pred } -| G ; L
-/
def typecheckFn (ctx : TypeContext) (x : Name) (st1 : Typ) (body : Expr) (st2 : Typ) : TypecheckM TypeResult := do
  -- A regular `fn` may not wrap a bare `extern fn` declaration as its body.  Such
  -- a closure would be applied by *extern dispatch* at runtime (`beval` matches on
  -- the closure body shape and runs the registered impl, returning the extern's
  -- result), which contradicts the arrow type this rule assigns it.  Reject it at
  -- declaration time so well-typed regular closures never carry an extern body.
  -- This mirrors the pure side, whose bodies are restricted to `PExpr` (via
  -- `toPExpr?`), which already excludes extern declarations.
  if body.isExternFnAstB then
    throw "fn body may not be a bare 'extern fn' declaration"
  -- Simply record the body and return type without typechecking the body
  -- (body typechecking is deferred until application time).
  -- Create arrow type ST1 -> ST2 with singleton closure list
  let arrowTyp : ETyp := ETyp.arrow st1 st2 ctx.pc [FnTClosure.regular x body (VarTypeEnv.toCaptured ctx.varEnv)]
  -- Create qualified type ST1 -> ST2 # pc { no_pred }
  let qt : QTyp := ⟨arrowTyp, ctx.pc, Predicate.noPred⟩
  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag, regime' := ctx.regime, declared' := ctx.declaredExternRefs }

/-- A successful `typecheckFn` guarantees the recorded body is not a bare
    `extern fn` AST node — the bridge fact threaded to the value-typing closure
    constructors so that regular closures are provably non-extern. -/
theorem typecheckFn_ok_not_externFnAst {ctx : TypeContext} {x : Name} {st1 : Typ}
    {body : Expr} {st2 : Typ} {res : TypeResult}
    (h : typecheckFn ctx x st1 body st2 = .ok res) : ¬ Expr.IsExternFnAst body := by
  have hb : body.isExternFnAstB = false := by
    cases hb' : body.isExternFnAstB with
    | true =>
        simp [typecheckFn, hb', Except.map, Functor.map, throw, throwThe,
          MonadExceptOf.throw] at h
    | false => rfl
  exact Expr.not_isExternFnAst_of_isExternFnAstB_eq_false hb

/-- The exact result of a successful `typecheckFn` (post-guard): the arrow type
    with the single regular closure member, all context fields threaded.  Lets
    callers recover the result shape without re-deriving past the body guard. -/
theorem typecheckFn_ok_eq {ctx : TypeContext} {x : Name} {st1 : Typ} {body : Expr}
    {st2 : Typ} {res : TypeResult} (htc : typecheckFn ctx x st1 body st2 = .ok res) :
    res =
      { qualType := ⟨ETyp.arrow st1 st2 ctx.pc
            [FnTClosure.regular x body (VarTypeEnv.toCaptured ctx.varEnv)],
          ctx.pc, Predicate.noPred⟩,
        memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc,
        nextTag' := ctx.nextTag, regime' := ctx.regime,
        declared' := ctx.declaredExternRefs } := by
  have hb : body.isExternFnAstB = false := by
    cases hb' : body.isExternFnAstB with
    | true =>
        simp [typecheckFn, hb', Except.map, Functor.map, throw, throwThe,
          MonadExceptOf.throw] at htc
    | false => rfl
  simp only [typecheckFn, hb, Bool.false_eq_true, ite_false, bind, Except.bind,
    pure, Except.pure] at htc
  exact (Except.ok.inj htc).symm

/-- Rule: pfn_abs (Ott rule: pfn_abs)
----------------------------------------------------------------------  :: pfn_abs
  pc ; G ; S ; L |- pfn x : ST1 => pe : ST2 : ST1 -> ST2 # pc tpclosures ( x , pe , S ) :> pc { no_pred } -| G ; L
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

  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag, regime' := ctx.regime, declared' := ctx.declaredExternRefs }

-- Helper functions for extern type conversion

-- The proofs in `LeanProofs/TypeSafety.lean` restate this loop's `MProd` state
-- layout (`CollectExternSeenState`), which the legacy `do` elaborator produces.
set_option backward.do.legacy true in
/-- Collect distinct TagIndex values from a list of SyntaxPredicates, allocate
    a fresh concrete Tag for each, and return the mapping plus the advanced nextTag.
    If the same TagIndex appears in multiple guardClosure entries, their Name and
    Expr must agree (else type error). guardOnly indices must reference a
    guardClosure index in the same batch.
-/
def collectAndAllocExternTags (preds : List SyntaxPredicate) (nextTag : Tag)
    : TypecheckM (ExtTreeMap TagIndex Tag × Tag) := do
  let mut seen : List (TagIndex × Name × Expr) := []
  let mut guardOnlyIndices : List TagIndex := []
  for pred in preds do
    match pred with
    | SyntaxPredicate.guardClosure idx name body =>
        match seen.find? (fun (i, _, _) => i == idx) with
        | some (_, name', body') =>
            if name != name' || !beqExpr body body' then
              throw s!"Conflicting guardClosure definitions for tag index {repr idx.val}"
        | none => seen := seen ++ [(idx, name, body)]
    | SyntaxPredicate.guardOnly idx =>
        guardOnlyIndices := guardOnlyIndices ++ [idx]
    | SyntaxPredicate.noPred => pure ()
  for idx in guardOnlyIndices do
    if !seen.any (fun (i, _, _) => i == idx) then
      throw s!"guardOnly tag index {repr idx.val} has no matching guardClosure in this extern spec"
  let mut mapping : ExtTreeMap TagIndex Tag := {}
  let mut tag := nextTag
  for (idx, _, _) in seen do
    mapping := mapping.insert idx tag
    tag := tag + 1
  return (mapping, tag)

/-- Resolve a SyntaxPredicate to a concrete Predicate using a tag mapping and
    the current variable typing environment.
-/
def resolveSyntaxPred (pred : SyntaxPredicate) (varEnv : VarTypeEnv)
    (mapping : ExtTreeMap TagIndex Tag) : TypecheckM Predicate := do
  match pred with
  | SyntaxPredicate.guardClosure idx arg body =>
      match mapping.get? idx with
      | some tag =>
          pure (Predicate.guardClosure tag arg (← body.toPExpr) (VarTypeEnv.toCaptured varEnv))
      | none => throw s!"Internal error: tag index {repr idx.val} not found in mapping"
  | SyntaxPredicate.guardOnly idx =>
      match mapping.get? idx with
      | some tag => pure (Predicate.guardOnly tag)
      | none => throw s!"guardOnly tag index {repr idx.val} has no matching guardClosure"
  | SyntaxPredicate.noPred => pure Predicate.noPred

/-- Collect the SyntaxPredicates that need fresh tags for a given extern
    application. For simple returns, this is the return pred plus all effect
    preds. For nested returns, only the outer effect preds (inner spec is
    deferred).
-/
def collectExternPreds (retSpec : ExternReturn) (effects : List Effect) : List SyntaxPredicate :=
  let effectPreds := effects.map (·.pred)
  match retSpec with
  | ExternReturn.simple _ _ pred => [pred] ++ effectPreds
  | ExternReturn.nestedFn _ _ _ _ _ _ _ _ => effectPreds
  | ExternReturn.nestedPfn _ _ _ _ _ _ _ => effectPreds

/-- Convert (Typ, Bool, Predicate) to QTyp for EXTERN VALUES.
    Used only for extern val declarations at definition time.
    Only base types are accepted: reference types are rejected (reference-valued
    externs use the `extern ref` form), as are arrow types, so no location is
    allocated and the context is returned as given.
    The predicate must already be resolved (concrete Tag, not TagIndex).
-/
def surfaceSpecToQTyp (typ : Typ) (poison : Bool) (pred : Predicate)
    (ctx : TypeContext) : TypecheckM (QTyp × TypeContext) := do
  -- Convert Typ to ETyp (base types only)
  let (etyp, ctx') ← (match typ with
    | Typ.int => pure (ETyp.int, ctx)
    | Typ.bool => pure (ETyp.bool, ctx)
    | Typ.unit => pure (ETyp.unit, ctx)
    | Typ.string => pure (ETyp.string, ctx)
    | Typ.ref _ =>
        -- Reference-valued externs must use the explicit `extern ref` form,
        -- which separates the reference qualifier from the pointed-to cell
        -- contract (see doc/externs.md, `@21`).
        throw "Type error: 'extern val' cannot have a ref type; use 'extern ref @id : (ref int :> ...), points_to: (int :> ...)' instead"
    | Typ.arrow _ _ => throw "Arrow types not expected in extern specs" : TypecheckM (ETyp × TypeContext))

  return (⟨etyp, poison, pred⟩, ctx')

/-- Convert (Bool, Predicate) to QTyp for EFFECT SPECIFICATIONS.
    Used when processing effects during extern function application.
    IMPORTANT: Memory currently stores only integers, so typ is always int.
    Effects specify the type stored AT a memory location (the contents type).
    No location allocation, no ctx updates.
    The predicate must already be resolved.
-/
def effectSpecToQTyp (poison : Bool) (pred : Predicate) : QTyp :=
  ⟨ETyp.int, poison, pred⟩

/-- Convert (Typ, Bool, Predicate) to QTyp for RETURN SPECIFICATIONS.
    Used when processing return specs during extern function application.
    MUST NOT allocate locations for reference types - extern functions cannot return references.
    The predicate must already be resolved.

    RESTRICTION: Extern functions are forbidden from returning reference types.
    This function will reject any attempt to create a return spec with type `ref T`.
    See issue #72: Extern Functions Returning Reference Types - Location Tracking Problem
-/
def returnSpecToQTyp (typ : Typ) (poison : Bool) (pred : Predicate)
    (nextLoc : Loc) : TypecheckM (QTyp × Loc) := do
  -- Convert Typ to ETyp, rejecting reference types
  let (etyp, nextLoc') ← (match typ with
    | Typ.int => pure (ETyp.int, nextLoc)
    | Typ.bool => pure (ETyp.bool, nextLoc)
    | Typ.unit => pure (ETyp.unit, nextLoc)
    | Typ.string => pure (ETyp.string, nextLoc)
    | Typ.ref _ => throw "Extern functions cannot return reference types"
    | Typ.arrow _ _ => throw "Arrow types not expected in extern specs" : TypecheckM (ETyp × Loc))

  return (⟨etyp, poison, pred⟩, nextLoc')

-- Type checking functions for extern expressions

/-- Typecheck extern value: let x = extern val @id : (T :> p { SP })
    Allocates fresh tags for TagIndex values in the SyntaxPredicate, resolves
    to a concrete Predicate, then converts the surface type.
-/
def typecheckExternVal (ctx : TypeContext) (typ : Typ) (poison : Bool) (pred : SyntaxPredicate)
    : TypecheckM TypeResult := do
    match (poison,pred) with
    | (false, SyntaxPredicate.guardOnly _)
    | (false, SyntaxPredicate.guardClosure _ _ _) =>
        throw "Clean types cannot have predicates"
    | _ => do
      let (tagMapping, nextTag') ← collectAndAllocExternTags [pred] ctx.nextTag
      let resolvedPred ← resolveSyntaxPred pred ctx.varEnv tagMapping
      let (qt, ctx') ← surfaceSpecToQTyp typ poison resolvedPred ctx
      return { qualType := qt, memEnv' := ctx'.memEnv, tagEnv' := ctx.tagEnv,
               nextLoc' := ctx'.nextLoc, nextTag' := nextTag', regime' := ctx.regime,
               declared' := ctx.declaredExternRefs }

/-- Typecheck a reference-valued extern declaration:
    `extern ref @id : (ref int :> clean {}), points_to: (int :> poisoned {})`

    Allocates one fresh logical location for the external cell, seeds it from
    the `points_to:` qualifier, and returns a `ref` type at that location.

    Restrictions (see `doc/externs.md`, `@21`):
    * the reference value must be declared `clean {}`;
    * the pointed-to cell must be declared `poisoned {}` — a clean (or
      predicated) initial cell would assert paired-run agreement that no
      mid-evaluation declaration can supply (a documented language
      limitation);
    * `extern ref` may not appear under fn/pfn bodies (evaluate-at-most-once
      positions only);
    * each extern id may be declared at most once per program.
-/
def typecheckExternRef (ctx : TypeContext) (id : ExternId)
    (refPoison : Bool) (refPred : SyntaxPredicate)
    (cellPoison : Bool) (cellPred : SyntaxPredicate) : TypecheckM TypeResult := do
  if ctx.pureCtx || !ctx.externRefAllowed then
    throw s!"extern ref @{id}: reference-valued extern declarations may not appear under fn/pfn bodies"
  if ctx.declaredExternRefs.contains id then
    throw s!"extern ref @{id}: duplicate declaration; each extern id may be declared at most once per program"
  match refPoison, refPred with
  | false, SyntaxPredicate.noPred => pure ()
  | _, _ =>
      throw s!"extern ref @{id}: the reference value must be declared '(ref int :> clean \{})'"
  match cellPoison, cellPred with
  | true, SyntaxPredicate.noPred => pure ()
  | false, _ =>
      throw s!"extern ref @{id}: clean 'points_to:' cells are not supported — a trusted initialized external cell would assert cross-run agreement that cannot be established at the declaration; declare the cell '(int :> poisoned \{})' and re-establish cleanness through a write effect"
  | _, _ =>
      throw s!"extern ref @{id}: the 'points_to:' cell must be declared '(int :> poisoned \{})'"
  let l := ctx.nextLoc
  let memEnv' := updateMemEnv ctx.memEnv l ⟨ETyp.int, true, Predicate.noPred⟩
  return { qualType := ⟨ETyp.ref (LocSet.singleton l), false, Predicate.noPred⟩,
           memEnv' := memEnv', tagEnv' := ctx.tagEnv,
           nextLoc' := l + 1, nextTag' := ctx.nextTag, regime' := ctx.regime,
           declared' := id :: ctx.declaredExternRefs }

-- ----------------------------------------------------------------------------
-- Extern argument conditions
--
-- An extern callable's declared argument is a qualified type (precondition).
-- The surface triple `(Typ, Bool, SyntaxPredicate)` is resolved here into a
-- concrete `QTyp` stored on the extern typing closure, and the call site checks
-- that the actual argument satisfies it via `argConditionSatisfied`.
-- ----------------------------------------------------------------------------

/-- Convert a first-order extern argument `Typ` to an `ETyp` signature.  A `ref`
    maps to `ETyp.ref LocSet.empty` (a signature placeholder; the argument-condition
    base check compares via `QTyp.toTyp`, which ignores the locset).  Function-typed
    arguments are rejected (mirrors `checkExternInputFirstOrder`). -/
def argTypToETyp (argTyp : Typ) : TypecheckM ETyp :=
  match argTyp with
  | Typ.int => pure ETyp.int
  | Typ.bool => pure ETyp.bool
  | Typ.unit => pure ETyp.unit
  | Typ.string => pure ETyp.string
  | Typ.ref t =>
      if t != Typ.int then
        throw s!"extern callable input must be first-order; ref {repr t} is not executable (only ref int is supported)"
      else
        pure (ETyp.ref LocSet.empty)
  | Typ.arrow _ _ => throw "extern callable input must be first-order; function-typed arguments are forbidden"

/-- Core of `resolveArgCondQTyp`: build the concrete `QTyp` precondition from the
    surface triple WITHOUT allocating fresh tags.  The declared argument predicate's
    tag is never inserted into the regime or tag environment — it is only compared
    *modulo tag* by `predShapeMatches` — so we reuse the source `TagIndex` directly. -/
def resolveArgCondQTyp' (argTyp : Typ) (argPoison : Bool) (argPred : SyntaxPredicate)
    (varEnv : VarTypeEnv) : TypecheckM QTyp := do
  let resolvedPred ← (match argPred with
    | SyntaxPredicate.guardClosure idx arg body => do
        let pe ← body.toPExpr
        pure (Predicate.guardClosure idx.val arg pe (VarTypeEnv.toCaptured varEnv))
    | SyntaxPredicate.guardOnly idx => pure (Predicate.guardOnly idx.val)
    | SyntaxPredicate.noPred => pure Predicate.noPred)
  let etyp ← argTypToETyp argTyp
  return ⟨etyp, argPoison, resolvedPred⟩

/-- Resolve a declared extern argument condition into a concrete `QTyp` precondition,
    leaving `nextTag` UNCHANGED (the resolution allocates no tags).  Keeping the
    tag-passthrough in a thin wrapper makes `nextTag`-preservation syntactically
    obvious to the downstream inversion lemmas.  Stored on the extern typing closure
    and consulted at the call site by `argConditionSatisfied`. -/
def resolveArgCondQTyp (argTyp : Typ) (argPoison : Bool) (argPred : SyntaxPredicate)
    (varEnv : VarTypeEnv) (nextTag : Tag) : TypecheckM (QTyp × Tag) := do
  let qt ← resolveArgCondQTyp' argTyp argPoison argPred varEnv
  return (qt, nextTag)

/-- A qualified type is *clean under regime `R`* when it is literally clean, or
    its guard tag is active in `R` (the depoisoning regime).  Mirrors the
    `R.lookup? k = some true` test used by `typecheckIf`. -/
def qtypCleanUnderRegime (qt : QTyp) (R : Regime) : Bool :=
  qt.poison == false ||
    (match qt.pred with
     | Predicate.guardClosure k _ _ _ => R.lookup? k == some true
     | Predicate.guardOnly k => R.lookup? k == some true
     | Predicate.noPred => false)

/-- Conservative predicate-SHAPE match for argument conditions: the actual
    predicate must carry the same guard shape as the declared one, modulo tag,
    captured environment, and binder name (no logical implication). -/
def predShapeMatches (declared actual : Predicate) (fuel : Nat) : Bool :=
  match declared with
  | Predicate.noPred => true
  | Predicate.guardOnly _ =>
      -- A bare declared guard requires the actual to carry the SAME (bare) guard
      -- shape — not an arbitrary guard-closure (that would be implication, not
      -- shape matching).
      match actual with
      | Predicate.guardOnly _ => true
      | _ => false
  | Predicate.guardClosure _ dArg dBody dEnv =>
      match actual with
      | Predicate.guardClosure _ aArg aBody aEnv =>
          PExpr.equalWithEnvs dBody dEnv aBody aEnv (some (dArg, PExpr.var aArg)) fuel
      | _ => false

/-- Conservative argument-condition satisfaction:
    (1) base/runtime types match; (2) a declared-clean condition requires the
    actual argument to be clean under the current regime `R`; (3) a declared
    no-predicate condition imposes no predicate match; (4) a declared predicate
    requires the actual to carry the same predicate shape.  No logical implication. -/
def argConditionSatisfied (declared actual : QTyp) (R : Regime) (fuel : Nat) : Bool :=
  QTyp.toTyp declared == QTyp.toTyp actual &&
    (declared.poison == true || qtypCleanUnderRegime actual R) &&
    predShapeMatches declared.pred actual.pred fuel

/-- Conservative predicate-shape match for a `captures:` dependency: the declared
    side is a surface `SyntaxPredicate`, so only its shape is compared against the
    resolved actual `Predicate` (no logical implication, no guarded
    reconciliation). -/
def captureSyntaxPredShapeMatches (declared : SyntaxPredicate) (actual : Predicate) : Bool :=
  match declared with
  | SyntaxPredicate.noPred => true
  | SyntaxPredicate.guardOnly _ =>
      match actual with | Predicate.guardOnly _ => true | _ => false
  | SyntaxPredicate.guardClosure _ _ _ =>
      match actual with | Predicate.guardClosure _ _ _ _ => true | _ => false

/-- Satisfaction of one declared `captures:` read dependency.  Mirrors
    `argConditionSatisfied` (`Qactual <:R Qdecl`): the resolved dependency's
    current qualified type must match the declared base type, be clean under the
    regime when the declared requirement is clean, and carry a matching predicate
    shape. -/
def captureCondSatisfied (c : Capture) (actual : QTyp) (R : Regime) : Bool :=
  c.typ == QTyp.toTyp actual &&
    (c.poison == true || qtypCleanUnderRegime actual R) &&
    captureSyntaxPredShapeMatches c.pred actual.pred

/-- Resolve and check one `captures:` dependency in the callable environment
    (captured env extended with the explicit argument) and memory typing.  Bare
    targets name environment entries; bang targets name memory entries reached
    through a reference variable. -/
def captureSatisfied (c : Capture) (unifiedEnv : VarTypeEnv) (memEnv : MemoryTypeEnv)
    (R : Regime) : Bool :=
  match c.target with
  | CaptureTarget.bareVar v =>
      match unifiedEnv.lookup v with
      | some qt => captureCondSatisfied c qt R
      | none => false
  | CaptureTarget.memVar v =>
      match unifiedEnv.lookup v with
      | some qt =>
          match qt.etyp with
          | ETyp.ref ls =>
              LocSet.fold ls true (fun acc l =>
                acc && (match memEnv.lookup l with
                        | some cellQt => captureCondSatisfied c cellQt R
                        | none => false))
          | _ => false
      | none => false

/-- All declared `captures:` read dependencies are satisfied.  Empty list is a
    no-op (`True`), so externs without a `captures:` clause are unaffected. -/
def capturesSatisfied (caps : List Capture) (unifiedEnv : VarTypeEnv)
    (memEnv : MemoryTypeEnv) (R : Regime) : Bool :=
  caps.all (fun c => captureSatisfied c unifiedEnv memEnv R)

def parseReturnType (retType : ExternReturn):Typ :=
 match retType with
 | ExternReturn.simple typ _ _ => typ
 | ExternReturn.nestedFn _ _ typ _ _ extReturn _ _ => Typ.arrow typ (parseReturnType extReturn)
 | ExternReturn.nestedPfn _ _ typ _ _ extReturn _ => Typ.arrow typ (parseReturnType extReturn)

/-- Require that an executable extern's input type is first-order: one of
    `{int, bool, unit, string, ref int}`.  Function-typed inputs are rejected.
    Arrow and non-int ref types are forbidden at declaration sites. -/
def checkExternInputFirstOrder (argTyp : Typ) : TypecheckM Unit :=
  match argTyp with
  | Typ.int | Typ.bool | Typ.unit | Typ.string => return ()
  | Typ.ref Typ.int => return ()
  | Typ.ref t => throw s!"extern callable input must be first-order; ref {repr t} is not executable (only ref int is supported)"
  | Typ.arrow _ _ => throw "extern callable input must be first-order; function-typed arguments are forbidden"

/-- Recursively enforce `checkExternInputFirstOrder` on every nested-return
    argument type in an `ExternReturn` chain. -/
def checkExternReturnInputsFirstOrder : ExternReturn → TypecheckM Unit
  | ExternReturn.simple _ _ _ => return ()
  | ExternReturn.nestedFn _ _ argTyp _ _ inner _ _ => do
      checkExternInputFirstOrder argTyp
      checkExternReturnInputsFirstOrder inner
  | ExternReturn.nestedPfn _ _ argTyp _ _ inner _ => do
      checkExternInputFirstOrder argTyp
      checkExternReturnInputsFirstOrder inner

/-- Typecheck extern impure function.  Per-declaration, rejects function-
    typed and non-`ref int` reference inputs — both at the top-level argument
    and inside every nested return descriptor. -/
def typecheckExternFn (ctx : TypeContext) (id : ExternId) (arg : Name) (argTyp : Typ)
    (argPoison : Bool) (argPred : SyntaxPredicate)
    (retSpec : ExternReturn) (effects : List Effect) (captures : List Capture) : TypecheckM TypeResult := do
  checkExternInputFirstOrder argTyp
  checkExternReturnInputsFirstOrder retSpec
  -- Resolve the declared argument condition (precondition) into a concrete QTyp.
  let (argQt, nextTag') ← resolveArgCondQTyp argTyp argPoison argPred ctx.varEnv ctx.nextTag
  -- Create extern closure with captured varEnv (singleton list), the precondition,
  -- and the declared `captures:` read dependencies (the trusted contract, checked
  -- at the call boundary via `capturesSatisfied`).
  let tcl := FnTClosure.extern id arg retSpec effects (VarTypeEnv.toCaptured ctx.varEnv) argQt captures


  let retTyp := parseReturnType retSpec
  let arrowTyp := ETyp.arrow argTyp retTyp ctx.pc [tcl]

  -- Return qualified type with poison = pc
  let qt : QTyp := ⟨arrowTyp, ctx.pc, Predicate.noPred⟩
  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv,
           nextLoc' := ctx.nextLoc, nextTag' := nextTag', regime' := ctx.regime,
           declared' := ctx.declaredExternRefs }

/-- Typecheck extern pure function. Same first-order-input rule as
    `typecheckExternFn`. -/
def typecheckExternPfn (ctx : TypeContext) (id : ExternId) (arg : Name) (argTyp : Typ)
    (argPoison : Bool) (argPred : SyntaxPredicate)
    (retSpec : ExternReturn) (captures : List Capture) : TypecheckM TypeResult := do
  checkExternInputFirstOrder argTyp
  checkExternReturnInputsFirstOrder retSpec
  -- Resolve the declared argument condition (precondition) into a concrete QTyp.
  let (argQt, nextTag') ← resolveArgCondQTyp argTyp argPoison argPred ctx.varEnv ctx.nextTag
  -- Create extern closure with captured varEnv (singleton list), the precondition,
  -- and the declared `captures:` read dependencies (the trusted contract, checked
  -- at the call boundary via `capturesSatisfied`).
  let tcl := PFnTClosure.extern id arg retSpec (VarTypeEnv.toCaptured ctx.varEnv) argQt captures

  let retTyp := parseReturnType retSpec
  -- Create arrow type with ambient pc
  let arrowTyp := ETyp.parrow argTyp retTyp ctx.pc [tcl]

  -- Return qualified type with poison = pc
  let qt : QTyp := ⟨arrowTyp, ctx.pc, Predicate.noPred⟩
  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv,
           nextLoc' := ctx.nextLoc, nextTag' := nextTag', regime' := ctx.regime,
           declared' := ctx.declaredExternRefs }


private def generateFreshVar (ctx : TypeContext) (pref : Name) (suffix : Nat) (fuel : Nat) : Name :=
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

  -- Check that all results have signature-compatible types using foldlM
  let _ ← List.foldlM (fun () result => do
    let ⟨resEtyp, _resP, _resPred⟩ := result.qualType
    if not (beqETypSignature firstEtyp resEtyp) then
      throw s!"Closure alternatives produced incompatible result types: {repr firstEtyp} vs {repr resEtyp}"
    else
      pure ()) () restResults

  -- Join all results using foldlM.
  -- For closure-alternative joins (app/papp), use the *strong* memory join:
  -- single-sided memory entries keep type/poison but drop predicates. This
  -- ensures the post-join context retains only predicate facts stable across
  -- hidden closure alternatives.
    let joinAccumulator := (firstEtyp, firstResult.memEnv', firstResult.qualType.poison,
                            firstResult.qualType.pred, firstResult.tagEnv', firstResult.regime',
                            firstResult.nextLoc', firstResult.nextTag')

    let joined ← List.foldlM (fun acc result => do
      let ⟨resEtyp, resPoison, resPred⟩ := result.qualType
      let (joinedEtyp, joinedMemEnv, joinedPoison, joinedPred, joinedTagEnv, joinedRegime, maxNextLoc, maxNextTag) := acc
      pure (joinETyps joinedEtyp resEtyp joinedPoison resPoison,
            joinMemEnvsStrong joinedMemEnv result.memEnv',
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
             nextLoc' := maxNextLoc, nextTag' := maxNextTag, regime' := joinedRegime,
             declared' := firstResult.declared' }

def applyClosuresThreaded {α : Type}
    (applyOne : α → Tag × Loc → TypecheckM TypeResult)
    (items : List α) (cursor : Tag × Loc) : TypecheckM (List TypeResult) :=
  match items with
  | [] => pure []
  | item :: rest => do
      let r ← applyOne item cursor
      let rs ← applyClosuresThreaded applyOne rest (r.nextTag', r.nextLoc')
      pure (r :: rs)
termination_by items.length

/-- Value-correct materialisation of an extern call's return guard into the tag
    environment.  When a simple-return
    predicate is a guard closure whose fresh tag the post-call regime interprets
    (driver-asserted via the initial `--regime` map, or inserted by the
    `--extern-regime` policy through `applyExternRegimePolicy`), the tag is
    inserted with the regime's value and the predicate's extracted dependencies.

    A regime-undetermined guard is NOT materialised: the tag-environment value
    drives the deref-time depoison, so an eager dummy value would poison cells
    that a driver-asserted regime keeps clean.  A predicate whose dependency
    extraction fails is also left unmaterialised — such a predicate already
    fails at any later `if` materialisation (`matchGuard` extracts the same
    dependencies and throws).

    Materialising the dependencies is what lets a later write effect invalidate
    a stale guard: an errno-reading return guard gains `deps ∋ errno`, so a
    subsequent `set_err`-style effect drops it from the tag environment and the
    regime (`invalidateTagDeps` / `invalidateRegimeDepsEffect`) instead of
    letting the stale regime fact de-poison values through it. -/
def installReturnGuard (env : TagEnv) (resolvedPred : Predicate) (R : Regime)
    (fuel : Nat) : TagEnv :=
  match resolvedPred with
  | Predicate.guardClosure k _ _ _ =>
      match R.lookup? k with
      | some b =>
          match extractDepsFromPred resolvedPred fuel with
          | .ok deps => env.insert k ⟨b, deps⟩
          | .error _ => env
      | none => env
  | _ => env

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
    | Expr.vlet x e1 e2 => typecheckVlet ctx x e1 e2 fuel
    | Expr.fn x paramType body returnType => typecheckFn ctx x paramType body returnType
    | Expr.pfn x paramType body returnType => typecheckPfn ctx x paramType body returnType
    | Expr.app e1 e2 => typecheckApp ctx e1 e2 fuel
    | Expr.ite e1 e2 e3 => typecheckIf ctx e1 e2 e3 fuel
    | Expr.unaryop op e => typecheckUnaryOp ctx op e fuel
    | Expr.externVal _ typ poison pred => typecheckExternVal ctx typ poison pred
    | Expr.externRef id refPoison refPred cellPoison cellPred =>
        typecheckExternRef ctx id refPoison refPred cellPoison cellPred
    | Expr.externFn id arg argTyp argPoison argPred retSpec effects captures =>
        typecheckExternFn ctx id arg argTyp argPoison argPred retSpec effects captures
    | Expr.externPfn id arg argTyp argPoison argPred retSpec captures =>
        typecheckExternPfn ctx id arg argTyp argPoison argPred retSpec captures
termination_by fuel

/-- Rules: op_* (Ott rules: op_plus, op_minus, op_mult, op_div, op_bitwise_and,
--   op_gteq, op_lteq, op_gt, op_lt, op_eq, op_neq, op_and, op_or)
-- pc ; G ; S ; L |- e1 : T1 :> p' { P1 } -| G' ; L'
-- pc ; G' ; S ; L' |- e2 : T2 :> p'' { P2 } -| G'' ; L''
-- T1, T2 and the result type T are fixed by op (see `opEType?`):
--   +,-,*,/,& : int, int -> int;  >=,<=,>,<,==,!= : int, int -> bool;  &&,|| : bool, bool -> bool
-- --------------------------------
-- pc ; G ; S ; L |- e1 op e2 : T :> join pc join p' p'' { no_pred } -| G'' ; L''
-/
def typecheckOp (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (op : Op) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    let result1 ← typecheckExpr ctx e1 fuel
    let ⟨etyp1, p1, _  ⟩ := result1.qualType

    -- Propagate fresh-name supplies and regime from first operand into second operand context
    let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime', declaredExternRefs := result1.declared' }
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
-- pc ; G ; S ; L |- e : int :> p { P } -| G' ; L'
-- fresh l
-- -----------------------
-- pc ; G ; S ; L |- ref e : ref @ l :> pc { no_pred } -| G'[l |-> join pc p { AppPred pc P }] ; L'
-- NOTE: Memory can only store integers; G stores poison and predicate only (mem entry p { P })
-/
def typecheckNewRef (ctx : TypeContext) (e : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    let result ← typecheckExpr ctx e fuel
    let ⟨etyp, poison, pred ⟩ := result.qualType

    -- Require that the allocated value has type int (heap stores only integers)
    if etyp != ETyp.int then
      throw s!"Type error: ref can only allocate integers, but got {repr etyp}"

    -- Generate fresh location (simplified)
    let (l, result') := freshTLocRes result
    let storedPoison := joinPoison ctx.pc poison
    let storedPred := if ctx.pc then Predicate.noPred else pred
    let storedQt : QTyp := ⟨ETyp.int, storedPoison, storedPred⟩
    let memEnv' := updateMemEnv result'.memEnv' l storedQt

    let qt : QTyp := ⟨ETyp.ref (LocSet.singleton l), ctx.pc, Predicate.noPred⟩
    return { qualType := qt, memEnv' := memEnv', tagEnv' := result'.tagEnv', nextLoc' := result'.nextLoc', nextTag' := result'.nextTag', regime' := result'.regime', declared' := result'.declared' }
termination_by fuel

/-- Rule: assign (Ott rules: assign_singleton, assign_locset, assign_singleton_poisoned_ref, assign_locset_poisoned_ref) -/
def typecheckAssign (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    let result1 ← typecheckExpr ctx e1 fuel
    let ⟨etyp1, p1, _  ⟩ := result1.qualType
    match etyp1 with
    | ETyp.ref ls =>
      let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime', declaredExternRefs := result1.declared' }
      let result2 ← typecheckExpr ctx' e2 fuel
      let ⟨etyp2, p2, pred2  ⟩ := result2.qualType

      -- Require that the RHS has type int
      if etyp2 != ETyp.int then
        throw s!"Type error: can only assign int values, but got {repr etyp2}"

      let storedPoison := joinPoison ctx.pc (joinPoison p1 p2)
      -- Poisoned references and control-poisoned writes erase predicates in memory.
      let storedPred := if p1 || ctx.pc then Predicate.noPred else pred2
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
      -- Invalidate dependencies on write (Ott rules: assign_*, premise invalidate_deps)
      let tagEnv' := invalidateTagDeps result2.tagEnv' ls
      let regime' := invalidateRegimeDeps result2.regime' result2.tagEnv' ls
      -- Bump nextLoc' past all locations in ls to ensure wfTypeResult holds
      -- (locations may not be in memEnv due to conservative if typing)
      let nextLoc' := LocSet.fold ls result2.nextLoc' (fun acc l => max acc (l + 1))
      return { qualType := qt, memEnv' := memEnv', tagEnv' := tagEnv', nextLoc' := nextLoc', nextTag' := result2.nextTag', regime' := regime', declared' := result2.declared' }
    | _ => throw "Left operand of assignment must be a reference"
termination_by fuel

/-- Rules: deref_* (Ott rules: deref_poisoned, deref_no_pred, deref_guard_true, deref_guard_false, deref_guard_unknown)
-- NOTE: Memory can only store integers (matching runtime semantics)
--/
def typecheckDeref (ctx : TypeContext) (e : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    let result ← typecheckExpr ctx e fuel
    let ⟨etyp, poisonRef, _predRef ⟩ := result.qualType
    match etyp with
    | ETyp.ref ls =>
      if ls.isEmpty then
        throw "Reference locset is empty"
      -- Fetch all referenced memory cells and ensure their types are compatible
      let (joinedCellPoison, mergedPred?) ←
        LocSet.foldM ls (init := (false, (none : Option Predicate))) (fun (accPoison, accPred?) l => do
          match result.memEnv'.lookup l with
          | some qt =>
              let nextPoison := joinPoison accPoison qt.poison
              let nextPred? :=
                match accPred? with
                | none => some qt.pred
                | some p => some (joinPredicates p qt.pred)
              pure (nextPoison, nextPred?)
          | none => throw s!"Location {l} not found in memory environment")

      let mergedPred := mergedPred?.getD Predicate.noPred

      if poisonRef then
        -- Reference itself poisoned: ignore predicates, return poisoned
        let qt : QTyp := ⟨ETyp.int, true, Predicate.noPred⟩
        return { qualType := qt, memEnv' := result.memEnv', tagEnv' := result.tagEnv', nextLoc' := result.nextLoc', nextTag' := result.nextTag', regime' := result.regime', declared' := result.declared' }
      else
        match mergedPred with
        | Predicate.noPred =>
            let poison := joinPoison ctx.pc joinedCellPoison
            let qt : QTyp := ⟨ETyp.int, poison, Predicate.noPred⟩
            return { qualType := qt, memEnv' := result.memEnv', tagEnv' := result.tagEnv', nextLoc' := result.nextLoc', nextTag' := result.nextTag', regime' := result.regime', declared' := result.declared' }
        | Predicate.guardOnly k | Predicate.guardClosure k _ _ _ =>
            match result.tagEnv'.get? k with
            | some ⟨true, _deps⟩ =>
              let qt : QTyp := ⟨ETyp.int, ctx.pc, Predicate.noPred⟩
              return { qualType := qt, memEnv' := result.memEnv', tagEnv' := result.tagEnv', nextLoc' := result.nextLoc', nextTag' := result.nextTag', regime' := result.regime', declared' := result.declared' }
            | some ⟨false, _deps⟩ =>
              let qt : QTyp := ⟨ETyp.int, true, Predicate.noPred⟩
              return { qualType := qt, memEnv' := result.memEnv', tagEnv' := result.tagEnv', nextLoc' := result.nextLoc', nextTag' := result.nextTag', regime' := result.regime', declared' := result.declared' }
            | none =>
              let poison := joinPoison ctx.pc joinedCellPoison
              let qt : QTyp := ⟨ETyp.int, poison, mergedPred⟩
              return { qualType := qt, memEnv' := result.memEnv', tagEnv' := result.tagEnv', nextLoc' := result.nextLoc', nextTag' := result.nextTag', regime' := result.regime', declared' := result.declared' }
    | _ => throw "Operand of dereference must be a reference"
termination_by fuel

/-- Rule: seq (Ott rule: seq)
-- pc ; G ; S ; L |- e1 : T1 :> p' { P' } -| G' ; L'
-- pc ; G' ; S ; L' |- e2 : T2 :> p'' { P'' } -| G'' ; L''
-- --------------------------------
-- pc ; G ; S ; L |- e1 ; e2 : T2 :> p'' { P'' } -| G'' ; L''
-/
def typecheckSeq (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    let result1 ← typecheckExpr ctx e1 fuel
    let ctx' := updateCtxFromResult ctx result1
    let result2 ← typecheckExpr ctx' e2 fuel
    return result2
termination_by fuel


/-- Issue #113: when p1p (join of function outer poison p1 and internal arrow poison p) is true,
    the application result is irrecoverably poisoned with no predicate. -/
def normalizeAppResultByProvenance (p1p : Poison) (qt : QTyp) : QTyp :=
  if p1p then { qt with poison := true, pred := Predicate.noPred } else qt

/-- Resolve one extern effect and write the result to memory at the
    locations referenced by the effect target.  A standalone function
    (called from the effect loop of `applyFnTClosure` and
    `applyFnTClosureAtCursor`) to enable per-effect reasoning in the
    fault-robustness proof. -/
def applyExternEffect (effect : Effect) (unifiedEnv : VarTypeEnv)
    (tagMapping : TagMapping) (pc : Poison)
    (memEnv : MemoryTypeEnv) : TypecheckM MemoryTypeEnv := do
  match effect.target with
  | EffectTarget.namedVar v =>
      match unifiedEnv.lookup v with
      | some qt =>
          match qt.etyp with
          | ETyp.ref ls =>
              -- The effect is typed exactly as `typecheckAssign` types an
              -- assignment through this reference.  `p1` is
              -- the captured target reference's own poison; a poisoned target
              -- (`p1`) or a control-poisoned write (`pc`) poisons the written
              -- cells and erases their predicates, mirroring assignment.  A
              -- multi-location target is *weak*-updated (join), never strong-
              -- updated: the runtime writes one physical cell, so strong-updating
              -- every member of `ls` would unsoundly mark unwritten members clean.
              let p1 := qt.poison
              let resolvedPred ← resolveSyntaxPred effect.pred unifiedEnv tagMapping
              let effectQt := effectSpecToQTyp effect.poison resolvedPred
              let storedPoison := joinPoison pc (joinPoison p1 effectQt.poison)
              let storedPred := if p1 || pc then Predicate.noPred else effectQt.pred
              return match ExtTreeSet.toList ls with
                | [l] =>
                    -- Singleton: strong update (assign_singleton)
                    let storedQt : QTyp := ⟨ETyp.int, storedPoison, storedPred⟩
                    updateMemEnv memEnv l storedQt
                | _ =>
                    -- Non-singleton: weak update (assign_locset)
                    updateLocsetWeak memEnv ls storedPoison storedPred
          | _ => throw s!"Effect target {v} must be a reference type"
      | none => throw s!"Effect target {v} not found in environment"

/-- The union of the logical locations written by a list of extern effects, as
    resolved in the unified type environment.  These are exactly the locations
    `applyExternEffect` strong/weak-updates, so the typing context invalidates its
    guard-tag / regime dependencies on them after the effect loop — mirroring
    `typecheckAssign`'s `invalidateTagDeps` / `invalidateRegimeDeps` on the
    assigned locset. -/
def effectTargetLocs (effects : List Effect) (unifiedEnv : VarTypeEnv) : LocSet :=
  effects.foldl (fun acc effect =>
    match effect.target with
    | EffectTarget.namedVar v =>
        match unifiedEnv.lookup v with
        | some qt =>
            match qt.etyp with
            | ETyp.ref ls => LocSet.union acc ls
            | _ => acc
        | none => acc) (∅ : LocSet)

/-- Extern-regime insertion: for each freshly-allocated
    output guard tag `k` of a selected extern id, query the scenario policy
    `policy id k`; when it returns `some b`, insert `k ↦ b` into the active regime.  Tags
    with `none` are left out (conservative path).  All tags in `tagMapping` are fresh
    (allocated `≥ ctx.nextTag`), so this only ever ADDS tags above the incoming `nextTag`. -/
def applyExternRegimePolicy (R : Regime) (id : ExternId)
    (policy : ExternId → Tag → Option Bool) (tagMapping : TagMapping) : Regime :=
  tagMapping.toList.foldl
    (fun R (p : TagIndex × Tag) =>
      match policy id p.2 with
      | some b => match R.lookup? p.2 with
                  | none => R.insert p.2 b
                  | some _ => R
      | none => R) R

/-- Helper: Apply a single FnTClosure and return the result type and updated environments.
    This encapsulates the body typing logic for a single closure alternative.
-/
def applyFnTClosureAtCursor (tcl : FnTClosure) (_st1 st2 : Typ) (p : Poison) (p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (ctx : TypeContext) (result2 : TypeResult) (cursor : Tag × Loc)
    (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel in applyFnTClosure"
  | fuel + 1 => do
    match tcl with
    | FnTClosure.regular x body env =>
        -- Type the body with the closure's captured environment
        -- pc = join p join p1 pc (Ott rule: app_fn_singleton)
        let argQt : QTyp := ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        let envMap := VarTypeEnv.ofCaptured env
        let env' := VarTypeEnv.update envMap x argQt
        let ctx'' := { ctx with pc := joinPoison p (joinPoison p1 ctx.pc),
                                memEnv := result2.memEnv', varEnv := env', tagEnv := result2.tagEnv',
                                nextTag := cursor.1, nextLoc := cursor.2, regime := result2.regime',
                                externRefAllowed := false, declaredExternRefs := result2.declared' }
        let result3 ← typecheckExpr ctx'' body fuel
        let ⟨_etyp3, _p3, _pred3⟩ := result3.qualType

        -- Check surface-type erasure
        if not (isErasureOf st2 result3.qualType) then
          throw s!"Type mismatch in function application: return type {repr st2} is not compatible with body type {repr (QTyp.toTyp result3.qualType)}"

        -- Issue #111: taint app result by function poison (p, p1)
        -- Issue #113: provenance gate - if join p1 p, force irrecoverable poison and no_pred
        let taintedPoison := joinPoison p1 (joinPoison p result3.qualType.poison)
        let taintedQt := { result3.qualType with poison := taintedPoison }
        -- Bodies are typechecked with `externRefAllowed := false`, so they cannot
        -- declare extern refs; pin the result's declared set to the pre-body one so
        -- all closure alternatives joined by `joinTypeResults` agree on it syntactically.
        return { result3 with
                 qualType := normalizeAppResultByProvenance (joinPoison p1 p) taintedQt
                 declared' := result2.declared' }

    | FnTClosure.extern id x retSpec effects capturedEnv declaredArgQt captures =>
        let argQt := ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        let unifiedEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured capturedEnv) x argQt
        -- Single trusted-result gate: the actual argument must satisfy the declared
        -- precondition AND each declared `captures:` read dependency must satisfy its
        -- qualified type in the callable environment / current (pre-effect) memory.
        -- `capturesSatisfied` is checked at call entry (`result2.memEnv'`), before this
        -- extern's own effects mutate memory — mirroring the pure (`pfn`) path.
        if !(argConditionSatisfied declaredArgQt argQt result2.regime' fuel
              && capturesSatisfied captures unifiedEnv result2.memEnv' result2.regime') then
          throw s!"extern @{id}: argument precondition or a captures: read dependency not satisfied (arg runtime type {repr (QTyp.toTyp argQt)}, poison={argQt.poison}; declared poison={declaredArgQt.poison})"
        let effectPc := joinPoison p (joinPoison p1 ctx.pc)

        let allPreds := collectExternPreds retSpec effects
        let (tagMapping, nextTag') ← collectAndAllocExternTags allPreds cursor.1
        let argBaseTag := nextTag'

        let mut memEnv := result2.memEnv'
        let mut nextLoc := cursor.2
        for effect in effects do
          memEnv ← applyExternEffect effect unifiedEnv tagMapping effectPc memEnv

        match retSpec with
        | ExternReturn.simple typ poison pred =>
            let resolvedPred ← resolveSyntaxPred pred unifiedEnv tagMapping
            let (retQt, nextLoc') ← returnSpecToQTyp typ poison resolvedPred nextLoc

            let poison' := joinPoison p1 (joinPoison p (joinPoison ctx.pc retQt.poison))
            let qt := ⟨retQt.etyp, poison', retQt.pred⟩
            let normalizedQt := normalizeAppResultByProvenance (joinPoison p1 p) qt
            return { qualType := normalizedQt, memEnv' := memEnv,
                     tagEnv' := installReturnGuard
                       (invalidateTagDeps result2.tagEnv' (effectTargetLocs effects unifiedEnv))
                       resolvedPred
                       (applyExternRegimePolicy
                         (invalidateRegimeDepsEffect result2.regime' result2.tagEnv' (effectTargetLocs effects unifiedEnv))
                         id ctx.externRegime tagMapping)
                       fuel,
                     nextLoc' := nextLoc', nextTag' := nextTag',
                     regime' := applyExternRegimePolicy
                       (invalidateRegimeDepsEffect result2.regime' result2.tagEnv' (effectTargetLocs effects unifiedEnv))
                       id ctx.externRegime tagMapping,
                     declared' := result2.declared' }

        | ExternReturn.nestedFn innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerEffects innerCaptures =>
            let (innerArgQt, nextTag'') ← resolveArgCondQTyp innerArgTyp innerArgPoison innerArgPred unifiedEnv argBaseTag
            -- Propagate the nested-return `captures:` contract onto the produced
            -- inner closure's type member (the call-site gate); the body AST shape
            -- is recorded separately (two-track discipline).
            let innerTcl := FnTClosure.extern innerId innerArg innerRet innerEffects (VarTypeEnv.toCaptured unifiedEnv) innerArgQt innerCaptures
            let innerArrowTyp := ETyp.arrow innerArgTyp (parseReturnType innerRet) ctx.pc [innerTcl]
            let poison' := joinPoison p1 (joinPoison p ctx.pc)
            let qt := ⟨innerArrowTyp, poison', Predicate.noPred⟩
            let normalizedQt := normalizeAppResultByProvenance (joinPoison p1 p) qt
            return { qualType := normalizedQt, memEnv' := memEnv,
                     tagEnv' := invalidateTagDeps result2.tagEnv' (effectTargetLocs effects unifiedEnv),
                     nextLoc' := nextLoc, nextTag' := nextTag'',
                     regime' := applyExternRegimePolicy
                       (invalidateRegimeDepsEffect result2.regime' result2.tagEnv' (effectTargetLocs effects unifiedEnv))
                       id ctx.externRegime tagMapping,
                     declared' := result2.declared' }

        | ExternReturn.nestedPfn innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerCaptures =>
            let (innerArgQt, nextTag'') ← resolveArgCondQTyp innerArgTyp innerArgPoison innerArgPred unifiedEnv argBaseTag
            -- Propagate the nested-return `captures:` contract onto the produced
            -- inner closure's type member (the call-site gate); the body AST shape
            -- is recorded separately (two-track discipline).
            let innerTcl := PFnTClosure.extern innerId innerArg innerRet (VarTypeEnv.toCaptured unifiedEnv) innerArgQt innerCaptures
            let innerArrowTyp := ETyp.parrow innerArgTyp (parseReturnType innerRet) ctx.pc [innerTcl]
            let poison' := joinPoison p1 (joinPoison p ctx.pc)
            let qt := ⟨innerArrowTyp, poison', Predicate.noPred⟩
            let normalizedQt := normalizeAppResultByProvenance (joinPoison p1 p) qt
            return { qualType := normalizedQt, memEnv' := memEnv,
                     tagEnv' := invalidateTagDeps result2.tagEnv' (effectTargetLocs effects unifiedEnv),
                     nextLoc' := nextLoc, nextTag' := nextTag'',
                     regime' := applyExternRegimePolicy
                       (invalidateRegimeDepsEffect result2.regime' result2.tagEnv' (effectTargetLocs effects unifiedEnv))
                       id ctx.externRegime tagMapping,
                     declared' := result2.declared' }
termination_by fuel

def applyFnTClosure (tcl : FnTClosure) (_st1 st2 : Typ) (p : Poison) (p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (ctx : TypeContext) (result2 : TypeResult) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel in applyFnTClosure"
  | fuel + 1 => do
    match tcl with
    | FnTClosure.regular x body env =>
        -- Type the body with the closure's captured environment
        -- pc = join p join p1 pc (Ott rule: app_fn_singleton)
        let argQt : QTyp := ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        let envMap := VarTypeEnv.ofCaptured env
        let env' := VarTypeEnv.update envMap x argQt
        let ctx'' := { ctx with pc := joinPoison p (joinPoison p1 ctx.pc),
                                memEnv := result2.memEnv', varEnv := env', tagEnv := result2.tagEnv',
                                nextTag := result2.nextTag', nextLoc := result2.nextLoc', regime := result2.regime',
                                externRefAllowed := false, declaredExternRefs := result2.declared' }
        let result3 ← typecheckExpr ctx'' body fuel
        let ⟨_etyp3, _p3, _pred3⟩ := result3.qualType

        -- Check surface-type erasure
        if not (isErasureOf st2 result3.qualType) then
          throw s!"Type mismatch in function application: return type {repr st2} is not compatible with body type {repr (QTyp.toTyp result3.qualType)}"

        -- Issue #111: taint app result by function poison (p, p1)
        -- Issue #113: provenance gate - if join p1 p, force irrecoverable poison and no_pred
        let taintedPoison := joinPoison p1 (joinPoison p result3.qualType.poison)
        let taintedQt := { result3.qualType with poison := taintedPoison }
        -- Bodies are typechecked with `externRefAllowed := false`, so they cannot
        -- declare extern refs; pin the result's declared set to the pre-body one so
        -- all closure alternatives joined by `joinTypeResults` agree on it syntactically.
        return { result3 with
                 qualType := normalizeAppResultByProvenance (joinPoison p1 p) taintedQt
                 declared' := result2.declared' }

    | FnTClosure.extern id x retSpec effects capturedEnv declaredArgQt captures =>
        let argQt := ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        let unifiedEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured capturedEnv) x argQt
        -- Single trusted-result gate: the actual argument must satisfy the declared
        -- precondition AND each declared `captures:` read dependency must satisfy its
        -- qualified type in the callable environment / current (pre-effect) memory.
        -- `capturesSatisfied` is checked at call entry (`result2.memEnv'`), before this
        -- extern's own effects mutate memory — mirroring the pure (`pfn`) path.
        if !(argConditionSatisfied declaredArgQt argQt result2.regime' fuel
              && capturesSatisfied captures unifiedEnv result2.memEnv' result2.regime') then
          throw s!"extern @{id}: argument precondition or a captures: read dependency not satisfied (arg runtime type {repr (QTyp.toTyp argQt)}, poison={argQt.poison}; declared poison={declaredArgQt.poison})"
        let effectPc := joinPoison p (joinPoison p1 ctx.pc)

        let allPreds := collectExternPreds retSpec effects
        let (tagMapping, nextTag') ← collectAndAllocExternTags allPreds result2.nextTag'
        let argBaseTag := nextTag'

        let mut memEnv := result2.memEnv'
        let mut nextLoc := result2.nextLoc'
        for effect in effects do
          memEnv ← applyExternEffect effect unifiedEnv tagMapping effectPc memEnv

        match retSpec with
        | ExternReturn.simple typ poison pred =>
            let resolvedPred ← resolveSyntaxPred pred unifiedEnv tagMapping
            let (retQt, nextLoc') ← returnSpecToQTyp typ poison resolvedPred nextLoc

            let poison' := joinPoison p1 (joinPoison p (joinPoison ctx.pc retQt.poison))
            let qt := ⟨retQt.etyp, poison', retQt.pred⟩
            let normalizedQt := normalizeAppResultByProvenance (joinPoison p1 p) qt
            return { qualType := normalizedQt, memEnv' := memEnv,
                     tagEnv' := installReturnGuard
                       (invalidateTagDeps result2.tagEnv' (effectTargetLocs effects unifiedEnv))
                       resolvedPred
                       (applyExternRegimePolicy
                         (invalidateRegimeDepsEffect result2.regime' result2.tagEnv' (effectTargetLocs effects unifiedEnv))
                         id ctx.externRegime tagMapping)
                       fuel,
                     nextLoc' := nextLoc', nextTag' := nextTag',
                     regime' := applyExternRegimePolicy
                       (invalidateRegimeDepsEffect result2.regime' result2.tagEnv' (effectTargetLocs effects unifiedEnv))
                       id ctx.externRegime tagMapping,
                     declared' := result2.declared' }

        | ExternReturn.nestedFn innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerEffects innerCaptures =>
            let (innerArgQt, nextTag'') ← resolveArgCondQTyp innerArgTyp innerArgPoison innerArgPred unifiedEnv argBaseTag
            -- Propagate the nested-return `captures:` contract onto the produced
            -- inner closure's type member (the call-site gate); the body AST shape
            -- is recorded separately (two-track discipline).
            let innerTcl := FnTClosure.extern innerId innerArg innerRet innerEffects (VarTypeEnv.toCaptured unifiedEnv) innerArgQt innerCaptures
            let innerArrowTyp := ETyp.arrow innerArgTyp (parseReturnType innerRet) ctx.pc [innerTcl]
            let poison' := joinPoison p1 (joinPoison p ctx.pc)
            let qt := ⟨innerArrowTyp, poison', Predicate.noPred⟩
            let normalizedQt := normalizeAppResultByProvenance (joinPoison p1 p) qt
            return { qualType := normalizedQt, memEnv' := memEnv,
                     tagEnv' := invalidateTagDeps result2.tagEnv' (effectTargetLocs effects unifiedEnv),
                     nextLoc' := nextLoc, nextTag' := nextTag'',
                     regime' := applyExternRegimePolicy
                       (invalidateRegimeDepsEffect result2.regime' result2.tagEnv' (effectTargetLocs effects unifiedEnv))
                       id ctx.externRegime tagMapping,
                     declared' := result2.declared' }

        | ExternReturn.nestedPfn innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerCaptures =>
            let (innerArgQt, nextTag'') ← resolveArgCondQTyp innerArgTyp innerArgPoison innerArgPred unifiedEnv argBaseTag
            -- Propagate the nested-return `captures:` contract onto the produced
            -- inner closure's type member (the call-site gate); the body AST shape
            -- is recorded separately (two-track discipline).
            let innerTcl := PFnTClosure.extern innerId innerArg innerRet (VarTypeEnv.toCaptured unifiedEnv) innerArgQt innerCaptures
            let innerArrowTyp := ETyp.parrow innerArgTyp (parseReturnType innerRet) ctx.pc [innerTcl]
            let poison' := joinPoison p1 (joinPoison p ctx.pc)
            let qt := ⟨innerArrowTyp, poison', Predicate.noPred⟩
            let normalizedQt := normalizeAppResultByProvenance (joinPoison p1 p) qt
            return { qualType := normalizedQt, memEnv' := memEnv,
                     tagEnv' := invalidateTagDeps result2.tagEnv' (effectTargetLocs effects unifiedEnv),
                     nextLoc' := nextLoc, nextTag' := nextTag'',
                     regime' := applyExternRegimePolicy
                       (invalidateRegimeDepsEffect result2.regime' result2.tagEnv' (effectTargetLocs effects unifiedEnv))
                       id ctx.externRegime tagMapping,
                     declared' := result2.declared' }

/-- Helper: Apply a single PFnTClosure and return the result type and updated environments.
    This encapsulates the body typing logic for a single pure closure alternative.
-/
def applyPFnTClosureAtCursor (tcl : PFnTClosure) (_st1 st2 : Typ) (p : Poison) (p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (ctx : TypeContext) (result2 : TypeResult) (cursor : Tag × Loc)
    (fuel : Nat) : TypecheckM TypeResult :=
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
                                pureCtx := true, nextLoc := cursor.2, nextTag := cursor.1, regime := result2.regime',
                                externRefAllowed := false, declaredExternRefs := result2.declared' }
        let result3 ← typecheckExpr ctx'' (PExpr.toExpr body) fuel
        let ⟨_etyp3, _p3, _pred3⟩ := result3.qualType

        -- Check surface-type erasure
        if not (isErasureOf st2 result3.qualType) then
          throw s!"Type mismatch in function application: return type {repr st2} is not compatible with body type {repr (QTyp.toTyp result3.qualType)}"

        -- Issue #111: taint app result by function poison (p, p1)
        -- Issue #113: provenance gate - if join p1 p, force irrecoverable poison and no_pred
        let taintedPoison := joinPoison p1 (joinPoison p result3.qualType.poison)
        let taintedQt := { result3.qualType with poison := taintedPoison }
        -- Bodies are typechecked with `externRefAllowed := false`, so they cannot
        -- declare extern refs; pin the result's declared set to the pre-body one so
        -- all closure alternatives joined by `joinTypeResults` agree on it syntactically.
        return { result3 with
                 qualType := normalizeAppResultByProvenance (joinPoison p1 p) taintedQt
                 declared' := result2.declared' }

    | PFnTClosure.extern id x retSpec capturedEnv declaredArgQt captures =>
        let argQt := ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        -- Argument-condition gate: a trusted/declared result is available only when
        -- the actual argument satisfies the declared precondition.
        let unifiedEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured capturedEnv) x argQt
        -- Single trusted-result gate: the actual argument must satisfy the declared
        -- precondition AND each declared `captures:` read dependency must satisfy its
        -- qualified type in the callable environment / current memory.  Fusing both
        -- into one guard lets the per-branch structural proofs over
        -- `applyPFnTClosure` split just once on this gate.
        if !(argConditionSatisfied declaredArgQt argQt result2.regime' fuel
              && capturesSatisfied captures unifiedEnv result2.memEnv' result2.regime') then
          throw s!"extern @{id}: argument precondition or a captures: read dependency not satisfied (arg runtime type {repr (QTyp.toTyp argQt)}, poison={argQt.poison}; declared poison={declaredArgQt.poison})"

        let mut nextLoc := cursor.2
        let argBaseTag := cursor.1

        match retSpec with
        | ExternReturn.simple typ poison pred =>
            let (tagMapping, nextTag') ← collectAndAllocExternTags [pred] cursor.1
            let resolvedPred ← resolveSyntaxPred pred unifiedEnv tagMapping
            let (retQt, nextLoc') ← returnSpecToQTyp typ poison resolvedPred nextLoc

            let poison' := joinPoison p1 (joinPoison p (joinPoison ctx.pc retQt.poison))
            let qt := ⟨retQt.etyp, poison', retQt.pred⟩
            let normalizedQt := normalizeAppResultByProvenance (joinPoison p1 p) qt
            return { qualType := normalizedQt, memEnv' := result2.memEnv',
                     tagEnv' := installReturnGuard result2.tagEnv' resolvedPred
                       (applyExternRegimePolicy result2.regime' id ctx.externRegime tagMapping) fuel,
                     nextLoc' := nextLoc', nextTag' := nextTag', regime' := applyExternRegimePolicy result2.regime' id ctx.externRegime tagMapping,
                     declared' := result2.declared' }

        | ExternReturn.nestedFn innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerEffects innerCaptures =>
            let (innerArgQt, nextTag'') ← resolveArgCondQTyp innerArgTyp innerArgPoison innerArgPred unifiedEnv argBaseTag
            -- Propagate the nested-return `captures:` contract onto the produced
            -- inner closure's type member (the call-site gate); the body AST shape
            -- is recorded separately (two-track discipline).
            let innerTcl := FnTClosure.extern innerId innerArg innerRet innerEffects (VarTypeEnv.toCaptured unifiedEnv) innerArgQt innerCaptures
            let innerArrowTyp := ETyp.arrow innerArgTyp (parseReturnType innerRet) ctx.pc [innerTcl]
            -- Issue #111: taint app result by function poison (p, p1)
            -- Issue #113: provenance gate
            let poison' := joinPoison p1 (joinPoison p ctx.pc)
            let qt := ⟨innerArrowTyp, poison', Predicate.noPred⟩
            let normalizedQt := normalizeAppResultByProvenance (joinPoison p1 p) qt
            return { qualType := normalizedQt, memEnv' := result2.memEnv', tagEnv' := result2.tagEnv',
                     nextLoc' := nextLoc, nextTag' := nextTag'', regime' := result2.regime',
                     declared' := result2.declared' }

        | ExternReturn.nestedPfn innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerCaptures =>
            let (innerArgQt, nextTag'') ← resolveArgCondQTyp innerArgTyp innerArgPoison innerArgPred unifiedEnv argBaseTag
            -- Propagate the nested-return `captures:` contract onto the produced
            -- inner closure's type member (the call-site gate); the body AST shape
            -- is recorded separately (two-track discipline).
            let innerTcl := PFnTClosure.extern innerId innerArg innerRet (VarTypeEnv.toCaptured unifiedEnv) innerArgQt innerCaptures
            let innerArrowTyp := ETyp.parrow innerArgTyp (parseReturnType innerRet) ctx.pc [innerTcl]
            -- Issue #111: taint app result by function poison (p, p1)
            -- Issue #113: provenance gate
            let poison' := joinPoison p1 (joinPoison p ctx.pc)
            let qt := ⟨innerArrowTyp, poison', Predicate.noPred⟩
            let normalizedQt := normalizeAppResultByProvenance (joinPoison p1 p) qt
            return { qualType := normalizedQt, memEnv' := result2.memEnv', tagEnv' := result2.tagEnv',
                     nextLoc' := nextLoc, nextTag' := nextTag'', regime' := result2.regime',
                     declared' := result2.declared' }
termination_by fuel

def applyPFnTClosure (tcl : PFnTClosure) (_st1 st2 : Typ) (p : Poison) (p1 : Poison)
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
                                pureCtx := true, nextLoc := result2.nextLoc', nextTag := result2.nextTag', regime := result2.regime',
                                externRefAllowed := false, declaredExternRefs := result2.declared' }
        let result3 ← typecheckExpr ctx'' (PExpr.toExpr body) fuel
        let ⟨_etyp3, _p3, _pred3⟩ := result3.qualType

        -- Check surface-type erasure
        if not (isErasureOf st2 result3.qualType) then
          throw s!"Type mismatch in function application: return type {repr st2} is not compatible with body type {repr (QTyp.toTyp result3.qualType)}"

        -- Issue #111: taint app result by function poison (p, p1)
        -- Issue #113: provenance gate - if join p1 p, force irrecoverable poison and no_pred
        let taintedPoison := joinPoison p1 (joinPoison p result3.qualType.poison)
        let taintedQt := { result3.qualType with poison := taintedPoison }
        -- Bodies are typechecked with `externRefAllowed := false`, so they cannot
        -- declare extern refs; pin the result's declared set to the pre-body one so
        -- all closure alternatives joined by `joinTypeResults` agree on it syntactically.
        return { result3 with
                 qualType := normalizeAppResultByProvenance (joinPoison p1 p) taintedQt
                 declared' := result2.declared' }

    | PFnTClosure.extern id x retSpec capturedEnv declaredArgQt captures =>
        let argQt := ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        -- Argument-condition gate: a trusted/declared result is available only when
        -- the actual argument satisfies the declared precondition.
        let unifiedEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured capturedEnv) x argQt
        -- Single trusted-result gate: the actual argument must satisfy the declared
        -- precondition AND each declared `captures:` read dependency must satisfy its
        -- qualified type in the callable environment / current memory.  Fusing both
        -- into one guard lets the per-branch structural proofs over
        -- `applyPFnTClosure` split just once on this gate.
        if !(argConditionSatisfied declaredArgQt argQt result2.regime' fuel
              && capturesSatisfied captures unifiedEnv result2.memEnv' result2.regime') then
          throw s!"extern @{id}: argument precondition or a captures: read dependency not satisfied (arg runtime type {repr (QTyp.toTyp argQt)}, poison={argQt.poison}; declared poison={declaredArgQt.poison})"

        let mut nextLoc := result2.nextLoc'
        let argBaseTag := result2.nextTag'

        match retSpec with
        | ExternReturn.simple typ poison pred =>
            let (tagMapping, nextTag') ← collectAndAllocExternTags [pred] result2.nextTag'
            let resolvedPred ← resolveSyntaxPred pred unifiedEnv tagMapping
            let (retQt, nextLoc') ← returnSpecToQTyp typ poison resolvedPred nextLoc

            let poison' := joinPoison p1 (joinPoison p (joinPoison ctx.pc retQt.poison))
            let qt := ⟨retQt.etyp, poison', retQt.pred⟩
            let normalizedQt := normalizeAppResultByProvenance (joinPoison p1 p) qt
            return { qualType := normalizedQt, memEnv' := result2.memEnv',
                     tagEnv' := installReturnGuard result2.tagEnv' resolvedPred
                       (applyExternRegimePolicy result2.regime' id ctx.externRegime tagMapping) fuel,
                     nextLoc' := nextLoc', nextTag' := nextTag', regime' := applyExternRegimePolicy result2.regime' id ctx.externRegime tagMapping,
                     declared' := result2.declared' }

        | ExternReturn.nestedFn innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerEffects innerCaptures =>
            let (innerArgQt, nextTag'') ← resolveArgCondQTyp innerArgTyp innerArgPoison innerArgPred unifiedEnv argBaseTag
            -- Propagate the nested-return `captures:` contract onto the produced
            -- inner closure's type member (the call-site gate); the body AST shape
            -- is recorded separately (two-track discipline).
            let innerTcl := FnTClosure.extern innerId innerArg innerRet innerEffects (VarTypeEnv.toCaptured unifiedEnv) innerArgQt innerCaptures
            let innerArrowTyp := ETyp.arrow innerArgTyp (parseReturnType innerRet) ctx.pc [innerTcl]
            -- Issue #111: taint app result by function poison (p, p1)
            -- Issue #113: provenance gate
            let poison' := joinPoison p1 (joinPoison p ctx.pc)
            let qt := ⟨innerArrowTyp, poison', Predicate.noPred⟩
            let normalizedQt := normalizeAppResultByProvenance (joinPoison p1 p) qt
            return { qualType := normalizedQt, memEnv' := result2.memEnv', tagEnv' := result2.tagEnv',
                     nextLoc' := nextLoc, nextTag' := nextTag'', regime' := result2.regime',
                     declared' := result2.declared' }

        | ExternReturn.nestedPfn innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerCaptures =>
            let (innerArgQt, nextTag'') ← resolveArgCondQTyp innerArgTyp innerArgPoison innerArgPred unifiedEnv argBaseTag
            -- Propagate the nested-return `captures:` contract onto the produced
            -- inner closure's type member (the call-site gate); the body AST shape
            -- is recorded separately (two-track discipline).
            let innerTcl := PFnTClosure.extern innerId innerArg innerRet (VarTypeEnv.toCaptured unifiedEnv) innerArgQt innerCaptures
            let innerArrowTyp := ETyp.parrow innerArgTyp (parseReturnType innerRet) ctx.pc [innerTcl]
            -- Issue #111: taint app result by function poison (p, p1)
            -- Issue #113: provenance gate
            let poison' := joinPoison p1 (joinPoison p ctx.pc)
            let qt := ⟨innerArrowTyp, poison', Predicate.noPred⟩
            let normalizedQt := normalizeAppResultByProvenance (joinPoison p1 p) qt
            return { qualType := normalizedQt, memEnv' := result2.memEnv', tagEnv' := result2.tagEnv',
                     nextLoc' := nextLoc, nextTag' := nextTag'', regime' := result2.regime',
                     declared' := result2.declared' }

def typecheckApp (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    -- NOTE: The operational semantics evaluates application argument-first (see `beval`),
    -- so we typecheck the argument before the function to mirror the evaluation order.
    --
    let result2 ← typecheckExpr ctx e2 fuel
    let ⟨etyp2, p2, pred2⟩ := result2.qualType

    let ctx' := { ctx with memEnv := result2.memEnv', tagEnv := result2.tagEnv', nextLoc := result2.nextLoc', nextTag := result2.nextTag', regime := result2.regime', declaredExternRefs := result2.declared' }
    let result1 ← typecheckExpr ctx' e1 fuel
    let ⟨etyp1, p1, _pred1⟩ := result1.qualType
    match etyp1 with
    | ETyp.arrow st1 st2 p tcls =>
      -- In pure context, disallow applying impure arrow
      if ctx.pureCtx then
        throw "Pure context disallows application of impure function"

      -- Check for empty closure list (should never happen in well-formed programs)
      if tcls.isEmpty then
        throw "Function type has empty closure set"

      -- Premise 3: erase T1 = ST1 (surface-type erasure check)
      if not (isErasureOf st1 result2.qualType) then
        throw s!"Type mismatch in function application: parameter type {repr st1} is not compatible with argument type {repr (QTyp.toTyp result2.qualType)}"

      let results ← applyClosuresThreaded
        (fun tcl cursor =>
          applyFnTClosureAtCursor tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 cursor fuel)
        tcls (result1.nextTag', result1.nextLoc')

      -- Check that we have at least one result and join them
      match results with
      | [] => throw "Internal error: no results from closure application"
      | firstResult :: restResults => joinTypeResults ctx firstResult restResults
    | ETyp.parrow st1 st2 p tcls =>
      -- Check for empty closure list (should never happen in well-formed programs)
      if tcls.isEmpty then
        throw "Function type has empty closure set"

      -- Premise 3: erase T1 = ST1 (surface-type erasure check)
      if not (isErasureOf st1 result2.qualType) then
        throw s!"Type mismatch in function application: parameter type {repr st1} is not compatible with argument type {repr (QTyp.toTyp result2.qualType)}"

      let results ← applyClosuresThreaded
        (fun tcl cursor =>
          applyPFnTClosureAtCursor tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 cursor fuel)
        tcls (result1.nextTag', result1.nextLoc')

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
def typecheckVlet (ctx : TypeContext) (x : Name) (e1 : Expr) (e2 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    -- Check for harmful shadowing (Ott premise: not_harmful_shadow): reject if outer binding has guardClosure with interpreted tag
    match ctx.varEnv.lookup x with
    | none => pure ()
    | some qt_outer =>
      match qt_outer.pred with
      | Predicate.guardClosure k _ _ _ =>
        if ctx.regime.lookup? k |>.isSome then
          throw s!"Cannot shadow variable '{x}': outer binding has an active guard predicate"
      | _ => pure ()

    let result1 ← typecheckExpr ctx e1 fuel
    let varEnv' := ctx.varEnv.update x result1.qualType
    let ctx' := { ctx with memEnv := result1.memEnv', varEnv := varEnv', tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime', declaredExternRefs := result1.declared' }

    let result2 ← typecheckExpr ctx' e2 fuel
    let ⟨etyp2, p2, pred2⟩ := result2.qualType
   --dbg_trace s!" In typecheck Let ,Poison val for exp {e1} is {p1}"
   -- dbg_trace s!"In typecheck Let ,Poison val for exp {e2} is {p2}"

    let poison := joinPoison ctx.pc p2
    let qt : QTyp := ⟨etyp2, poison, pred2⟩
    return { qualType := qt, memEnv' := result2.memEnv', tagEnv' := result2.tagEnv', nextLoc' := result2.nextLoc', nextTag' := result2.nextTag', regime' := result2.regime', declared' := result2.declared' }
termination_by fuel


/-- Rule: if_depoison_* and if_std_* (Ott rules with regime awareness)
-- When matchGuard succeeds: consult R(k) for regime-aware typing.
-- If the regime is unknown, fall back to the same conservative typing path
-- used by the standard if rules; no branch-local tag or regime fact is added.
--/
def typecheckIf (ctx : TypeContext) (e1 e2 e3 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    -- Step 1: Try matchGuard first
    match matchGuard e1 ctx.memEnv ctx.varEnv fuel with
    | .ok (k, deps) => do
      -- Predicate-based case: consult R(k)

      -- Typecheck e1 in pure mode (all if_depoison_* rules require this)
      let pureCtx := { ctx with pureCtx := true }
      let result1 ← typecheckExpr pureCtx e1 fuel
      let ⟨etyp1, p1, _⟩ := result1.qualType
      if etyp1 != ETyp.bool then throw "Condition of if must be bool"

      -- Setup branch contexts with tag knowledge.  The declared extern-ref set
      -- threads FULLY SERIALLY (like nextLoc): condition, then-arm, else-arm.
      -- The else-arm therefore sees the then-arm's declarations, so the
      -- per-declaration duplicate gate in typecheckExternRef also rejects
      -- same-id declarations across the two arms.
      let ctxTrue := { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩,
                                declaredExternRefs := result1.declared' }
      let ctxFalse := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩,
                                 declaredExternRefs := result1.declared' }

      -- Consult R(k) for branch selection
      match ctx.regime.lookup? k with
      | some true => do
        -- R(k) = true: then-branch effective (if_depoison_*_R_true rules)
        let result2 ← typecheckExpr ctxTrue e2 fuel
        let ⟨etyp2, p2, _pred2⟩ := result2.qualType

        let ctxFalse' := { ctxFalse with nextLoc := result2.nextLoc', nextTag := result2.nextTag',
                                         declaredExternRefs := result2.declared' }
        let result3 ← typecheckExpr ctxFalse' e3 fuel
        let ⟨etyp3, _p3, _pred3⟩ := result3.qualType
        if not (beqETypSignature etyp2 etyp3) then throw s!"Branches of if must have same type (etyp2: {etyp2}, etyp3: {etyp3})"
        let poison := joinPoison ctx.pc p2
        let qt : QTyp := ⟨etyp2, poison, Predicate.noPred⟩
        return { qualType := qt, memEnv' := result2.memEnv', tagEnv' := result2.tagEnv',
                 nextLoc' := max result2.nextLoc' result3.nextLoc', nextTag' := max result2.nextTag' result3.nextTag', regime' := result2.regime',
                 declared' := result3.declared' }

      | some false => do
        let result2 ← typecheckExpr ctxTrue e2 fuel
        let ⟨etyp2, _p2, _pred2⟩ := result2.qualType
        let ctxFalse' := { ctxFalse with nextLoc := result2.nextLoc', nextTag := result2.nextTag',
                                         declaredExternRefs := result2.declared' }
        let result3 ← typecheckExpr ctxFalse' e3 fuel
        let ⟨etyp3, p3, _pred3⟩ := result3.qualType
        if not (beqETypSignature etyp2 etyp3) then throw s!"Branches of if must have same type (etyp2: {etyp2}, etyp3: {etyp3})"
        let poison := joinPoison ctx.pc p3
        let qt : QTyp := ⟨etyp3, poison, Predicate.noPred⟩
        return { qualType := qt, memEnv' := result3.memEnv', tagEnv' := result3.tagEnv',
                 nextLoc' := max result2.nextLoc' result3.nextLoc', nextTag' := max result2.nextTag' result3.nextTag', regime' := result3.regime',
                 declared' := result3.declared' }

      | none => do
        let result1 ← typecheckExpr ctx e1 fuel
        let ⟨etyp1, p1, _⟩ := result1.qualType
        if etyp1 != ETyp.bool then throw "Condition of if must be bool"

        let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv',
                               nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime',
                               declaredExternRefs := result1.declared' }

        let branchPc := joinPoison ctx.pc p1
        let ctx'' := { ctx' with pc := branchPc }

        let result2 ← typecheckExpr ctx'' e2 fuel
        let ⟨etyp2, p2, _⟩ := result2.qualType

        let ctxForE3 := { ctx'' with nextLoc := result2.nextLoc', nextTag := result2.nextTag',
                                     declaredExternRefs := result2.declared' }
        let result3 ← typecheckExpr ctxForE3 e3 fuel
        let ⟨etyp3, p3, _⟩ := result3.qualType

        if not (beqETypSignature etyp2 etyp3) then throw s!"Branches of if must have same type"

        let joinedEtyp := joinETyps etyp2 etyp3 p2 p3
        let poison := joinPoison ctx.pc (joinPoison p1 (joinPoison p2 p3))
        let qt : QTyp := ⟨joinedEtyp, poison, Predicate.noPred⟩
        let memEnv' := joinMemEnvsStrong result2.memEnv' result3.memEnv'
        let tagEnv' := joinTagEnvs result2.tagEnv' result3.tagEnv'
        let regime' := joinRegimes result2.regime' result3.regime'
        let nextLoc' := max result2.nextLoc' result3.nextLoc'
        let nextTag' := max result2.nextTag' result3.nextTag'
        return { qualType := qt, memEnv' := memEnv', tagEnv' := tagEnv', nextLoc' := nextLoc', nextTag' := nextTag', regime' := regime', declared' := result3.declared' }

    | .error _ => do
      -- Standard case (if_std_*) - no matching predicate found
      let result1 ← typecheckExpr ctx e1 fuel
      let ⟨etyp1, p1, _⟩ := result1.qualType
      if etyp1 != ETyp.bool then throw "Condition of if must be bool"

      let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv',
                             nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime',
                             declaredExternRefs := result1.declared' }

      -- Branch pc is poisoned by guard poison
      let branchPc := joinPoison ctx.pc p1
      let ctx'' := { ctx' with pc := branchPc }

      let result2 ← typecheckExpr ctx'' e2 fuel
      let ⟨etyp2, p2, _⟩ := result2.qualType

      -- Ensure disjoint fresh supplies across branches
      -- Note: regime stays as ctx''.regime (= result1.regime') since branches are parallel, not sequential
      let ctxForE3 := { ctx'' with nextLoc := result2.nextLoc', nextTag := result2.nextTag',
                                   declaredExternRefs := result2.declared' }
      let result3 ← typecheckExpr ctxForE3 e3 fuel
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
      return { qualType := qt, memEnv' := memEnv', tagEnv' := tagEnv', nextLoc' := nextLoc', nextTag' := nextTag', regime' := regime', declared' := result3.declared' }
termination_by fuel



/- Rule: unary_op_not_typing (Ott rule: unary_op_not_typing)

pm ; pc ; G ; S ; L |- e : bool :> p { P } -| G' ; L'
----------------------------------------------------------------------  :: unary_op_not_typing
pm ; pc ; G ; S ; L |- not e : bool :> join pc p { no_pred } -| G' ; L'

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

end

lemma normalizeAppResultByProvenance_etyp (p1p : Poison) (qt : QTyp) :
  (normalizeAppResultByProvenance p1p qt).etyp = qt.etyp := by
  simp only [normalizeAppResultByProvenance]; split_ifs <;> rfl

/-- Public typecheck entry point.  Thin wrapper over `typecheckExpr`
    for callers outside the recursive kernel.  The language-level rule that
    executable extern callables must have first-order input types is enforced
    per-declaration inside `typecheckExpr` (at the `Expr.externFn` /
    `Expr.externPfn` dispatch).  Global extern-id uniqueness is NOT enforced
    here (only duplicate `extern ref` declarations are rejected, by
    `typecheckExternRef`) — the driver's `register` already rejects duplicate
    ids at registration time, and any mismatch between a declared type and a
    registered value is caught by `valueMatchesTyp` at runtime. -/
def typecheck (ctx : TypeContext) (e : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  typecheckExpr ctx e fuel
