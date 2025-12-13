-- Non-Interference properties for the poison language

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanPoison.BigStep
import LeanProofs.TypeSafety
import LeanProofs.GuardlessIfClean
import Mathlib.Data.List.Forall2
import Std.Data.HashMap
import Std.Data.HashMap.Lemmas
open Std

-- ================================================================
-- Non-Interference (semantic formulation)
-- ================================================================

abbrev MemoryETypEnv := HashMap Loc ETyp
namespace MemoryETypEnv

  @[inline] def lookup (m : MemoryETypEnv) (l : Loc) : Option ETyp :=
    m.get? l

  @[inline] def update (m : MemoryETypEnv) (l : Loc) (qt : ETyp) : MemoryETypEnv :=
    m.insert l qt

  /-- `m` contains a binding for `l`. -/
  def hasKey (m : MemoryETypEnv) (l : Loc) : Prop :=
    m.contains l

end MemoryETypEnv

-- What parts of the final state are observable
structure ObservableSpec where
  locs       : MemoryETypEnv
  retEtyp?   : Option ETyp
deriving Repr

-- Critical inputs specification
--
-- We specify only the designated critical inputs and their qualified types.
-- Non-critical inputs are not listed here and are unconstrained by the spec.
-- In the initial typing context, any entry not listed in this spec must be
-- conservative: poisoned with no_pred, so it cannot influence de-poisoning.
structure InputSpec where
  locs : MemoryTypeEnv
  vars : VarTypeEnv
deriving Repr

open List

/-- Keys are unique in both `s.locs` (addresses) and `s.vars` (names). -/
def inputKeysUnique (vars : VarTypeEnv) : Prop :=
  Nodup (vars.map Prod.fst)
  -- for `s.locs` we don't need to check uniqueness because it is implemented as a HashMap

-- Regime: partial mapping from guard tags to their truth values.
-- A regime R : K_S → {true, false} assigns a truth value to each guard tag
-- that occurs in predicates attached to entries of the input specification S.
-- We model this as Tag → Option Bool where the regime is defined exactly for
-- tags appearing in S (enforced by wfRegime predicate).
abbrev Regime := Tag → Option Bool

-- Extract all guard tags from the input specification (functional version for wfRegime)
def inputSpecTags (s : InputSpec) : List Tag :=
  let locTags := s.locs.toList.filterMap (qtypGuardTag ·.2)
  let varTags := s.vars.filterMap (qtypGuardTag ·.2)
  locTags ++ varTags

-- Predicate-shape helpers
def isGuardClosure (qt : QTyp) : Prop :=
  ∃ k arg_name pred_body var_env, qt.pred = Predicate.guardClosure k arg_name pred_body var_env

def isGuardOnly (qt : QTyp) : Prop :=
  ∃ k, qt.pred = Predicate.guardOnly k

-- Regime is well-formed with respect to spec S if it's defined exactly for tags in S
def wfRegime (R : Regime) (s : InputSpec) : Prop :=
  let tags := inputSpecTags s
  (∀ k, k ∈ tags → (R k).isSome) ∧
  (∀ k, (R k).isSome → k ∈ tags)

inductive wfRegimeForReturn (R : Regime) : QTyp → Prop where
  | noPred (retType : QTyp)
      (hpred : retType.pred = Predicate.noPred) :
      wfRegimeForReturn R retType
  | guardOnly (retType : QTyp) (k : Tag)
      (hpred : retType.pred = Predicate.guardOnly k)
      (hregime : R k = some true) :
      wfRegimeForReturn R retType
  | guardClosure (retType : QTyp) (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : List (Name × QTyp))
      (hpred : retType.pred = Predicate.guardClosure k arg_name pred_body var_env)
      (hregime : R k = some true) :
      wfRegimeForReturn R retType

-- Abstract predicate satisfaction: does a predicate with the given tag hold
-- for a value in a given memory state?
--
-- This is left abstract (as a parameter) to avoid committing the NI proofs to a
-- concrete semantics for predicate closures / captured environments.
-- Instead, we assume a small set of laws (`PredSatLaws`) that connect this
-- abstract satisfaction relation to the type system's mechanisms (syntactic
-- matching, dependency tracking).
--
-- Note: No VarEnv parameter because captured variables are encoded in the tag's identity.
-- Memory is needed because predicates can dereference heap locations.
abbrev PredSat := Tag → Memory → Value → Prop

-- Laws that constrain the abstract `PredSat` relation.
-- These are required to hold for any tag, including tags generated at runtime.
structure PredSatLaws (predSat : PredSat) : Prop where
  -- Syntactic Matching Axiom: If a condition syntactically matches a tagged predicate
  -- via matchGuard and evaluates to true, then the predicate is satisfied for the value
  -- being tested (extracted from the runtime environment).
  --
  -- The matchGuard function verifies that 'condition' is syntactically identical to the
  -- predicate body after substituting the predicate's formal parameter with the actual
  -- value expression (variable or dereference). When the condition evaluates to true,
  -- it means the predicate (with captured environment baked into the tag) is satisfied.
  -- Value-sensitive formulation tied to a specific runtime value v.
  -- When a condition matches tag k and evaluates to true at check time,
  -- v must be exactly the runtime value denoted by one of the two
  -- substitution modes used by matchGuard (variable or dereference);
  -- then the predicate for k holds at memory μ for that v.
  match_sound : ∀ (condition : Expr) (Γ : MemoryTypeEnv) (σ : VarTypeEnv)
                  (k : Tag) (deps : Deps)
                  (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) (l : Address) (pm : Bool) (cfg : Config)
                  (v : Value),
    -- If matchGuard identifies that condition matches predicate k
    matchGuard condition Γ σ = .ok (k, deps) →
    -- And the condition evaluates to true
    terminatesTo condition { memory := μ, varEnv := ρ, nextLoc := l, pureMode := pm } cfg (Value.bool true) →
    -- And v arises from either the variable or dereference case used in matching:
    ( (∃ (x : Name) (qt : QTyp),
          σ.lookup x = some qt ∧
          qtypGuardTag qt = some k ∧
          ρ.lookup x = some v)
      ∨
      (∃ (x : Name) (qt memQt : QTyp) (t : ETyp) (ls : LocSet) (l0 : Loc) (a : Address) (n : Int),
          σ.lookup x = some qt ∧
          qt.etyp = ETyp.ref t ls ∧
          l0 ∈ ls ∧
          Γ.lookup l0 = some memQt ∧
          qtypGuardTag memQt = some k ∧
          θ.lookup l0 = some a ∧
          μ.lookup a = some n ∧
          v = Value.num n) ) →
    -- Then the predicate k is satisfied for this specific value v
    predSat k μ v

  -- Memory Monotonicity Law: predicate satisfaction is stable under memory
  -- changes that do not affect the locations it depends on.
  --
  -- Here `deps` is a set of *logical* locations (computed by `extractDepsFromPred`).
  -- To relate `deps` to the concrete heap, we interpret it via a single
  -- realisation map `θ` (logical loc ↦ concrete address).
  --
  -- We quantify over one `θ` because this is a single-run stability property:
  -- the predicate tag (and any captured environment baked into it) is fixed.
  -- In contrast, non-interference compares two runs and therefore uses `θ₁/θ₂`.
  mem_monotone : ∀ (k : Tag) (pred : Predicate) (μ μ' : Memory) (v : Value) (deps : Deps) (θ : RealizationMap),
    -- If k's dependencies are deps (as computed by extractDepsFromPred)
    extractDepsFromPred pred = .ok deps →
    -- And all dependent locations have the same values in both memories
    (∀ l, l ∈ deps → ∀ a, θ.lookup l = some a → μ.lookup a = μ'.lookup a) →
    -- Then predicate satisfaction is the same in both memories
    (predSat k μ v ↔ predSat k μ' v)

-- Check if a QTyp-attached predicate holds using abstract satisfaction relation
inductive qtypPredHolds (predSat : PredSat) : QTyp → Memory → Value → Prop where
  | noPred_ok {qt : QTyp} {μ v}
      (h : qt.pred = Predicate.noPred) :
      qtypPredHolds predSat qt μ v
  | guardClosure_ok {qt : QTyp} {μ v k arg_name pred_body var_env}
      (h : qt.pred = Predicate.guardClosure k arg_name pred_body var_env)
      (hSat : predSat k μ v) :
      qtypPredHolds predSat qt μ v
  | guardOnly_ok {qt : QTyp} {μ v k}
      (h : qt.pred = Predicate.guardOnly k)
      (hSat : predSat k μ v) :
      qtypPredHolds predSat qt μ v

-- Helper: equality of observables in the final states
def observablesEqual (obs : ObservableSpec)
    (θ₁ θ₂ : RealizationMap)
    (c₁ c₂ : Config) (o₁ o₂ : Value) : Prop :=
  let sameMem : Prop :=
    ∀ {l et}, obs.locs.lookup l = some et →
      ∃ a₁ a₂,
        θ₁.lookup l = some a₁ ∧
        θ₂.lookup l = some a₂ ∧
        c₁.memory.lookup a₁ = c₂.memory.lookup a₂
  -- If the return is observable (retEtyp? = some et), we constrain it.
  -- For references, observability is via the logical-location set, not the
  -- concrete address, so the two concrete addresses may differ across runs.
  let sameRet : Prop :=
    match obs.retEtyp? with
    | none => True
    | some (ETyp.ref _ ls) =>
        (∃ l₁ a₁, l₁ ∈ ls ∧ θ₁.lookup l₁ = some a₁ ∧ o₁ = Value.loc a₁) ∧
        (∃ l₂ a₂, l₂ ∈ ls ∧ θ₂.lookup l₂ = some a₂ ∧ o₂ = Value.loc a₂)
    | some _ => o₁ = o₂
  sameMem ∧ sameRet

-- Helper: check if guard tag present
def hasGuardTag (p : Predicate) : Bool :=
  match p with
  | Predicate.noPred => false
  | _ => true

mutual
  inductive deepVarEnvProperty : (VarTypeEnv → Prop) → VarTypeEnv → Prop
  | intro (P : VarTypeEnv → Prop) (env : VarTypeEnv) :
    P env →
    (forall x qt, env.lookup x = some qt → deepQTypProperty P qt) →
    deepVarEnvProperty P env

  inductive deepQTypProperty : (VarTypeEnv → Prop) → QTyp → Prop
  | arrow (P : VarTypeEnv → Prop) (qt : QTyp) :
    (∃ st1 st2 p tcls, qt.etyp = ETyp.arrow st1 st2 p tcls ∧
     (∀ tcl ∈ tcls, match tcl with
     | FnTClosure.regular _ _ env => P env
     | FnTClosure.extern _ _ _ env => P env)) →
    deepQTypProperty P qt
  | parrow (P : VarTypeEnv → Prop) (qt : QTyp) :
    (∃ st1 st2 p tcls, qt.etyp = ETyp.parrow st1 st2 p tcls ∧
     (∀ tcl ∈ tcls, match tcl with
     | PFnTClosure.regular _ _ env => P env
     | PFnTClosure.extern _ _ env => P env)) →
    deepQTypProperty P qt
  | other (P : VarTypeEnv → Prop) (qt : QTyp) :
    nonClosureQTyp qt →
    deepQTypProperty P qt
end

lemma deep_implies_shallow {P : VarTypeEnv → Prop} {env : VarTypeEnv} :
  deepVarEnvProperty P env → P env := by
  intro h
  cases h
  assumption

mutual
  inductive deepVarEnvProperty₂ : (VarTypeEnv → VarTypeEnv → Prop) → VarTypeEnv → VarTypeEnv → Prop
  | intro (P : VarTypeEnv → VarTypeEnv → Prop) (env₁ env₂ : VarTypeEnv) :
    P env₁ env₂ →
    (forall x qt₁ qt₂,
      env₁.lookup x = some qt₁ →
      env₂.lookup x = some qt₂ →
      deepQTypProperty₂ P qt₁ qt₂) →
    deepVarEnvProperty₂ P env₁ env₂

  inductive deepQTypProperty₂ : (VarTypeEnv → VarTypeEnv → Prop) → QTyp → QTyp → Prop
  | arrow (P : VarTypeEnv → VarTypeEnv → Prop) (qt₁ qt₂ : QTyp) :
    (∃ st1 st2 p tcls₁, qt₁.etyp = ETyp.arrow st1 st2 p tcls₁ ∧
     (∀ tcl₁ ∈ tcls₁, match tcl₁ with
     | FnTClosure.regular _ _ env₁ =>
       (∃ st1' st2' p' tcls₂, qt₂.etyp = ETyp.arrow st1' st2' p' tcls₂ ∧
        (∀ tcl₂ ∈ tcls₂, match tcl₂ with
        | FnTClosure.regular _ _ env₂ => P env₁ env₂
        | FnTClosure.extern _ _ _ env₂ => P env₁ env₂))
     | FnTClosure.extern _ _ _ env₁ =>
       (∃ st1' st2' p' tcls₂, qt₂.etyp = ETyp.arrow st1' st2' p' tcls₂ ∧
        (∀ tcl₂ ∈ tcls₂, match tcl₂ with
        | FnTClosure.regular _ _ env₂ => P env₁ env₂
        | FnTClosure.extern _ _ _ env₂ => P env₁ env₂)))) →
    deepQTypProperty₂ P qt₁ qt₂
  | parrow (P : VarTypeEnv → VarTypeEnv → Prop) (qt₁ qt₂ : QTyp) :
    (∃ st1 st2 p tcls₁, qt₁.etyp = ETyp.parrow st1 st2 p tcls₁ ∧
     (∀ tcl₁ ∈ tcls₁, match tcl₁ with
     | PFnTClosure.regular _ _ env₁ =>
       (∃ st1' st2' p' tcls₂, qt₂.etyp = ETyp.parrow st1' st2' p' tcls₂ ∧
        (∀ tcl₂ ∈ tcls₂, match tcl₂ with
        | PFnTClosure.regular _ _ env₂ => P env₁ env₂
        | PFnTClosure.extern _ _ env₂ => P env₁ env₂))
     | PFnTClosure.extern _ _ env₁ =>
       (∃ st1' st2' p' tcls₂, qt₂.etyp = ETyp.parrow st1' st2' p' tcls₂ ∧
        (∀ tcl₂ ∈ tcls₂, match tcl₂ with
        | PFnTClosure.regular _ _ env₂ => P env₁ env₂
        | PFnTClosure.extern _ _ env₂ => P env₁ env₂)))) →
    deepQTypProperty₂ P qt₁ qt₂
  | other (P : VarTypeEnv → VarTypeEnv → Prop) (qt₁ qt₂ : QTyp) :
    (nonClosureQTyp qt₁ ∨ nonClosureQTyp qt₂) →
    deepQTypProperty₂ P qt₁ qt₂
end

-- Well-formedness: memory stores integers at critical locations; additionally,
-- align predicate and poison for critical inputs: no predicate ⇒ clean;
-- predicate present ⇒ initially poisoned.
def wfInputSpecMem (locs : MemoryTypeEnv) : Prop :=
  ∀ l qt, locs.lookup l = some qt →
    qt.etyp = ETyp.int ∧ qt.poison = hasGuardTag qt.pred

def wfInputSpecVars (vars : VarTypeEnv) : Prop :=
  inputKeysUnique vars ∧
  (∀ x qt, vars.lookup x = some qt →
     qt.poison = hasGuardTag qt.pred)

def wfInputSpecVarsDeep (vars : VarTypeEnv) : Prop :=
  deepVarEnvProperty wfInputSpecVars vars

def wfInputSpec (s : InputSpec) : Prop :=
  wfInputSpecMem s.locs ∧ wfInputSpecVarsDeep s.vars

-- Well-formedness: observable spec
-- Always correct by construction
def wfObsSpec (_obs : ObservableSpec) : Prop := True

-- Derive return-observability and a conservative QTyp for the return from ObservableSpec.
-- If the return is observable (some et), we require equality on that enriched type and we
-- use a no_pred return qualified type with clean poison.
-- If it is not observable (none), the chosen QTyp is irrelevant (guarded later),
-- we pick a dummy value.
def isRetObservableFromObs (obs : ObservableSpec) : Bool :=
  obs.retEtyp?.isSome

def retQTypFromObs (obs : ObservableSpec) : QTyp :=
  match obs.retEtyp? with
  | some et => ⟨et, false, Predicate.noPred⟩
  | none    => ⟨ETyp.unit, true, Predicate.noPred⟩

-- Context compliance with the critical-only spec all listed critical entries
-- must be present with exactly the specified qualified types. Any unlisted
-- entry that appears in the context (to allow the program to typecheck when
-- referenced) is permitted, but it must be poisoned and carry no predicate.

def ctxMatchesInputSpec (s : InputSpec) (ctx : TypeContext) : Prop :=
  (∀ {l qt}, s.locs.lookup l = some qt → ctx.memEnv.lookup l = some qt) ∧
  (∀ {x qt}, s.vars.lookup x = some qt → ctx.varEnv.lookup x = some qt) ∧
  (∀ {l qt}, ctx.memEnv.lookup l = some qt → ¬ s.locs.hasKey l → qt.poison = true ∧ qt.pred = Predicate.noPred) ∧
  (∀ {x qt}, ctx.varEnv.lookup x = some qt → ¬ s.vars.hasKey x → qt.poison = true ∧ qt.pred = Predicate.noPred)

-- Deep version?
-- def ctxMatchesInputSpecMem (s ctx : MemoryTypeEnv) : Prop :=
--   (∀ {l qt}, s.lookup l = some qt → ctx.lookup l = some qt) ∧
--   (∀ {l qt}, ctx.lookup l = some qt → ¬ s.hasKey l → qt.poison = true ∧ qt.pred = Predicate.noPred)

-- def ctxMatchesInputSpecVars (s ctx : VarTypeEnv) : Prop :=
--   (∀ {l qt}, s.lookup l = some qt → ctx.lookup l = some qt) ∧
--   (∀ {l qt}, ctx.lookup l = some qt → ¬ s.hasKey l → qt.poison = true ∧ qt.pred = Predicate.noPred)

-- def ctxMatchesInputSpecVarsDeep (s ctx : VarTypeEnv) : Prop :=
--   deepVarEnvProperty₂ ctxMatchesInputSpecVars s ctx

-- def ctxMatchesInputSpec (s : InputSpec) (ctx : TypeContext) : Prop :=
--   ctxMatchesInputSpecMem s.locs ctx.memEnv ∧
--   ctxMatchesInputSpecVarsDeep s.vars ctx.varEnv

def inputsConformSpec (s : InputSpec) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) : Prop :=
  (∀ {l}, s.locs.contains l → ∃ a, θ.lookup l = some a ∧ μ.contains a) ∧
  (∀ {x qt v}, s.vars.lookup x = some qt → ρ.lookup x = some v → valueHasETyp θ v qt.etyp)

-- Elementwise predicate for location regime consistency (inductive for easy inversion)
inductive locsRegime (predSat : PredSat) (R : Regime) (μ : Memory) (θ : RealizationMap) : (Loc × QTyp) → Prop where
  | noPred_ok (entry : Loc × QTyp)
      (hpred : qtypGuardTag entry.snd = none) :
      locsRegime predSat R μ θ entry
  -- Guard-only predicates impose no regime consistency beyond tag presence in S
  | guardOnly_ok (entry : Loc × QTyp) (k : Tag)
      (hgo : entry.snd.pred = Predicate.guardOnly k) :
      locsRegime predSat R μ θ entry
  -- Guard-closure predicates must align with the regime: holds iff R(k)=true
  | withPred_ok (entry : Loc × QTyp) (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : List (Name × QTyp))
      (a : Address) (n : Int) (b : Bool)
      (hclos : entry.snd.pred = Predicate.guardClosure k arg_name pred_body var_env)
      (hregime : R k = some b)
      (hreal : θ.lookup entry.fst = some a)
      (hmem : μ.lookup a = some n)
      (hconsist : (b = true → qtypPredHolds predSat entry.snd μ (Value.num n)) ∧
                  (b = false → ¬qtypPredHolds predSat entry.snd μ (Value.num n))) :
      locsRegime predSat R μ θ entry

-- Elementwise predicate for variable regime consistency (inductive for easy inversion)
inductive varsRegime (predSat : PredSat) (R : Regime) (μ : Memory) (ρ : VarEnv) : (Name × QTyp) → Prop where
  | noPred_ok (entry : Name × QTyp)
      (hpred : qtypGuardTag entry.snd = none) :
      varsRegime predSat R μ ρ entry
  -- Guard-only predicates impose no regime consistency beyond tag presence in S
  | guardOnly_ok (entry : Name × QTyp) (k : Tag)
      (hgo : entry.snd.pred = Predicate.guardOnly k) :
      varsRegime predSat R μ ρ entry
  -- Guard-closure predicates must align with the regime: holds iff R(k)=true
  | withPred_ok (entry : Name × QTyp) (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : List (Name × QTyp))
      (v : Value) (b : Bool)
      (hclos : entry.snd.pred = Predicate.guardClosure k arg_name pred_body var_env)
      (hregime : R k = some b)
      (hvar : ρ.lookup entry.fst = some v)
      (hconsist : (b = true → qtypPredHolds predSat entry.snd μ v) ∧
                  (b = false → ¬qtypPredHolds predSat entry.snd μ v)) :
      varsRegime predSat R μ ρ entry

-- Regime consistency (via Forall over lists).
-- The regime must be defined for all critical inputs in the spec.
def consistentRegimeSpec (predSat : PredSat) (R : Regime) (s : InputSpec) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) : Prop :=
  List.Forall (locsRegime predSat R μ θ) s.locs.toList ∧
  List.Forall (varsRegime predSat R μ ρ) s.vars

-- Two values agree under a given regime and memory environments
  inductive agreeValueUnder (predSat : PredSat) (R : Regime) (μ₁ : Memory) (μ₂ : Memory)
      (θ₁ θ₂ : RealizationMap)
      (qt: QTyp) (v₁ v₂ : Value) : Prop where
  | noPred_eq
      (hpred : qtypGuardTag qt = none)
      (hnotref : ¬ (∃ (t : ETyp) (ls : LocSet), qt.etyp = ETyp.ref t ls))
      (hagree : v₁ = v₂) :
      agreeValueUnder predSat R μ₁ μ₂ θ₁ θ₂ qt v₁ v₂
  | noPred_ref {t : ETyp} {ls : LocSet} {l₁ l₂ : Loc} {a₁ a₂ : Address}
      (hetyp : qt.etyp = ETyp.ref t ls)
      (hpred : qtypGuardTag qt = none)
      (hlookup1 : θ₁.lookup l₁ = some a₁)
      (hin1 : l₁ ∈ ls)
      (hv1 : v₁ = Value.loc a₁)
      (hlookup2 : θ₂.lookup l₂ = some a₂)
      (hin2 : l₂ ∈ ls)
      (hv2 : v₂ = Value.loc a₂) :
      agreeValueUnder predSat R μ₁ μ₂ θ₁ θ₂ qt v₁ v₂
  | withPred_true_eq (k : Tag)
      (htag : qtypGuardTag qt = some k)
      (hregime : R k = some true)
      (hagree : v₁ = v₂) :
      agreeValueUnder predSat R μ₁ μ₂ θ₁ θ₂ qt v₁ v₂
  -- False-regime case for guard-closures: both runs fail the predicate
  | withPred_false_both_fail (k : Tag)
      (hclos : isGuardClosure qt)
      (htag : qtypGuardTag qt = some k)
      (hregime : R k = some false)
      (hfail1 : ¬qtypPredHolds predSat qt μ₁ v₁)
      (hfail2 : ¬qtypPredHolds predSat qt μ₂ v₂) :
      agreeValueUnder predSat R μ₁ μ₂ θ₁ θ₂ qt v₁ v₂
  -- False-regime case for guard-only: unconstrained (values may differ)
  | guardOnly_false_any (k : Tag)
      (hgo : qt.pred = Predicate.guardOnly k)
      (hregime : R k = some false) :
      agreeValueUnder predSat R μ₁ μ₂ θ₁ θ₂ qt v₁ v₂

-- Two initial states agree on a critical location under a given regime.
-- Refactored to use agreeValueUnder
--
-- Note on the two “option layers” (Issue #76):
-- (1) `θ.lookup l` says whether logical `l` is realised in this run.
-- (2) `μ.lookup a` says whether concrete address `a` exists in the heap.
-- We model “unallocated/ghost in this run” via (1) being `none` (constructor `both_unrealized`),
-- not via (2) being `none`. The ill-formed case “`θ(l)=some a` but `μ.lookup a = none`” is
-- ruled out by well-formedness premises such as `runtimeInstantiatesCtx` / `inputsConformSpec`.
inductive agreeLocUnder (predSat : PredSat) (R : Regime) (μ₁ : Memory) (μ₂ : Memory)
    (θ₁ θ₂ : RealizationMap)
    : (Loc × QTyp) → Prop where
  | agree_values (l : Loc) (qt : QTyp) (a₁ a₂ : Address) (n₁ n₂ : Nat)
      (hreal1 : θ₁.lookup l = some a₁)
      (hreal2 : θ₂.lookup l = some a₂)
      (hlookup1 : μ₁.lookup a₁ = some n₁)
      (hlookup2 : μ₂.lookup a₂ = some n₂)
      (hagree : agreeValueUnder predSat R μ₁ μ₂ θ₁ θ₂ qt (Value.num n₁) (Value.num n₂)) :
      agreeLocUnder predSat R μ₁ μ₂ θ₁ θ₂ (l, qt)
  | both_unrealized (l : Loc) (qt : QTyp)
      (hreal1 : θ₁.lookup l = none)
      (hreal2 : θ₂.lookup l = none) :
      agreeLocUnder predSat R μ₁ μ₂ θ₁ θ₂ (l, qt)

-- Two initial states agree on a critical variable under a given regime.
-- Refactored to use agreeValueUnder
inductive agreeVarUnder (predSat : PredSat) (R : Regime) (μ₁ : Memory) (ρ₁ : VarEnv) (μ₂ : Memory) (ρ₂ : VarEnv)
    (θ₁ θ₂ : RealizationMap)
    : (Name × QTyp) → Prop where
  | agree_values (x : Name) (qt : QTyp) (v₁ v₂ : Value)
      (hlookup1 : ρ₁.lookup x = some v₁)
      (hlookup2 : ρ₂.lookup x = some v₂)
      (hagree : agreeValueUnder predSat R μ₁ μ₂ θ₁ θ₂ qt v₁ v₂) :
      agreeVarUnder predSat R μ₁ ρ₁ μ₂ ρ₂ θ₁ θ₂ (x, qt)
  | both_none (x : Name) (qt : QTyp)
      (hlookup1 : ρ₁.lookup x = none)
      (hlookup2 : ρ₂.lookup x = none) :
      agreeVarUnder predSat R μ₁ ρ₁ μ₂ ρ₂ θ₁ θ₂ (x, qt)

-- Two initial states agree on critical inputs under a given regime.
def agreeOnCriticalInputsUnderRegimeSpec
  (predSat : PredSat) (R : Regime) (s : InputSpec)
  (μ₁ : Memory) (ρ₁ : VarEnv) (θ₁ : RealizationMap)
  (μ₂ : Memory) (ρ₂ : VarEnv) (θ₂ : RealizationMap) : Prop :=
  List.Forall (agreeLocUnder predSat R μ₁ μ₂ θ₁ θ₂) s.locs.toList ∧
  List.Forall (agreeVarUnder predSat R μ₁ ρ₁ μ₂ ρ₂ θ₁ θ₂) s.vars

-- Typing results must satisfy the observable constraints:
def ObsConstraints (obs : ObservableSpec) (res : TypeResult) : Prop :=
  -- (i) If the return value is observable, require the inferred return
  -- enriched type to match the observable enriched type. If the return
  -- is not observable, no constraint is imposed on the result type.
  let retMatches : Prop :=
    ∀ et, obs.retEtyp? = some et → res.qualType.etyp = et ∧ res.qualType.poison = false
  -- (ii) the memory must contain entries for each observable location
  -- with the correct enriched type
  let memMatches : Prop :=
    ∀ l et, obs.locs.lookup l = some et → ∃ qt, (res.memEnv'.lookup l = some qt ∧ qt.etyp = et ∧ qt.poison = false)
  retMatches ∧ memMatches

-- ------------------------ Top-level definitions -------------------------------

-- Non-Interference property
-- ==========================
def NonInterferenceSpec (e : Expr) (s : InputSpec) (obs : ObservableSpec) (ctx : TypeContext) (predSat : PredSat) : Prop :=
  ∀ (μ₁ μ₂ : Memory) (ρ₁ ρ₂ : VarEnv) (θ₁ θ₂ : RealizationMap) (l : Address) (pm : Bool) (R : Regime)
    (cf₁ cf₂ : Config) (o₁ o₂ : Value),
    wfRegime R s →
    inputsConformSpec s μ₁ ρ₁ θ₁ →  inputsConformSpec s μ₂ ρ₂ θ₂ →
    runtimeInstantiatesCtx ctx μ₁ ρ₁ θ₁ →  runtimeInstantiatesCtx ctx μ₂ ρ₂ θ₂ →
    consistentRegimeSpec predSat R s μ₁ ρ₁ θ₁ →  consistentRegimeSpec predSat R s μ₂ ρ₂ θ₂ →
    agreeOnCriticalInputsUnderRegimeSpec predSat R s μ₁ ρ₁ θ₁ μ₂ ρ₂ θ₂ →
    terminatesTo e { memory := μ₁, varEnv := ρ₁, nextLoc := l, pureMode := pm } cf₁ o₁ →
    terminatesTo e { memory := μ₂, varEnv := ρ₂, nextLoc := l, pureMode := pm } cf₂ o₂ →
    observablesEqual obs θ₁ θ₂ cf₁ cf₂ o₁ o₂

-- Type system enforces Non-Interference
def TypeSystemEnforcesNonInterference_spec
  (e : Expr) (s : InputSpec) (obs : ObservableSpec) :=
  wfInputSpec s →
  wfObsSpec obs →
  ∀ (ctx : TypeContext),
      ctxMatchesInputSpec s ctx →
      ctx.pc = false → -- we start from clean program counter
      ctx.tagEnv = {} → -- we start with empty tag environment
      ∀ (predSat : PredSat),
        PredSatLaws predSat →
        ((∃ (fuel : Nat) (res : TypeResult),
          typecheck ctx e fuel = .ok res ∧
          ObsConstraints obs res) →
          NonInterferenceSpec e s obs ctx predSat)
