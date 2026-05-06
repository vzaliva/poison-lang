-- Fault-Robustness properties for the poison language

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanPoison.BigStep
import LeanProofs.RegimeConsistency
import LeanProofs.ExternTypingAssumptions
import LeanProofs.TypeSafety
import LeanProofs.SemanticsProperties
import Mathlib.Data.List.Forall2
import Std.Data.ExtTreeMap
open Std

-- ================================================================
-- Fault-Robustness (semantic formulation)
-- ================================================================

private abbrev MemoryETypEnv := ExtTreeMap Loc ETyp
namespace MemoryETypEnv

  @[inline] def lookup (m : MemoryETypEnv) (l : Loc) : Option ETyp :=
    m.get? l

  @[inline] def update (m : MemoryETypEnv) (l : Loc) (qt : ETyp) : MemoryETypEnv :=
    m.insert l qt

  /-- `m` contains a binding for `l`. -/
  def hasKey (m : MemoryETypEnv) (l : Loc) : Prop :=
    m.contains l

  instance : BEq MemoryETypEnv where
    beq m₁ m₂ := (ExtTreeMap.toList m₁) == (ExtTreeMap.toList m₂)

  instance : Repr MemoryETypEnv where
    reprPrec m _ := s!"ofList {repr (ExtTreeMap.toList m)}"

end MemoryETypEnv

def nonClosureQTyp (qt : QTyp) : Prop :=
  match qt.etyp with
  | ETyp.arrow _ _ _ _ => False
  | ETyp.parrow _ _ _ _ => False
  | _ => True

-- What parts of the final state are observable
structure ObservableSpec where
  locs       : MemoryETypEnv
  retEtyp?   : Option ETyp
deriving Repr

-- Critical inputs specification
structure InputSpec where
  locs : MemoryTypeEnv
  vars : VarTypeEnv
deriving Repr

-- Output realizations should include every location in the spec.
/-- Keys are unique in both `s.locs` (addresses) and `s.vars` (names). -/
private def inputKeysUnique (vars : VarTypeEnv) : Prop :=
  vars.keys.Nodup
  -- `vars` is an ExtTreeMap, so keys are already unique

-- Extract all guard tags from the input specification (functional version for wfRegime)
def inputSpecTags (s : InputSpec) : List Tag :=
  let locTags := s.locs.toList.filterMap (fun (_, e) => qtypGuardTag ⟨ETyp.int, e.poison, e.pred⟩)
  let varTags := s.vars.toList.filterMap (qtypGuardTag ·.2)
  locTags ++ varTags

-- Predicate-shape helpers
def wfRegime (R : Regime) (s : InputSpec) : Prop :=
  let tags := inputSpecTags s
  (∀ k, k ∈ tags → (R.lookup? k).isSome) ∧
  (∀ k, (R.lookup? k).isSome → k ∈ tags)

private inductive wfRegimeForReturn (R : Regime) : QTyp → Prop where
  | noPred (retType : QTyp)
      (hpred : retType.pred = Predicate.noPred) :
      wfRegimeForReturn R retType
  | guardOnly (retType : QTyp) (k : Tag)
      (hpred : retType.pred = Predicate.guardOnly k)
      (hregime : R.lookup? k = some true) :
      wfRegimeForReturn R retType
  | guardClosure (retType : QTyp) (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv)
      (hpred : retType.pred = Predicate.guardClosure k arg_name pred_body var_env)
      (hregime : R.lookup? k = some true) :
      wfRegimeForReturn R retType

-- Helper: equality of observables in the final states.
-- For references, observability is via the logical-location set, not concrete addresses.
def observablesEqual (obs : ObservableSpec)
    (θ₁ θ₂ : RealizationMap)
    (c₁ c₂ : Config) (o₁ o₂ : Value) : Prop :=
  let sameMem : Prop :=
    ∀ {l et}, obs.locs.lookup l = some et →
      (∃ a₁ a₂,
        θ₁.lookup l = some a₁ ∧
        θ₂.lookup l = some a₂ ∧
        c₁.memory.lookup a₁ = c₂.memory.lookup a₂)
      ∨
      (θ₁.lookup l = none ∧ θ₂.lookup l = none)
  let sameRet : Prop :=
    match obs.retEtyp? with
    | none => True
    | some (ETyp.ref ls) =>
        (∃ l₁ a₁, l₁ ∈ ls ∧ θ₁.lookup l₁ = some a₁ ∧ o₁ = Value.loc a₁) ∧
        (∃ l₂ a₂, l₂ ∈ ls ∧ θ₂.lookup l₂ = some a₂ ∧ o₂ = Value.loc a₂)
    | some _ => o₁ = o₂
  sameMem ∧ sameRet

-- Helper: check if guard tag present
private def hasGuardTag (p : Predicate) : Bool :=
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
     | FnTClosure.regular _ _ env => P (VarTypeEnv.ofCaptured env)
     | FnTClosure.extern _ _ _ _ env => P (VarTypeEnv.ofCaptured env))) →
    deepQTypProperty P qt
  | parrow (P : VarTypeEnv → Prop) (qt : QTyp) :
    (∃ st1 st2 p tcls, qt.etyp = ETyp.parrow st1 st2 p tcls ∧
     (∀ tcl ∈ tcls, match tcl with
     | PFnTClosure.regular _ _ env => P (VarTypeEnv.ofCaptured env)
     | PFnTClosure.extern _ _ _ env => P (VarTypeEnv.ofCaptured env))) →
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
    (∃ st1 st2 p tcls₁,
      qt₁.etyp = ETyp.arrow st1 st2 p tcls₁ ∧
      (∀ tcl₁ ∈ tcls₁, match tcl₁ with
      | FnTClosure.regular _ _ env₁ =>
          ∃ st1' st2' p' tcls₂,
            qt₂.etyp = ETyp.arrow st1' st2' p' tcls₂ ∧
            (∀ tcl₂ ∈ tcls₂, match tcl₂ with
            | FnTClosure.regular _ _ env₂ =>
                P (VarTypeEnv.ofCaptured env₁) (VarTypeEnv.ofCaptured env₂)
            | FnTClosure.extern _ _ _ _ env₂ =>
                P (VarTypeEnv.ofCaptured env₁) (VarTypeEnv.ofCaptured env₂))
      | FnTClosure.extern _ _ _ _ env₁ =>
          ∃ st1' st2' p' tcls₂,
            qt₂.etyp = ETyp.arrow st1' st2' p' tcls₂ ∧
            (∀ tcl₂ ∈ tcls₂, match tcl₂ with
            | FnTClosure.regular _ _ env₂ =>
                P (VarTypeEnv.ofCaptured env₁) (VarTypeEnv.ofCaptured env₂)
            | FnTClosure.extern _ _ _ _ env₂ =>
                P (VarTypeEnv.ofCaptured env₁) (VarTypeEnv.ofCaptured env₂)))) →
    deepQTypProperty₂ P qt₁ qt₂
  | parrow (P : VarTypeEnv → VarTypeEnv → Prop) (qt₁ qt₂ : QTyp) :
    (∃ st1 st2 p tcls₁,
      qt₁.etyp = ETyp.parrow st1 st2 p tcls₁ ∧
      (∀ tcl₁ ∈ tcls₁, match tcl₁ with
      | PFnTClosure.regular _ _ env₁ =>
          ∃ st1' st2' p' tcls₂,
            qt₂.etyp = ETyp.parrow st1' st2' p' tcls₂ ∧
            (∀ tcl₂ ∈ tcls₂, match tcl₂ with
            | PFnTClosure.regular _ _ env₂ =>
                P (VarTypeEnv.ofCaptured env₁) (VarTypeEnv.ofCaptured env₂)
            | PFnTClosure.extern _ _ _ env₂ =>
                P (VarTypeEnv.ofCaptured env₁) (VarTypeEnv.ofCaptured env₂))
      | PFnTClosure.extern _ _ _ env₁ =>
          ∃ st1' st2' p' tcls₂,
            qt₂.etyp = ETyp.parrow st1' st2' p' tcls₂ ∧
            (∀ tcl₂ ∈ tcls₂, match tcl₂ with
            | PFnTClosure.regular _ _ env₂ =>
                P (VarTypeEnv.ofCaptured env₁) (VarTypeEnv.ofCaptured env₂)
            | PFnTClosure.extern _ _ _ env₂ =>
                P (VarTypeEnv.ofCaptured env₁) (VarTypeEnv.ofCaptured env₂)))) →
    deepQTypProperty₂ P qt₁ qt₂
  | other (P : VarTypeEnv → VarTypeEnv → Prop) (qt₁ qt₂ : QTyp) :
    (nonClosureQTyp qt₁ ∨ nonClosureQTyp qt₂) →
    deepQTypProperty₂ P qt₁ qt₂
end

-- Well-formedness: memory stores integers at critical locations; additionally,
-- align predicate and poison for critical inputs: no predicate ⇒ clean;
-- predicate present ⇒ initially poisoned.
private def wfInputSpecMem (locs : MemoryTypeEnv) : Prop :=
  ∀ l qt, locs.lookup l = some qt →
    qt.etyp = ETyp.int ∧ qt.poison = hasGuardTag qt.pred

private def wfInputSpecVars (vars : VarTypeEnv) : Prop :=
  inputKeysUnique vars ∧
  (∀ x qt, vars.lookup x = some qt →
     qt.poison = hasGuardTag qt.pred)

private def wfInputSpecVarsDeep (vars : VarTypeEnv) : Prop :=
  deepVarEnvProperty wfInputSpecVars vars

/-- Critical input variables are first-order values (no function closures).
    This keeps the user-provided input specification focused on explicit data,
    not hidden captured runtime environments. -/
private def wfInputSpecVarsFirstOrder (vars : VarTypeEnv) : Prop :=
  ∀ x qt, vars.lookup x = some qt → nonClosureQTyp qt

def wfInputSpec (s : InputSpec) : Prop :=
  wfInputSpecMem s.locs ∧ wfInputSpecVarsDeep s.vars ∧ wfInputSpecVarsFirstOrder s.vars

-- Well-formedness: observable spec
-- Return values of function type are not treated as observables.
def wfObsSpec (obs : ObservableSpec) : Prop :=
  match obs.retEtyp? with
  | none => True
  | some et => et.isFunctionType = false

-- Derive return-observability and a conservative QTyp for the return from ObservableSpec.
def ctxMatchesInputSpec (s : InputSpec) (ctx : TypeContext) : Prop :=
  (∀ {l qt}, s.locs.lookup l = some qt → ctx.memEnv.lookup l = some qt) ∧
  (∀ {x qt}, s.vars.lookup x = some qt → ctx.varEnv.lookup x = some qt) ∧
  (∀ l qt k, ctx.memEnv.lookup l = some qt → qtypGuardTag qt = some k →
    ¬ s.locs.hasKey l → k ∉ inputSpecTags s) ∧
  deepVarEnvProperty (fun env =>
    ∀ x qt k, env.lookup x = some qt → qtypGuardTag qt = some k →
      ¬ s.vars.hasKey x → k ∉ inputSpecTags s) ctx.varEnv

private def inputsConformSpec (s : InputSpec) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) : Prop :=
  (∀ {l a}, s.locs.contains l → θ.lookup l = some a → μ.contains a) ∧
  (∀ {x qt v}, s.vars.lookup x = some qt → ρ.lookup x = some v → valueHasETyp θ v qt.etyp)

-- deepValueQTypProperty, capturedVarsRegimeProperty, and closureCapturedVarsRegime
-- are defined in RegimeConsistency.lean (upstream of this file, to avoid
-- circular imports with consistentWithRegime).

-- Regime consistency for a single (QTyp, Value) pair
-- This tracks whether a value's predicate is consistent with the regime
inductive valueConsistentWithRegime (predSat : PredSat) (R : Regime)
    (qt : QTyp) (μ : Memory) (θ : RealizationMap) (v : Value) : Prop where
  | noTag :
      qtypGuardTag qt = none →
      closureCapturedVarsRegime predSat R qt μ θ v →
      valueConsistentWithRegime predSat R qt μ θ v
  | guardOnly_ok (k : Tag) :
      qt.pred = Predicate.guardOnly k →
      closureCapturedVarsRegime predSat R qt μ θ v →
      valueConsistentWithRegime predSat R qt μ θ v
  | notInRegime (k : Tag) :
      qtypGuardTag qt = some k →
      R.lookup? k = none →
      closureCapturedVarsRegime predSat R qt μ θ v →
      valueConsistentWithRegime predSat R qt μ θ v
  | inRegimeTrue (k : Tag) :
      qtypGuardTag qt = some k →
      R.lookup? k = some true →
      qtypPredHolds predSat qt μ v →
      closureCapturedVarsRegime predSat R qt μ θ v →
      valueConsistentWithRegime predSat R qt μ θ v
  | inRegimeFalse (k : Tag) :
      qtypGuardTag qt = some k →
      R.lookup? k = some false →
      ¬qtypPredHolds predSat qt μ v →
      closureCapturedVarsRegime predSat R qt μ θ v →
      valueConsistentWithRegime predSat R qt μ θ v

-- Monotonicity lemmas for regime predicates
-- When Regime.monotoneStep R R' and the lookup values match, we can transfer locsRegime/varsRegime

lemma locsRegime_monotone {predSat : PredSat} {R R' : Regime} {μ : Memory} {θ : RealizationMap}
    {entry : Loc × QTyp} {k : Tag} {b : Bool}
    (h_mono : Regime.monotoneStep R R')
    (hguard : qtypGuardTag entry.snd = some k)
    (hkR' : R'.lookup? k = some b)
    (h_loc : locsRegime predSat R μ θ entry) :
    locsRegime predSat R' μ θ entry := by
  cases h_loc with
  | noPred_ok hpred =>
      exact locsRegime.noPred_ok entry hpred
  | guardOnly_ok k' hgo =>
      exact locsRegime.guardOnly_ok entry k' hgo
  | withPred_ok k' arg_name pred_body var_env a n b' hclos hregime hreal hmem hconsist =>
      -- hregime : R.lookup? k' = some b' for the guard tag k' in the predicate
      -- From hclos, qtypGuardTag entry.snd = some k', so k' = k by hguard
      have hk_eq : k' = k := by
        simp only [qtypGuardTag, hclos] at hguard
        exact Option.some.inj hguard
      -- By monotoneStep.entries_preserved: R.lookup? k' = some b' → R'.lookup? k' = some b' ∨ R'.lookup? k' = none
      have h_cases := h_mono.1 k' b' hregime
      cases h_cases with
      | inl h_eq =>
          -- R'.lookup? k' = some b', can construct the R' version
          exact locsRegime.withPred_ok entry k' arg_name pred_body var_env a n b' hclos h_eq hreal hmem hconsist
      | inr h_none =>
          -- R'.lookup? k' = none contradicts hkR' since k' = k
          rw [hk_eq] at h_none
          simp [h_none] at hkR'

lemma varsRegime_monotone {predSat : PredSat} {R R' : Regime} {μ : Memory} {ρ : VarEnv}
    {entry : Name × QTyp} {k : Tag} {b : Bool}
    (h_mono : Regime.monotoneStep R R')
    (hguard : qtypGuardTag entry.snd = some k)
    (hkR' : R'.lookup? k = some b)
    (h_var : varsRegime predSat R μ ρ entry) :
    varsRegime predSat R' μ ρ entry := by
  cases h_var with
  | noPred_ok hpred =>
      exact varsRegime.noPred_ok entry hpred
  | guardOnly_ok k' hgo =>
      exact varsRegime.guardOnly_ok entry k' hgo
  | withPred_ok k' arg_name pred_body var_env v b' hclos hregime hvar hconsist =>
      have hk_eq : k' = k := by
        simp only [qtypGuardTag, hclos] at hguard
        exact Option.some.inj hguard
      have h_cases := h_mono.1 k' b' hregime
      cases h_cases with
      | inl h_eq =>
          exact varsRegime.withPred_ok entry k' arg_name pred_body var_env v b' hclos h_eq hvar hconsist
      | inr h_none =>
          rw [hk_eq] at h_none
          simp [h_none] at hkR'

-- Regime consistency (via Forall over lists).
-- The regime must be defined for all critical inputs in the spec.
def memEnvToLocQTypList (m : MemoryTypeEnv) : List (Loc × QTyp) :=
  m.toList.map (fun (l, e) => (l, ⟨ETyp.int, e.poison, e.pred⟩))

def consistentRegimeSpec (predSat : PredSat) (R : Regime) (s : InputSpec) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) : Prop :=
  List.Forall (locsRegime predSat R μ θ) (memEnvToLocQTypList s.locs) ∧
  List.Forall (varsRegime predSat R μ ρ) s.vars.toList

-- A qualified type is considered clean under regime R if it is clean outright
-- or if its guard tag is true under R (de-poisoned).
-- Guard tags may de-poison only non-function types: for functions, outer poison
-- must be literally clean; guard tags do not make a function clean-under-R.
--
-- This is the "clean-under-R" predicate used by the step theorem.
inductive qtypCleanUnder (R : Regime) : QTyp → Prop where
  | clean {qt : QTyp} (hpoison : qt.poison = false) :
      qtypCleanUnder R qt
  | guard {qt : QTyp} (k : Tag)
      (htag : qtypGuardTag qt = some k)
      (hregime : R.lookup? k = some true)
      (hnotfun : qt.etyp.isFunctionType = false) :
      qtypCleanUnder R qt

-- Extract internal poison from arrow/parrow types.
-- For non-function types, returns none.
def getInternalPoison (et : ETyp) : Option Poison :=
  match et with
  | ETyp.arrow _ _ p _ => some p
  | ETyp.parrow _ _ p _ => some p
  | _ => none

-- Internal poison cleanliness for function types.
-- For arrow/parrow types, internal poison is clean if and only if the
-- internal poison boolean is literally false. Guard tags do NOT de-poison
-- internal arrow poison.
-- For non-function types, this is vacuously true.
def internalPoisonClean (qt : QTyp) : Prop :=
  match getInternalPoison qt.etyp with
  | none => True        -- non-function types
  | some p => p = false -- clean iff internal poison is literally false

-- Lemmas about preserving dirty internal poison through joinETyps

/-- If an arrow type has dirty internal poison (p = true), then joinETyps preserves this. -/
lemma joinETyps_preserves_dirty_arrow
    {st1 st2 : Typ} {p1 : Poison} {tcls1 : List FnTClosure}
    {t2 : ETyp} {p1' p2' : Poison}
    (hDirty : p1 = true) :
    getInternalPoison (joinETyps (ETyp.arrow st1 st2 p1 tcls1) t2 p1' p2') = some true := by
  cases t2 with
  | arrow st1' st2' p2 tcls2 =>
      simp only [joinETyps]
      split
      · -- Compatible signatures: result is arrow with joinPoison p1 p2
        simp [getInternalPoison, hDirty, joinPoison]
      · -- Incompatible: result is original arrow with p1
        simp [getInternalPoison, hDirty]
  | parrow _ _ _ _ | int | bool | unit | string | ref _ =>
      -- t2 is not arrow: joinETyps returns left operand unchanged
      simp [joinETyps, getInternalPoison, hDirty]

/-- If a parrow type has dirty internal poison (p = true), then joinETyps preserves this. -/
lemma joinETyps_preserves_dirty_parrow
    {st1 st2 : Typ} {p1 : Poison} {tcls1 : List PFnTClosure}
    {t2 : ETyp} {p1' p2' : Poison}
    (hDirty : p1 = true) :
    getInternalPoison (joinETyps (ETyp.parrow st1 st2 p1 tcls1) t2 p1' p2') = some true := by
  cases t2 with
  | parrow st1' st2' p2 tcls2 =>
      simp only [joinETyps]
      split
      · -- Compatible signatures: result is parrow with joinPoison p1 p2
        simp [getInternalPoison, hDirty, joinPoison]
      · -- Incompatible: result is original parrow with p1
        simp [getInternalPoison, hDirty]
  | arrow _ _ _ _ | int | bool | unit | string | ref _ =>
      -- t2 is not parrow: joinETyps returns left operand unchanged
      simp [joinETyps, getInternalPoison, hDirty]

-- Two values agree under a given regime and memory environments.
-- Clean values must agree; poisoned values may agree vacuously depending on regime.
/-- Path D payload: direct member-level active-guard facts
for a fixed captured member `(σcap, ρcap)` at the current regime/memory. -/
def MemberVarsRegimeEvidence
    (predSat : PredSat) (R : Regime) (μ : Memory)
    (σcap : CapturedVarEnv) (ρcap : VarEnv) : Prop :=
  ∀ (y : Name) (qt_y : QTyp) (k_y : Tag) (v_y : Value),
    (VarTypeEnv.ofCaptured σcap).lookup y = some qt_y →
    ρcap.lookup y = some v_y →
    qtypGuardTag qt_y = some k_y →
    R.lookup? k_y ≠ none →
    varsRegime predSat R μ ρcap (y, qt_y)

/-- Path D payload: direct recursive captured-value
closure-regime facts for a fixed captured member `(σcap, ρcap)` at the current regime/memory. -/
def MemberCvcrEvidence
    (predSat : PredSat) (R : Regime) (μ : Memory) (θ : RealizationMap)
    (σcap : CapturedVarEnv) (ρcap : VarEnv) : Prop :=
  ∀ (y : Name) (qt_y : QTyp) (v_y : Value),
    (VarTypeEnv.ofCaptured σcap).lookup y = some qt_y →
    ρcap.lookup y = some v_y →
    closureCapturedVarsRegime predSat R qt_y μ θ v_y

mutual
  inductive agreeValueUnder (predSat : PredSat) (R : Regime) (μ₁ : Memory) (μ₂ : Memory)
      (θ₁ θ₂ : RealizationMap) :
      QTyp → Value → Value → Prop where
    -- Non-ref/non-arrow cases:
    | clean_eq_nonref_nonarrow
        {qt : QTyp} {v₁ v₂ : Value}
        (hpoison : qt.poison = false)
        (hnotfun : qt.etyp.isFunctionType = false)
        (hnotref : ¬ (∃ (ls : LocSet), qt.etyp = ETyp.ref ls))
        (hagree : v₁ = v₂) :
        agreeValueUnder predSat R μ₁ μ₂ θ₁ θ₂ qt v₁ v₂
    -- Arrow cases:
    -- Closure agreement cases are gated on INTERNAL poison, not outer poison.
    -- When internal poison is clean, we require same body and captured environment agreement.
    -- When internal poison is dirty, we impose no constraints (vacuous agreement).
    | clean_internal_arrow {st1 st2 : Typ} {p : Poison} {tcls : List FnTClosure}
        {qt : QTyp} {tcl : FnTClosure} {x : Name} {body : Expr} {σcap : CapturedVarEnv} {ρcap₁ ρcap₂ : VarEnv}
        {v₁ v₂ : Value}
        (hclean_internal : internalPoisonClean qt)
        (hetyp : qt.etyp = ETyp.arrow st1 st2 p tcls)
        (htcl : tcl ∈ tcls)
        (hmatch : tcl = FnTClosure.regular x body σcap)
        (hcap : agreeCapturedEnv predSat R μ₁ μ₂ θ₁ θ₂ σcap ρcap₁ ρcap₂)
        (hmemberVars₁ : MemberVarsRegimeEvidence predSat R μ₁ σcap ρcap₁)
        (hmemberCvcr₁ : MemberCvcrEvidence predSat R μ₁ θ₁ σcap ρcap₁)
        (hmemberVars₂ : MemberVarsRegimeEvidence predSat R μ₂ σcap ρcap₂)
        (hmemberCvcr₂ : MemberCvcrEvidence predSat R μ₂ θ₂ σcap ρcap₂)
        (hv₁ : v₁ = Value.closure x body ρcap₁)
        (hv₂ : v₂ = Value.closure x body ρcap₂) :
        agreeValueUnder predSat R μ₁ μ₂ θ₁ θ₂ qt v₁ v₂
    | clean_internal_arrow_extern
        {id : ExternId} {x y : Name} {argTyp : Typ} {retSpec : ExternReturn}
        {effects : List Effect} {p : Poison} {tcls : List FnTClosure}
        {qt : QTyp} {tcl : FnTClosure} {σcap : CapturedVarEnv} {ρcap₁ ρcap₂ : VarEnv}
        {v₁ v₂ : Value}
        (hclean_internal : internalPoisonClean qt)
        (hetyp : qt.etyp = ETyp.arrow argTyp (parseReturnType retSpec) p tcls)
        (htcl : tcl ∈ tcls)
        (hmatch : tcl = FnTClosure.extern id x retSpec effects σcap)
        (hcap : agreeCapturedEnv predSat R μ₁ μ₂ θ₁ θ₂ σcap ρcap₁ ρcap₂)
        (hmemberVars₁ : MemberVarsRegimeEvidence predSat R μ₁ σcap ρcap₁)
        (hmemberCvcr₁ : MemberCvcrEvidence predSat R μ₁ θ₁ σcap ρcap₁)
        (hmemberVars₂ : MemberVarsRegimeEvidence predSat R μ₂ σcap ρcap₂)
        (hmemberCvcr₂ : MemberCvcrEvidence predSat R μ₂ θ₂ σcap ρcap₂)
        (hv₁ : v₁ = Value.closure x (Expr.externFn id y argTyp retSpec effects) ρcap₁)
        (hv₂ : v₂ = Value.closure x (Expr.externFn id y argTyp retSpec effects) ρcap₂) :
        agreeValueUnder predSat R μ₁ μ₂ θ₁ θ₂ qt v₁ v₂
    | dirty_internal_arrow
        {qt : QTyp} {v₁ v₂ : Value}
        (hdirty_internal : ¬ internalPoisonClean qt)
        (hisArrow : qt.etyp.isArrow = true)
        (htyp1 : valueHasETyp θ₁ v₁ qt.etyp)
        (htyp2 : valueHasETyp θ₂ v₂ qt.etyp) :
        agreeValueUnder predSat R μ₁ μ₂ θ₁ θ₂ qt v₁ v₂
    | clean_internal_parrow {st1 st2 : Typ} {p : Poison} {tcls : List PFnTClosure}
        {qt : QTyp} {tcl : PFnTClosure} {x : Name} {body : Expr} {pbody : PExpr} {σcap : CapturedVarEnv} {ρcap₁ ρcap₂ : VarEnv}
        {v₁ v₂ : Value}
        (hclean_internal : internalPoisonClean qt)
        (hetyp : qt.etyp = ETyp.parrow st1 st2 p tcls)
        (htcl : tcl ∈ tcls)
        (hmatch : Expr.toPExpr? body = some pbody ∧ tcl = PFnTClosure.regular x pbody σcap)
        (hcap : agreeCapturedEnv predSat R μ₁ μ₂ θ₁ θ₂ σcap ρcap₁ ρcap₂)
        (hmemberVars₁ : MemberVarsRegimeEvidence predSat R μ₁ σcap ρcap₁)
        (hmemberCvcr₁ : MemberCvcrEvidence predSat R μ₁ θ₁ σcap ρcap₁)
        (hmemberVars₂ : MemberVarsRegimeEvidence predSat R μ₂ σcap ρcap₂)
        (hmemberCvcr₂ : MemberCvcrEvidence predSat R μ₂ θ₂ σcap ρcap₂)
        (hv₁ : v₁ = Value.peClosure x body ρcap₁)
        (hv₂ : v₂ = Value.peClosure x body ρcap₂) :
        agreeValueUnder predSat R μ₁ μ₂ θ₁ θ₂ qt v₁ v₂
    | clean_internal_parrow_extern
        {id : ExternId} {x y : Name} {argTyp : Typ} {retSpec : ExternReturn}
        {p : Poison} {tcls : List PFnTClosure}
        {qt : QTyp} {tcl : PFnTClosure} {σcap : CapturedVarEnv} {ρcap₁ ρcap₂ : VarEnv}
        {v₁ v₂ : Value}
        (hclean_internal : internalPoisonClean qt)
        (hetyp : qt.etyp = ETyp.parrow argTyp (parseReturnType retSpec) p tcls)
        (htcl : tcl ∈ tcls)
        (hmatch : tcl = PFnTClosure.extern id x retSpec σcap)
        (hcap : agreeCapturedEnv predSat R μ₁ μ₂ θ₁ θ₂ σcap ρcap₁ ρcap₂)
        (hmemberVars₁ : MemberVarsRegimeEvidence predSat R μ₁ σcap ρcap₁)
        (hmemberCvcr₁ : MemberCvcrEvidence predSat R μ₁ θ₁ σcap ρcap₁)
        (hmemberVars₂ : MemberVarsRegimeEvidence predSat R μ₂ σcap ρcap₂)
        (hmemberCvcr₂ : MemberCvcrEvidence predSat R μ₂ θ₂ σcap ρcap₂)
        (hv₁ : v₁ = Value.peClosure x (Expr.externPfn id y argTyp retSpec) ρcap₁)
        (hv₂ : v₂ = Value.peClosure x (Expr.externPfn id y argTyp retSpec) ρcap₂) :
        agreeValueUnder predSat R μ₁ μ₂ θ₁ θ₂ qt v₁ v₂
    | dirty_internal_parrow
        {qt : QTyp} {v₁ v₂ : Value}
        (hdirty_internal : ¬ internalPoisonClean qt)
        (hisParrow : qt.etyp.isParrow = true)
        (htyp1 : valueHasETyp θ₁ v₁ qt.etyp)
        (htyp2 : valueHasETyp θ₂ v₂ qt.etyp) :
        agreeValueUnder predSat R μ₁ μ₂ θ₁ θ₂ qt v₁ v₂
    -- Ref cases:
    | clean_ref {ls : LocSet} {l : Loc} {a₁ a₂ : Address}
        {qt : QTyp} {v₁ v₂ : Value}
        (hpoison : qt.poison = false)
        (hetyp : qt.etyp = ETyp.ref ls)
        (hlookup1 : θ₁.lookup l = some a₁)
        (hin : l ∈ ls)
        (hv1 : v₁ = Value.loc a₁)
        (hlookup2 : θ₂.lookup l = some a₂)
        (hv2 : v₂ = Value.loc a₂) :
        agreeValueUnder predSat R μ₁ μ₂ θ₁ θ₂ qt v₁ v₂
    -- de-poisoning cases:
    | withPred_true_eq (k : Tag)
        {qt : QTyp} {v₁ v₂ : Value}
        (htag : qtypGuardTag qt = some k)
        (hregime : R.lookup? k = some true)
        (hnotfun : qt.etyp.isFunctionType = false)
        (hnotref : ¬ (∃ (ls : LocSet), qt.etyp = ETyp.ref ls))
        (hagree : v₁ = v₂) :
        agreeValueUnder predSat R μ₁ μ₂ θ₁ θ₂ qt v₁ v₂
    | withPred_true_ref (k : Tag) {ls : LocSet} {l : Loc} {a₁ a₂ : Address}
        {qt : QTyp} {v₁ v₂ : Value}
        (htag : qtypGuardTag qt = some k)
        (hregime : R.lookup? k = some true)
        (hetyp : qt.etyp = ETyp.ref ls)
        (hlookup1 : θ₁.lookup l = some a₁)
        (hin : l ∈ ls)
        (hv1 : v₁ = Value.loc a₁)
        (hlookup2 : θ₂.lookup l = some a₂)
        (hv2 : v₂ = Value.loc a₂) :
        agreeValueUnder predSat R μ₁ μ₂ θ₁ θ₂ qt v₁ v₂

  /-- Agreement of captured runtime environments w.r.t. the captured typing environment.

  The captured typing environment `σcap` is a finite association list (produced by `VarTypeEnv.toCaptured`).
  For each captured entry `(x, qt)`:
  - if `qt` is clean-under-`R`, then the two runtime captured environments must bind `x` to values `v₁` and
    `v₂` that agree under `agreeValueUnder`;
  - otherwise, there is no agreement obligation for `x`.

  This is defined inductively over the finite list `σcap` to support structural inversion and recursion in
  proofs (e.g. when transporting agreement across realisation-map extensions).
  -/
  inductive agreeCapturedEnv (predSat : PredSat) (R : Regime) (μ₁ : Memory) (μ₂ : Memory)
      (θ₁ θ₂ : RealizationMap) :
      CapturedVarEnv → VarEnv → VarEnv → Prop where
    | nil {ρcap₁ ρcap₂ : VarEnv} :
        agreeCapturedEnv predSat R μ₁ μ₂ θ₁ θ₂ [] ρcap₁ ρcap₂
    | cons_clean {x : Name} {qt : QTyp} {σcap : CapturedVarEnv} {ρcap₁ ρcap₂ : VarEnv}
        {v₁ v₂ : Value}
        (hclean : qtypCleanUnder R qt)
        (hlookup1 : ρcap₁.lookup x = some v₁)
        (hlookup2 : ρcap₂.lookup x = some v₂)
        (htyp1 : valueHasETyp θ₁ v₁ qt.etyp)
        (htyp2 : valueHasETyp θ₂ v₂ qt.etyp)
        (hagree : agreeValueUnder predSat R μ₁ μ₂ θ₁ θ₂ qt v₁ v₂)
        (htail : agreeCapturedEnv predSat R μ₁ μ₂ θ₁ θ₂ σcap ρcap₁ ρcap₂) :
        agreeCapturedEnv predSat R μ₁ μ₂ θ₁ θ₂ ((x, qt) :: σcap) ρcap₁ ρcap₂
    | cons_dirty {x : Name} {qt : QTyp} {σcap : CapturedVarEnv} {ρcap₁ ρcap₂ : VarEnv}
        {v₁ v₂ : Value}
        (hdirty : ¬ qtypCleanUnder R qt)
        (hlookup1 : ρcap₁.lookup x = some v₁)
        (hlookup2 : ρcap₂.lookup x = some v₂)
        (htyp1 : valueHasETyp θ₁ v₁ qt.etyp)
        (htyp2 : valueHasETyp θ₂ v₂ qt.etyp)
        (htail : agreeCapturedEnv predSat R μ₁ μ₂ θ₁ θ₂ σcap ρcap₁ ρcap₂) :
        agreeCapturedEnv predSat R μ₁ μ₂ θ₁ θ₂ ((x, qt) :: σcap) ρcap₁ ρcap₂
end

-- Two initial states agree on a critical location under a given regime.
-- Note: address agreement for refs lives in agreeValueUnder; heap contents
-- agreement is enforced here via memory lookups.
inductive agreeLocUnder (predSat : PredSat) (R : Regime) (μ₁ : Memory) (μ₂ : Memory)
    (θ₁ θ₂ : RealizationMap)
    : (Loc × QTyp) → Prop where
  | agree_values (l : Loc) (qt : QTyp) (a₁ a₂ : Address) (n₁ n₂ : Int)
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
  List.Forall (agreeLocUnder predSat R μ₁ μ₂ θ₁ θ₂) (memEnvToLocQTypList s.locs) ∧
  List.Forall (agreeVarUnder predSat R μ₁ ρ₁ μ₂ ρ₂ θ₁ θ₂) s.vars.toList

-- Typing results must satisfy the observable constraints.
private def ObsConstraints (obs : ObservableSpec) (res : TypeResult) : Prop :=
  let retMatches : Prop :=
    ∀ et, obs.retEtyp? = some et → res.qualType.etyp = et ∧ res.qualType.poison = false
  let memMatches : Prop :=
    ∀ l et, obs.locs.lookup l = some et → ∃ qt, (res.memEnv'.lookup l = some qt ∧ qt.etyp = et ∧ qt.poison = false)
  retMatches ∧ memMatches

-- Agreement on all clean items in the typing context (variables and locations).
-- This is the step-level invariant: only clean-under-R entries must agree.
def agreeOnClean (predSat : PredSat) (R : Regime) (ctx : TypeContext)
  (μ₁ : Memory) (ρ₁ : VarEnv) (θ₁ : RealizationMap)
  (μ₂ : Memory) (ρ₂ : VarEnv) (θ₂ : RealizationMap) : Prop :=
  (∀ l qt, ctx.memEnv.lookup l = some qt → qtypCleanUnder R qt →
    agreeLocUnder predSat R μ₁ μ₂ θ₁ θ₂ (l, qt)) ∧
  (∀ x qt, ctx.varEnv.lookup x = some qt → qtypCleanUnder R qt →
    agreeVarUnder predSat R μ₁ ρ₁ μ₂ ρ₂ θ₁ θ₂ (x, qt))

-- Agreement on trusted inputs: clean context entries not listed in S.
-- This is the FR-specific top-level premise that replaces NI's "unconstrained"
-- non-critical inputs.
def agreeOnTrustedInputs (predSat : PredSat) (R : Regime) (s : InputSpec) (ctx : TypeContext)
  (μ₁ : Memory) (ρ₁ : VarEnv) (θ₁ : RealizationMap)
  (μ₂ : Memory) (ρ₂ : VarEnv) (θ₂ : RealizationMap) : Prop :=
  (∀ l qt, ctx.memEnv.lookup l = some qt → ¬ s.locs.hasKey l → qtypCleanUnder R qt →
    agreeLocUnder predSat R μ₁ μ₂ θ₁ θ₂ (l, qt)) ∧
  (∀ x qt, ctx.varEnv.lookup x = some qt → ¬ s.vars.hasKey x → qtypCleanUnder R qt →
    agreeVarUnder predSat R μ₁ ρ₁ μ₂ ρ₂ θ₁ θ₂ (x, qt))

/-- Unary initialization premise for trusted top-level variables (those not listed in
`InputSpec.vars`): their runtime values already satisfy the deep closure-captured-vars
regime invariant.

This is a top-level FR assumption about the initial state (per run). It complements
`consistentRegimeSpec`, which constrains only critical variables in `s.vars`, so that the
bridge to context-indexed `consistentWithRegime` can discharge the third conjunct for
trusted variables as well. -/
inductive trustedVarsClosureRegimeInit
    (predSat : PredSat) (R : Regime) (s : InputSpec) (ctx : TypeContext)
    (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) : Prop where
  | intro :
      (∀ x qt v, ctx.varEnv.lookup x = some qt → ¬ s.vars.hasKey x → ρ.lookup x = some v →
        closureCapturedVarsRegime predSat R qt μ θ v) →
      trustedVarsClosureRegimeInit predSat R s ctx μ ρ θ

-- ------------------------ Top-level definitions -------------------------------

-- Fault-Robustness property (top-level, spec-driven).
-- Same shape as NI but with an extra premise requiring agreement on trusted inputs.
private def FaultRobustnessSpec (e : Expr) (s : InputSpec) (obs : ObservableSpec) (ctx : TypeContext) (predSat : PredSat) (_tm : TagMeaning) : Prop :=
  ∀ (μ₁ μ₂ : Memory) (ρ₁ ρ₂ : VarEnv) (θ₁ θ₂ : RealizationMap) (a₁ a₂ : Address) (pm : Bool),
    ∀ (cf₁ cf₂ : Config) (o₁ o₂ : Value),
    wfRegime ctx.regime s →
    wfRealizationMap θ₁ →  wfRealizationMap θ₂ →
    wfConfig { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm} →  -- initial config₁ well-formed
    wfConfig { memory := μ₂, varEnv := ρ₂, nextAddr := a₂, pureMode := pm} →  -- initial config₂ well-formed
    inputsConformSpec s μ₁ ρ₁ θ₁ →  inputsConformSpec s μ₂ ρ₂ θ₂ →
    runtimeInstantiatesCtx ctx μ₁ ρ₁ θ₁ →  runtimeInstantiatesCtx ctx μ₂ ρ₂ θ₂ →
    trustedVarsClosureRegimeInit predSat ctx.regime s ctx μ₁ ρ₁ θ₁ →
    trustedVarsClosureRegimeInit predSat ctx.regime s ctx μ₂ ρ₂ θ₂ →
    consistentRegimeSpec predSat ctx.regime s μ₁ ρ₁ θ₁ →  consistentRegimeSpec predSat ctx.regime s μ₂ ρ₂ θ₂ →
    agreeOnCriticalInputsUnderRegimeSpec predSat ctx.regime s μ₁ ρ₁ θ₁ μ₂ ρ₂ θ₂ →
    agreeOnTrustedInputs predSat ctx.regime s ctx μ₁ ρ₁ θ₁ μ₂ ρ₂ θ₂ →
    terminatesTo e { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm} cf₁ o₁ →
    terminatesTo e { memory := μ₂, varEnv := ρ₂, nextAddr := a₂, pureMode := pm} cf₂ o₂ →
    ∃ (θ₁' θ₂' : RealizationMap),
      wfExtendsMap θ₁ θ₁' ∧
      wfExtendsMap θ₂ θ₂' ∧
      observablesEqual obs θ₁' θ₂' cf₁ cf₂ o₁ o₂

/-- Registry-relative fault-robustness property.

    This is the same top-level semantic property as `FaultRobustnessSpec`, but
    the two initial configurations carry an explicit runtime extern registry
    instead of relying on `Config.mk`'s default empty registry.  The proof side
    trusted registry projects to this runtime registry in `LeanProofs.ExternBoundary`. -/
def FaultRobustnessSpecWithRegistry
    (registry : ExternRegistry)
    (e : Expr) (s : InputSpec) (obs : ObservableSpec)
    (ctx : TypeContext) (predSat : PredSat) (_tm : TagMeaning) : Prop :=
  ∀ (μ₁ μ₂ : Memory) (ρ₁ ρ₂ : VarEnv) (θ₁ θ₂ : RealizationMap)
    (a₁ a₂ : Address) (pm : Bool),
    ∀ (cf₁ cf₂ : Config) (o₁ o₂ : Value),
    wfRegime ctx.regime s →
    wfRealizationMap θ₁ → wfRealizationMap θ₂ →
    wfConfig { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm, registry := registry } →
    wfConfig { memory := μ₂, varEnv := ρ₂, nextAddr := a₂, pureMode := pm, registry := registry } →
    inputsConformSpec s μ₁ ρ₁ θ₁ → inputsConformSpec s μ₂ ρ₂ θ₂ →
    runtimeInstantiatesCtx ctx μ₁ ρ₁ θ₁ → runtimeInstantiatesCtx ctx μ₂ ρ₂ θ₂ →
    trustedVarsClosureRegimeInit predSat ctx.regime s ctx μ₁ ρ₁ θ₁ →
    trustedVarsClosureRegimeInit predSat ctx.regime s ctx μ₂ ρ₂ θ₂ →
    consistentRegimeSpec predSat ctx.regime s μ₁ ρ₁ θ₁ →
    consistentRegimeSpec predSat ctx.regime s μ₂ ρ₂ θ₂ →
    agreeOnCriticalInputsUnderRegimeSpec predSat ctx.regime s μ₁ ρ₁ θ₁ μ₂ ρ₂ θ₂ →
    agreeOnTrustedInputs predSat ctx.regime s ctx μ₁ ρ₁ θ₁ μ₂ ρ₂ θ₂ →
    terminatesTo e { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm, registry := registry } cf₁ o₁ →
    terminatesTo e { memory := μ₂, varEnv := ρ₂, nextAddr := a₂, pureMode := pm, registry := registry } cf₂ o₂ →
    ∃ (θ₁' θ₂' : RealizationMap),
      wfExtendsMap θ₁ θ₁' ∧
      wfExtendsMap θ₂ θ₂' ∧
      observablesEqual obs θ₁' θ₂' cf₁ cf₂ o₁ o₂

-- Type system enforces Fault-Robustness.
def TypeSystemEnforcesFaultRobustness_spec
  (e : Expr) (s : InputSpec) (obs : ObservableSpec) :=
  wfInputSpec s →
  wfObsSpec obs →
  ∀ (ctx : TypeContext),
      ctxMatchesInputSpec s ctx →
      wfTypeContext ctx → -- all locations in memEnv are below nextLoc
      ctx.pc = false → -- we start from clean program counter
      ctx.tagEnv = {} → -- we start with empty tag environment
      TagBoundedCtx ctx → -- all tags in varEnv/memEnv predicates and closures are below nextTag
      ∀ (predSat : PredSat) (tm : TagMeaning),
        wfTagMeaningCtx tm ctx →
        TagMeaningBounded tm ctx.nextTag →
        PredSatLaws predSat tm →
        ExternTypingAssumptions →
        ((∃ (fuel : Nat) (res : TypeResult),
          typecheck ctx e fuel = .ok res ∧
          ObsConstraints obs res) →
          FaultRobustnessSpec e s obs ctx predSat tm)

def TypeSystemEnforcesFaultRobustness_spec_with_registry
  (registry : ExternRegistry)
  (e : Expr) (s : InputSpec) (obs : ObservableSpec) :=
  wfInputSpec s →
  wfObsSpec obs →
  ∀ (ctx : TypeContext),
      ctxMatchesInputSpec s ctx →
      wfTypeContext ctx →
      ctx.pc = false →
      ctx.tagEnv = {} →
      TagBoundedCtx ctx →
      ∀ (predSat : PredSat) (tm : TagMeaning),
        wfTagMeaningCtx tm ctx →
        TagMeaningBounded tm ctx.nextTag →
        PredSatLaws predSat tm →
        ExternTypingAssumptions →
        ((∃ (fuel : Nat) (res : TypeResult),
          typecheck ctx e fuel = .ok res ∧
          ObsConstraints obs res) →
          FaultRobustnessSpecWithRegistry registry e s obs ctx predSat tm)
