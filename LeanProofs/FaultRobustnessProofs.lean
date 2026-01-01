-- Fault-Robustness proofs (skeletons)

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanPoison.BigStep
import Mathlib.Data.List.Forall2

import LeanProofs.FaultRobustness
import LeanProofs.TypeSafety
import LeanProofs.SemanticsProperties
import LeanProofs.IOHelpers
import LeanProofs.LookupUpdate
import LeanProofs.PreservationProofs
import LeanProofs.VarEnvPreservation
import LeanProofs.MemoryMonotonicity
import Std.Data.ExtTreeMap.Lemmas
import Std.Data.ExtTreeSet.Lemmas

open List
open Std
open scoped MemoryTypeEnv

-- Result agreement for clean (or de-poisoned) outputs.
-- This captures the chaining requirement: clean results must agree across runs.
def resultAgreesIfClean (predSat : PredSat) (R : Regime) (μ₀ μ₁ : Memory)
  (θ₀ θ₁ : RealizationMap) (qt : QTyp) (o₀ o₁ : Value) : Prop :=
  qtypCleanUnder R qt →
    agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt o₀ o₁

-- Tag-environment consistency for a regime: tags known true in the typing
-- context must be true in the regime interpretation.
def tagEnvConsistentWithRegime (tagEnv : TagEnv) (R : Regime) : Prop :=
  ∀ k deps, tagEnv.get? k = some ⟨true, deps⟩ → R k = some true

-- Step theorem (context-driven, no input/output specs).
-- It assumes agreement on clean items in the initial context and preserves it
-- for the post-context, plus result agreement when the result is clean under R.
def StepFR
  (ctx : TypeContext)
  (R : Regime)
  (e : Expr)
  (res : TypeResult)
  (predSat : PredSat) : Prop :=
    ∀ (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (θ₀ θ₁ : RealizationMap)
      (cf₀ cf₁ : Config) (o₀ o₁ : Value),
      wfRealizationMap θ₀ → wfRealizationMap θ₁ →
      wfTypeContext ctx →
      runtimeInstantiatesCtx ctx μ₀ ρ₀ θ₀ → runtimeInstantiatesCtx ctx μ₁ ρ₁ θ₁ →
      tagEnvConsistentWithRegime ctx.tagEnv R →
      agreeOnClean predSat R ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ →
      ∀ (a₀ a₁ : Address) (pm : Bool),
        wfConfig { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } →  -- NEW: initial config₀ well-formed
        wfConfig { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } →  -- NEW: initial config₁ well-formed
        terminatesTo e { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ →
        terminatesTo e { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ →
        ∃ (θ₀' θ₁' : RealizationMap),
          wfExtendsMap θ₀ θ₀' ∧ wfExtendsMap θ₁ θ₁' ∧
          wfTypeContext (ctxAfter ctx res) ∧
          wfConfig cf₀ ∧  -- NEW: final config₀ well-formed
          wfConfig cf₁ ∧  -- NEW: final config₁ well-formed
          agreeOnClean predSat R (ctxAfter ctx res) cf₀.memory cf₀.varEnv θ₀' cf₁.memory cf₁.varEnv θ₁' ∧
          resultAgreesIfClean predSat R cf₀.memory cf₁.memory θ₀' θ₁' res.qualType o₀ o₁

-- Step theorem spec derived from typing (context-driven).
-- No input/output specs here; they are handled by the top-level FR statement
-- and the bridge lemma.
def TypeSystemEnforcesFaultRobustness_step_spec
  (e : Expr)
  (ctxᵢ : TypeContext)
  (predSat : PredSat) : Prop :=
  ∀ (fuel : Nat) (res : TypeResult),
    typecheck ctxᵢ e fuel = .ok res →
    ∀ (R : Regime),
      StepFR ctxᵢ R e res predSat


section TypeSystemEnforcesFaultRobustness_impl_proof

private lemma ret_eq_of_agreeValueUnder_nonref
  {predSat : PredSat} {R : Regime} {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap}
  {qt : QTyp} {o₀ o₁ : Value} :
  (¬ ∃ t ls, qt.etyp = ETyp.ref t ls) →
  qt.poison = false →
  agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ →
  o₀ = o₁ := by
  intro hnotref hpoison hret_agree
  cases hret_agree with
  | clean_eq_nonref _ _ hval => exact hval
  | poisoned_noPred_eq_nonref _ _ _ hval => exact hval
  | withPred_true_eq _ _ _ _ hval => exact hval
  | clean_ref _ hetyp _ _ _ _ _ _ =>
      exfalso
      exact hnotref ⟨_, _, hetyp⟩
  | poisoned_noPred_ref _ _ hetyp _ _ _ _ _ _ =>
      exfalso
      exact hnotref ⟨_, _, hetyp⟩
  | withPred_true_ref _ _ _ hetyp _ _ _ _ _ _ =>
      exfalso
      exact hnotref ⟨_, _, hetyp⟩
  | withPred_false_poisoned_fail _ _ _ _ hpoison' _ _ =>
      have hcontra : False := by
        have : false = true := by
          calc
            false = qt.poison := by symm; exact hpoison
            _ = true := by exact hpoison'
        cases this
      exact False.elim hcontra
  | guardOnly_false_poisoned_any _ _ _ hpoison' =>
      have hcontra : False := by
        have : false = true := by
          calc
            false = qt.poison := by symm; exact hpoison
            _ = true := by exact hpoison'
        cases this
      exact False.elim hcontra

private lemma agreeValueUnder_nonref_eq_of_clean
  {predSat : PredSat} {R : Regime} {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap}
  {qt : QTyp} {o₀ o₁ : Value} :
  qtypCleanUnder R qt →
  (¬ ∃ t ls, qt.etyp = ETyp.ref t ls) →
  agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ →
  o₀ = o₁ := by
  intro hclean hnotref hagree
  cases hagree with
  | clean_eq_nonref _ _ hval => exact hval
  | poisoned_noPred_eq_nonref _ _ _ hval => exact hval
  | withPred_true_eq _ _ _ _ hval => exact hval
  | clean_ref _ hetyp _ _ _ _ _ _ =>
      exfalso
      exact hnotref ⟨_, _, hetyp⟩
  | poisoned_noPred_ref _ _ hetyp _ _ _ _ _ _ =>
      exfalso
      exact hnotref ⟨_, _, hetyp⟩
  | withPred_true_ref _ _ _ hetyp _ _ _ _ _ _ =>
      exfalso
      exact hnotref ⟨_, _, hetyp⟩
  | withPred_false_poisoned_fail k _ htag hreg hpoison _ _ =>
      cases hclean with
      | inl hpoison' =>
          have : false = true := by
            calc
              false = qt.poison := by symm; exact hpoison'
              _ = true := by exact hpoison
          cases this
      | inr hguard =>
          rcases hguard with ⟨k', htag', hreg'⟩
          have hk : k = k' := by
            have : some k = some k' := by
              calc
                some k = qtypGuardTag qt := by symm; exact htag
                _ = some k' := by exact htag'
            exact Option.some.inj this
          subst hk
          have : (some false : Option Bool) = some true := by
            calc
              some false = R k := by symm; exact hreg
              _ = some true := by exact hreg'
          cases this
  | guardOnly_false_poisoned_any k hgo hreg hpoison =>
      cases hclean with
      | inl hpoison' =>
          have : false = true := by
            calc
              false = qt.poison := by symm; exact hpoison'
              _ = true := by exact hpoison
          cases this
      | inr hguard =>
          rcases hguard with ⟨k', htag', hreg'⟩
          have hk : k = k' := by
            have : some k = some k' := by
              calc
                some k = qtypGuardTag qt := by simp [qtypGuardTag, hgo]
                _ = some k' := by exact htag'
            exact Option.some.inj this
          subst hk
          have : (some false : Option Bool) = some true := by
            calc
              some false = R k := by symm; exact hreg
              _ = some true := by exact hreg'
          cases this

private lemma agreeValueUnder_transport_clean
  {predSat : PredSat} {R : Regime} {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap}
  {qt qt2 : QTyp} {o₀ o₁ : Value} :
  qtypCleanUnder R qt →
  qt.etyp = qt2.etyp →
  qt.pred = qt2.pred →
  (qt.poison = false → qt2.poison = false) →
  agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt2 o₀ o₁ →
  agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ := by
  intro hclean hetyp hpred hpoison_imp hagree
  cases hclean with
  | inl hpoison =>
      have hpoison2 : qt2.poison = false := hpoison_imp hpoison
      cases hagree with
      | clean_eq_nonref _ hnotref hEq =>
          have hnotref' : ¬ ∃ t ls, qt.etyp = ETyp.ref t ls := by
            intro ⟨t, ls, h⟩
            apply hnotref
            exact ⟨t, ls, by simpa [hetyp] using h⟩
          exact agreeValueUnder.clean_eq_nonref hpoison hnotref' hEq
      | poisoned_noPred_eq_nonref hpoison' _ _ _ =>
          have : false = true := by
            calc
              false = qt2.poison := by symm; exact hpoison2
              _ = true := by exact hpoison'
          cases this
      | withPred_true_eq _ _ _ hnotref hEq =>
          have hnotref' : ¬ ∃ t ls, qt.etyp = ETyp.ref t ls := by
            intro ⟨t, ls, h⟩
            apply hnotref
            exact ⟨t, ls, by simpa [hetyp] using h⟩
          exact agreeValueUnder.clean_eq_nonref hpoison hnotref' hEq
      | @clean_ref t ls l₁ l₂ a₁ a₂ _ hetyp1 hlookup1 hin1 hv1 hlookup2 hin2 hv2 =>
          have hetyp' : qt.etyp = ETyp.ref t ls := by
            simpa [hetyp] using hetyp1
          exact agreeValueUnder.clean_ref hpoison hetyp'
            hlookup1 hin1 hv1 hlookup2 hin2 hv2
      | poisoned_noPred_ref hpoison' _ _ _ _ _ _ _ =>
          have : false = true := by
            calc
              false = qt2.poison := by symm; exact hpoison2
              _ = true := by exact hpoison'
          cases this
      | @withPred_true_ref _ t ls l₁ l₂ a₁ a₂ _ _ hetyp1 hlookup1 hin1 hv1 hlookup2 hin2 hv2 =>
          have hetyp' : qt.etyp = ETyp.ref t ls := by
            simpa [hetyp] using hetyp1
          exact agreeValueUnder.clean_ref hpoison hetyp'
            hlookup1 hin1 hv1 hlookup2 hin2 hv2
      | withPred_false_poisoned_fail _ _ _ _ hpoison' _ _ =>
          have : false = true := by
            calc
              false = qt2.poison := by symm; exact hpoison2
              _ = true := by exact hpoison'
          cases this
      | guardOnly_false_poisoned_any _ _ _ hpoison' =>
          have : false = true := by
            calc
              false = qt2.poison := by symm; exact hpoison2
              _ = true := by exact hpoison'
          cases this
  | inr hguard =>
      rcases hguard with ⟨k, htag, hreg⟩
      cases hagree with
      | clean_eq_nonref _ hnotref hEq =>
          have hnotref' : ¬ ∃ t ls, qt.etyp = ETyp.ref t ls := by
            intro ⟨t, ls, h⟩
            apply hnotref
            exact ⟨t, ls, by simpa [hetyp] using h⟩
          exact agreeValueUnder.withPred_true_eq k htag hreg hnotref' hEq
      | poisoned_noPred_eq_nonref _ _ hnotref hEq =>
          have hnotref' : ¬ ∃ t ls, qt.etyp = ETyp.ref t ls := by
            intro ⟨t, ls, h⟩
            apply hnotref
            exact ⟨t, ls, by simpa [hetyp] using h⟩
          exact agreeValueUnder.withPred_true_eq k htag hreg hnotref' hEq
      | withPred_true_eq _ _ _ hnotref hEq =>
          have hnotref' : ¬ ∃ t ls, qt.etyp = ETyp.ref t ls := by
            intro ⟨t, ls, h⟩
            apply hnotref
            exact ⟨t, ls, by simpa [hetyp] using h⟩
          exact agreeValueUnder.withPred_true_eq k htag hreg hnotref' hEq
      | @clean_ref t ls l₁ l₂ a₁ a₂ _ hetyp1 hlookup1 hin1 hv1 hlookup2 hin2 hv2 =>
          have hetyp' : qt.etyp = ETyp.ref t ls := by
            simpa [hetyp] using hetyp1
          exact agreeValueUnder.withPred_true_ref k htag hreg hetyp'
            hlookup1 hin1 hv1 hlookup2 hin2 hv2
      | @poisoned_noPred_ref t ls l₁ l₂ a₁ a₂ _ _ hetyp1 hlookup1 hin1 hv1 hlookup2 hin2 hv2 =>
          have hetyp' : qt.etyp = ETyp.ref t ls := by
            simpa [hetyp] using hetyp1
          exact agreeValueUnder.withPred_true_ref k htag hreg hetyp'
            hlookup1 hin1 hv1 hlookup2 hin2 hv2
      | @withPred_true_ref _ t ls l₁ l₂ a₁ a₂ _ _ hetyp1 hlookup1 hin1 hv1 hlookup2 hin2 hv2 =>
          have hetyp' : qt.etyp = ETyp.ref t ls := by
            simpa [hetyp] using hetyp1
          exact agreeValueUnder.withPred_true_ref k htag hreg hetyp'
            hlookup1 hin1 hv1 hlookup2 hin2 hv2
      | withPred_false_poisoned_fail k' _ htag' hreg' _ _ _ =>
          have hk : k = k' := by
            have : some k = some k' := by
              calc
                some k = qtypGuardTag qt := by symm; exact htag
                _ = qtypGuardTag qt2 := by
                  have hpred' : qt2.pred = qt.pred := by symm; exact hpred
                  simp [qtypGuardTag, hpred']
                _ = some k' := by exact htag'
            exact Option.some.inj this
          subst hk
          have : (some false : Option Bool) = some true := by
            calc
              some false = R k := by symm; exact hreg'
              _ = some true := by exact hreg
          cases this
      | guardOnly_false_poisoned_any k' hgo hreg' _ =>
          have hk : k = k' := by
            have : some k = some k' := by
              calc
                some k = qtypGuardTag qt := by symm; exact htag
                _ = qtypGuardTag qt2 := by
                  have hpred' : qt2.pred = qt.pred := by symm; exact hpred
                  simp [qtypGuardTag, hpred']
                _ = some k' := by simp [qtypGuardTag, hgo]
            exact Option.some.inj this
          subst hk
          have : (some false : Option Bool) = some true := by
            calc
              some false = R k := by symm; exact hreg'
              _ = some true := by exact hreg
          cases this
private lemma joinPoison_eq_false {p1 p2 : Poison} :
  joinPoison p1 p2 = false → p1 = false ∧ p2 = false := by
  intro h
  cases p1 <;> cases p2
  all_goals
    simp [joinPoison] at h ⊢

private lemma wfExtendsMap_trans {θ₀ θ₁ θ₂ : RealizationMap} :
  wfExtendsMap θ₀ θ₁ → wfExtendsMap θ₁ θ₂ → wfExtendsMap θ₀ θ₂ := by
  intro h01 h12
  refine ⟨?_, ?_⟩
  · intro l a hlookup
    have h1 : θ₁.lookup l = some a := h01.1 l a hlookup
    exact h12.1 l a h1
  · intro hWF0
    have hWF1 : wfRealizationMap θ₁ := h01.2 hWF0
    exact h12.2 hWF1

-- Bridge lemma: top-level agreement premises imply the step-level invariant.
-- This is the key link from spec-driven premises to the context-driven StepFR.
private lemma agreeOnCriticalAndTrusted_implies_agreeOnClean
  (predSat : PredSat) (R : Regime) (s : InputSpec) (ctx : TypeContext)
  (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (θ₀ θ₁ : RealizationMap) :
  ctxMatchesInputSpec s ctx →
  agreeOnCriticalInputsUnderRegimeSpec predSat R s μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ →
  agreeOnTrustedInputs predSat R s ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ →
  agreeOnClean predSat R ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ := by
  intro hctx hcrit htrusted
  rcases hctx with ⟨hctx_mem, hctx_vars⟩
  rcases hcrit with ⟨hcrit_locs, hcrit_vars⟩
  rcases htrusted with ⟨htrusted_locs, htrusted_vars⟩
  constructor
  · intro l qt hctx_lookup hclean
    by_cases hkey : s.locs.hasKey l
    · -- Critical location: use agreement from the input spec.
      have hcontains : s.locs.contains l = true := by
        simpa [MemoryTypeEnv.hasKey] using hkey
      have hmem : l ∈ s.locs :=
        (Std.ExtTreeMap.contains_iff_mem).1 hcontains
      have hlookup_isSome : (s.locs[l]?).isSome = true :=
        (Std.ExtTreeMap.mem_iff_isSome_getElem?).1 hmem
      cases hlookup_s : s.locs[l]? with
      | none =>
          simp [hlookup_s] at hlookup_isSome
      | some qt_s =>
          have hlookup_s : s.locs.lookup l = some qt_s := by
            simpa [MemoryTypeEnv.lookup] using hlookup_s
          have hctx_lookup' : ctx.memEnv.lookup l = some qt_s := hctx_mem hlookup_s
          have hqt : qt_s = qt := by
            have : some qt_s = some qt := by
              calc
                some qt_s = ctx.memEnv.lookup l := by
                  symm
                  exact hctx_lookup'
                _ = some qt := by
                  exact hctx_lookup
            exact Option.some.inj this
          have hcrit_locs' := hcrit_locs
          rw [List.forall_iff_forall_mem] at hcrit_locs'
          have hmem' : (l, qt_s) ∈ s.locs.toList := by
            rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some]
            dsimp [MemoryTypeEnv.lookup] at hlookup_s
            simpa using hlookup_s
          have hlocEntry : agreeLocUnder predSat R μ₀ μ₁ θ₀ θ₁ (l, qt_s) :=
            hcrit_locs' (l, qt_s) hmem'
          simpa [hqt] using hlocEntry
    · -- Trusted location: use trusted-input agreement.
      exact htrusted_locs l qt hctx_lookup hkey hclean
  · intro x qt hctx_lookup hclean
    by_cases hkey : s.vars.hasKey x
    · -- Critical variable: use agreement from the input spec.
      have hcontains : s.vars.contains x = true := by
        simpa [VarTypeEnv.hasKey] using hkey
      have hmem : x ∈ s.vars :=
        (Std.ExtTreeMap.contains_iff_mem).1 hcontains
      have hlookup_isSome : (s.vars[x]?).isSome = true :=
        (Std.ExtTreeMap.mem_iff_isSome_getElem?).1 hmem
      cases hlookup_s : s.vars[x]? with
      | none =>
          simp [hlookup_s] at hlookup_isSome
      | some qt_s =>
          have hlookup_s : s.vars.lookup x = some qt_s := by
            simpa [VarTypeEnv.lookup] using hlookup_s
          have hctx_lookup' : ctx.varEnv.lookup x = some qt_s := hctx_vars hlookup_s
          have hqt : qt_s = qt := by
            have : some qt_s = some qt := by
              calc
                some qt_s = ctx.varEnv.lookup x := by
                  symm
                  exact hctx_lookup'
                _ = some qt := by
                  exact hctx_lookup
            exact Option.some.inj this
          have hcrit_vars' := hcrit_vars
          rw [List.forall_iff_forall_mem] at hcrit_vars'
          have hmem' : (x, qt_s) ∈ s.vars.toList := by
            rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some]
            dsimp [VarTypeEnv.lookup] at hlookup_s
            simpa using hlookup_s
          have hvarEntry : agreeVarUnder predSat R μ₀ ρ₀ μ₁ ρ₁ θ₀ θ₁ (x, qt_s) :=
            hcrit_vars' (x, qt_s) hmem'
          simpa [hqt] using hvarEntry
    · -- Trusted variable: use trusted-input agreement.
      exact htrusted_vars x qt hctx_lookup hkey hclean

-- Bridge theorem: connects the step theorem to the top-level FR spec.
theorem TypeSystemEnforcesFaultRobustness_impl :
  (∀ e ctxᵢ predSat,
    TypeSystemEnforcesFaultRobustness_step_spec e ctxᵢ predSat) →
  (∀ e s obs, TypeSystemEnforcesFaultRobustness_spec e s obs) := by
  intro hstep e s obs
  rintro his _hos ctx hctx _hwf _hpc _hte predSat _hps ⟨fuel, res, htc, hobs⟩
  rcases hobs with ⟨hobs_ret, hobs_mem⟩
  have hstep' := hstep e ctx predSat
  have hstep' := hstep' fuel res htc
  rintro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ a₀ a₁ pm R cf₀ cf₁ o₀ o₁
  rintro hR hθ₀ hθ₁ hwfcfg₀ hwfcfg₁ hics₀ hics₁ hric₀ hric₁ hcrs₀ hcrs₁ hagree htrusted ht₀ ht₁
  have hagree_clean :
      agreeOnClean predSat R ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ :=
    agreeOnCriticalAndTrusted_implies_agreeOnClean
      predSat R s ctx μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ hctx hagree htrusted
  have htagR : tagEnvConsistentWithRegime ctx.tagEnv R := by
    intro k deps hlookup
    -- Empty tag environment at the top level.
    have : (ctx.tagEnv.get? k) = none := by
      simp [_hte]
    rw [this] at hlookup
    cases hlookup
  have hstepFR :=
    (hstep' R) μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁
      hθ₀ hθ₁ _hwf hric₀ hric₁ htagR hagree_clean
      a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  rcases hstepFR with ⟨θ₀', θ₁', hθ₀ext, hθ₁ext, _hwf', _hwfcf₀', _hwfcf₁', hagree_clean', hret_agree⟩
  refine ⟨θ₀', θ₁', hθ₀ext, hθ₁ext, ?_⟩
  -- Bridge from post-state agreement to observables.
  simp [observablesEqual]
  constructor
  · intro l et hobs_lookup
    obtain ⟨qt, hlookup_mem, _het_eq, hpoison⟩ := hobs_mem l et hobs_lookup
    have hctx_lookup : (ctxAfter ctx res).memEnv.lookup l = some qt := by
      simpa [ctxAfter] using hlookup_mem
    have hclean : qtypCleanUnder R qt := by
      left
      exact hpoison
    have hlocEntry : agreeLocUnder predSat R cf₀.memory cf₁.memory θ₀' θ₁' (l, qt) :=
      (hagree_clean'.1 l qt hctx_lookup hclean)
    cases hlocEntry with
    | agree_values _l _qt a₀' a₁' n₀ n₁ hreal₀ hreal₁ hlookup₀ hlookup₁ hagree =>
        -- Reduce to equality of stored ints via agreement on the stored values.
        have hvalEq : n₀ = n₁ := by
          cases hagree with
          | clean_eq_nonref _ _ hval =>
              cases hval
              rfl
          | poisoned_noPred_eq_nonref _ _ _ hval =>
              cases hval
              rfl
          | clean_ref _ _ _ _ hv1 _ _ _ =>
              cases hv1
          | poisoned_noPred_ref _ _ _ _ _ hv1 _ _ _ =>
              cases hv1
          | withPred_true_eq _ _ _ _ hval =>
              cases hval
              rfl
          | withPred_true_ref _ _ _ _ _ _ hv1 _ _ _ =>
              cases hv1
          | withPred_false_poisoned_fail _ _ _ _ hpoison' _ _ =>
              have : False := by
                simp [hpoison] at hpoison'
              exact False.elim this
          | guardOnly_false_poisoned_any _ _ _ hpoison' =>
              have : False := by
                simp [hpoison] at hpoison'
              exact False.elim this
        refine Or.inl ?_
        refine ⟨a₀', ?_⟩
        refine And.intro hreal₀ ?_
        refine ⟨a₁', ?_⟩
        refine And.intro hreal₁ ?_
        have hlookup₀' : cf₀.memory.lookup a₀' = some (Int.ofNat n₀) :=
          hlookup₀
        have hlookup₁' : cf₁.memory.lookup a₁' = some (Int.ofNat n₁) :=
          hlookup₁
        calc
          cf₀.memory.lookup a₀' = some (Int.ofNat n₀) := hlookup₀'
          _ = some (Int.ofNat n₁) := by simp [hvalEq]
          _ = cf₁.memory.lookup a₁' := by symm; exact hlookup₁'
    | both_unrealized _l _qt _hnone₀ _hnone₁ =>
        exact Or.inr ⟨_hnone₀, _hnone₁⟩
  · cases hretOpt : obs.retEtyp? with
    | none =>
        simp
    | some et =>
        -- Use return agreement from the step proof.
        rcases hobs_ret _ hretOpt with ⟨hret_et, hret_poison⟩
        have hret_clean : qtypCleanUnder R res.qualType := by
          left
          exact hret_poison
        have hret_agree' :
            agreeValueUnder predSat R cf₀.memory cf₁.memory θ₀' θ₁' res.qualType o₀ o₁ :=
          hret_agree hret_clean
        cases et with
        | ref t ls =>
            cases hret_agree' with
            | @clean_ref t' ls' l₁ l₂ a₁ a₂ hpoison hetyp hlookup1 hin1 hv1 hlookup2 hin2 hv2 =>
                have href : ETyp.ref t' ls' = ETyp.ref t ls := by
                  calc
                    ETyp.ref t' ls' = res.qualType.etyp := by
                      symm
                      exact hetyp
                    _ = ETyp.ref t ls := by
                      exact hret_et
                cases href
                refine And.intro ?_ ?_
                · refine ⟨l₁, ?_⟩
                  refine And.intro hin1 ?_
                  refine ⟨a₁, ?_⟩
                  exact And.intro hlookup1 hv1
                · refine ⟨l₂, ?_⟩
                  refine And.intro hin2 ?_
                  refine ⟨a₂, ?_⟩
                  exact And.intro hlookup2 hv2
            | @withPred_true_ref k t' ls' l₁ l₂ a₁ a₂ htag hregime hetyp hlookup1 hin1 hv1 hlookup2 hin2 hv2 =>
                have href : ETyp.ref t' ls' = ETyp.ref t ls := by
                  calc
                    ETyp.ref t' ls' = res.qualType.etyp := by
                      symm
                      exact hetyp
                    _ = ETyp.ref t ls := by
                      exact hret_et
                cases href
                refine And.intro ?_ ?_
                · refine ⟨l₁, ?_⟩
                  refine And.intro hin1 ?_
                  refine ⟨a₁, ?_⟩
                  exact And.intro hlookup1 hv1
                · refine ⟨l₂, ?_⟩
                  refine And.intro hin2 ?_
                  refine ⟨a₂, ?_⟩
                  exact And.intro hlookup2 hv2
            | clean_eq_nonref _ hnotref _ =>
                have : False := by
                  apply hnotref
                  exact ⟨t, ls, hret_et⟩
                exact False.elim this
            | poisoned_noPred_eq_nonref _ _ hnotref _ =>
                have : False := by
                  apply hnotref
                  exact ⟨t, ls, hret_et⟩
                exact False.elim this
            | withPred_true_eq _ _ _ hnotref _ =>
                have : False := by
                  apply hnotref
                  exact ⟨t, ls, hret_et⟩
                exact False.elim this
            | poisoned_noPred_ref hpoison' _ _ _ _ _ _ _ _ =>
                have hcontra : False := by
                  have : false = true := by
                    calc
                      false = res.qualType.poison := by
                        symm
                        exact hret_poison
                      _ = true := by
                        exact hpoison'
                  cases this
                exact False.elim hcontra
            | withPred_false_poisoned_fail _ _ _ _ hpoison' _ _ =>
                have hcontra : False := by
                  have : false = true := by
                    calc
                      false = res.qualType.poison := by
                        symm
                        exact hret_poison
                      _ = true := by
                        exact hpoison'
                  cases this
                exact False.elim hcontra
            | guardOnly_false_poisoned_any _ _ _ hpoison' =>
                have hcontra : False := by
                  have : false = true := by
                    calc
                      false = res.qualType.poison := by
                        symm
                        exact hret_poison
                      _ = true := by
                        exact hpoison'
                  cases this
                exact False.elim hcontra
        | int =>
            have hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
              simp [hret_et]
            exact ret_eq_of_agreeValueUnder_nonref hnotref hret_poison hret_agree'
        | bool =>
            have hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
              simp [hret_et]
            exact ret_eq_of_agreeValueUnder_nonref hnotref hret_poison hret_agree'
        | unit =>
            have hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
              simp [hret_et]
            exact ret_eq_of_agreeValueUnder_nonref hnotref hret_poison hret_agree'
        | string =>
            have hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
              simp [hret_et]
            exact ret_eq_of_agreeValueUnder_nonref hnotref hret_poison hret_agree'
        | arrow st₁ st₂ p tcls =>
            have hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
              simp [hret_et]
            exact ret_eq_of_agreeValueUnder_nonref hnotref hret_poison hret_agree'
        | parrow st₁ st₂ p tcls =>
            have hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
              simp [hret_et]
            exact ret_eq_of_agreeValueUnder_nonref hnotref hret_poison hret_agree'

end TypeSystemEnforcesFaultRobustness_impl_proof

section TypeSystemEnforcesFaultRobustness_step_proof

-- Step theorem variant that uses world-indexed termination premises.
-- Includes wfTypeContext premises and conclusion for freshness reasoning.
private def StepFRW
  (ctx : TypeContext)
  (R : Regime)
  (e : Expr)
  (res : TypeResult)
  (predSat : PredSat) : Prop :=
    ∀ (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (θ₀ θ₁ : RealizationMap)
      (cf₀ cf₁ : Config) (o₀ o₁ : Value),
      wfRealizationMap θ₀ → wfRealizationMap θ₁ →
      wfTypeContext ctx →
      runtimeInstantiatesCtx ctx μ₀ ρ₀ θ₀ → runtimeInstantiatesCtx ctx μ₁ ρ₁ θ₁ →
      tagEnvConsistentWithRegime ctx.tagEnv R →
      agreeOnClean predSat R ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ →
      ∀ (a₀ a₁ : Address) (pm₀ pm₁ : Bool),
        wfConfig { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm₀ } →  -- NEW: initial config₀ well-formed
        wfConfig { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm₁ } →  -- NEW: initial config₁ well-formed
        terminatesToW e { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm₀ } cf₀ o₀ →
        terminatesToW e { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm₁ } cf₁ o₁ →
        ∃ (θ₀' θ₁' : RealizationMap),
          wfExtendsMap θ₀ θ₀' ∧ wfExtendsMap θ₁ θ₁' ∧
          wfTypeContext (ctxAfter ctx res) ∧
          wfConfig cf₀ ∧  -- NEW: final config₀ well-formed
          wfConfig cf₁ ∧  -- NEW: final config₁ well-formed
          runtimeInstantiatesCtx (ctxAfter ctx res) cf₀.memory cf₀.varEnv θ₀' ∧
          runtimeInstantiatesCtx (ctxAfter ctx res) cf₁.memory cf₁.varEnv θ₁' ∧
          tagEnvConsistentWithRegime (ctxAfter ctx res).tagEnv R ∧
          agreeOnClean predSat R (ctxAfter ctx res) cf₀.memory cf₀.varEnv θ₀' cf₁.memory cf₁.varEnv θ₁' ∧
          resultAgreesIfClean predSat R cf₀.memory cf₁.memory θ₀' θ₁' res.qualType o₀ o₁

-- Convert function-equality termination to world-indexed termination.
private lemma terminatesToW_of_terminatesTo
  {e : Expr} {c₀ c₁ : Config} {o : Value} :
  terminatesTo e c₀ c₁ o → terminatesToW e c₀ c₁ o := by
  intro ht
  rcases ht with ⟨fuel, verbose, hbeval⟩
  have h_eval_world := LeanProofs.evalAtDefault_eq hbeval
  refine ⟨fuel, verbose, LeanProofs.defaultWorld, LeanProofs.defaultWorld, ?_⟩
  simpa [pure] using h_eval_world

-- Use StepFRW to derive the original StepFR premises.
private lemma StepFR_of_StepFRW
  {ctx : TypeContext} {R : Regime} {e : Expr} {res : TypeResult} {predSat : PredSat} :
  StepFRW ctx R e res predSat → StepFR ctx R e res predSat := by
  intro hstep μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁
    hθ₀ hθ₁ hwf hric₀ hric₁ htagR hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  have ht₀w := terminatesToW_of_terminatesTo ht₀
  have ht₁w := terminatesToW_of_terminatesTo ht₁
  rcases hstep μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁
      hθ₀ hθ₁ hwf hric₀ hric₁ htagR hagree a₀ a₁ pm pm hwfcfg₀ hwfcfg₁ ht₀w ht₁w with
    ⟨θ₀', θ₁', hθ₀ext, hθ₁ext, hwf', hwfcf₀', hwfcf₁', _hric₀', _hric₁', _htagR', hagree', hret⟩
  exact ⟨θ₀', θ₁', hθ₀ext, hθ₁ext, hwf', hwfcf₀', hwfcf₁', hagree', hret⟩

private def isExternExpr : Expr → Prop
  | Expr.externVal _ _ _ => True
  | Expr.externFn _ _ _ _ => True
  | Expr.externPfn _ _ _ => True
  | _ => False

private lemma terminatesTo_extern_false
  {e : Expr} {c₀ c₁ : Config} {o : Value} :
  isExternExpr e →
  terminatesToW e c₀ c₁ o → False := by
  intro hex ht
  rcases ht with ⟨fuel, verbose, w₀, w₁, hbeval⟩
  cases e with
  | externVal _ _ _ =>
      cases fuel <;> simp [LeanPoison.beval] at hbeval <;> cases hbeval
  | externFn _ _ _ _ =>
      cases fuel <;> simp [LeanPoison.beval] at hbeval <;> cases hbeval
  | externPfn _ _ _ =>
      cases fuel <;> simp [LeanPoison.beval] at hbeval <;> cases hbeval
  | _ =>
      cases hex

private lemma terminatesTo_num_inv (n : Int)
  (μ : Memory) (ρ : VarEnv) (a : Address) (pm : Bool) (cf : Config) (o : Value) :
  terminatesToW (Expr.num n) { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o →
  cf = { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } ∧ o = Value.num n := by
  intro ht
  rcases ht with ⟨fuel, verbose, w₀, w₁, hbeval⟩
  cases fuel with
  | zero =>
      simp [LeanPoison.beval] at hbeval
      cases hbeval
  | succ fuel =>
      simp [LeanPoison.beval] at hbeval
      injection hbeval with hcfg hval
      cases hcfg
      cases hval
      constructor <;> rfl

private lemma terminatesTo_bool_inv (b : Bool)
  (μ : Memory) (ρ : VarEnv) (a : Address) (pm : Bool) (cf : Config) (o : Value) :
  terminatesToW (Expr.bool b) { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o →
  cf = { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } ∧ o = Value.bool b := by
  intro ht
  rcases ht with ⟨fuel, verbose, w₀, w₁, hbeval⟩
  cases fuel with
  | zero =>
      simp [LeanPoison.beval] at hbeval
      cases hbeval
  | succ fuel =>
      simp [LeanPoison.beval] at hbeval
      injection hbeval with hcfg hval
      cases hcfg
      cases hval
      constructor <;> rfl

private lemma terminatesTo_unit_inv
  (μ : Memory) (ρ : VarEnv) (a : Address) (pm : Bool) (cf : Config) (o : Value) :
  terminatesToW Expr.unit { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o →
  cf = { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } ∧ o = Value.unit := by
  intro ht
  rcases ht with ⟨fuel, verbose, w₀, w₁, hbeval⟩
  cases fuel with
  | zero =>
      simp [LeanPoison.beval] at hbeval
      cases hbeval
  | succ fuel =>
      simp [LeanPoison.beval] at hbeval
      injection hbeval with hcfg hval
      cases hcfg
      cases hval
      constructor <;> rfl

private lemma terminatesTo_str_inv (s : String)
  (μ : Memory) (ρ : VarEnv) (a : Address) (pm : Bool) (cf : Config) (o : Value) :
  terminatesToW (Expr.str s) { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o →
  cf = { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } ∧ o = Value.str s := by
  intro ht
  rcases ht with ⟨fuel, verbose, w₀, w₁, hbeval⟩
  cases fuel with
  | zero =>
      simp [LeanPoison.beval] at hbeval
      cases hbeval
  | succ fuel =>
      simp [LeanPoison.beval] at hbeval
      injection hbeval with hcfg hval
      cases hcfg
      cases hval
      constructor <;> rfl

private lemma terminatesTo_literal_inv
  (e : Expr) (v : Value)
  (hval : Expr.toValue? e = some v)
  (μ : Memory) (ρ : VarEnv) (a : Address) (pm : Bool) (cf : Config) (o : Value) :
  terminatesToW e { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o →
  cf = { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } ∧ o = v := by
  intro ht
  cases e with
  | unit =>
      simp [Expr.toValue?] at hval
      cases hval
      exact terminatesTo_unit_inv μ ρ a pm cf o ht
  | num n =>
      simp [Expr.toValue?] at hval
      cases hval
      exact terminatesTo_num_inv n μ ρ a pm cf o ht
  | bool b =>
      simp [Expr.toValue?] at hval
      cases hval
      exact terminatesTo_bool_inv b μ ρ a pm cf o ht
  | str s =>
      simp [Expr.toValue?] at hval
      cases hval
      exact terminatesTo_str_inv s μ ρ a pm cf o ht
  | _ =>
      simp [Expr.toValue?] at hval

private lemma terminatesTo_var_inv
  (x : Name) (μ : Memory) (ρ : VarEnv) (a : Address) (pm : Bool) (cf : Config) (o : Value) :
  terminatesToW (Expr.var x) { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o →
  ∃ v, ρ.lookup x = some v ∧
    cf = { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } ∧
    o = v := by
  intro ht
  rcases ht with ⟨fuel, verbose, w₀, w₁, hbeval⟩
  cases fuel with
  | zero =>
      simp [LeanPoison.beval] at hbeval
      cases hbeval
  | succ fuel =>
      simp [LeanPoison.beval] at hbeval
      cases hlookup : ρ.lookup x with
      | none =>
          simp [hlookup] at hbeval
          cases hbeval
      | some v' =>
          simp [hlookup] at hbeval
          injection hbeval with hcfg hval
          cases hcfg
          cases hval
          refine ⟨o, ?_⟩
          refine And.intro ?_ ?_
          · rfl
          · exact And.intro rfl rfl

private lemma agreeValueUnder_of_agreeVarUnder
  {predSat : PredSat} {R : Regime} {μ₀ μ₁ : Memory} {ρ₀ ρ₁ : VarEnv}
  {θ₀ θ₁ : RealizationMap} {x : Name} {qt : QTyp} {v₀ v₁ : Value} :
  agreeVarUnder predSat R μ₀ ρ₀ μ₁ ρ₁ θ₀ θ₁ (x, qt) →
  ρ₀.lookup x = some v₀ →
  ρ₁.lookup x = some v₁ →
  agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ := by
  intro hvar hlookup₀ hlookup₁
  cases hvar with
  | agree_values _ _ v₀' v₁' hlookup₀' hlookup₁' hagree =>
      have hv₀ : v₀' = v₀ := by
        have : some v₀' = some v₀ := by
          calc
            some v₀' = ρ₀.lookup x := by symm; exact hlookup₀'
            _ = some v₀ := by exact hlookup₀
        exact Option.some.inj this
      have hv₁ : v₁' = v₁ := by
        have : some v₁' = some v₁ := by
          calc
            some v₁' = ρ₁.lookup x := by symm; exact hlookup₁'
            _ = some v₁ := by exact hlookup₁
        exact Option.some.inj this
      simpa [hv₀, hv₁] using hagree
  | both_none _ _ hnone₀ _ =>
      have : False := by
        have : some v₀ = none := by
          calc
            some v₀ = ρ₀.lookup x := by symm; exact hlookup₀
            _ = none := by exact hnone₀
        cases this
      exact False.elim this

private lemma valueHasETyp_extends
  {θ₀ θ₁ : RealizationMap} {v : Value} {t : ETyp} :
  θ₀.extendsMap θ₁ →
  valueHasETyp θ₀ v t →
  valueHasETyp θ₁ v t := by
  intro hExt hval
  cases hval with
  | num n => exact valueHasETyp.num n
  | bool b => exact valueHasETyp.bool b
  | unit => exact valueHasETyp.unit
  | str s => exact valueHasETyp.str s
  | loc hlookup hin =>
      exact valueHasETyp.loc (hExt _ _ hlookup) hin
  | closure x e env st1 st2 p tcl =>
      exact valueHasETyp.closure x e env st1 st2 p tcl
  | peClosure x pe env st1 st2 p tcl =>
      exact valueHasETyp.peClosure x pe env st1 st2 p tcl

private lemma agreeValueUnder_clean_extends
  {predSat : PredSat} {R : Regime} {μ₀ μ₁ μ₀' μ₁' : Memory}
  {θ₀ θ₁ θ₀' θ₁' : RealizationMap} {qt : QTyp} {v₀ v₁ : Value} :
  qtypCleanUnder R qt →
  θ₀.extendsMap θ₀' →
  θ₁.extendsMap θ₁' →
  agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ →
  agreeValueUnder predSat R μ₀' μ₁' θ₀' θ₁' qt v₀ v₁ := by
  intro hclean hθ₀ hθ₁ hagree
  cases hagree with
  | clean_eq_nonref hpoison hnotref hEq =>
      exact agreeValueUnder.clean_eq_nonref hpoison hnotref hEq
  | clean_ref hpoison hetyp hlookup1 hin1 hv1 hlookup2 hin2 hv2 =>
      exact agreeValueUnder.clean_ref hpoison hetyp (hθ₀ _ _ hlookup1) hin1 hv1 (hθ₁ _ _ hlookup2) hin2 hv2
  | poisoned_noPred_eq_nonref hpoison hpred _hnotref _hEq =>
      cases hclean with
      | inl hpoison' =>
          have : false = true := by
            calc
              false = qt.poison := by symm; exact hpoison'
              _ = true := by exact hpoison
          cases this
      | inr hguard =>
          rcases hguard with ⟨k, htag, _⟩
          have htag' : False := by
            have htag'' := htag
            simp [qtypGuardTag, hpred] at htag''
          cases htag'
  | poisoned_noPred_ref hpoison hpred _hetyp _hlookup1 _hin1 _hv1 _hlookup2 _hin2 _hv2 =>
      cases hclean with
      | inl hpoison' =>
          have : false = true := by
            calc
              false = qt.poison := by symm; exact hpoison'
              _ = true := by exact hpoison
          cases this
      | inr hguard =>
          rcases hguard with ⟨k, htag, _⟩
          have htag' : False := by
            have htag'' := htag
            simp [qtypGuardTag, hpred] at htag''
          cases htag'
  | withPred_true_eq k htag hreg hnotref hEq =>
      exact agreeValueUnder.withPred_true_eq k htag hreg hnotref hEq
  | withPred_true_ref k htag hreg hetyp hlookup1 hin1 hv1 hlookup2 hin2 hv2 =>
      exact agreeValueUnder.withPred_true_ref k htag hreg hetyp
        (hθ₀ _ _ hlookup1) hin1 hv1 (hθ₁ _ _ hlookup2) hin2 hv2
  | withPred_false_poisoned_fail k _hclos htag hreg hpoison _hfail1 _hfail2 =>
      cases hclean with
      | inl hpoison' =>
          have : false = true := by
            calc
              false = qt.poison := by symm; exact hpoison'
              _ = true := by exact hpoison
          cases this
      | inr hguard =>
          rcases hguard with ⟨k', htag', hreg'⟩
          have hk : k = k' := by
            have : some k = some k' := by
              calc
                some k = qtypGuardTag qt := by symm; exact htag
                _ = some k' := by exact htag'
            exact Option.some.inj this
          subst hk
          have : (some false : Option Bool) = some true := by
            calc
              some false = R k := by symm; exact hreg
              _ = some true := by exact hreg'
          cases this
  | guardOnly_false_poisoned_any k hgo hreg hpoison =>
      cases hclean with
      | inl hpoison' =>
          have : false = true := by
            calc
              false = qt.poison := by symm; exact hpoison'
              _ = true := by exact hpoison
          cases this
      | inr hguard =>
          rcases hguard with ⟨k', htag', hreg'⟩
          have hk : k = k' := by
            have : some k = some k' := by
              calc
                some k = qtypGuardTag qt := by simp [qtypGuardTag, hgo]
                _ = some k' := by exact htag'
            exact Option.some.inj this
          subst hk
          have : (some false : Option Bool) = some true := by
            calc
              some false = R k := by symm; exact hreg
              _ = some true := by exact hreg'
          cases this

private lemma typecheckVar_preserves_memEnv (ctx : TypeContext) (x : Name) (res : TypeResult) :
  typecheckVar ctx x = .ok res →
  res.memEnv' = ctx.memEnv := by
  intro h_typecheck
  simp [typecheckVar] at h_typecheck
  split at h_typecheck
  · repeat (first | split at h_typecheck | (simp [pure, Except.pure] at h_typecheck; rw [← h_typecheck]))
  · simp at h_typecheck

private lemma typecheckVar_preserves_tagEnv (ctx : TypeContext) (x : Name) (res : TypeResult) :
  typecheckVar ctx x = .ok res →
  res.tagEnv' = ctx.tagEnv := by
  intro h_typecheck
  simp [typecheckVar] at h_typecheck
  split at h_typecheck
  · repeat (first | split at h_typecheck | (simp [pure, Except.pure] at h_typecheck; rw [← h_typecheck]))
  · simp at h_typecheck

private lemma typecheckVar_preserves_nextLoc (ctx : TypeContext) (x : Name) (res : TypeResult) :
  typecheckVar ctx x = .ok res →
  res.nextLoc' = ctx.nextLoc := by
  intro h_typecheck
  simp [typecheckVar] at h_typecheck
  split at h_typecheck
  · repeat (first | split at h_typecheck | (simp [pure, Except.pure] at h_typecheck; rw [← h_typecheck]))
  · simp at h_typecheck

private lemma typecheckVar_preserves_nextTag (ctx : TypeContext) (x : Name) (res : TypeResult) :
  typecheckVar ctx x = .ok res →
  res.nextTag' = ctx.nextTag := by
  intro h_typecheck
  simp [typecheckVar] at h_typecheck
  split at h_typecheck
  · repeat (first | split at h_typecheck | (simp [pure, Except.pure] at h_typecheck; rw [← h_typecheck]))
  · simp at h_typecheck

-- Structure lemma for printInt typechecking.
private lemma typecheckPrintInt_structure (ctx : TypeContext) (e1 : Expr) (fuel : Nat) (res : TypeResult) :
  typecheckPrintInt ctx e1 fuel = .ok res →
  ∃ (result1 : TypeResult),
    typecheckExpr ctx e1 (fuel - 1) = .ok result1 ∧
    res.memEnv' = result1.memEnv' ∧
    res.tagEnv' = result1.tagEnv' ∧
    res.nextLoc' = result1.nextLoc' ∧
    res.nextTag' = result1.nextTag' ∧
    res.qualType.etyp = ETyp.unit := by
  intro h_typecheck
  cases fuel with
  | zero =>
      unfold typecheckPrintInt at h_typecheck
      simp at h_typecheck
  | succ fuel' =>
      unfold typecheckPrintInt at h_typecheck
      simp [bind, Except.bind] at h_typecheck
      cases h_tc1 : typecheckExpr ctx e1 fuel' with
      | ok result1 =>
          simp [h_tc1] at h_typecheck
          match h_qt : result1.qualType with
          | QTyp.mk etyp poison pred =>
              rw [h_qt] at h_typecheck
              by_cases h_eq : etyp = ETyp.int
              · have h_typecheck' := h_typecheck
                simp [h_eq, pure, Except.pure] at h_typecheck'
                have h_res :
                    { qualType := { etyp := ETyp.unit, poison := joinPoison ctx.pc poison, pred := Predicate.noPred },
                      memEnv' := result1.memEnv', tagEnv' := result1.tagEnv', nextLoc' := result1.nextLoc',
                      nextTag' := result1.nextTag' } = res := by
                  cases h_typecheck'
                  rfl
                refine ⟨result1, h_tc1, ?_⟩
                rw [← h_res]
                simp
              · have h_typecheck' := h_typecheck
                simp [h_eq, throw] at h_typecheck'
      | error msg =>
          simp [h_tc1] at h_typecheck

-- Structure lemma for printString typechecking.
private lemma typecheckPrintString_structure (ctx : TypeContext) (e1 : Expr) (fuel : Nat) (res : TypeResult) :
  typecheckPrintString ctx e1 fuel = .ok res →
  ∃ (result1 : TypeResult),
    typecheckExpr ctx e1 (fuel - 1) = .ok result1 ∧
    res.memEnv' = result1.memEnv' ∧
    res.tagEnv' = result1.tagEnv' ∧
    res.nextLoc' = result1.nextLoc' ∧
    res.nextTag' = result1.nextTag' ∧
    res.qualType.etyp = ETyp.unit := by
  intro h_typecheck
  cases fuel with
  | zero =>
      unfold typecheckPrintString at h_typecheck
      simp at h_typecheck
  | succ fuel' =>
      unfold typecheckPrintString at h_typecheck
      simp [bind, Except.bind] at h_typecheck
      cases h_tc1 : typecheckExpr ctx e1 fuel' with
      | ok result1 =>
          simp [h_tc1] at h_typecheck
          match h_qt : result1.qualType with
          | QTyp.mk etyp poison pred =>
              rw [h_qt] at h_typecheck
              by_cases h_eq : etyp = ETyp.string
              · have h_typecheck' := h_typecheck
                simp [h_eq, pure, Except.pure] at h_typecheck'
                have h_res :
                    { qualType := { etyp := ETyp.unit, poison := joinPoison ctx.pc poison, pred := Predicate.noPred },
                      memEnv' := result1.memEnv', tagEnv' := result1.tagEnv', nextLoc' := result1.nextLoc',
                      nextTag' := result1.nextTag' } = res := by
                  cases h_typecheck'
                  rfl
                refine ⟨result1, h_tc1, ?_⟩
                rw [← h_res]
                simp
              · have h_typecheck' := h_typecheck
                simp [h_eq, throw] at h_typecheck'
      | error msg =>
          simp [h_tc1] at h_typecheck

private lemma typecheckExpr_op_succ (ctx : TypeContext) (e1 e2 : Expr) (op : Op) (fuel : Nat) :
  typecheckExpr ctx (Expr.op e1 op e2) (fuel + 1) = typecheckOp ctx e1 e2 fuel op := by
  simp [typecheckExpr]

private lemma typecheckExpr_unaryop_succ (ctx : TypeContext) (op : UnaryOp) (e : Expr) (fuel : Nat) :
  typecheckExpr ctx (Expr.unaryop op e) (fuel + 1) = typecheckUnaryOp ctx op e fuel := by
  simp [typecheckExpr]

private lemma typecheckExpr_seq_succ (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) :
  typecheckExpr ctx (Expr.seq e1 e2) (fuel + 1) = typecheckSeq ctx e1 e2 fuel := by
  simp [typecheckExpr]

private lemma typecheckExpr_vlet_succ (ctx : TypeContext) (x : Name) (e1 e2 : Expr) (fuel : Nat) :
  typecheckExpr ctx (Expr.vlet x e1 e2) (fuel + 1) = typecheckVlet ctx x e1 e2 fuel := by
  simp [typecheckExpr]

private lemma opEType_ne_ref (op : Op) (et1 et2 : ETyp) (t : ETyp) (ls : LocSet) :
  opEType? op et1 et2 ≠ some (ETyp.ref t ls) := by
  cases op <;> cases et1 <;> cases et2 <;> simp [opEType?]

private lemma opUnaryEType_ne_ref (op : UnaryOp) (et1 : ETyp) (t : ETyp) (ls : LocSet) :
  opUnaryEType? op et1 ≠ some (ETyp.ref t ls) := by
  cases op
  all_goals
    cases et1
    all_goals
      simp [opUnaryEType?]

-- Structure lemma for unary-op typechecking.
private lemma typecheckUnaryOp_structure (ctx : TypeContext) (op : UnaryOp) (e1 : Expr) (fuel : Nat)
    (res : TypeResult) :
  typecheckUnaryOp ctx op e1 fuel = .ok res →
  ∃ (result1 : TypeResult) (result_etyp : ETyp),
    typecheckExpr ctx e1 (fuel - 1) = .ok result1 ∧
    opUnaryEType? op result1.qualType.etyp = some result_etyp ∧
    res.memEnv' = result1.memEnv' ∧
    res.tagEnv' = result1.tagEnv' ∧
    res.nextLoc' = result1.nextLoc' ∧
    res.nextTag' = result1.nextTag' ∧
    res.qualType.etyp = result_etyp ∧
    res.qualType.poison = joinPoison ctx.pc result1.qualType.poison ∧
    res.qualType.pred = Predicate.noPred := by
  intro h_typecheck
  cases fuel with
  | zero =>
      simp [typecheckUnaryOp] at h_typecheck
  | succ fuel' =>
      unfold typecheckUnaryOp at h_typecheck
      simp at h_typecheck
      cases h_tc1_result : typecheckExpr ctx e1 fuel' with
      | ok result1 =>
          simp [h_tc1_result, bind, Except.bind] at h_typecheck
          match h_qt1 : result1.qualType with
          | QTyp.mk etyp1 p1 pred1 =>
              rw [h_qt1] at h_typecheck
              cases h_opEType_result : opUnaryEType? op etyp1 with
              | some result_etyp =>
                  simp [h_opEType_result] at h_typecheck
                  injection h_typecheck with h_res_eq
                  have h_opEType_final : opUnaryEType? op result1.qualType.etyp = some result_etyp := by
                    rw [h_qt1]
                    exact h_opEType_result
                  simp only [Nat.add_sub_cancel]
                  subst h_res_eq
                  refine ⟨result1, result_etyp, h_tc1_result, h_opEType_final, rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
                  simp [h_qt1]
              | none =>
                  simp [h_opEType_result] at h_typecheck
      | error msg =>
          simp [h_tc1_result, bind, Except.bind] at h_typecheck

-- Helper lemma: extract evaluation structure from successful beval of unary operation.
private lemma bevalUnaryOp_structure (op : UnaryOp) (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₂ : Config) (v : Value) :
  (∃ w₀ w₁, LeanPoison.beval fuel config₀ (Expr.unaryop op e1) verbose w₀ =
      EST.Out.ok (.success config₂ v) w₁) →
  ∃ (config₁ : Config) (v1 : Value),
    (∃ w₀' w₁', LeanPoison.beval (fuel - 1) config₀ e1 verbose w₀' =
        EST.Out.ok (.success config₁ v1) w₁') ∧
    LeanPoison.evalUnaryOp op v1 = some v ∧
    config₁.memory = config₂.memory ∧
    config₁.varEnv = config₂.varEnv := by
  intro h_eval
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  cases fuel with
  | zero =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      injection h_eq with h_contr
      cases h_contr
  | succ fuel' =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      simp [bind, Bind.bind, EST.bind] at h_eq
      split at h_eq
      · next h_result1 h_state1 h_beval1 =>
        split at h_eq
        · next config₁ v₁ =>
          cases h_evalOp : LeanPoison.evalUnaryOp op v₁ with
          | some v_result =>
              simp [h_evalOp] at h_eq
              injection h_eq with h_eq_result h_eq_state
              injection h_eq_result with h_eq_cfg h_eq_val
              have h_mem_eq : config₁.memory = config₂.memory := by
                rw [h_eq_cfg]
              have h_var_eq : config₁.varEnv = config₂.varEnv := by
                rw [h_eq_cfg]
              -- Rewrite evalUnaryOp to use the final value v.
              rw [h_eq_val] at h_evalOp
              subst h_eq_cfg
              have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval fuel' config₀ e1 verbose w₀' =
                  EST.Out.ok (.success config₁ v₁) w₁' :=
                ⟨w₀, h_state1, h_beval1⟩
              simp only [Nat.add_sub_cancel]
              exact ⟨config₁, v₁, h_beval1_ex, h_evalOp, h_mem_eq, h_var_eq⟩
          | none =>
              simp [h_evalOp] at h_eq
              injection h_eq with h_eq_result h_eq_state
              injection h_eq_result
        · next =>
            simp [pure] at h_eq
            injection h_eq with h_eq_result h_eq_state
            injection h_eq_result
        · next msg =>
            simp [pure] at h_eq
            injection h_eq with h_eq_result h_eq_state
            injection h_eq_result
      · next h_error1 h_state1 =>
        injection h_eq

-- Structure lemma for binary-op typechecking.
private lemma typecheckOp_structure (ctx : TypeContext) (e1 e2 : Expr) (op : Op) (fuel : Nat)
    (res : TypeResult) :
  typecheckOp ctx e1 e2 fuel op = .ok res →
  ∃ (result1 result2 : TypeResult) (result_etyp : ETyp),
    typecheckExpr ctx e1 (fuel - 1) = .ok result1 ∧
    typecheckExpr { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv',
                             nextLoc := result1.nextLoc', nextTag := result1.nextTag' } e2 (fuel - 1) = .ok result2 ∧
    opEType? op result1.qualType.etyp result2.qualType.etyp = some result_etyp ∧
    res.memEnv' = result2.memEnv' ∧
    res.tagEnv' = result2.tagEnv' ∧
    res.nextLoc' = result2.nextLoc' ∧
    res.nextTag' = result2.nextTag' ∧
    res.qualType.etyp = result_etyp ∧
    res.qualType.poison = joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison) ∧
    res.qualType.pred = Predicate.noPred := by
  intro h_typecheck
  cases fuel with
  | zero =>
      simp [typecheckOp] at h_typecheck
  | succ fuel' =>
      unfold typecheckOp at h_typecheck
      simp at h_typecheck
      cases h_tc1_result : typecheckExpr ctx e1 fuel' with
      | ok result1 =>
          simp [h_tc1_result, bind, Except.bind] at h_typecheck
          match h_qt1 : result1.qualType with
          | QTyp.mk etyp1 p1 pred1 =>
              rw [h_qt1] at h_typecheck
              cases h_tc2_result :
                (typecheckExpr { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv',
                                             nextLoc := result1.nextLoc', nextTag := result1.nextTag' } e2 fuel') with
              | ok result2 =>
                  simp [h_tc2_result] at h_typecheck
                  match h_qt2 : result2.qualType with
                  | QTyp.mk etyp2 p2 pred2 =>
                      rw [h_qt2] at h_typecheck
                      simp at h_typecheck
                      cases h_opEType_result : opEType? op etyp1 etyp2 with
                      | some result_etyp =>
                          simp [h_opEType_result] at h_typecheck
                          injection h_typecheck with h_res_eq
                          have h_opEType_final :
                              opEType? op result1.qualType.etyp result2.qualType.etyp = some result_etyp := by
                            rw [h_qt1, h_qt2]
                            exact h_opEType_result
                          simp only [Nat.add_sub_cancel]
                          subst h_res_eq
                          refine ⟨result1, result2, result_etyp, h_tc1_result, h_tc2_result, h_opEType_final,
                                  rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
                          simp [h_qt1, h_qt2]
                      | none =>
                          simp [h_opEType_result] at h_typecheck
              | error msg2 =>
                  simp [h_tc2_result] at h_typecheck
      | error msg =>
          simp [h_tc1_result, bind, Except.bind] at h_typecheck

-- Helper lemma: extract evaluation structure from successful beval of binary operation.
private lemma bevalOp_structure (e1 e2 : Expr) (op : Op) (fuel : Nat) (verbose : Bool)
    (config₀ config₃ : Config) (v : Value) :
  (∃ w₀ w₁, LeanPoison.beval fuel config₀ (Expr.op e1 op e2) verbose w₀ =
      EST.Out.ok (.success config₃ v) w₁) →
  ∃ (config₁ config₂ : Config) (v1 v2 : Value),
    (∃ w₀' w₁', LeanPoison.beval (fuel - 1) config₀ e1 verbose w₀' =
        EST.Out.ok (.success config₁ v1) w₁') ∧
    (∃ w₀'' w₁'', LeanPoison.beval (fuel - 1) config₁ e2 verbose w₀'' =
        EST.Out.ok (.success config₂ v2) w₁'') ∧
    LeanPoison.evalOp op v1 v2 = some v ∧
    config₂.memory = config₃.memory ∧
    config₂.varEnv = config₃.varEnv := by
  intro h_eval
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  cases fuel with
  | zero =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      injection h_eq with h_contr
      cases h_contr
  | succ fuel' =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      simp [bind, Bind.bind, EST.bind] at h_eq
      split at h_eq
      · next h_result1 h_state1 h_beval1 =>
        split at h_eq
        · next config₁ v₁ =>
          try simp [EST.bind] at h_eq
          split at h_eq
          · next h_result2 h_state2 h_beval2 =>
            split at h_eq
            · next config₂ v₂ =>
              cases h_evalOp : LeanPoison.evalOp op v₁ v₂ with
              | some v_result =>
                  simp [h_evalOp] at h_eq
                  injection h_eq with h_eq_result h_eq_state
                  injection h_eq_result with h_eq_cfg h_eq_val
                  have h_mem_eq : config₂.memory = config₃.memory := by
                    rw [h_eq_cfg]
                  have h_var_eq : config₂.varEnv = config₃.varEnv := by
                    rw [h_eq_cfg]
                  rw [h_eq_val] at h_evalOp
                  subst h_eq_cfg
                  have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval fuel' config₀ e1 verbose w₀' =
                        EST.Out.ok (.success config₁ v₁) w₁' :=
                    ⟨w₀, h_state1, h_beval1⟩
                  have h_beval2_ex : ∃ w₀'' w₁'', LeanPoison.beval fuel' config₁ e2 verbose w₀'' =
                        EST.Out.ok (.success config₂ v₂) w₁'' :=
                    ⟨h_state1, h_state2, h_beval2⟩
                  simp only [Nat.add_sub_cancel]
                  exact ⟨config₁, config₂, v₁, v₂, h_beval1_ex, h_beval2_ex, h_evalOp, h_mem_eq, h_var_eq⟩
              | none =>
                  simp [h_evalOp] at h_eq
                  injection h_eq with h_eq_result h_eq_state
                  injection h_eq_result
            · next =>
                simp [pure] at h_eq
                injection h_eq with h_eq_result h_eq_state
                injection h_eq_result
            · next msg =>
                simp [pure] at h_eq
                injection h_eq with h_eq_result h_eq_state
                injection h_eq_result
          · next h_error2 h_state2 =>
            injection h_eq
        · next =>
            simp [pure] at h_eq
            injection h_eq with h_eq_result h_eq_state
            injection h_eq_result
        · next msg =>
            simp [pure] at h_eq
            injection h_eq with h_eq_result h_eq_state
            injection h_eq_result
      · next h_error1 h_state1 =>
        injection h_eq

-- Structure lemma for seq typechecking.
private lemma typecheckSeq_structure (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult) :
  typecheckSeq ctx e1 e2 fuel = .ok res →
  ∃ (result1 result2 : TypeResult) (ctx' : TypeContext),
    typecheckExpr ctx e1 (fuel - 1) = .ok result1 ∧
    ctx' = { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag' } ∧
    typecheckExpr ctx' e2 (fuel - 1) = .ok result2 ∧
    res.qualType.etyp = result2.qualType.etyp ∧
    res.memEnv' = result2.memEnv' ∧
    res.tagEnv' = result2.tagEnv' ∧
    res.nextLoc' = result2.nextLoc' ∧
    res.nextTag' = result2.nextTag' ∧
    res.qualType.poison = joinPoison result1.qualType.poison result2.qualType.poison ∧
    res.qualType.pred = result2.qualType.pred := by
  intro h_typecheck
  cases fuel with
  | zero =>
      simp [typecheckSeq] at h_typecheck
  | succ fuel' =>
      unfold typecheckSeq at h_typecheck
      simp at h_typecheck
      simp [bind, Except.bind] at h_typecheck
      cases h_tc1 : typecheckExpr ctx e1 fuel' with
      | ok result1 =>
          simp [h_tc1] at h_typecheck
          cases h_qt1 : result1.qualType with
          | mk _etyp1 p1 pred1 =>
              rw [h_qt1] at h_typecheck
              simp at h_typecheck
              cases h_tc2 :
                (typecheckExpr { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv',
                                             nextLoc := result1.nextLoc', nextTag := result1.nextTag' } e2 fuel') with
              | ok result2 =>
                  simp (config := { failIfUnchanged := false }) [h_tc2] at h_typecheck
                  cases h_qt2 : result2.qualType with
                  | mk _etyp2 p2 pred2 =>
                      rw [h_qt2] at h_typecheck
                      simp at h_typecheck
                      simp [pure, Except.pure] at h_typecheck
                      let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv',
                                              nextLoc := result1.nextLoc', nextTag := result1.nextTag' }
                      cases h_typecheck
                      refine ⟨result1, result2, ctx', ?_⟩
                      simp [ctx', h_tc1, h_tc2, h_qt1, h_qt2]
              | error err =>
                  simp (config := { failIfUnchanged := false }) [h_tc2] at h_typecheck
      | error err =>
          simp [h_tc1] at h_typecheck

-- Helper lemma: extract evaluation structure from successful beval of sequence.
private lemma bevalSeq_structure (e1 e2 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₂ : Config) (v : Value) :
  (∃ w₀ w₁, LeanPoison.beval fuel config₀ (Expr.seq e1 e2) verbose w₀ =
      EST.Out.ok (.success config₂ v) w₁) →
  ∃ (config₁ : Config) (v1 : Value),
    (∃ w₀' w₁', LeanPoison.beval (fuel - 1) config₀ e1 verbose w₀' =
        EST.Out.ok (.success config₁ v1) w₁') ∧
    (∃ w₀'' w₁'', LeanPoison.beval (fuel - 1) config₁ e2 verbose w₀'' =
        EST.Out.ok (.success config₂ v) w₁'') := by
  intro h_eval
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  cases fuel with
  | zero =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      injection h_eq with h_contr
      cases h_contr
  | succ fuel' =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      simp [bind, Bind.bind, EST.bind] at h_eq
      split at h_eq
      · next h_result1 h_state1 h_beval1 =>
        split at h_eq
        · next config₁ v₁ =>
          try simp [EST.bind] at h_eq
          split at h_eq
          · next h_result2 h_state2 h_beval2 =>
            split at h_eq
            · next config₂ v₂ =>
              injection h_eq with h_eq_result h_eq_state
              injection h_eq_result with h_eq_cfg h_eq_val
              subst h_eq_val
              subst h_eq_cfg
              have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval fuel' config₀ e1 verbose w₀' =
                    EST.Out.ok (.success config₁ v₁) w₁' :=
                ⟨w₀, h_state1, h_beval1⟩
              have h_beval2_ex : ∃ w₀'' w₁'', LeanPoison.beval fuel' config₁ e2 verbose w₀'' =
                    EST.Out.ok (.success config₂ v₂) w₁'' :=
                ⟨h_state1, h_state2, h_beval2⟩
              simp only [Nat.add_sub_cancel]
              exact ⟨config₁, v₁, h_beval1_ex, h_beval2_ex⟩
            · next =>
                simp [pure] at h_eq
                injection h_eq with h_eq_result h_eq_state
                injection h_eq_result
            · next msg =>
                simp [pure] at h_eq
                injection h_eq with h_eq_result h_eq_state
                injection h_eq_result
          · next h_error2 h_state2 =>
            injection h_eq
        · next =>
            simp [pure] at h_eq
            injection h_eq with h_eq_result h_eq_state
            injection h_eq_result
        · next msg =>
            simp [pure] at h_eq
            injection h_eq with h_eq_result h_eq_state
            injection h_eq_result
      · next h_error1 h_state1 =>
        injection h_eq

-- Structure lemma for vlet typechecking.
private lemma typecheckVlet_structure (ctx : TypeContext) (x : Name) (e1 e2 : Expr) (fuel : Nat)
    (res : TypeResult) :
  typecheckVlet ctx x e1 e2 fuel = .ok res →
  ∃ (result1 result2 : TypeResult) (ctx' : TypeContext),
    typecheckExpr ctx e1 (fuel - 1) = .ok result1 ∧
    ctx' = ({ ctx with memEnv := result1.memEnv', varEnv := ctx.varEnv.update x result1.qualType, tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag' }) ∧
    typecheckExpr ctx' e2 (fuel - 1) = .ok result2 ∧
    res.qualType.etyp = result2.qualType.etyp ∧
    res.memEnv' = result2.memEnv' ∧
    res.tagEnv' = result2.tagEnv' ∧
    res.nextLoc' = result2.nextLoc' ∧
    res.nextTag' = result2.nextTag' ∧
    res.qualType.poison = joinPoison ctx.pc result2.qualType.poison ∧
    res.qualType.pred = result2.qualType.pred := by
  intro h_typecheck
  cases fuel with
  | zero =>
      simp [typecheckVlet] at h_typecheck
  | succ fuel' =>
      unfold typecheckVlet at h_typecheck
      simp at h_typecheck
      simp [bind, Except.bind] at h_typecheck
      cases h_tc1 : typecheckExpr ctx e1 fuel' with
      | ok result1 =>
          simp [h_tc1] at h_typecheck
          cases h_tc2 :
            typecheckExpr
                { ctx with memEnv := result1.memEnv', varEnv := ctx.varEnv.update x result1.qualType,
                           tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag' }
                e2 fuel' with
          | ok result2 =>
              simp [h_tc2] at h_typecheck
              cases h_qt2 : result2.qualType with
              | mk _etyp2 p2 pred2 =>
                  rw [h_qt2] at h_typecheck
                  simp at h_typecheck
                  simp [pure, Except.pure] at h_typecheck
                  let ctx' := { ctx with memEnv := result1.memEnv', varEnv := ctx.varEnv.update x result1.qualType, tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag' }
                  cases h_typecheck
                  refine ⟨result1, result2, ctx', ?_⟩
                  simp [ctx', h_tc1, h_tc2, h_qt2]
          | error err =>
              simp [h_tc2] at h_typecheck
      | error err =>
          simp [h_tc1] at h_typecheck

-- Helper lemma: extract evaluation structure from successful beval of vlet.
private lemma bevalVlet_structure (x : Name) (e1 e2 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config_final : Config) (v : Value) :
  (∃ w₀ w₁, LeanPoison.beval fuel config₀ (Expr.vlet x e1 e2) verbose w₀ =
      EST.Out.ok (.success config_final v) w₁) →
  ∃ (config₁ config₂ config₃ : Config) (v1 : Value),
    (∃ w₀' w₁', LeanPoison.beval (fuel - 1) config₀ e1 verbose w₀' =
        EST.Out.ok (.success config₁ v1) w₁') ∧
    config₂ = { config₁ with varEnv := config₁.varEnv.update x v1 } ∧
    (∃ w₀'' w₁'', LeanPoison.beval (fuel - 1) config₂ e2 verbose w₀'' =
        EST.Out.ok (.success config₃ v) w₁'') ∧
    config_final = { config₃ with varEnv := config₁.varEnv } := by
  intro h_eval
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  cases fuel with
  | zero =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      injection h_eq with h_contr
      cases h_contr
  | succ fuel' =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      simp [bind, Bind.bind, EST.bind] at h_eq
      split at h_eq
      · next h_result1 h_state1 h_beval1 =>
        split at h_eq
        · next config₁' v₁ =>
          -- e1 evaluated successfully, now e2
          let config₂' := { config₁' with varEnv := config₁'.varEnv.update x v₁ }
          -- Evaluate e2 in config₂'
          simp [EST.bind] at h_eq
          split at h_eq
          · next h_result2 h_state2 h_beval2 =>
            split at h_eq
            · next config₃' v₂ =>
              -- e2 evaluated successfully
              injection h_eq with h_eq_result h_eq_state
              injection h_eq_result with h_eq_cfg h_eq_val
              -- Construct existentials for h_beval1 and h_beval2
              have h_beval1_ex :
                  ∃ w₀' w₁', LeanPoison.beval fuel' config₀ e1 verbose w₀' =
                    EST.Out.ok (.success config₁' v₁) w₁' :=
                ⟨w₀, h_state1, h_beval1⟩
              have h_beval2_ex :
                  ∃ w₀'' w₁'', LeanPoison.beval fuel' config₂' e2 verbose w₀'' =
                    EST.Out.ok (.success config₃' v₂) w₁'' :=
                ⟨h_state1, h_state2, h_beval2⟩
              -- Now subst to get final config and value
              subst h_eq_cfg h_eq_val
              simp only [Nat.add_sub_cancel]
              exact ⟨config₁', config₂', config₃', v₁, h_beval1_ex, rfl, h_beval2_ex, rfl⟩
            · next =>
              simp [pure] at h_eq
              injection h_eq with h_eq_result h_eq_state
              injection h_eq_result
            · next msg =>
              simp [pure] at h_eq
              injection h_eq with h_eq_result h_eq_state
              injection h_eq_result
          · next h_error2 h_state2 =>
            injection h_eq
        · next =>
          simp [pure] at h_eq
          injection h_eq with h_eq_result h_eq_state
          injection h_eq_result
        · next msg =>
          simp [pure] at h_eq
          injection h_eq with h_eq_result h_eq_state
          injection h_eq_result
      · next h_error1 h_state1 =>
        injection h_eq

-- Helper lemma: extract evaluation structure from successful beval of printInt
private lemma bevalPrintInt_structure (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value) :
  (∃ w₀ w₁, LeanPoison.beval fuel config₀ (Expr.printInt e1) verbose w₀ =
      EST.Out.ok (.success config₁ v) w₁) →
  ∃ (config' : Config) (v1 : Value),
    (∃ w₀' w₁', LeanPoison.beval (fuel - 1) config₀ e1 verbose w₀' = EST.Out.ok (.success config' v1) w₁') ∧
    (∃ n, v1 = Value.num n) ∧
    v = Value.unit ∧
    config'.memory = config₁.memory ∧
    config'.varEnv = config₁.varEnv := by
  intro h_eval
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  cases fuel with
  | zero =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      injection h_eq with h_contr
      cases h_contr
  | succ fuel' =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      simp [bind, Bind.bind, EST.bind] at h_eq
      split at h_eq
      · next h_result1 h_state1 h_beval1 =>
        split at h_eq
        · next config' v₁ =>
          -- After the println, we return success
          simp [Functor.map, EST.bind] at h_eq
          split at h_eq
          · next p_result p_state =>
            injection h_eq with h_eq_result h_eq_state
            injection h_eq_result with h_eq_cfg h_eq_val
            subst h_eq_cfg h_eq_val
            -- Construct existential for h_beval1
            have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config' (Value.num v₁)) w₁' :=
              ⟨w₀, h_state1, h_beval1⟩
            simp only [Nat.add_sub_cancel]
            refine ⟨config', Value.num v₁, h_beval1_ex, ⟨v₁, rfl⟩, ?_, ?_, ?_⟩
            · simp
            · simp
            · simp
          · next p_error p_state =>
            injection h_eq
        · next v =>
          -- e1 evaluated to non-number value (contradiction)
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
        · next =>
          -- e1 evaluation returned outOfFuel (contradiction)
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
        · next msg =>
          -- e1 evaluation returned runtimeError (contradiction)
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
      · next h_error1 h_state1 =>
        injection h_eq

-- Helper lemma: extract evaluation structure from successful beval of printString
private lemma bevalPrintString_structure (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value) :
  (∃ w₀ w₁, LeanPoison.beval fuel config₀ (Expr.printString e1) verbose w₀ =
      EST.Out.ok (.success config₁ v) w₁) →
  ∃ (config' : Config) (v1 : Value),
    (∃ w₀' w₁', LeanPoison.beval (fuel - 1) config₀ e1 verbose w₀' = EST.Out.ok (.success config' v1) w₁') ∧
    (∃ s, v1 = Value.str s) ∧
    v = Value.unit ∧
    config'.memory = config₁.memory ∧
    config'.varEnv = config₁.varEnv := by
  intro h_eval
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  cases fuel with
  | zero =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      injection h_eq with h_contr
      cases h_contr
  | succ fuel' =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      simp [bind, Bind.bind, EST.bind] at h_eq
      split at h_eq
      · next h_result1 h_state1 h_beval1 =>
        split at h_eq
        · next config' v₁ =>
          -- After the println, we return success
          simp [Functor.map, EST.bind] at h_eq
          split at h_eq
          · next p_result p_state =>
            injection h_eq with h_eq_result h_eq_state
            injection h_eq_result with h_eq_cfg h_eq_val
            subst h_eq_cfg h_eq_val
            -- Construct existential for h_beval1
            have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config' (Value.str v₁)) w₁' :=
              ⟨w₀, h_state1, h_beval1⟩
            simp only [Nat.add_sub_cancel]
            refine ⟨config', Value.str v₁, h_beval1_ex, ⟨v₁, rfl⟩, ?_, ?_, ?_⟩
            · simp
            · simp
            · simp
          · next p_error p_state =>
            injection h_eq
        · next v =>
          -- e1 evaluated to non-string value (contradiction)
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
        · next =>
          -- e1 evaluation returned outOfFuel (contradiction)
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
        · next msg =>
          -- e1 evaluation returned runtimeError (contradiction)
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
      · next h_error1 h_state1 =>
        injection h_eq

-- Helper lemma: extract structure from typecheckNewRef
private lemma typecheckNewRef_structure (ctx : TypeContext) (e1 : Expr) (fuel : Nat) (res : TypeResult) :
  typecheckNewRef ctx e1 fuel = .ok res →
  ∃ (result1 : TypeResult) (l : Loc) (etyp : ETyp),
    typecheckExpr ctx e1 (fuel - 1) = .ok result1 ∧
    l = result1.nextLoc' ∧
    res.qualType.etyp = ETyp.ref etyp (LocSet.singleton l) ∧
    res.qualType.poison = ctx.pc ∧
    res.qualType.pred = Predicate.noPred ∧
    res.memEnv' = updateMemEnv result1.memEnv' l ⟨etyp, joinPoison ctx.pc result1.qualType.poison, result1.qualType.pred⟩ ∧
    res.tagEnv' = result1.tagEnv' ∧
    res.nextLoc' = result1.nextLoc' + 1 ∧
    res.nextTag' = result1.nextTag' := by
  intro h_typecheck
  cases fuel with
  | zero =>
    unfold typecheckNewRef at h_typecheck
    simp at h_typecheck
  | succ fuel' =>
    unfold typecheckNewRef at h_typecheck
    simp at h_typecheck
    simp [bind, Except.bind] at h_typecheck
    cases h_tc1 : typecheckExpr ctx e1 fuel' with
    | ok result1 =>
      simp [h_tc1] at h_typecheck
      cases h_qt1 : result1.qualType with
      | mk etyp poison pred =>
        rw [h_qt1] at h_typecheck
        simp at h_typecheck
        -- Extract freshTLocRes result
        -- freshTLocRes result1 = (result1.nextLoc', { result1 with nextLoc' := result1.nextLoc' + 1 })
        have h_fresh : (result1.nextLoc', { result1 with nextLoc' := result1.nextLoc' + 1 }) = freshTLocRes result1 := rfl
        -- Simplify the do notation
        simp [pure, Except.pure] at h_typecheck
        -- Extract projections from h_fresh to rewrite freshTLocRes in h_typecheck
        have h_fresh1 : (freshTLocRes result1).1 = result1.nextLoc' := by
          simp [← h_fresh]
        have h_fresh2 : (freshTLocRes result1).2 = { result1 with nextLoc' := result1.nextLoc' + 1 } := by
          simp [← h_fresh]
        rw [h_fresh1, h_fresh2] at h_typecheck
        simp at h_typecheck
        -- Now h_typecheck is a record equality: {...} = res
        -- Extract field equalities by projecting from the record equality
        have h_qualType : res.qualType = ⟨ETyp.ref etyp (LocSet.singleton result1.nextLoc'), ctx.pc, Predicate.noPred⟩ := by
          have := congrArg TypeResult.qualType h_typecheck
          simp at this
          exact this.symm
        have h_memEnv : res.memEnv' = updateMemEnv result1.memEnv' result1.nextLoc' ⟨etyp, joinPoison ctx.pc poison, pred⟩ := by
          have := congrArg TypeResult.memEnv' h_typecheck
          simp at this
          exact this.symm
        have h_tagEnv : res.tagEnv' = result1.tagEnv' := by
          have := congrArg TypeResult.tagEnv' h_typecheck
          simp at this
          exact this.symm
        have h_nextLoc : res.nextLoc' = result1.nextLoc' + 1 := by
          have := congrArg TypeResult.nextLoc' h_typecheck
          simp at this
          exact this.symm
        have h_nextTag : res.nextTag' = result1.nextTag' := by
          have := congrArg TypeResult.nextTag' h_typecheck
          simp at this
          exact this.symm
        -- Extract qualType field equalities (QTyp is a structure, so we use congrArg)
        have h_etyp : res.qualType.etyp = ETyp.ref etyp (LocSet.singleton result1.nextLoc') := by
          have := congrArg QTyp.etyp h_qualType
          simp at this
          exact this
        have h_poison_eq : res.qualType.poison = ctx.pc := by
          have := congrArg QTyp.poison h_qualType
          simp at this
          exact this
        have h_pred_eq : res.qualType.pred = Predicate.noPred := by
          have := congrArg QTyp.pred h_qualType
          simp at this
          exact this
        -- Now we have all the field equalities
        -- Construct the existential
        simp only [Nat.add_sub_cancel]
        use result1, result1.nextLoc', etyp
        constructor
        · exact h_tc1
        constructor
        · rfl  -- l = result1.nextLoc'
        constructor
        · -- res.qualType.etyp = ETyp.ref etyp (LocSet.singleton l)
          rw [h_etyp]
        constructor
        · -- res.qualType.poison = ctx.pc
          rw [h_poison_eq]
        constructor
        · -- res.qualType.pred = Predicate.noPred
          rw [h_pred_eq]
        constructor
        · -- res.memEnv' = updateMemEnv result1.memEnv' result1.nextLoc' ...
          rw [h_memEnv]
          -- The goal is: updateMemEnv ... { etyp := etyp, poison := joinPoison ctx.pc poison, pred := pred } =
          --            updateMemEnv ... { etyp := etyp, poison := joinPoison ctx.pc result1.qualType.poison, pred := result1.qualType.pred }
          -- We need to show poison = result1.qualType.poison and pred = result1.qualType.pred
          -- This follows from h_qt1
          congr 1
          congr 1
          -- Extract poison and pred from h_qt1
          -- h_qt1 shows result1.qualType = { etyp := etyp, poison := poison, pred := pred }
          -- So result1.qualType.poison = poison and result1.qualType.pred = pred
          -- Use congr to show the equalities
          congr 1
          -- Now we need to show poison = result1.qualType.poison
          -- This follows from h_qt1 by extracting the poison field
          -- h_qt1 shows result1.qualType = { etyp := etyp, poison := poison, pred := pred }
          -- So result1.qualType.poison = poison
          simp [h_qt1]
          -- And pred = result1.qualType.pred
          simp [h_qt1]
        constructor
        · -- res.tagEnv' = result1.tagEnv'
          rw [h_tagEnv]
        constructor
        · -- res.nextLoc' = result1.nextLoc' + 1
          rw [h_nextLoc]
        · -- res.nextTag' = result1.nextTag'
          rw [h_nextTag]
    | error err =>
      simp [h_tc1] at h_typecheck

-- Helper lemma: extract evaluation structure from successful beval of newRef
private lemma bevalNewRef_structure (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₂ : Config) (v : Value) :
  (∃ w₀ w₁, LeanPoison.beval fuel config₀ (Expr.newRef e1) verbose w₀ =
      EST.Out.ok (.success config₂ v) w₁) →
  ∃ (config₁ : Config) (n : Int) (a : Address),
    (∃ w₀' w₁', LeanPoison.beval (fuel - 1) config₀ e1 verbose w₀' =
        EST.Out.ok (.success config₁ (Value.num n)) w₁') ∧
    a = config₁.nextAddr ∧
    config₂.memory = (config₁.memory.update a n) ∧
    config₂.nextAddr = config₁.nextAddr + 1 ∧
    config₂.varEnv = config₁.varEnv ∧
    v = Value.loc a := by
  intro h_eval
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  cases fuel with
  | zero =>
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    injection h_eq with h_contr
    cases h_contr
  | succ fuel' =>
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    simp [bind, Bind.bind, EST.bind] at h_eq
    split at h_eq
    · next h_result1 h_state1 h_beval1 =>
      cases h_result1 with
      | success config' v' =>
        cases v' with
        | num n =>
          simp at h_eq
          injection h_eq with h_eq_result h_eq_state
          injection h_eq_result with h_eq_cfg h_eq_val
          have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval fuel' config₀ e1 verbose w₀' =
              EST.Out.ok (.success config' (Value.num n)) w₁' :=
            ⟨w₀, h_state1, h_beval1⟩
          simp only [Nat.add_sub_cancel]
          use config', n, config'.nextAddr, h_beval1_ex, rfl
          simp [freshAddr] at h_eq_cfg h_eq_val
          constructor
          · -- config₂.memory = config₁.memory.update a n
            rw [← h_eq_cfg]
          constructor
          · -- config₂.nextAddr = config₁.nextAddr + 1
            rw [← h_eq_cfg]
          constructor
          · -- config₂.varEnv = config₁.varEnv
            rw [← h_eq_cfg]
          · -- v = Value.loc a
            rw [← h_eq_val]
        | bool _ | unit | str _ | loc _ | closure _ _ _ | peClosure _ _ _ =>
          simp [pure] at h_eq
          injection h_eq with h_contr
          cases h_contr
      | outOfFuel =>
        simp [pure] at h_eq
        injection h_eq with h_contr
        cases h_contr
      | runtimeError msg =>
        simp [pure] at h_eq
        injection h_eq with h_contr
        cases h_contr
    · next h_error1 h_state1 =>
      injection h_eq

private lemma stepFR_literal
  (ctx : TypeContext) (predSat : PredSat) (R : Regime)
  (e : Expr) (res : TypeResult) (v : Value)
  (hval : Expr.toValue? e = some v)
  (hpoison : res.qualType.poison = false)
  (hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls)
  (hctxAfter : ctxAfter ctx res = ctx) :
  StepFRW ctx R e res predSat := by
  intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hagree a₀ a₁ pm₀ pm₁ hwfcfg₀ hwfcfg₁ ht₀ ht₁
  have hterm₀ := terminatesTo_literal_inv e v hval μ₀ ρ₀ a₀ pm₀ cf₀ o₀ ht₀
  have hterm₁ := terminatesTo_literal_inv e v hval μ₁ ρ₁ a₁ pm₁ cf₁ o₁ ht₁
  rcases hterm₀ with ⟨hcf₀, ho₀⟩
  rcases hterm₁ with ⟨hcf₁, ho₁⟩
  subst hcf₀
  subst hcf₁
  refine ⟨θ₀, θ₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro l a hlookup
      exact hlookup
    · intro hwf'
      exact hwf'
  · refine ⟨?_, ?_⟩
    · intro l a hlookup
      exact hlookup
    · intro hwf'
      exact hwf'
  · simpa [hctxAfter] using hwf
  · exact hwfcfg₀  -- wfConfig cf₀ (unchanged since literal doesn't modify config)
  · exact hwfcfg₁  -- wfConfig cf₁ (unchanged since literal doesn't modify config)
  · simpa [hctxAfter] using hric₀
  · simpa [hctxAfter] using hric₁
  · simpa [hctxAfter] using htagR
  · simpa [hctxAfter] using hagree
  · intro _hclean
    have hval' : o₀ = o₁ := by
      simp [ho₀, ho₁]
    exact agreeValueUnder.clean_eq_nonref hpoison hnotref hval'

private lemma stepFR_var
  (ctxᵢ : TypeContext) (predSat : PredSat) (R : Regime)
  (name : Name) (res : TypeResult) (fuel : Nat)
  (htc : typecheck ctxᵢ (Expr.var name) (Nat.succ fuel) = .ok res) :
  StepFRW ctxᵢ R (Expr.var name) res predSat := by
  -- Variable case proof skeleton (full proof requires case analysis
  -- on predicates and tag environment).
  intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hagree a₀ a₁ pm₀ pm₁ hwfcfg₀ hwfcfg₁ ht₀ ht₁
  have hterm₀ := terminatesTo_var_inv name μ₀ ρ₀ a₀ pm₀ cf₀ o₀ ht₀
  have hterm₁ := terminatesTo_var_inv name μ₁ ρ₁ a₁ pm₁ cf₁ o₁ ht₁
  rcases hterm₀ with ⟨v₀, _hlookup₀, hcf₀, _ho₀⟩
  rcases hterm₁ with ⟨v₁, _hlookup₁, hcf₁, _ho₁⟩
  subst hcf₀
  subst hcf₁
  refine ⟨θ₀, θ₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro l a hlookup'
      exact hlookup'
    · intro hwf'
      exact hwf'
  · refine ⟨?_, ?_⟩
    · intro l a hlookup'
      exact hlookup'
    · intro hwf'
      exact hwf'
  · -- wfTypeContext: typecheckVar does not change the context
    have htc' : typecheckVar ctxᵢ name = .ok res := by
      simpa [typecheck, typecheckExpr] using htc
    have hmem : res.memEnv' = ctxᵢ.memEnv :=
      typecheckVar_preserves_memEnv ctxᵢ name res htc'
    have hnextLoc : res.nextLoc' = ctxᵢ.nextLoc :=
      typecheckVar_preserves_nextLoc ctxᵢ name res htc'
    simpa [ctxAfter, wfTypeContext, hmem, hnextLoc] using hwf
  · exact hwfcfg₀  -- wfConfig cf₀ (unchanged since var doesn't modify config)
  · exact hwfcfg₁  -- wfConfig cf₁ (unchanged since var doesn't modify config)
  · -- runtimeInstantiatesCtx for θ₀: typecheckVar does not change the context
    -- (memEnv, tagEnv, and fresh supplies are preserved)
    have htc' : typecheckVar ctxᵢ name = .ok res := by
      simpa [typecheck, typecheckExpr] using htc
    have hmem : res.memEnv' = ctxᵢ.memEnv :=
      typecheckVar_preserves_memEnv ctxᵢ name res htc'
    have htag : res.tagEnv' = ctxᵢ.tagEnv :=
      typecheckVar_preserves_tagEnv ctxᵢ name res htc'
    have hnextLoc : res.nextLoc' = ctxᵢ.nextLoc :=
      typecheckVar_preserves_nextLoc ctxᵢ name res htc'
    have hnextTag : res.nextTag' = ctxᵢ.nextTag :=
      typecheckVar_preserves_nextTag ctxᵢ name res htc'
    simpa [ctxAfter, hmem, htag, hnextLoc, hnextTag] using hric₀
  ·
    have htc' : typecheckVar ctxᵢ name = .ok res := by
      simpa [typecheck, typecheckExpr] using htc
    have hmem : res.memEnv' = ctxᵢ.memEnv :=
      typecheckVar_preserves_memEnv ctxᵢ name res htc'
    have htag : res.tagEnv' = ctxᵢ.tagEnv :=
      typecheckVar_preserves_tagEnv ctxᵢ name res htc'
    have hnextLoc : res.nextLoc' = ctxᵢ.nextLoc :=
      typecheckVar_preserves_nextLoc ctxᵢ name res htc'
    have hnextTag : res.nextTag' = ctxᵢ.nextTag :=
      typecheckVar_preserves_nextTag ctxᵢ name res htc'
    simpa [ctxAfter, hmem, htag, hnextLoc, hnextTag] using hric₁
  ·
    have htc' : typecheckVar ctxᵢ name = .ok res := by
      simpa [typecheck, typecheckExpr] using htc
    have hmem : res.memEnv' = ctxᵢ.memEnv :=
      typecheckVar_preserves_memEnv ctxᵢ name res htc'
    have htag : res.tagEnv' = ctxᵢ.tagEnv :=
      typecheckVar_preserves_tagEnv ctxᵢ name res htc'
    have hnextLoc : res.nextLoc' = ctxᵢ.nextLoc :=
      typecheckVar_preserves_nextLoc ctxᵢ name res htc'
    have hnextTag : res.nextTag' = ctxᵢ.nextTag :=
      typecheckVar_preserves_nextTag ctxᵢ name res htc'
    simpa [ctxAfter, hmem, htag, hnextLoc, hnextTag] using htagR
  · -- typecheckVar does not change the context
    -- (memEnv, tagEnv, and fresh supplies are preserved)
    have htc' : typecheckVar ctxᵢ name = .ok res := by
      simpa [typecheck, typecheckExpr] using htc
    have hmem : res.memEnv' = ctxᵢ.memEnv :=
      typecheckVar_preserves_memEnv ctxᵢ name res htc'
    have htag : res.tagEnv' = ctxᵢ.tagEnv :=
      typecheckVar_preserves_tagEnv ctxᵢ name res htc'
    have hnextLoc : res.nextLoc' = ctxᵢ.nextLoc :=
      typecheckVar_preserves_nextLoc ctxᵢ name res htc'
    have hnextTag : res.nextTag' = ctxᵢ.nextTag :=
      typecheckVar_preserves_nextTag ctxᵢ name res htc'
    simpa [ctxAfter, hmem, htag, hnextLoc, hnextTag] using hagree
  · -- Result agreement for clean outputs (requires predicate/tagEnv analysis).
    intro hclean
    have htc' : typecheckVar ctxᵢ name = .ok res := by
      simpa [typecheck, typecheckExpr] using htc
    cases hlookup_ctx : ctxᵢ.varEnv.lookup name with
    | none =>
        -- typecheckVar cannot succeed if the variable is missing
        simp [typecheckVar, hlookup_ctx] at htc'
    | some qt =>
        have hvar_agree_of_clean :
            qtypCleanUnder R qt →
            agreeVarUnder predSat R μ₀ ρ₀ μ₁ ρ₁ θ₀ θ₁ (name, qt) := by
          intro hclean_qt
          exact (hagree.2 name qt hlookup_ctx hclean_qt)
        cases hpred : qt.pred with
        | noPred =>
            have hres :
                res.qualType =
                  ⟨qt.etyp, joinPoison ctxᵢ.pc qt.poison, Predicate.noPred⟩ := by
              have htc'' := htc'
              cases hqt : qt with
              | mk etyp poison pred =>
                  have hpred' : pred = Predicate.noPred := by
                    simpa [hqt] using hpred
                  simp [typecheckVar, hlookup_ctx, hpred', hqt] at htc''
                  cases htc''
                  rfl
            have hjoin : joinPoison ctxᵢ.pc qt.poison = false := by
              simpa [qtypCleanUnder, qtypGuardTag, hres] using hclean
            have hpc_poison := joinPoison_eq_false hjoin
            have hpc : ctxᵢ.pc = false := hpc_poison.1
            have hpoison : qt.poison = false := hpc_poison.2
            have hclean_qt : qtypCleanUnder R qt := by
              simp [qtypCleanUnder, qtypGuardTag, hpred, hpoison]
            have hvar := hvar_agree_of_clean hclean_qt
            have hval : agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ :=
              agreeValueUnder_of_agreeVarUnder hvar _hlookup₀ _hlookup₁
            have hres_eq : res.qualType = qt := by
              cases qt with
              | mk etyp poison pred =>
                  cases hpred
                  simp [hres, hpc, joinPoison]
            have hres_agree :
                agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ res.qualType v₀ v₁ := by
              simpa [hres_eq] using hval
            simpa [_ho₀, _ho₁] using hres_agree
        | guardOnly k =>
            cases htag : ctxᵢ.tagEnv.get? k with
            | none =>
                have hres :
                    res.qualType =
                      ⟨qt.etyp, joinPoison ctxᵢ.pc qt.poison, qt.pred⟩ := by
                  have htc'' := htc'
                  cases hqt : qt with
                  | mk etyp poison pred =>
                      have hpred' : pred = Predicate.guardOnly k := by
                        simpa [hqt] using hpred
                      have htag' : ctxᵢ.tagEnv[k]? = none := by
                        simpa using htag
                      simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', pure, Except.pure] at htc''
                      cases htc''
                      simp [hpred']
                cases hclean with
                | inl hpoison_res =>
                    have hjoin : joinPoison ctxᵢ.pc qt.poison = false := by
                      have hpoison_res' := hpoison_res
                      simp [hres] at hpoison_res'
                      exact hpoison_res'
                    have hpc_poison := joinPoison_eq_false hjoin
                    have hpc : ctxᵢ.pc = false := hpc_poison.1
                    have hpoison : qt.poison = false := hpc_poison.2
                    have hclean_qt : qtypCleanUnder R qt := by
                      left
                      exact hpoison
                    have hvar := hvar_agree_of_clean hclean_qt
                    have hval : agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ :=
                      agreeValueUnder_of_agreeVarUnder hvar _hlookup₀ _hlookup₁
                    have hres_eq : res.qualType = qt := by
                      cases qt with
                      | mk etyp poison pred =>
                          cases hpred
                          simp [hres, hpc, joinPoison]
                    have hres_agree :
                        agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ res.qualType v₀ v₁ := by
                      simpa [hres_eq] using hval
                    simpa [_ho₀, _ho₁] using hres_agree
                | inr hguard =>
                    rcases hguard with ⟨k', htag', hregime⟩
                    have hk : k = k' := by
                      have : some k = some k' := by
                        simpa [qtypGuardTag, hres, hpred] using htag'
                      exact Option.some.inj this
                    subst hk
                    have hclean_qt : qtypCleanUnder R qt := by
                      right
                      refine ⟨k, ?_, hregime⟩
                      simp [qtypGuardTag, hpred]
                    have hvar := hvar_agree_of_clean hclean_qt
                    have hval : agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ :=
                      agreeValueUnder_of_agreeVarUnder hvar _hlookup₀ _hlookup₁
                    have hres_agree :
                        agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ res.qualType v₀ v₁ := by
                      cases hval with
                      | clean_eq_nonref _ hnotref hEq =>
                          have hnotref' : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
                            intro ⟨t, ls, h⟩
                            apply hnotref
                            exact ⟨t, ls, by simpa [hres] using h⟩
                          have htagRes : qtypGuardTag res.qualType = some k := by
                            simp [qtypGuardTag, hres, hpred]
                          exact agreeValueUnder.withPred_true_eq k htagRes hregime hnotref' hEq
                      | poisoned_noPred_eq_nonref _ hpred' _ _ =>
                          have : Predicate.noPred = Predicate.guardOnly k := by
                            calc
                              Predicate.noPred = qt.pred := by symm; exact hpred'
                              _ = Predicate.guardOnly k := by exact hpred
                          cases this
                      | clean_ref _ hetyp hlookup1 hin1 hv1 hlookup2 hin2 hv2 =>
                          have htagRes : qtypGuardTag res.qualType = some k := by
                            simp [qtypGuardTag, hres, hpred]
                          have hetyp' : res.qualType.etyp = qt.etyp := by
                            simp [hres]
                          exact agreeValueUnder.withPred_true_ref k htagRes hregime (hetyp'.trans hetyp)
                            hlookup1 hin1 hv1 hlookup2 hin2 hv2
                      | poisoned_noPred_ref _ hpred' hetyp _ _ _ _ _ _ =>
                          have : Predicate.noPred = Predicate.guardOnly k := by
                            calc
                              Predicate.noPred = qt.pred := by symm; exact hpred'
                              _ = Predicate.guardOnly k := by exact hpred
                          cases this
                      | withPred_true_eq _ _ _ hnotref hEq =>
                          have hnotref' : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
                            intro ⟨t, ls, h⟩
                            apply hnotref
                            exact ⟨t, ls, by simpa [hres] using h⟩
                          have htagRes : qtypGuardTag res.qualType = some k := by
                            simp [qtypGuardTag, hres, hpred]
                          exact agreeValueUnder.withPred_true_eq k htagRes hregime hnotref' hEq
                      | withPred_true_ref _ _ _ hetyp hlookup1 hin1 hv1 hlookup2 hin2 hv2 =>
                          have htagRes : qtypGuardTag res.qualType = some k := by
                            simp [qtypGuardTag, hres, hpred]
                          have hetyp' : res.qualType.etyp = qt.etyp := by
                            simp [hres]
                          exact agreeValueUnder.withPred_true_ref k htagRes hregime (hetyp'.trans hetyp)
                            hlookup1 hin1 hv1 hlookup2 hin2 hv2
                      | withPred_false_poisoned_fail k' _ htag hreg _ _ _ =>
                          have hk : k = k' := by
                            have : some k = some k' := by
                              calc
                                some k = qtypGuardTag qt := by simp [qtypGuardTag, hpred]
                                _ = some k' := by exact htag
                            exact Option.some.inj this
                          subst hk
                          have : (some false : Option Bool) = some true := by
                            calc
                              some false = R k := by symm; exact hreg
                              _ = some true := by exact hregime
                          cases this
                      | guardOnly_false_poisoned_any k' hgo hreg _ =>
                          have hk : k = k' := by
                            have : some k = some k' := by
                              calc
                                some k = qtypGuardTag qt := by simp [qtypGuardTag, hpred]
                                _ = some k' := by simp [qtypGuardTag, hgo]
                            exact Option.some.inj this
                          subst hk
                          have : (some false : Option Bool) = some true := by
                            calc
                              some false = R k := by symm; exact hreg
                              _ = some true := by exact hregime
                          cases this
                    simpa [_ho₀, _ho₁] using hres_agree
            | some tv =>
                cases tv with
                | mk b deps =>
                    cases b with
                    | true =>
                        have hres :
                            res.qualType =
                              ⟨qt.etyp, ctxᵢ.pc, Predicate.noPred⟩ := by
                          have htc'' := htc'
                          cases hqt : qt with
                          | mk etyp poison pred =>
                              have hpred' : pred = Predicate.guardOnly k := by
                                simpa [hqt] using hpred
                              have htag' : ctxᵢ.tagEnv[k]? = some ⟨true, deps⟩ := by
                                simpa using htag
                              simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', pure, Except.pure] at htc''
                              cases htc''
                              rfl
                        have hpc : ctxᵢ.pc = false := by
                          -- clean result requires pc = false
                          simpa [qtypCleanUnder, qtypGuardTag, hres] using hclean
                        have hregime : R k = some true := by
                          exact htagR k deps (by simpa [htag] using htag)
                        have hclean_qt : qtypCleanUnder R qt := by
                          right
                          refine ⟨k, ?_, hregime⟩
                          simp [qtypGuardTag, hpred]
                        have hvar := hvar_agree_of_clean hclean_qt
                        have hval : agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ :=
                          agreeValueUnder_of_agreeVarUnder hvar _hlookup₀ _hlookup₁
                        have hres_agree :
                            agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ res.qualType v₀ v₁ := by
                          cases hval with
                          | clean_eq_nonref _ hnotref hEq =>
                              have hnotref' : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
                                intro ⟨t, ls, h⟩
                                apply hnotref
                                exact ⟨t, ls, by simpa [hres] using h⟩
                              exact agreeValueUnder.clean_eq_nonref (by simp [hres, hpc]) hnotref' hEq
                          | poisoned_noPred_eq_nonref _ hpred' _ _ =>
                              have : Predicate.noPred = Predicate.guardOnly k := by
                                calc
                                  Predicate.noPred = qt.pred := by symm; exact hpred'
                                  _ = Predicate.guardOnly k := by exact hpred
                              cases this
                          | clean_ref _ hetyp hlookup1 hin1 hv1 hlookup2 hin2 hv2 =>
                              have hetyp' : res.qualType.etyp = qt.etyp := by
                                simp [hres]
                              have hpoison' : res.qualType.poison = false := by
                                simp [hres, hpc]
                              exact agreeValueUnder.clean_ref hpoison' (hetyp'.trans hetyp)
                                hlookup1 hin1 hv1 hlookup2 hin2 hv2
                          | poisoned_noPred_ref _ hpred' hetyp _ _ _ _ _ _ =>
                              have : Predicate.noPred = Predicate.guardOnly k := by
                                calc
                                  Predicate.noPred = qt.pred := by symm; exact hpred'
                                  _ = Predicate.guardOnly k := by exact hpred
                              cases this
                          | withPred_true_eq _ _ _ hnotref hEq =>
                              have hnotref' : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
                                intro ⟨t, ls, h⟩
                                apply hnotref
                                exact ⟨t, ls, by simpa [hres] using h⟩
                              have hpoison' : res.qualType.poison = false := by
                                simp [hres, hpc]
                              exact agreeValueUnder.clean_eq_nonref hpoison' hnotref' hEq
                          | withPred_true_ref _ _ _ hetyp hlookup1 hin1 hv1 hlookup2 hin2 hv2 =>
                              have hetyp' : res.qualType.etyp = qt.etyp := by
                                simp [hres]
                              have hpoison' : res.qualType.poison = false := by
                                simp [hres, hpc]
                              exact agreeValueUnder.clean_ref hpoison' (hetyp'.trans hetyp)
                                hlookup1 hin1 hv1 hlookup2 hin2 hv2
                          | withPred_false_poisoned_fail k' _ htag hreg _ _ _ =>
                              have hk : k = k' := by
                                have : some k = some k' := by
                                  calc
                                    some k = qtypGuardTag qt := by simp [qtypGuardTag, hpred]
                                    _ = some k' := by exact htag
                                exact Option.some.inj this
                              subst hk
                              have : (some false : Option Bool) = some true := by
                                calc
                                  some false = R k := by symm; exact hreg
                                  _ = some true := by exact hregime
                              cases this
                          | guardOnly_false_poisoned_any k' hgo hreg _ =>
                              have hk : k = k' := by
                                have : some k = some k' := by
                                  calc
                                    some k = qtypGuardTag qt := by simp [qtypGuardTag, hpred]
                                    _ = some k' := by simp [qtypGuardTag, hgo]
                                exact Option.some.inj this
                              subst hk
                              have : (some false : Option Bool) = some true := by
                                calc
                                  some false = R k := by symm; exact hreg
                                  _ = some true := by exact hregime
                              cases this
                        simpa [_ho₀, _ho₁] using hres_agree
                    | false =>
                        have hres :
                            res.qualType =
                              ⟨qt.etyp, true, Predicate.noPred⟩ := by
                          have htc'' := htc'
                          cases hqt : qt with
                          | mk etyp poison pred =>
                              have hpred' : pred = Predicate.guardOnly k := by
                                simpa [hqt] using hpred
                              have htag' : ctxᵢ.tagEnv[k]? = some ⟨false, deps⟩ := by
                                simpa using htag
                              simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', pure, Except.pure] at htc''
                              cases htc''
                              rfl
                        -- poisoned result is not clean
                        simp [qtypCleanUnder, qtypGuardTag, hres] at hclean
        | guardClosure k arg_name pred_body var_env =>
            cases htag : ctxᵢ.tagEnv.get? k with
            | none =>
                have hres :
                    res.qualType =
                      ⟨qt.etyp, joinPoison ctxᵢ.pc qt.poison, qt.pred⟩ := by
                  have htc'' := htc'
                  cases hqt : qt with
                  | mk etyp poison pred =>
                      have hpred' : pred = Predicate.guardClosure k arg_name pred_body var_env := by
                        simpa [hqt] using hpred
                      have htag' : ctxᵢ.tagEnv[k]? = none := by
                        simpa using htag
                      simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', pure, Except.pure] at htc''
                      cases htc''
                      simp [hpred']
                cases hclean with
                | inl hpoison_res =>
                    have hjoin : joinPoison ctxᵢ.pc qt.poison = false := by
                      have hpoison_res' := hpoison_res
                      simp [hres] at hpoison_res'
                      exact hpoison_res'
                    have hpc_poison := joinPoison_eq_false hjoin
                    have hpc : ctxᵢ.pc = false := hpc_poison.1
                    have hpoison : qt.poison = false := hpc_poison.2
                    have hclean_qt : qtypCleanUnder R qt := by
                      left
                      exact hpoison
                    have hvar := hvar_agree_of_clean hclean_qt
                    have hval : agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ :=
                      agreeValueUnder_of_agreeVarUnder hvar _hlookup₀ _hlookup₁
                    have hres_agree :
                        agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ res.qualType v₀ v₁ := by
                      have hqt_eq : qt = ⟨qt.etyp, false, qt.pred⟩ := by
                        cases qt with
                        | mk etyp poison pred =>
                            simpa [hpoison]
                      have hres_eq : res.qualType = qt := by
                        have : res.qualType = ⟨qt.etyp, false, qt.pred⟩ := by
                          simp [hres, hpoison, hpc, joinPoison]
                        exact this.trans hqt_eq.symm
                      simpa [hres_eq] using hval
                    simpa [_ho₀, _ho₁] using hres_agree
                | inr hguard =>
                    rcases hguard with ⟨k', htag', hregime⟩
                    have hk : k = k' := by
                      have : some k = some k' := by
                        simpa [qtypGuardTag, hres, hpred] using htag'
                      exact Option.some.inj this
                    subst hk
                    have hclean_qt : qtypCleanUnder R qt := by
                      right
                      refine ⟨k, ?_, hregime⟩
                      simp [qtypGuardTag, hpred]
                    have hvar := hvar_agree_of_clean hclean_qt
                    have hval : agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ :=
                      agreeValueUnder_of_agreeVarUnder hvar _hlookup₀ _hlookup₁
                    have hres_agree :
                        agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ res.qualType v₀ v₁ := by
                      cases hval with
                      | clean_eq_nonref _ hnotref hEq =>
                          have hnotref' : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
                            intro ⟨t, ls, h⟩
                            apply hnotref
                            exact ⟨t, ls, by simpa [hres] using h⟩
                          have htagRes : qtypGuardTag res.qualType = some k := by
                            simp [qtypGuardTag, hres, hpred]
                          exact agreeValueUnder.withPred_true_eq k htagRes hregime hnotref' hEq
                      | poisoned_noPred_eq_nonref _ hpred' _ _ =>
                          have : Predicate.noPred = Predicate.guardClosure k arg_name pred_body var_env := by
                            calc
                              Predicate.noPred = qt.pred := by symm; exact hpred'
                              _ = Predicate.guardClosure k arg_name pred_body var_env := by exact hpred
                          cases this
                      | clean_ref _ hetyp hlookup1 hin1 hv1 hlookup2 hin2 hv2 =>
                          have htagRes : qtypGuardTag res.qualType = some k := by
                            simp [qtypGuardTag, hres, hpred]
                          have hetyp' : res.qualType.etyp = qt.etyp := by
                            simp [hres]
                          exact agreeValueUnder.withPred_true_ref k htagRes hregime (hetyp'.trans hetyp)
                            hlookup1 hin1 hv1 hlookup2 hin2 hv2
                      | poisoned_noPred_ref _ hpred' hetyp _ _ _ _ _ _ =>
                          have : Predicate.noPred = Predicate.guardClosure k arg_name pred_body var_env := by
                            calc
                              Predicate.noPred = qt.pred := by symm; exact hpred'
                              _ = Predicate.guardClosure k arg_name pred_body var_env := by exact hpred
                          cases this
                      | withPred_true_eq _ _ _ hnotref hEq =>
                          have hnotref' : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
                            intro ⟨t, ls, h⟩
                            apply hnotref
                            exact ⟨t, ls, by simpa [hres] using h⟩
                          have htagRes : qtypGuardTag res.qualType = some k := by
                            simp [qtypGuardTag, hres, hpred]
                          exact agreeValueUnder.withPred_true_eq k htagRes hregime hnotref' hEq
                      | withPred_true_ref _ _ _ hetyp hlookup1 hin1 hv1 hlookup2 hin2 hv2 =>
                          have htagRes : qtypGuardTag res.qualType = some k := by
                            simp [qtypGuardTag, hres, hpred]
                          have hetyp' : res.qualType.etyp = qt.etyp := by
                            simp [hres]
                          exact agreeValueUnder.withPred_true_ref k htagRes hregime (hetyp'.trans hetyp)
                            hlookup1 hin1 hv1 hlookup2 hin2 hv2
                      | withPred_false_poisoned_fail k' _ htag hreg _ _ _ =>
                          have hk : k = k' := by
                            have : some k = some k' := by
                              calc
                                some k = qtypGuardTag qt := by simp [qtypGuardTag, hpred]
                                _ = some k' := by exact htag
                            exact Option.some.inj this
                          subst hk
                          have : (some false : Option Bool) = some true := by
                            calc
                              some false = R k := by symm; exact hreg
                              _ = some true := by exact hregime
                          cases this
                      | guardOnly_false_poisoned_any k' hgo hreg _ =>
                          have hk : k = k' := by
                            have : some k = some k' := by
                              calc
                                some k = qtypGuardTag qt := by simp [qtypGuardTag, hpred]
                                _ = some k' := by simp [qtypGuardTag, hgo]
                            exact Option.some.inj this
                          subst hk
                          have : (some false : Option Bool) = some true := by
                            calc
                              some false = R k := by symm; exact hreg
                              _ = some true := by exact hregime
                          cases this
                    simpa [_ho₀, _ho₁] using hres_agree
            | some tv =>
                cases tv with
                | mk b deps =>
                    cases b with
                    | true =>
                        have hres :
                            res.qualType =
                              ⟨qt.etyp, ctxᵢ.pc, Predicate.noPred⟩ := by
                          have htc'' := htc'
                          cases hqt : qt with
                          | mk etyp poison pred =>
                              have hpred' : pred = Predicate.guardClosure k arg_name pred_body var_env := by
                                simpa [hqt] using hpred
                              have htag' : ctxᵢ.tagEnv[k]? = some ⟨true, deps⟩ := by
                                simpa using htag
                              simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', pure, Except.pure] at htc''
                              cases htc''
                              rfl
                        have hpc : ctxᵢ.pc = false := by
                          simpa [qtypCleanUnder, qtypGuardTag, hres] using hclean
                        have hregime : R k = some true := by
                          exact htagR k deps (by simpa [htag] using htag)
                        have hclean_qt : qtypCleanUnder R qt := by
                          right
                          refine ⟨k, ?_, hregime⟩
                          simp [qtypGuardTag, hpred]
                        have hvar := hvar_agree_of_clean hclean_qt
                        have hval : agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ :=
                          agreeValueUnder_of_agreeVarUnder hvar _hlookup₀ _hlookup₁
                        have hres_agree :
                            agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ res.qualType v₀ v₁ := by
                          cases hval with
                          | clean_eq_nonref _ hnotref hEq =>
                              have hnotref' : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
                                intro ⟨t, ls, h⟩
                                apply hnotref
                                exact ⟨t, ls, by simpa [hres] using h⟩
                              have hpoison' : res.qualType.poison = false := by
                                simp [hres, hpc]
                              exact agreeValueUnder.clean_eq_nonref hpoison' hnotref' hEq
                          | poisoned_noPred_eq_nonref _ hpred' _ _ =>
                              have : Predicate.noPred = Predicate.guardClosure k arg_name pred_body var_env := by
                                calc
                                  Predicate.noPred = qt.pred := by symm; exact hpred'
                                  _ = Predicate.guardClosure k arg_name pred_body var_env := by exact hpred
                              cases this
                          | clean_ref _ hetyp hlookup1 hin1 hv1 hlookup2 hin2 hv2 =>
                              have hetyp' : res.qualType.etyp = qt.etyp := by
                                simp [hres]
                              have hpoison' : res.qualType.poison = false := by
                                simp [hres, hpc]
                              exact agreeValueUnder.clean_ref hpoison' (hetyp'.trans hetyp)
                                hlookup1 hin1 hv1 hlookup2 hin2 hv2
                          | poisoned_noPred_ref _ hpred' hetyp _ _ _ _ _ _ =>
                              have : Predicate.noPred = Predicate.guardClosure k arg_name pred_body var_env := by
                                calc
                                  Predicate.noPred = qt.pred := by symm; exact hpred'
                                  _ = Predicate.guardClosure k arg_name pred_body var_env := by exact hpred
                              cases this
                          | withPred_true_eq _ _ _ hnotref hEq =>
                              have hnotref' : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
                                intro ⟨t, ls, h⟩
                                apply hnotref
                                exact ⟨t, ls, by simpa [hres] using h⟩
                              have hpoison' : res.qualType.poison = false := by
                                simp [hres, hpc]
                              exact agreeValueUnder.clean_eq_nonref hpoison' hnotref' hEq
                          | withPred_true_ref _ _ _ hetyp hlookup1 hin1 hv1 hlookup2 hin2 hv2 =>
                              have hetyp' : res.qualType.etyp = qt.etyp := by
                                simp [hres]
                              have hpoison' : res.qualType.poison = false := by
                                simp [hres, hpc]
                              exact agreeValueUnder.clean_ref hpoison' (hetyp'.trans hetyp)
                                hlookup1 hin1 hv1 hlookup2 hin2 hv2
                          | withPred_false_poisoned_fail k' _ htag hreg _ _ _ =>
                              have hk : k = k' := by
                                have : some k = some k' := by
                                  calc
                                    some k = qtypGuardTag qt := by simp [qtypGuardTag, hpred]
                                    _ = some k' := by exact htag
                                exact Option.some.inj this
                              subst hk
                              have : (some false : Option Bool) = some true := by
                                calc
                                  some false = R k := by symm; exact hreg
                                  _ = some true := by exact hregime
                              cases this
                          | guardOnly_false_poisoned_any k' hgo hreg _ =>
                              have hk : k = k' := by
                                have : some k = some k' := by
                                  calc
                                    some k = qtypGuardTag qt := by simp [qtypGuardTag, hpred]
                                    _ = some k' := by simp [qtypGuardTag, hgo]
                                exact Option.some.inj this
                              subst hk
                              have : (some false : Option Bool) = some true := by
                                calc
                                  some false = R k := by symm; exact hreg
                                  _ = some true := by exact hregime
                              cases this
                        simpa [_ho₀, _ho₁] using hres_agree
                    | false =>
                        have hres :
                            res.qualType =
                              ⟨qt.etyp, true, Predicate.noPred⟩ := by
                          have htc'' := htc'
                          cases hqt : qt with
                          | mk etyp poison pred =>
                              have hpred' : pred = Predicate.guardClosure k arg_name pred_body var_env := by
                                simpa [hqt] using hpred
                              have htag' : ctxᵢ.tagEnv[k]? = some ⟨false, deps⟩ := by
                                simpa using htag
                              simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', pure, Except.pure] at htc''
                              cases htc''
                              rfl
                        -- poisoned result is not clean
                        simp [qtypCleanUnder, qtypGuardTag, hres] at hclean

-- Step theorem spec variant using world-indexed termination.
private def TypeSystemEnforcesFaultRobustness_step_specW
  (e : Expr)
  (ctxᵢ : TypeContext)
  (predSat : PredSat) : Prop :=
  ∀ (fuel : Nat) (res : TypeResult),
    typecheck ctxᵢ e fuel = .ok res →
    ∀ (R : Regime),
      StepFRW ctxᵢ R e res predSat

private theorem TypeSystemEnforcesFaultRobustness_stepW
  (e : Expr) (ctxᵢ : TypeContext) (predSat : PredSat) :
  TypeSystemEnforcesFaultRobustness_step_specW e ctxᵢ predSat := by
  unfold TypeSystemEnforcesFaultRobustness_step_specW
  intro fuel
  revert e ctxᵢ
  induction fuel using Nat.strong_induction_on with
  | _ n IH =>
    intro e ctxᵢ res htc R
    cases n with
    | zero =>
        simp [typecheck, typecheckExpr] at htc
    | succ fuel =>
        cases e with
        | unit =>
            simp [typecheck, typecheckExpr, typecheckUnit] at htc
            let res_expected : TypeResult := {
              qualType := ⟨ETyp.unit, false, Predicate.noPred⟩
              memEnv' := ctxᵢ.memEnv
              tagEnv' := ctxᵢ.tagEnv
              nextLoc' := ctxᵢ.nextLoc
              nextTag' := ctxᵢ.nextTag
            }
            have hres : res = res_expected := by
              cases htc
              rfl
            have hval : Expr.toValue? Expr.unit = some Value.unit := by
              simp [Expr.toValue?]
            have hpoison : res.qualType.poison = false := by
              simp [hres, res_expected]
            have hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
              simp [hres, res_expected]
            have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
              simp [ctxAfter, hres, res_expected]
            exact stepFR_literal ctxᵢ predSat R Expr.unit res Value.unit hval hpoison hnotref hctxAfter
        | num n =>
            simp [typecheck, typecheckExpr, typecheckInt] at htc
            let res_expected : TypeResult := {
              qualType := ⟨ETyp.int, false, Predicate.noPred⟩
              memEnv' := ctxᵢ.memEnv
              tagEnv' := ctxᵢ.tagEnv
              nextLoc' := ctxᵢ.nextLoc
              nextTag' := ctxᵢ.nextTag
            }
            have hres : res = res_expected := by
              cases htc
              rfl
            have hval : Expr.toValue? (Expr.num n) = some (Value.num n) := by
              simp [Expr.toValue?]
            have hpoison : res.qualType.poison = false := by
              simp [hres, res_expected]
            have hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
              simp [hres, res_expected]
            have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
              simp [ctxAfter, hres, res_expected]
            exact stepFR_literal ctxᵢ predSat R (Expr.num n) res (Value.num n) hval hpoison hnotref hctxAfter
        | bool b =>
            simp [typecheck, typecheckExpr, typecheckBool] at htc
            let res_expected : TypeResult := {
              qualType := ⟨ETyp.bool, false, Predicate.noPred⟩
              memEnv' := ctxᵢ.memEnv
              tagEnv' := ctxᵢ.tagEnv
              nextLoc' := ctxᵢ.nextLoc
              nextTag' := ctxᵢ.nextTag
            }
            have hres : res = res_expected := by
              cases htc
              rfl
            have hval : Expr.toValue? (Expr.bool b) = some (Value.bool b) := by
              simp [Expr.toValue?]
            have hpoison : res.qualType.poison = false := by
              simp [hres, res_expected]
            have hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
              simp [hres, res_expected]
            have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
              simp [ctxAfter, hres, res_expected]
            exact stepFR_literal ctxᵢ predSat R (Expr.bool b) res (Value.bool b) hval hpoison hnotref hctxAfter
        | str s =>
            simp [typecheck, typecheckExpr, typecheckString] at htc
            let res_expected : TypeResult := {
              qualType := ⟨ETyp.string, false, Predicate.noPred⟩
              memEnv' := ctxᵢ.memEnv
              tagEnv' := ctxᵢ.tagEnv
              nextLoc' := ctxᵢ.nextLoc
              nextTag' := ctxᵢ.nextTag
            }
            have hres : res = res_expected := by
              cases htc
              rfl
            have hval : Expr.toValue? (Expr.str s) = some (Value.str s) := by
              simp [Expr.toValue?]
            have hpoison : res.qualType.poison = false := by
              simp [hres, res_expected]
            have hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
              simp [hres, res_expected]
            have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
              simp [ctxAfter, hres, res_expected]
            exact stepFR_literal ctxᵢ predSat R (Expr.str s) res (Value.str s) hval hpoison hnotref hctxAfter
        | var name =>
            exact stepFR_var ctxᵢ predSat R name res fuel htc
        | op e1 op e2 =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr_op_succ, typecheckOp] at htc
            | succ fuel' =>
                have htc' : typecheckOp ctxᵢ e1 e2 (Nat.succ fuel') op = .ok res := by
                  simpa [typecheck, typecheckExpr, typecheckExpr_op_succ] using htc
                obtain ⟨res1, res2, result_etyp, htc1, htc2, h_op, h_mem, h_tag, h_loc, h_ntag,
                        h_ret_etyp, h_ret_poison, h_ret_pred⟩ :=
                  typecheckOp_structure ctxᵢ e1 e2 op (Nat.succ fuel') res htc'
                let ctx' : TypeContext :=
                  { ctxᵢ with memEnv := res1.memEnv', tagEnv := res1.tagEnv', nextLoc := res1.nextLoc', nextTag := res1.nextTag' }
                have htc1' : typecheck ctxᵢ e1 fuel' = .ok res1 := by
                  simpa [typecheck, Nat.succ_sub_one] using htc1
                have htc2' : typecheck ctx' e2 fuel' = .ok res2 := by
                  simpa [ctx', typecheck, Nat.succ_sub_one] using htc2
                have hIH1 := IH (m := fuel') (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
                  e1 ctxᵢ res1 htc1' R
                have hIH2 := IH (m := fuel') (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
                  e2 ctx' res2 htc2' R
                intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hagree a₀ a₁ pm₀ pm₁ hwfcfg₀ hwfcfg₁ ht₀ ht₁
                -- Derive wfConfig for final configs using preservation lemma
                have hwfcf₀_final : wfConfig cf₀ := wfConfig_preservedW _ _ _ _ ht₀ hwfcfg₀
                have hwfcf₁_final : wfConfig cf₁ := wfConfig_preservedW _ _ _ _ ht₁ hwfcfg₁
                rcases ht₀ with ⟨fuel₀, verbose₀, w₀₀, w₀₁, hbeval₀⟩
                have hstruct₀ :=
                  bevalOp_structure e1 e2 op fuel₀ verbose₀
                    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm₀ }
                    cf₀ o₀ ⟨w₀₀, w₀₁, hbeval₀⟩
                rcases hstruct₀ with ⟨cfg₀1, cfg₀2, v₀1, v₀2, hbeval₀_e1, hbeval₀_e2, h_evalop₀, hmem₀, hvar₀⟩
                rcases ht₁ with ⟨fuel₁, verbose₁, w₁₀, w₁₁, hbeval₁⟩
                have hstruct₁ :=
                  bevalOp_structure e1 e2 op fuel₁ verbose₁
                    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm₁ }
                    cf₁ o₁ ⟨w₁₀, w₁₁, hbeval₁⟩
                rcases hstruct₁ with ⟨cfg₁1, cfg₁2, v₁1, v₁2, hbeval₁_e1, hbeval₁_e2, h_evalop₁, hmem₁, hvar₁⟩
                rcases hbeval₀_e1 with ⟨w₀e1, w₀e1', hbeval₀_e1'⟩
                rcases hbeval₀_e2 with ⟨w₀e2, w₀e2', hbeval₀_e2'⟩
                rcases hbeval₁_e1 with ⟨w₁e1, w₁e1', hbeval₁_e1'⟩
                rcases hbeval₁_e2 with ⟨w₁e2, w₁e2', hbeval₁_e2'⟩
                have ht₀_e1 :
                    terminatesToW e1
                      { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm₀ }
                      cfg₀1 v₀1 :=
                  ⟨fuel₀ - 1, verbose₀, w₀e1, w₀e1', hbeval₀_e1'⟩
                have ht₁_e1 :
                    terminatesToW e1
                      { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm₁ }
                      cfg₁1 v₁1 :=
                  ⟨fuel₁ - 1, verbose₁, w₁e1, w₁e1', hbeval₁_e1'⟩
                have hstep_e1 :=
                  hIH1 μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀1 cfg₁1 v₀1 v₁1
                    hθ₀ hθ₁ hwf hric₀ hric₁ htagR hagree a₀ a₁ pm₀ pm₁ hwfcfg₀ hwfcfg₁ ht₀_e1 ht₁_e1
                rcases hstep_e1 with
                  ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hwf1, hwfcf₀1, hwfcf₁1, hric₀1, hric₁1, htagR1, hagree_clean1, hres_agree1⟩
                have hθ₀1wf : wfRealizationMap θ₀1 := hθext₀1.2 hθ₀
                have hθ₁1wf : wfRealizationMap θ₁1 := hθext₁1.2 hθ₁
                have htagR_ctx' : tagEnvConsistentWithRegime ctx'.tagEnv R := by
                  simpa [ctx', ctxAfter] using htagR1
                have hric₀1' : runtimeInstantiatesCtx ctx' cfg₀1.memory cfg₀1.varEnv θ₀1 := by
                  simpa [ctx', ctxAfter] using hric₀1
                have hric₁1' : runtimeInstantiatesCtx ctx' cfg₁1.memory cfg₁1.varEnv θ₁1 := by
                  simpa [ctx', ctxAfter] using hric₁1
                have hagree_clean1' :
                    agreeOnClean predSat R ctx' cfg₀1.memory cfg₀1.varEnv θ₀1 cfg₁1.memory cfg₁1.varEnv θ₁1 := by
                  simpa [ctx', ctxAfter] using hagree_clean1
                have ht₀_e2 : terminatesToW e2 cfg₀1 cfg₀2 v₀2 :=
                  ⟨fuel₀ - 1, verbose₀, w₀e2, w₀e2', hbeval₀_e2'⟩
                have ht₁_e2 : terminatesToW e2 cfg₁1 cfg₁2 v₁2 :=
                  ⟨fuel₁ - 1, verbose₁, w₁e2, w₁e2', hbeval₁_e2'⟩
                have hwf1' : wfTypeContext ctx' := by simpa [ctx', ctxAfter] using hwf1
                have hstep_e2 :=
                  hIH2 cfg₀1.memory cfg₁1.memory cfg₀1.varEnv cfg₁1.varEnv θ₀1 θ₁1
                    cfg₀2 cfg₁2 v₀2 v₁2
                    hθ₀1wf hθ₁1wf hwf1' hric₀1' hric₁1' htagR_ctx' hagree_clean1'
                    cfg₀1.nextAddr cfg₁1.nextAddr cfg₀1.pureMode cfg₁1.pureMode hwfcf₀1 hwfcf₁1 ht₀_e2 ht₁_e2
                rcases hstep_e2 with
                  ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, hwf2, hwfcf₀2, hwfcf₁2, hric₀2, hric₁2, htagR2, hagree_clean2, hres_agree2⟩
                have hθext₀ : wfExtendsMap θ₀ θ₀2 := wfExtendsMap_trans hθext₀1 hθext₀2
                have hθext₁ : wfExtendsMap θ₁ θ₁2 := wfExtendsMap_trans hθext₁1 hθext₁2
                have hctxAfter : ctxAfter ctxᵢ res = ctxAfter ctx' res2 := by
                  simp [ctxAfter, ctx', h_mem, h_tag, h_loc, h_ntag]
                have hric₀'' :
                    runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 := by
                  simpa [hctxAfter, hmem₀, hvar₀] using hric₀2
                have hric₁'' :
                    runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁2 := by
                  simpa [hctxAfter, hmem₁, hvar₁] using hric₁2
                have htagR'' : tagEnvConsistentWithRegime (ctxAfter ctxᵢ res).tagEnv R := by
                  simpa [hctxAfter] using htagR2
                have hagree_clean :
                    agreeOnClean predSat R (ctxAfter ctxᵢ res)
                      cf₀.memory cf₀.varEnv θ₀2 cf₁.memory cf₁.varEnv θ₁2 := by
                  simpa [hctxAfter, hmem₀, hvar₀, hmem₁, hvar₁] using hagree_clean2
                refine ⟨θ₀2, θ₁2, hθext₀, hθext₁, ?_, ?_, ?_, hric₀'', hric₁'', htagR'', hagree_clean, ?_⟩
                · simpa [hctxAfter] using hwf2
                · exact hwfcf₀_final
                · exact hwfcf₁_final
                intro hclean
                have hpoison_res : res.qualType.poison = false := by
                  simpa [qtypCleanUnder, qtypGuardTag, h_ret_pred] using hclean
                have hjoin :
                    joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison) = false := by
                  calc
                    joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison) =
                        res.qualType.poison := by
                          symm
                          exact h_ret_poison
                    _ = false := by exact hpoison_res
                have hjoin_pc := joinPoison_eq_false hjoin
                have hjoin_12 := joinPoison_eq_false hjoin_pc.2
                have hclean1 : qtypCleanUnder R res1.qualType := by
                  left
                  exact hjoin_12.1
                have hclean2 : qtypCleanUnder R res2.qualType := by
                  left
                  exact hjoin_12.2
                have hagree_v1 :
                    agreeValueUnder predSat R cfg₀1.memory cfg₁1.memory θ₀1 θ₁1 res1.qualType v₀1 v₁1 :=
                  hres_agree1 hclean1
                have hagree_v2 :
                    agreeValueUnder predSat R cfg₀2.memory cfg₁2.memory θ₀2 θ₁2 res2.qualType v₀2 v₁2 :=
                  hres_agree2 hclean2
                have hnotref1 : ¬ ∃ t ls, res1.qualType.etyp = ETyp.ref t ls := by
                  intro hcontra
                  rcases hcontra with ⟨t, ls, h_etyp⟩
                  have hnone : opEType? op res1.qualType.etyp res2.qualType.etyp = none := by
                    simp [h_etyp, opEType?]
                  rw [hnone] at h_op
                  cases h_op
                have hnotref2 : ¬ ∃ t ls, res2.qualType.etyp = ETyp.ref t ls := by
                  intro hcontra
                  rcases hcontra with ⟨t, ls, h_etyp⟩
                  have hnone : opEType? op res1.qualType.etyp res2.qualType.etyp = none := by
                    simp [h_etyp, opEType?]
                  rw [hnone] at h_op
                  cases h_op
                have hv1Eq : v₀1 = v₁1 :=
                  agreeValueUnder_nonref_eq_of_clean hclean1 hnotref1 hagree_v1
                have hv2Eq : v₀2 = v₁2 :=
                  agreeValueUnder_nonref_eq_of_clean hclean2 hnotref2 hagree_v2
                have hEval₁' : LeanPoison.evalOp op v₀1 v₀2 = some o₁ := by
                  simpa [hv1Eq, hv2Eq] using h_evalop₁
                have hEq : o₀ = o₁ := by
                  have : some o₀ = some o₁ := by
                    calc
                      some o₀ = LeanPoison.evalOp op v₀1 v₀2 := by
                        symm
                        exact h_evalop₀
                      _ = some o₁ := by
                        exact hEval₁'
                  exact Option.some.inj this
                have hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
                  intro hcontra
                  rcases hcontra with ⟨t, ls, h_etyp⟩
                  have h_etyp' : result_etyp = ETyp.ref t ls := by
                    simpa [h_ret_etyp] using h_etyp
                  have h_op' : opEType? op res1.qualType.etyp res2.qualType.etyp = some (ETyp.ref t ls) := by
                    simpa [h_etyp'] using h_op
                  exact (opEType_ne_ref op res1.qualType.etyp res2.qualType.etyp t ls) h_op'
                exact agreeValueUnder.clean_eq_nonref hpoison_res hnotref hEq
        | unaryop op e =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr_unaryop_succ, typecheckUnaryOp] at htc
            | succ fuel' =>
                have htc' : typecheckUnaryOp ctxᵢ op e (Nat.succ fuel') = .ok res := by
                  simpa [typecheck, typecheckExpr, typecheckExpr_unaryop_succ] using htc
                obtain ⟨res1, result_etyp, htc1, h_op, h_mem, h_tag, h_loc, h_ntag, h_ret_etyp, h_ret_poison, h_ret_pred⟩ :=
                  typecheckUnaryOp_structure ctxᵢ op e (Nat.succ fuel') res htc'
                have htc1' : typecheck ctxᵢ e fuel' = .ok res1 := by
                  simpa [typecheck, Nat.succ_sub_one] using htc1
                have hIH := IH (m := fuel') (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
                  e ctxᵢ res1 htc1' R
                intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hagree a₀ a₁ pm₀ pm₁ hwfcfg₀ hwfcfg₁ ht₀ ht₁
                -- Derive wfConfig for final configs using preservation lemma
                have hwfcf₀_final : wfConfig cf₀ := wfConfig_preservedW _ _ _ _ ht₀ hwfcfg₀
                have hwfcf₁_final : wfConfig cf₁ := wfConfig_preservedW _ _ _ _ ht₁ hwfcfg₁
                rcases ht₀ with ⟨fuel₀, verbose₀, w₀₀, w₀₁, hbeval₀⟩
                have hstruct₀ :=
                  bevalUnaryOp_structure op e fuel₀ verbose₀
                    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm₀ }
                    cf₀ o₀ ⟨w₀₀, w₀₁, hbeval₀⟩
                rcases hstruct₀ with ⟨cfg₀', v₀', hbeval₀_e, h_evalop₀, hmem₀, hvar₀⟩
                rcases ht₁ with ⟨fuel₁, verbose₁, w₁₀, w₁₁, hbeval₁⟩
                have hstruct₁ :=
                  bevalUnaryOp_structure op e fuel₁ verbose₁
                    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm₁ }
                    cf₁ o₁ ⟨w₁₀, w₁₁, hbeval₁⟩
                rcases hstruct₁ with ⟨cfg₁', v₁', hbeval₁_e, h_evalop₁, hmem₁, hvar₁⟩
                rcases hbeval₀_e with ⟨w₀', w₀'', hbeval₀_e'⟩
                rcases hbeval₁_e with ⟨w₁', w₁'', hbeval₁_e'⟩
                have ht₀_e :
                    terminatesToW e
                      { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm₀ }
                      cfg₀' v₀' :=
                  ⟨fuel₀ - 1, verbose₀, w₀', w₀'', hbeval₀_e'⟩
                have ht₁_e :
                    terminatesToW e
                      { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm₁ }
                      cfg₁' v₁' :=
                  ⟨fuel₁ - 1, verbose₁, w₁', w₁'', hbeval₁_e'⟩
                have hstep_e :=
                  hIH μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀' cfg₁' v₀' v₁'
                    hθ₀ hθ₁ hwf hric₀ hric₁ htagR hagree a₀ a₁ pm₀ pm₁ hwfcfg₀ hwfcfg₁ ht₀_e ht₁_e
                rcases hstep_e with ⟨θ₀', θ₁', hθext₀, hθext₁, hwf', _hwfcf₀', _hwfcf₁', hric₀', hric₁', htagR', hagree_clean_e, hres_agree_e⟩
                have hctxAfter : ctxAfter ctxᵢ res = ctxAfter ctxᵢ res1 := by
                  simp [ctxAfter, h_mem, h_tag, h_loc, h_ntag]
                have hric₀'' :
                    runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀' := by
                  simpa [hctxAfter, hmem₀, hvar₀] using hric₀'
                have hric₁'' :
                    runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁' := by
                  simpa [hctxAfter, hmem₁, hvar₁] using hric₁'
                have htagR'' : tagEnvConsistentWithRegime (ctxAfter ctxᵢ res).tagEnv R := by
                  simpa [hctxAfter] using htagR'
                have hagree_clean :
                    agreeOnClean predSat R (ctxAfter ctxᵢ res)
                      cf₀.memory cf₀.varEnv θ₀' cf₁.memory cf₁.varEnv θ₁' := by
                  simpa [hctxAfter, hmem₀, hvar₀, hmem₁, hvar₁] using hagree_clean_e
                refine ⟨θ₀', θ₁', hθext₀, hθext₁, ?_, ?_, ?_, hric₀'', hric₁'', htagR'', hagree_clean, ?_⟩
                · simpa [hctxAfter] using hwf'
                · exact hwfcf₀_final
                · exact hwfcf₁_final
                intro hclean
                have hpoison_res : res.qualType.poison = false := by
                  simpa [qtypCleanUnder, qtypGuardTag, h_ret_pred] using hclean
                have hjoin : joinPoison ctxᵢ.pc res1.qualType.poison = false := by
                  calc
                    joinPoison ctxᵢ.pc res1.qualType.poison = res.qualType.poison := by
                      symm
                      exact h_ret_poison
                    _ = false := by exact hpoison_res
                have hres1_poison : res1.qualType.poison = false :=
                  (joinPoison_eq_false hjoin).2
                have hclean1 : qtypCleanUnder R res1.qualType := by
                  left
                  exact hres1_poison
                have hagree_v :
                    agreeValueUnder predSat R cfg₀'.memory cfg₁'.memory θ₀' θ₁' res1.qualType v₀' v₁' :=
                  hres_agree_e hclean1
                have hnotref1 : ¬ ∃ t ls, res1.qualType.etyp = ETyp.ref t ls := by
                  intro hcontra
                  rcases hcontra with ⟨t, ls, h_etyp⟩
                  have hnone : opUnaryEType? op res1.qualType.etyp = none := by
                    simp [h_etyp, opUnaryEType?]
                  rw [hnone] at h_op
                  cases h_op
                have hvEq : v₀' = v₁' :=
                  agreeValueUnder_nonref_eq_of_clean hclean1 hnotref1 hagree_v
                have hEval₁' : LeanPoison.evalUnaryOp op v₀' = some o₁ := by
                  simpa [hvEq] using h_evalop₁
                have hEq : o₀ = o₁ := by
                  have : some o₀ = some o₁ := by
                    calc
                      some o₀ = LeanPoison.evalUnaryOp op v₀' := by
                        symm
                        exact h_evalop₀
                      _ = some o₁ := by
                        exact hEval₁'
                  exact Option.some.inj this
                have hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
                  intro hcontra
                  rcases hcontra with ⟨t, ls, h_etyp⟩
                  have h_etyp' : result_etyp = ETyp.ref t ls := by
                    simpa [h_ret_etyp] using h_etyp
                  have h_op' : opUnaryEType? op res1.qualType.etyp = some (ETyp.ref t ls) := by
                    simpa [h_etyp'] using h_op
                  exact (opUnaryEType_ne_ref op res1.qualType.etyp t ls) h_op'
                exact agreeValueUnder.clean_eq_nonref hpoison_res hnotref hEq
        | ite e1 e2 e3 =>
            sorry
        | newRef e =>
            -- newRef case: allocate fresh location and store initial value
            -- Key: use freshLoc_not_realized to prove the new location is fresh
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr, typecheckNewRef] at htc
            | succ fuel' =>
                have htc' : typecheckNewRef ctxᵢ e (Nat.succ fuel') = .ok res := by
                  simpa [typecheck, typecheckExpr] using htc
                obtain ⟨res1, l, etyp, htc1, hl, h_etyp, h_poison, h_pred, h_mem, h_tag, h_loc, h_ntag⟩ :=
                  typecheckNewRef_structure ctxᵢ e (Nat.succ fuel') res htc'
                have htc1' : typecheck ctxᵢ e fuel' = .ok res1 := by
                  simpa [typecheck, Nat.succ_sub_one] using htc1
                have hIH := IH (m := fuel') (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
                  e ctxᵢ res1 htc1' R
                intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hagree a₀ a₁ pm₀ pm₁ hwfcfg₀ hwfcfg₁ ht₀ ht₁
                -- Derive wfConfig for final configs using preservation lemma
                have hwfcf₀_final : wfConfig cf₀ := wfConfig_preservedW _ _ _ _ ht₀ hwfcfg₀
                have hwfcf₁_final : wfConfig cf₁ := wfConfig_preservedW _ _ _ _ ht₁ hwfcfg₁
                rcases ht₀ with ⟨fuel₀, verbose₀, w₀₀, w₀₁, hbeval₀⟩
                have hstruct₀ :=
                  bevalNewRef_structure e fuel₀ verbose₀
                    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm₀ }
                    cf₀ o₀ ⟨w₀₀, w₀₁, hbeval₀⟩
                rcases hstruct₀ with ⟨cfg₀', n₀, a₀_new, hbeval₀_e, ha₀_new, hmem₀, hnextaddr₀, hvar₀, ho₀⟩
                rcases ht₁ with ⟨fuel₁, verbose₁, w₁₀, w₁₁, hbeval₁⟩
                have hstruct₁ :=
                  bevalNewRef_structure e fuel₁ verbose₁
                    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm₁ }
                    cf₁ o₁ ⟨w₁₀, w₁₁, hbeval₁⟩
                rcases hstruct₁ with ⟨cfg₁', n₁, a₁_new, hbeval₁_e, ha₁_new, hmem₁, hnextaddr₁, hvar₁, ho₁⟩
                rcases hbeval₀_e with ⟨w₀', w₀'', hbeval₀_e'⟩
                rcases hbeval₁_e with ⟨w₁', w₁'', hbeval₁_e'⟩
                have ht₀_e :
                    terminatesToW e
                      { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm₀ }
                      cfg₀' (Value.num n₀) :=
                  ⟨fuel₀ - 1, verbose₀, w₀', w₀'', hbeval₀_e'⟩
                have ht₁_e :
                    terminatesToW e
                      { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm₁ }
                      cfg₁' (Value.num n₁) :=
                  ⟨fuel₁ - 1, verbose₁, w₁', w₁'', hbeval₁_e'⟩
                have hstep_e :=
                  hIH μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀' cfg₁' (Value.num n₀) (Value.num n₁)
                    hθ₀ hθ₁ hwf hric₀ hric₁ htagR hagree a₀ a₁ pm₀ pm₁ hwfcfg₀ hwfcfg₁ ht₀_e ht₁_e
                rcases hstep_e with ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hwf1, hwfcf₀1, hwfcf₁1, hric₀1, hric₁1, htagR1, hagree_clean_e, hres_agree_e⟩
                -- Use freshLoc_not_realized to prove l is not in θ₀1 or θ₁1
                -- We need: l ≥ ctxᵢ.nextLoc
                -- From typecheckNewRef_structure: l = res1.nextLoc'
                -- We have hwf1 : wfTypeContext (ctxAfter ctxᵢ res1)
                -- This means: ∀ l', res1.memEnv'.contains l' → l' < res1.nextLoc'
                -- We also have hwf : wfTypeContext ctxᵢ
                -- This means: ∀ l', ctxᵢ.memEnv.contains l' → l' < ctxᵢ.nextLoc
                -- If res1.nextLoc' < ctxᵢ.nextLoc, then locations in ctxᵢ.memEnv (which are < ctxᵢ.nextLoc)
                -- would also be < res1.nextLoc', which is fine. But typechecking can only preserve or increase nextLoc.
                -- Actually, the key is: if res1.nextLoc' < ctxᵢ.nextLoc, then we'd have a contradiction
                -- because res1.memEnv' extends ctxᵢ.memEnv, and if ctxᵢ.memEnv contains locations ≥ res1.nextLoc',
                -- then wfTypeContext (ctxAfter ctxᵢ res1) would be violated.
                -- More directly: by wfTypeContext, all locations in ctxᵢ.memEnv are < ctxᵢ.nextLoc.
                -- If res1.nextLoc' < ctxᵢ.nextLoc, then all locations in ctxᵢ.memEnv are also < res1.nextLoc',
                -- which is consistent. But typechecking never decreases nextLoc, so res1.nextLoc' ≥ ctxᵢ.nextLoc.
                have h_l_ge : l ≥ ctxᵢ.nextLoc := by
                  -- l = res1.nextLoc' from hl
                  rw [hl]
                  -- Prove res1.nextLoc' ≥ ctxᵢ.nextLoc using wfTypeContext
                  -- By wfTypeContext, nextLoc is the high-water mark for locations in memEnv.
                  -- Typechecking can only add locations (never remove), so the high-water mark
                  -- can only increase or stay the same. Therefore, res1.nextLoc' ≥ ctxᵢ.nextLoc.
                  -- Direct proof: typechecking never decreases nextLoc (it preserves or increases it).
                  -- This is an invariant of the typechecking function that follows from its definition.
                  -- We use it directly here.
                  sorry  -- TODO: Prove res1.nextLoc' ≥ ctxᵢ.nextLoc (typechecking preserves/increases nextLoc)
                -- Need to show runtimeInstantiatesCtx ctxᵢ for freshLoc_not_realized
                -- We have hric₀1 for ctxAfter ctxᵢ res1, need to relate back to ctxᵢ
                -- For now, use the fact that ctxAfter extends ctxᵢ
                have hric₀1_ctx : runtimeInstantiatesCtx ctxᵢ cfg₀'.memory cfg₀'.varEnv θ₀1 := by
                  sorry  -- TODO: Prove runtimeInstantiatesCtx ctxᵢ from ctxAfter version
                have hric₁1_ctx : runtimeInstantiatesCtx ctxᵢ cfg₁'.memory cfg₁'.varEnv θ₁1 := by
                  sorry  -- TODO: Prove runtimeInstantiatesCtx ctxᵢ from ctxAfter version
                have h_fresh₀ : θ₀1.lookup l = none :=
                  freshLoc_not_realized ctxᵢ cfg₀'.memory cfg₀'.varEnv θ₀1 l hwf hric₀1_ctx h_l_ge
                have h_fresh₁ : θ₁1.lookup l = none :=
                  freshLoc_not_realized ctxᵢ cfg₁'.memory cfg₁'.varEnv θ₁1 l hwf hric₁1_ctx h_l_ge
                -- Extend maps: θ₀' = θ₀1.update l a₀_new, θ₁' = θ₁1.update l a₁_new
                let θ₀' := θ₀1.update l a₀_new
                let θ₁' := θ₁1.update l a₁_new
                -- Prove wfExtendsMap for the extended maps
                have hθext₀' : wfExtendsMap θ₀1 θ₀' := by
                  refine ⟨?_, ?_⟩
                  · -- extendsMap: θ₀1.lookup l' = some a' → θ₀'.lookup l' = some a'
                    intro l' a' hlookup
                    simp [RealizationMap.lookup]
                    -- If l' = l, then θ₀' has l → a₀_new, but θ₀1 doesn't have l (h_fresh₀)
                    -- So l' ≠ l, and insert preserves existing lookups
                    by_cases h_eq : l' = l
                    · -- l' = l: contradiction since θ₀1.lookup l = none
                      subst h_eq
                      rw [h_fresh₀] at hlookup
                      cases hlookup
                    · -- l' ≠ l: insert preserves lookup
                      -- θ₀' = θ₀1.update l a₀_new = θ₀1.insert l a₀_new
                      -- Since l' ≠ l, the lookup should be preserved
                      -- Expand θ₀' definition and use ExtTreeMap.getElem?_insert
                      have h_theta_def : θ₀' = θ₀1.insert l a₀_new := rfl
                      rw [h_theta_def]
                      rw [ExtTreeMap.getElem?_insert]
                      -- Need to show cmp l l' ≠ Ordering.eq (where cmp is Nat.compare since Loc = Nat)
                      by_cases h_cmp : compare l l' = Ordering.eq
                      · -- If cmp l l' = Ordering.eq, then l = l', which contradicts h_eq : ¬l' = l
                        have h_eq' : l = l' := LawfulEqCmp.eq_of_compare h_cmp
                        exact absurd h_eq'.symm h_eq
                      · -- cmp l l' ≠ Ordering.eq, so the if-then-else evaluates to θ₀1[l']?
                        simp [h_cmp]
                        -- Now we need θ₀1[l']? = some a', which is hlookup
                        -- hlookup is: θ₀1.lookup l' = some a'
                        -- Convert lookup to getElem? and use hlookup
                        simp [RealizationMap.lookup] at hlookup
                        rw [← ExtTreeMap.get?_eq_getElem?]
                        exact hlookup
                  · -- Preserves injectivity
                    intro hWF
                    -- θ₀' = θ₀1.insert l a₀_new, and l is fresh (not in θ₀1)
                    -- If θ₀1 is injective and l is fresh, then θ₀' is also injective
                    -- Use ExtTreeMap_insert_preserves_injectivity lemma
                    -- hWF : wfRealizationMap θ₀1 means θ₀1.isInjective
                    -- h_fresh₀ : θ₀1.lookup l = none means l is fresh
                    -- Convert to ExtTreeMap operations for the generic lemma
                    -- wfRealizationMap θ₀' = θ₀'.isInjective
                    simp only [wfRealizationMap] at hWF ⊢
                    unfold RealizationMap.isInjective
                    intro l₁ l₂ a hlookup1 hlookup2
                    -- Convert RealizationMap.lookup to ExtTreeMap.get?
                    -- Prove that a₀_new is not already in the range of θ₀1
                    -- This follows from the fact that a₀_new is a fresh address (nextAddr)
                    -- and runtimeInstantiatesCtx ensures all realized addresses are in memory
                    -- Since a₀_new hasn't been allocated yet, it's not in the range
                    have h_fresh_value' : ∀ l', θ₀1.get? l' ≠ some a₀_new := by
                      intro l' h_eq
                      -- If θ₀1.get? l' = some a₀_new, then by runtimeInstantiatesCtx,
                      -- we have cfg₀'.memory.contains a₀_new
                      -- But a₀_new = cfg₀'.nextAddr is the next address to allocate,
                      -- so it hasn't been allocated yet (not in cfg₀'.memory)
                      -- This is a contradiction
                      have h_lookup : θ₀1.lookup l' = some a₀_new := by
                        rw [RealizationMap.lookup]
                        rw [ExtTreeMap.get?_eq_getElem?]
                        exact h_eq
                      have h_contains : cfg₀'.memory.contains a₀_new :=
                        (hric₀1_ctx.1 l' a₀_new h_lookup).2
                      -- Use wfConfig: cfg₀'.memory.contains cfg₀'.nextAddr contradicts wfConfig cfg₀'
                      rw [ha₀_new] at h_contains
                      exact Nat.lt_irrefl cfg₀'.nextAddr (hwfcf₀1 cfg₀'.nextAddr h_contains)
                    have h_inj' : ∀ k₁ k₂ a, θ₀1.get? k₁ = some a → θ₀1.get? k₂ = some a → k₁ = k₂ := by
                      intro k₁ k₂ a h1 h2
                      exact hWF k₁ k₂ a h1 h2
                    have hlookup1' : (θ₀1.insert l a₀_new).get? l₁ = some a := hlookup1
                    have hlookup2' : (θ₀1.insert l a₀_new).get? l₂ = some a := hlookup2
                    exact ExtTreeMap_insert_preserves_injectivity θ₀1 l a₀_new h_fresh_value' h_inj' l₁ l₂ a hlookup1' hlookup2'
                have hθext₁' : wfExtendsMap θ₁1 θ₁' := by
                  -- Similar to hθext₀'
                  refine ⟨?_, ?_⟩
                  · intro l' a' hlookup
                    simp [RealizationMap.lookup]
                    by_cases h_eq : l' = l
                    · subst h_eq
                      rw [h_fresh₁] at hlookup
                      cases hlookup
                    · -- ExtTreeMap.insert preserves lookups for different keys
                      -- θ₁' = θ₁1.update l a₁_new = θ₁1.insert l a₁_new
                      -- Since l' ≠ l, the lookup should be preserved
                      have h_theta_def : θ₁' = θ₁1.insert l a₁_new := rfl
                      rw [h_theta_def]
                      rw [ExtTreeMap.getElem?_insert]
                      -- Need to show cmp l l' ≠ Ordering.eq (where cmp is Nat.compare since Loc = Nat)
                      by_cases h_cmp : compare l l' = Ordering.eq
                      · -- If cmp l l' = Ordering.eq, then l = l', which contradicts h_eq : ¬l' = l
                        have h_eq' : l = l' := LawfulEqCmp.eq_of_compare h_cmp
                        exact absurd h_eq'.symm h_eq
                      · -- cmp l l' ≠ Ordering.eq, so the if-then-else evaluates to θ₁1[l']?
                        simp [h_cmp]
                        simp [RealizationMap.lookup] at hlookup
                        rw [← ExtTreeMap.get?_eq_getElem?]
                        exact hlookup
                  · intro hWF
                    -- Similar to hθext₀', use ExtTreeMap_insert_preserves_injectivity
                    simp only [wfRealizationMap] at hWF ⊢
                    unfold RealizationMap.isInjective
                    intro l₁ l₂ a hlookup1 hlookup2
                    -- Convert RealizationMap.lookup to ExtTreeMap.get?
                    -- Prove that a₁_new is not already in the range of θ₁1 (similar to above)
                    have h_fresh_value' : ∀ l', θ₁1.get? l' ≠ some a₁_new := by
                      intro l' h_eq
                      -- Similar to θ₀1: use wfConfig to derive contradiction
                      have hric₁1_ctx := hric₁1
                      simp only [ctxAfter] at hric₁1_ctx
                      have h_lookup : θ₁1.lookup l' = some a₁_new := by
                        rw [RealizationMap.lookup]
                        rw [ExtTreeMap.get?_eq_getElem?]
                        exact h_eq
                      have h_contains : cfg₁'.memory.contains a₁_new :=
                        (hric₁1_ctx.1 l' a₁_new h_lookup).2
                      rw [ha₁_new] at h_contains
                      exact Nat.lt_irrefl cfg₁'.nextAddr (hwfcf₁1 cfg₁'.nextAddr h_contains)
                    have h_inj' : ∀ k₁ k₂ a, θ₁1.get? k₁ = some a → θ₁1.get? k₂ = some a → k₁ = k₂ := by
                      intro k₁ k₂ a h1 h2
                      exact hWF k₁ k₂ a h1 h2
                    have hlookup1' : (θ₁1.insert l a₁_new).get? l₁ = some a := hlookup1
                    have hlookup2' : (θ₁1.insert l a₁_new).get? l₂ = some a := hlookup2
                    exact ExtTreeMap_insert_preserves_injectivity θ₁1 l a₁_new h_fresh_value' h_inj' l₁ l₂ a hlookup1' hlookup2'
                -- Prove wfTypeContext for result
                have hwf_result : wfTypeContext (ctxAfter ctxᵢ res) := by
                  -- Use wfTypeContext_of_wfTypeResult if we can prove wfTypeResult res
                  -- Actually, we need to prove wfTypeResult res from typechecking
                  sorry  -- TODO: Prove wfTypeResult res from typechecking
                -- Prove runtimeInstantiatesCtx (new location is realized)
                have hric₀' : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀' := by
                  -- Need to show: all locations in res.memEnv' are in cf₀.memory with correct types
                  -- and the new location l is realized as a₀_new
                  sorry  -- TODO: Prove runtimeInstantiatesCtx with extended map
                have hric₁' : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁' := by
                  sorry  -- TODO: Prove runtimeInstantiatesCtx with extended map
                -- Prove tagEnvConsistentWithRegime
                have htagR' : tagEnvConsistentWithRegime (ctxAfter ctxᵢ res).tagEnv R := by
                  simp [ctxAfter, h_tag]
                  exact htagR1
                -- Prove agreeOnClean
                have hagree_clean :
                    agreeOnClean predSat R (ctxAfter ctxᵢ res)
                      cf₀.memory cf₀.varEnv θ₀' cf₁.memory cf₁.varEnv θ₁' := by
                  -- Use hagree_clean_e and extend with the new location
                  sorry  -- TODO: Prove agreeOnClean with extended maps
                refine ⟨θ₀', θ₁', ?_, ?_, ?_, ?_, ?_, hric₀', hric₁', htagR', hagree_clean, ?_⟩
                · -- wfExtendsMap θ₀ θ₀'
                  exact wfExtendsMap_trans hθext₀1 hθext₀'
                · -- wfExtendsMap θ₁ θ₁'
                  exact wfExtendsMap_trans hθext₁1 hθext₁'
                · -- wfTypeContext (ctxAfter ctxᵢ res)
                  exact hwf_result
                · exact hwfcf₀_final
                · exact hwfcf₁_final
                · -- resultAgreesIfClean
                  intro hclean
                  -- res.qualType.etyp = ETyp.ref etyp (LocSet.singleton l)
                  -- o₀ = Value.loc a₀_new, o₁ = Value.loc a₁_new
                  -- Need to use agreeValueUnder.clean_ref
                  have hpoison_res : res.qualType.poison = false := by
                    -- From hclean: qtypCleanUnder R res.qualType
                    -- res.qualType.poison = ctx.pc (from h_poison)
                    -- If ctx.pc = false, then res.qualType.poison = false
                    -- Actually, we need to extract this from hclean
                    sorry  -- TODO: Extract poison = false from hclean
                  -- Use agreeValueUnder.clean_ref
                  have hlookup1 : θ₀'.lookup l = some a₀_new := by
                    -- θ₀' = θ₀1.insert l a₀_new, so lookup l should return some a₀_new
                    -- Use ExtTreeMap.getElem?_insert_self: (t.insert k v)[k]? = some v
                    simp [RealizationMap.lookup]
                    rw [← ExtTreeMap.get?_eq_getElem?]
                    exact ExtTreeMap.getElem?_insert_self
                  have hlookup2 : θ₁'.lookup l = some a₁_new := by
                    -- Use ExtTreeMap.getElem?_insert_self: (t.insert k v)[k]? = some v
                    simp [RealizationMap.lookup]
                    rw [← ExtTreeMap.get?_eq_getElem?]
                    exact ExtTreeMap.getElem?_insert_self
                  have hin1 : l ∈ LocSet.singleton l := by
                    -- LocSet.singleton l = (∅ : LocSet).insert l
                    -- Need to show l is in this set
                    -- LocSet = ExtTreeSet Loc, so we need l ∈ (∅ : ExtTreeSet Loc).insert l
                    simp [LocSet.singleton]
                  have hin2 : l ∈ LocSet.singleton l := by
                    simp [LocSet.singleton]
                  exact agreeValueUnder.clean_ref hpoison_res h_etyp hlookup1 hin1 ho₀ hlookup2 hin2 ho₁
        | assign e1 e2 =>
            sorry
        | deref e =>
            sorry
        | seq e1 e2 =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr_seq_succ, typecheckSeq] at htc
            | succ fuel' =>
                have htc' : typecheckSeq ctxᵢ e1 e2 (Nat.succ fuel') = .ok res := by
                  simpa [typecheck, typecheckExpr, typecheckExpr_seq_succ] using htc
                obtain ⟨res1, res2, ctx', htc1, hctx', htc2, h_ret_etyp, h_mem, h_tag, h_loc, h_ntag,
                        h_ret_poison, h_ret_pred⟩ :=
                  typecheckSeq_structure ctxᵢ e1 e2 (Nat.succ fuel') res htc'
                have htc1' : typecheck ctxᵢ e1 fuel' = .ok res1 := by
                  simpa [typecheck, Nat.succ_sub_one] using htc1
                have htc2' : typecheck ctx' e2 fuel' = .ok res2 := by
                  simpa [hctx', typecheck, Nat.succ_sub_one] using htc2
                have hIH1 := IH (m := fuel') (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
                  e1 ctxᵢ res1 htc1' R
                have hIH2 := IH (m := fuel') (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
                  e2 ctx' res2 htc2' R
                intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hagree a₀ a₁ pm₀ pm₁ hwfcfg₀ hwfcfg₁ ht₀ ht₁
                -- Derive wfConfig for final configs using preservation lemma
                have hwfcf₀_final : wfConfig cf₀ := wfConfig_preservedW _ _ _ _ ht₀ hwfcfg₀
                have hwfcf₁_final : wfConfig cf₁ := wfConfig_preservedW _ _ _ _ ht₁ hwfcfg₁
                rcases ht₀ with ⟨fuel₀, verbose₀, w₀₀, w₀₁, hbeval₀⟩
                have hstruct₀ :=
                  bevalSeq_structure e1 e2 fuel₀ verbose₀
                    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm₀ }
                    cf₀ o₀ ⟨w₀₀, w₀₁, hbeval₀⟩
                rcases hstruct₀ with ⟨cfg₀1, v₀1, hbeval₀_e1, hbeval₀_e2⟩
                rcases ht₁ with ⟨fuel₁, verbose₁, w₁₀, w₁₁, hbeval₁⟩
                have hstruct₁ :=
                  bevalSeq_structure e1 e2 fuel₁ verbose₁
                    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm₁ }
                    cf₁ o₁ ⟨w₁₀, w₁₁, hbeval₁⟩
                rcases hstruct₁ with ⟨cfg₁1, v₁1, hbeval₁_e1, hbeval₁_e2⟩
                rcases hbeval₀_e1 with ⟨w₀e1, w₀e1', hbeval₀_e1'⟩
                rcases hbeval₀_e2 with ⟨w₀e2, w₀e2', hbeval₀_e2'⟩
                rcases hbeval₁_e1 with ⟨w₁e1, w₁e1', hbeval₁_e1'⟩
                rcases hbeval₁_e2 with ⟨w₁e2, w₁e2', hbeval₁_e2'⟩
                have ht₀_e1 :
                    terminatesToW e1
                      { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm₀ }
                      cfg₀1 v₀1 :=
                  ⟨fuel₀ - 1, verbose₀, w₀e1, w₀e1', hbeval₀_e1'⟩
                have ht₁_e1 :
                    terminatesToW e1
                      { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm₁ }
                      cfg₁1 v₁1 :=
                  ⟨fuel₁ - 1, verbose₁, w₁e1, w₁e1', hbeval₁_e1'⟩
                have hstep_e1 :=
                  hIH1 μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀1 cfg₁1 v₀1 v₁1
                    hθ₀ hθ₁ hwf hric₀ hric₁ htagR hagree a₀ a₁ pm₀ pm₁ hwfcfg₀ hwfcfg₁ ht₀_e1 ht₁_e1
                rcases hstep_e1 with
                  ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hwf1, hwfcf₀1, hwfcf₁1, hric₀1, hric₁1, htagR1, hagree_clean1, hres_agree1⟩
                have hθ₀1wf : wfRealizationMap θ₀1 := hθext₀1.2 hθ₀
                have hθ₁1wf : wfRealizationMap θ₁1 := hθext₁1.2 hθ₁
                have htagR_ctx' : tagEnvConsistentWithRegime ctx'.tagEnv R := by
                  simpa [hctx', ctxAfter] using htagR1
                have hric₀1' : runtimeInstantiatesCtx ctx' cfg₀1.memory cfg₀1.varEnv θ₀1 := by
                  simpa [hctx', ctxAfter] using hric₀1
                have hric₁1' : runtimeInstantiatesCtx ctx' cfg₁1.memory cfg₁1.varEnv θ₁1 := by
                  simpa [hctx', ctxAfter] using hric₁1
                have hagree_clean1' :
                    agreeOnClean predSat R ctx' cfg₀1.memory cfg₀1.varEnv θ₀1 cfg₁1.memory cfg₁1.varEnv θ₁1 := by
                  simpa [hctx', ctxAfter] using hagree_clean1
                have ht₀_e2 : terminatesToW e2 cfg₀1 cf₀ o₀ :=
                  ⟨fuel₀ - 1, verbose₀, w₀e2, w₀e2', hbeval₀_e2'⟩
                have ht₁_e2 : terminatesToW e2 cfg₁1 cf₁ o₁ :=
                  ⟨fuel₁ - 1, verbose₁, w₁e2, w₁e2', hbeval₁_e2'⟩
                have hwf1' : wfTypeContext ctx' := by simpa [hctx', ctxAfter] using hwf1
                have hstep_e2 :=
                  hIH2 cfg₀1.memory cfg₁1.memory cfg₀1.varEnv cfg₁1.varEnv θ₀1 θ₁1
                    cf₀ cf₁ o₀ o₁
                    hθ₀1wf hθ₁1wf hwf1' hric₀1' hric₁1' htagR_ctx' hagree_clean1'
                    cfg₀1.nextAddr cfg₁1.nextAddr cfg₀1.pureMode cfg₁1.pureMode hwfcf₀1 hwfcf₁1 ht₀_e2 ht₁_e2
                rcases hstep_e2 with
                  ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, hwf2, hwfcf₀2, hwfcf₁2, hric₀2, hric₁2, htagR2, hagree_clean2, hres_agree2⟩
                have hθext₀ : wfExtendsMap θ₀ θ₀2 := wfExtendsMap_trans hθext₀1 hθext₀2
                have hθext₁ : wfExtendsMap θ₁ θ₁2 := wfExtendsMap_trans hθext₁1 hθext₁2
                have hctxAfter : ctxAfter ctxᵢ res = ctxAfter ctx' res2 := by
                  simp [ctxAfter, hctx', h_mem, h_tag, h_loc, h_ntag]
                have hric₀'' :
                    runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 := by
                  simpa [hctxAfter] using hric₀2
                have hric₁'' :
                    runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁2 := by
                  simpa [hctxAfter] using hric₁2
                have htagR'' : tagEnvConsistentWithRegime (ctxAfter ctxᵢ res).tagEnv R := by
                  simpa [hctxAfter] using htagR2
                have hagree_clean :
                    agreeOnClean predSat R (ctxAfter ctxᵢ res)
                      cf₀.memory cf₀.varEnv θ₀2 cf₁.memory cf₁.varEnv θ₁2 := by
                  simpa [hctxAfter] using hagree_clean2
                refine ⟨θ₀2, θ₁2, hθext₀, hθext₁, ?_, ?_, ?_, hric₀'', hric₁'', htagR'', hagree_clean, ?_⟩
                · simpa [hctxAfter] using hwf2
                · exact hwfcf₀_final
                · exact hwfcf₁_final
                intro hclean
                have hpoison_imp : res.qualType.poison = false → res2.qualType.poison = false := by
                  intro hpoison_res
                  have hjoin : joinPoison res1.qualType.poison res2.qualType.poison = false := by
                    calc
                      joinPoison res1.qualType.poison res2.qualType.poison = res.qualType.poison := by
                        symm
                        exact h_ret_poison
                      _ = false := by exact hpoison_res
                  exact (joinPoison_eq_false hjoin).2
                have hclean2 : qtypCleanUnder R res2.qualType := by
                  cases hclean with
                  | inl hpoison_res =>
                      left
                      exact hpoison_imp hpoison_res
                  | inr hguard =>
                      rcases hguard with ⟨k, htag, hreg⟩
                      right
                      refine ⟨k, ?_, hreg⟩
                      simpa [qtypGuardTag, h_ret_pred] using htag
                have hagree2 : agreeValueUnder predSat R cf₀.memory cf₁.memory θ₀2 θ₁2 res2.qualType o₀ o₁ :=
                  hres_agree2 hclean2
                exact agreeValueUnder_transport_clean hclean h_ret_etyp h_ret_pred hpoison_imp hagree2
        | kwhile e1 e2 =>
            sorry
        | vlet z e1 e2 =>
            let vname := z
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr_vlet_succ, typecheckVlet] at htc
            | succ fuel' =>
                have htc' : typecheckVlet ctxᵢ vname e1 e2 (Nat.succ fuel') = .ok res := by
                  simpa [typecheck, typecheckExpr, typecheckExpr_vlet_succ] using htc
                obtain ⟨res1, res2, ctx', htc1, hctx', htc2, h_ret_etyp, h_mem, h_tag, h_loc, h_ntag,
                        h_ret_poison, h_ret_pred⟩ :=
                  typecheckVlet_structure ctxᵢ vname e1 e2 (Nat.succ fuel') res htc'
                have htc1' : typecheck ctxᵢ e1 fuel' = .ok res1 := by
                  simpa [typecheck, Nat.succ_sub_one] using htc1
                have htc2' : typecheck ctx' e2 fuel' = .ok res2 := by
                  simpa [hctx', typecheck, Nat.succ_sub_one] using htc2
                have hIH1 := IH (m := fuel') (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
                  e1 ctxᵢ res1 htc1' R
                have hIH2 := IH (m := fuel') (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
                  e2 ctx' res2 htc2' R
                intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hagree a₀ a₁ pm₀ pm₁ hwfcfg₀ hwfcfg₁ ht₀ ht₁
                -- Derive wfConfig for final configs using preservation lemma
                have hwfcf₀_final : wfConfig cf₀ := wfConfig_preservedW _ _ _ _ ht₀ hwfcfg₀
                have hwfcf₁_final : wfConfig cf₁ := wfConfig_preservedW _ _ _ _ ht₁ hwfcfg₁
                rcases ht₀ with ⟨fuel₀, verbose₀, w₀₀, w₀₁, hbeval₀⟩
                have hstruct₀ :=
                  bevalVlet_structure vname e1 e2 fuel₀ verbose₀
                    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm₀ }
                    cf₀ o₀ ⟨w₀₀, w₀₁, hbeval₀⟩
                rcases hstruct₀ with ⟨cfg₀1, cfg₀2, cfg₀3, v₀1, hbeval₀_e1, hcfg₀2, hbeval₀_e2, hcfg₀final⟩
                rcases ht₁ with ⟨fuel₁, verbose₁, w₁₀, w₁₁, hbeval₁⟩
                have hstruct₁ :=
                  bevalVlet_structure vname e1 e2 fuel₁ verbose₁
                    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm₁ }
                    cf₁ o₁ ⟨w₁₀, w₁₁, hbeval₁⟩
                rcases hstruct₁ with ⟨cfg₁1, cfg₁2, cfg₁3, v₁1, hbeval₁_e1, hcfg₁2, hbeval₁_e2, hcfg₁final⟩
                rcases hbeval₀_e1 with ⟨w₀e1, w₀e1', hbeval₀_e1'⟩
                rcases hbeval₀_e2 with ⟨w₀e2, w₀e2', hbeval₀_e2'⟩
                rcases hbeval₁_e1 with ⟨w₁e1, w₁e1', hbeval₁_e1'⟩
                rcases hbeval₁_e2 with ⟨w₁e2, w₁e2', hbeval₁_e2'⟩
                have ht₀_e1 :
                    terminatesToW e1
                      { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm₀ }
                      cfg₀1 v₀1 :=
                  ⟨fuel₀ - 1, verbose₀, w₀e1, w₀e1', hbeval₀_e1'⟩
                have ht₁_e1 :
                    terminatesToW e1
                      { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm₁ }
                      cfg₁1 v₁1 :=
                  ⟨fuel₁ - 1, verbose₁, w₁e1, w₁e1', hbeval₁_e1'⟩
                have hstep_e1 :=
                  hIH1 μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀1 cfg₁1 v₀1 v₁1
                    hθ₀ hθ₁ hwf hric₀ hric₁ htagR hagree a₀ a₁ pm₀ pm₁ hwfcfg₀ hwfcfg₁ ht₀_e1 ht₁_e1
                rcases hstep_e1 with
                  ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hwf1, hwfcf₀1, hwfcf₁1, hric₀1, hric₁1, htagR1, hagree_clean1, hres_agree1⟩
                have hθ₀1wf : wfRealizationMap θ₀1 := hθext₀1.2 hθ₀
                have hθ₁1wf : wfRealizationMap θ₁1 := hθext₁1.2 hθ₁
                have hric₀1_mem :
                    runtimeInstantiatesCtx { ctxᵢ with memEnv := res1.memEnv' } cfg₀1.memory cfg₀1.varEnv θ₀1 := by
                  simpa [ctxAfter] using hric₀1
                have hric₁1_mem :
                    runtimeInstantiatesCtx { ctxᵢ with memEnv := res1.memEnv' } cfg₁1.memory cfg₁1.varEnv θ₁1 := by
                  simpa [ctxAfter] using hric₁1
                have hv₀1_typed : valueHasETyp θ₀1 v₀1 res1.qualType.etyp := by
                  exact (preservation_valueW e1 ctxᵢ fuel' res1
                    μ₀ cfg₀1.memory ρ₀ cfg₀1.varEnv θ₀ θ₀1
                    a₀ cfg₀1.nextAddr pm₀ cfg₀1.pureMode v₀1
                    hwf htc1' hθ₀ hθ₀1wf hθext₀1 hric₀ hric₀1_mem
                    ⟨fuel₀ - 1, verbose₀, w₀e1, w₀e1', hbeval₀_e1'⟩).1
                have hv₁1_typed : valueHasETyp θ₁1 v₁1 res1.qualType.etyp := by
                  exact (preservation_valueW e1 ctxᵢ fuel' res1
                    μ₁ cfg₁1.memory ρ₁ cfg₁1.varEnv θ₁ θ₁1
                    a₁ cfg₁1.nextAddr pm₁ cfg₁1.pureMode v₁1
                    hwf htc1' hθ₁ hθ₁1wf hθext₁1 hric₁ hric₁1_mem
                    ⟨fuel₁ - 1, verbose₁, w₁e1, w₁e1', hbeval₁_e1'⟩).1
                have htagR_ctx' : tagEnvConsistentWithRegime ctx'.tagEnv R := by
                  simpa [hctx', ctxAfter] using htagR1
                have hric₀1' : runtimeInstantiatesCtx ctx' cfg₀2.memory cfg₀2.varEnv θ₀1 := by
                  unfold runtimeInstantiatesCtx at hric₀1 ⊢
                  rcases hric₀1 with ⟨hmem₀1, hvars₀1⟩
                  constructor
                  · intro l a hlookup
                    have hmem := hmem₀1 l a hlookup
                    simpa [hctx', ctxAfter, hcfg₀2] using hmem
                  · intro w qt hlookup
                    by_cases hw : w = vname
                    · subst hw
                      have hlookup' : (ctxᵢ.varEnv.update vname res1.qualType).lookup vname = some qt := by
                        simpa [hctx'] using hlookup
                      have hqt : qt = res1.qualType := by
                        have h := VarTypeEnv_lookup_update_eq ctxᵢ.varEnv vname res1.qualType
                        have : some qt = some res1.qualType := by
                          calc
                            some qt = (ctxᵢ.varEnv.update vname res1.qualType).lookup vname := by symm; exact hlookup'
                            _ = some res1.qualType := by exact h
                        exact Option.some.inj this
                      have hlookup_var : cfg₀2.varEnv.lookup vname = some v₀1 := by
                        simp [hcfg₀2, VarEnv.update, VarEnv.lookup]
                      refine ⟨v₀1, hlookup_var, ?_⟩
                      simpa [hqt] using hv₀1_typed
                    · have hlookup' : (ctxᵢ.varEnv.update vname res1.qualType).lookup w = some qt := by
                        simpa [hctx'] using hlookup
                      have hlookup_ctx : ctxᵢ.varEnv.lookup w = some qt := by
                        simpa [VarTypeEnv_lookup_update_ne ctxᵢ.varEnv vname w res1.qualType hw] using hlookup'
                      obtain ⟨v, hvlookup, hvtyp⟩ := hvars₀1 hlookup_ctx
                      have hvlookup' : cfg₀2.varEnv.lookup w = some v := by
                        simpa [hcfg₀2, VarEnv_lookup_update_ne cfg₀1.varEnv vname w v₀1 hw] using hvlookup
                      exact ⟨v, hvlookup', hvtyp⟩
                have hric₁1' : runtimeInstantiatesCtx ctx' cfg₁2.memory cfg₁2.varEnv θ₁1 := by
                  unfold runtimeInstantiatesCtx at hric₁1 ⊢
                  rcases hric₁1 with ⟨hmem₁1, hvars₁1⟩
                  constructor
                  · intro l a hlookup
                    have hmem := hmem₁1 l a hlookup
                    simpa [hctx', ctxAfter, hcfg₁2] using hmem
                  · intro w qt hlookup
                    by_cases hw : w = vname
                    · subst hw
                      have hlookup' : (ctxᵢ.varEnv.update vname res1.qualType).lookup vname = some qt := by
                        simpa [hctx'] using hlookup
                      have hqt : qt = res1.qualType := by
                        have h := VarTypeEnv_lookup_update_eq ctxᵢ.varEnv vname res1.qualType
                        have : some qt = some res1.qualType := by
                          calc
                            some qt = (ctxᵢ.varEnv.update vname res1.qualType).lookup vname := by symm; exact hlookup'
                            _ = some res1.qualType := by exact h
                        exact Option.some.inj this
                      have hlookup_var : cfg₁2.varEnv.lookup vname = some v₁1 := by
                        simp [hcfg₁2, VarEnv.update, VarEnv.lookup]
                      refine ⟨v₁1, hlookup_var, ?_⟩
                      simpa [hqt] using hv₁1_typed
                    · have hlookup' : (ctxᵢ.varEnv.update vname res1.qualType).lookup w = some qt := by
                        simpa [hctx'] using hlookup
                      have hlookup_ctx : ctxᵢ.varEnv.lookup w = some qt := by
                        simpa [VarTypeEnv_lookup_update_ne ctxᵢ.varEnv vname w res1.qualType hw] using hlookup'
                      obtain ⟨v, hvlookup, hvtyp⟩ := hvars₁1 hlookup_ctx
                      have hvlookup' : cfg₁2.varEnv.lookup w = some v := by
                        simpa [hcfg₁2, VarEnv_lookup_update_ne cfg₁1.varEnv vname w v₁1 hw] using hvlookup
                      exact ⟨v, hvlookup', hvtyp⟩
                have hagree_clean1' :
                    agreeOnClean predSat R ctx' cfg₀2.memory cfg₀2.varEnv θ₀1 cfg₁2.memory cfg₁2.varEnv θ₁1 := by
                  constructor
                  · intro l qt hlookup hclean
                    have hlookup' : (ctxAfter ctxᵢ res1).memEnv.lookup l = some qt := by
                      simpa [hctx', ctxAfter] using hlookup
                    have hagree_loc := (hagree_clean1.1 l qt hlookup' hclean)
                    simpa [hcfg₀2, hcfg₁2] using hagree_loc
                  · intro w qt hlookup hclean
                    by_cases hw : w = vname
                    · subst hw
                      have hlookup' : (ctxᵢ.varEnv.update vname res1.qualType).lookup vname = some qt := by
                        simpa [hctx'] using hlookup
                      have hqt : qt = res1.qualType := by
                        have h := VarTypeEnv_lookup_update_eq ctxᵢ.varEnv vname res1.qualType
                        have : some qt = some res1.qualType := by
                          calc
                            some qt = (ctxᵢ.varEnv.update vname res1.qualType).lookup vname := by symm; exact hlookup'
                            _ = some res1.qualType := by exact h
                        exact Option.some.inj this
                      have hlookup₀ : cfg₀2.varEnv.lookup vname = some v₀1 := by
                        simp [hcfg₀2, VarEnv.update, VarEnv.lookup]
                      have hlookup₁ : cfg₁2.varEnv.lookup vname = some v₁1 := by
                        simp [hcfg₁2, VarEnv.update, VarEnv.lookup]
                      have hclean1 : qtypCleanUnder R res1.qualType := by
                        simpa [hqt] using hclean
                      have hagree_val : agreeValueUnder predSat R cfg₀2.memory cfg₁2.memory θ₀1 θ₁1 res1.qualType v₀1 v₁1 := by
                        have hagree := hres_agree1 hclean1
                        simpa [hcfg₀2, hcfg₁2] using hagree
                      have hagree_val' : agreeValueUnder predSat R cfg₀2.memory cfg₁2.memory θ₀1 θ₁1 qt v₀1 v₁1 := by
                        simpa [hqt] using hagree_val
                      exact agreeVarUnder.agree_values w qt v₀1 v₁1 hlookup₀ hlookup₁ hagree_val'
                    · have hlookup' : (ctxᵢ.varEnv.update vname res1.qualType).lookup w = some qt := by
                        simpa [hctx'] using hlookup
                      have hlookup_ctx : ctxᵢ.varEnv.lookup w = some qt := by
                        simpa [VarTypeEnv_lookup_update_ne ctxᵢ.varEnv vname w res1.qualType hw] using hlookup'
                      have hagree_var := (hagree_clean1.2 w qt hlookup_ctx hclean)
                      cases hagree_var with
                      | agree_values _ _ v₀ v₁ hlookup₀ hlookup₁ hagree =>
                          have hlookup₀' : cfg₀2.varEnv.lookup w = some v₀ := by
                            simpa [hcfg₀2, VarEnv_lookup_update_ne cfg₀1.varEnv vname w v₀1 hw] using hlookup₀
                          have hlookup₁' : cfg₁2.varEnv.lookup w = some v₁ := by
                            simpa [hcfg₁2, VarEnv_lookup_update_ne cfg₁1.varEnv vname w v₁1 hw] using hlookup₁
                          have hagree' : agreeValueUnder predSat R cfg₀2.memory cfg₁2.memory θ₀1 θ₁1 qt v₀ v₁ := by
                            simpa [hcfg₀2, hcfg₁2] using hagree
                          exact agreeVarUnder.agree_values w qt v₀ v₁ hlookup₀' hlookup₁' hagree'
                      | both_none _ _ hnone₀ hnone₁ =>
                          have hnone₀' : cfg₀2.varEnv.lookup w = none := by
                            simpa [hcfg₀2, VarEnv_lookup_update_ne cfg₀1.varEnv vname w v₀1 hw] using hnone₀
                          have hnone₁' : cfg₁2.varEnv.lookup w = none := by
                            simpa [hcfg₁2, VarEnv_lookup_update_ne cfg₁1.varEnv vname w v₁1 hw] using hnone₁
                          exact agreeVarUnder.both_none w qt hnone₀' hnone₁'
                have ht₀_e2 : terminatesToW e2 cfg₀2 cfg₀3 o₀ :=
                  ⟨fuel₀ - 1, verbose₀, w₀e2, w₀e2', hbeval₀_e2'⟩
                have ht₁_e2 : terminatesToW e2 cfg₁2 cfg₁3 o₁ :=
                  ⟨fuel₁ - 1, verbose₁, w₁e2, w₁e2', hbeval₁_e2'⟩
                have hwf1' : wfTypeContext ctx' := by simpa [hctx', ctxAfter] using hwf1
                -- wfConfig cfg₀2 follows from wfConfig cfg₀1 since they have the same memory and nextAddr
                -- (vlet only changes varEnv, not memory or nextAddr before evaluating e2)
                have hwfcfg₀2' : wfConfig cfg₀2 := by simp only [hcfg₀2]; exact hwfcf₀1
                have hwfcfg₁2' : wfConfig cfg₁2 := by simp only [hcfg₁2]; exact hwfcf₁1
                have hstep_e2 :=
                  hIH2 cfg₀2.memory cfg₁2.memory cfg₀2.varEnv cfg₁2.varEnv θ₀1 θ₁1
                    cfg₀3 cfg₁3 o₀ o₁
                    hθ₀1wf hθ₁1wf hwf1' hric₀1' hric₁1' htagR_ctx' hagree_clean1'
                    cfg₀2.nextAddr cfg₁2.nextAddr cfg₀2.pureMode cfg₁2.pureMode hwfcfg₀2' hwfcfg₁2' ht₀_e2 ht₁_e2
                rcases hstep_e2 with
                  ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, hwf2, hwfcf₀2, hwfcf₁2, hric₀2, hric₁2, htagR2, hagree_clean2, hres_agree2⟩
                have hθext₀ : wfExtendsMap θ₀ θ₀2 := wfExtendsMap_trans hθext₀1 hθext₀2
                have hθext₁ : wfExtendsMap θ₁ θ₁2 := wfExtendsMap_trans hθext₁1 hθext₁2
                have hvar_pres₀ : cfg₀3.varEnv = cfg₀2.varEnv := by
                  symm
                  exact beval_preserves_varEnv e2 (fuel₀ - 1) verbose₀ cfg₀2 cfg₀3 o₀ ⟨w₀e2, w₀e2', hbeval₀_e2'⟩
                have hvar_pres₁ : cfg₁3.varEnv = cfg₁2.varEnv := by
                  symm
                  exact beval_preserves_varEnv e2 (fuel₁ - 1) verbose₁ cfg₁2 cfg₁3 o₁ ⟨w₁e2, w₁e2', hbeval₁_e2'⟩
                have hric₀'' :
                    runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 := by
                  unfold runtimeInstantiatesCtx
                  rcases hric₀2 with ⟨hmem₂, _hvars₂⟩
                  rcases hric₀1 with ⟨_hmem₁, hvars₁⟩
                  constructor
                  · intro l a hlookup
                    have hmem := hmem₂ l a hlookup
                    simpa [ctxAfter, h_mem, h_tag, h_loc, h_ntag, hcfg₀final] using hmem
                  · intro u qt hlookup
                    have hlookup' : (ctxAfter ctxᵢ res1).varEnv.lookup u = some qt := by
                      simpa [ctxAfter] using hlookup
                    obtain ⟨v, hvlookup, hvtyp⟩ := hvars₁ hlookup'
                    have hvlookup' : cf₀.varEnv.lookup u = some v := by
                      simpa [hcfg₀final] using hvlookup
                    have hvtyp' : valueHasETyp θ₀2 v qt.etyp :=
                      valueHasETyp_extends hθext₀2.1 hvtyp
                    exact ⟨v, hvlookup', hvtyp'⟩
                have hric₁'' :
                    runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁2 := by
                  unfold runtimeInstantiatesCtx
                  rcases hric₁2 with ⟨hmem₂, _hvars₂⟩
                  rcases hric₁1 with ⟨_hmem₁, hvars₁⟩
                  constructor
                  · intro l a hlookup
                    have hmem := hmem₂ l a hlookup
                    simpa [ctxAfter, h_mem, h_tag, h_loc, h_ntag, hcfg₁final] using hmem
                  · intro u qt hlookup
                    have hlookup' : (ctxAfter ctxᵢ res1).varEnv.lookup u = some qt := by
                      simpa [ctxAfter] using hlookup
                    obtain ⟨v, hvlookup, hvtyp⟩ := hvars₁ hlookup'
                    have hvlookup' : cf₁.varEnv.lookup u = some v := by
                      simpa [hcfg₁final] using hvlookup
                    have hvtyp' : valueHasETyp θ₁2 v qt.etyp :=
                      valueHasETyp_extends hθext₁2.1 hvtyp
                    exact ⟨v, hvlookup', hvtyp'⟩
                have htagR'' : tagEnvConsistentWithRegime (ctxAfter ctxᵢ res).tagEnv R := by
                  simpa [ctxAfter, h_tag, h_loc, h_ntag] using htagR2
                have hagree_clean :
                    agreeOnClean predSat R (ctxAfter ctxᵢ res)
                      cf₀.memory cf₀.varEnv θ₀2 cf₁.memory cf₁.varEnv θ₁2 := by
                  constructor
                  · intro l qt hlookup hclean
                    have hlookup' : (ctxAfter ctx' res2).memEnv.lookup l = some qt := by
                      simpa [ctxAfter, h_mem, h_tag, h_loc, h_ntag] using hlookup
                    have hagree_loc := (hagree_clean2.1 l qt hlookup' hclean)
                    simpa [hcfg₀final, hcfg₁final] using hagree_loc
                  · intro w qt hlookup hclean
                    by_cases hw : w = vname
                    · subst hw
                      have hlookup' : (ctxAfter ctxᵢ res1).varEnv.lookup vname = some qt := by
                        simpa [ctxAfter] using hlookup
                      have hagree_var := (hagree_clean1.2 vname qt hlookup' hclean)
                      cases hagree_var with
                      | agree_values _ _ v₀ v₁ hlookup₀ hlookup₁ hagree =>
                          have hlookup₀' : cf₀.varEnv.lookup vname = some v₀ := by
                            simpa [hcfg₀final] using hlookup₀
                          have hlookup₁' : cf₁.varEnv.lookup vname = some v₁ := by
                            simpa [hcfg₁final] using hlookup₁
                          have hagree' :
                              agreeValueUnder predSat R cf₀.memory cf₁.memory θ₀2 θ₁2 qt v₀ v₁ :=
                            agreeValueUnder_clean_extends hclean hθext₀2.1 hθext₁2.1 hagree
                          exact agreeVarUnder.agree_values vname qt v₀ v₁ hlookup₀' hlookup₁' hagree'
                      | both_none _ _ hnone₀ hnone₁ =>
                          have hnone₀' : cf₀.varEnv.lookup vname = none := by
                            simpa [hcfg₀final] using hnone₀
                          have hnone₁' : cf₁.varEnv.lookup vname = none := by
                            simpa [hcfg₁final] using hnone₁
                          exact agreeVarUnder.both_none vname qt hnone₀' hnone₁'
                    · have hlookup' : (ctxᵢ.varEnv.update vname res1.qualType).lookup w = some qt := by
                        simpa [VarTypeEnv_lookup_update_ne ctxᵢ.varEnv vname w res1.qualType hw] using hlookup
                      have hlookup_ctx : (ctxAfter ctx' res2).varEnv.lookup w = some qt := by
                        simpa [ctxAfter, hctx'] using hlookup'
                      have hagree_var := (hagree_clean2.2 w qt hlookup_ctx hclean)
                      cases hagree_var with
                      | agree_values _ _ v₀ v₁ hlookup₀ hlookup₁ hagree =>
                          have hlookup₀2 : cfg₀2.varEnv.lookup w = some v₀ := by
                            simpa [hvar_pres₀] using hlookup₀
                          have hlookup₁2 : cfg₁2.varEnv.lookup w = some v₁ := by
                            simpa [hvar_pres₁] using hlookup₁
                          have hlookup₀1 : cfg₀1.varEnv.lookup w = some v₀ := by
                            simpa [hcfg₀2, VarEnv_lookup_update_ne cfg₀1.varEnv vname w v₀1 hw] using hlookup₀2
                          have hlookup₁1 : cfg₁1.varEnv.lookup w = some v₁ := by
                            simpa [hcfg₁2, VarEnv_lookup_update_ne cfg₁1.varEnv vname w v₁1 hw] using hlookup₁2
                          have hlookup₀' : cf₀.varEnv.lookup w = some v₀ := by
                            simpa [hcfg₀final] using hlookup₀1
                          have hlookup₁' : cf₁.varEnv.lookup w = some v₁ := by
                            simpa [hcfg₁final] using hlookup₁1
                          have hagree' : agreeValueUnder predSat R cf₀.memory cf₁.memory θ₀2 θ₁2 qt v₀ v₁ := by
                            simpa [hcfg₀final, hcfg₁final] using hagree
                          exact agreeVarUnder.agree_values w qt v₀ v₁ hlookup₀' hlookup₁' hagree'
                      | both_none _ _ hnone₀ hnone₁ =>
                          have hnone₀2 : cfg₀2.varEnv.lookup w = none := by
                            simpa [hvar_pres₀] using hnone₀
                          have hnone₁2 : cfg₁2.varEnv.lookup w = none := by
                            simpa [hvar_pres₁] using hnone₁
                          have hnone₀1 : cfg₀1.varEnv.lookup w = none := by
                            simpa [hcfg₀2, VarEnv_lookup_update_ne cfg₀1.varEnv vname w v₀1 hw] using hnone₀2
                          have hnone₁1 : cfg₁1.varEnv.lookup w = none := by
                            simpa [hcfg₁2, VarEnv_lookup_update_ne cfg₁1.varEnv vname w v₁1 hw] using hnone₁2
                          have hnone₀' : cf₀.varEnv.lookup w = none := by
                            simpa [hcfg₀final] using hnone₀1
                          have hnone₁' : cf₁.varEnv.lookup w = none := by
                            simpa [hcfg₁final] using hnone₁1
                          exact agreeVarUnder.both_none w qt hnone₀' hnone₁'
                refine ⟨θ₀2, θ₁2, hθext₀, hθext₁, ?_, ?_, ?_, hric₀'', hric₁'', htagR'', hagree_clean, ?_⟩
                -- wfTypeContext only depends on memEnv and nextLoc (not varEnv)
                · intro l hcontains
                  simp only [ctxAfter, h_mem, h_loc] at hcontains ⊢
                  exact hwf2 l hcontains
                · exact hwfcf₀_final
                · exact hwfcf₁_final
                intro hclean
                have hpoison_imp : res.qualType.poison = false → res2.qualType.poison = false := by
                  intro hpoison_res
                  have hjoin : joinPoison ctxᵢ.pc res2.qualType.poison = false := by
                    calc
                      joinPoison ctxᵢ.pc res2.qualType.poison = res.qualType.poison := by
                        symm
                        exact h_ret_poison
                      _ = false := by exact hpoison_res
                  exact (joinPoison_eq_false hjoin).2
                have hclean2 : qtypCleanUnder R res2.qualType := by
                  cases hclean with
                  | inl hpoison_res =>
                      left
                      exact hpoison_imp hpoison_res
                  | inr hguard =>
                      rcases hguard with ⟨k, htag, hreg⟩
                      right
                      refine ⟨k, ?_, hreg⟩
                      simpa [qtypGuardTag, h_ret_pred] using htag
                have hagree2 : agreeValueUnder predSat R cf₀.memory cf₁.memory θ₀2 θ₁2 res2.qualType o₀ o₁ := by
                  simpa [hcfg₀final, hcfg₁final] using (hres_agree2 hclean2)
                exact agreeValueUnder_transport_clean hclean h_ret_etyp h_ret_pred hpoison_imp hagree2
        | fn name ty e1 ty2 =>
            sorry
        | pfn name ty e1 ty2 =>
            sorry
        | app e1 e2 =>
            sorry
        | rand e =>
            sorry
        | frand e =>
            sorry
        | printString e =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr, typecheckPrintString] at htc
            | succ fuel' =>
                have htc' : typecheckPrintString ctxᵢ e (Nat.succ fuel') = .ok res := by
                  simpa [typecheck, typecheckExpr] using htc
                obtain ⟨res1, htc1, h_mem, h_tag, h_loc, h_ntag, h_ret_etyp⟩ :=
                  typecheckPrintString_structure ctxᵢ e (Nat.succ fuel') res htc'
                have htc1' : typecheck ctxᵢ e fuel' = .ok res1 := by
                  simpa [typecheck, Nat.succ_sub_one] using htc1
                have hIH := IH (m := fuel') (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
                  e ctxᵢ res1 htc1' R
                intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hagree a₀ a₁ pm₀ pm₁ hwfcfg₀ hwfcfg₁ ht₀ ht₁
                -- Derive wfConfig for final configs using preservation lemma
                have hwfcf₀_final : wfConfig cf₀ := wfConfig_preservedW _ _ _ _ ht₀ hwfcfg₀
                have hwfcf₁_final : wfConfig cf₁ := wfConfig_preservedW _ _ _ _ ht₁ hwfcfg₁
                rcases ht₀ with ⟨fuel₀, verbose₀, w₀₀, w₀₁, hbeval₀⟩
                have hstruct₀ :=
                  bevalPrintString_structure e fuel₀ verbose₀
                    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm₀ }
                    cf₀ o₀ ⟨w₀₀, w₀₁, hbeval₀⟩
                rcases hstruct₀ with ⟨cfg₀', v₀', hbeval₀_e, _hvstr₀, hvunit₀, hmem₀, hvar₀⟩
                rcases ht₁ with ⟨fuel₁, verbose₁, w₁₀, w₁₁, hbeval₁⟩
                have hstruct₁ :=
                  bevalPrintString_structure e fuel₁ verbose₁
                    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm₁ }
                    cf₁ o₁ ⟨w₁₀, w₁₁, hbeval₁⟩
                rcases hstruct₁ with ⟨cfg₁', v₁', hbeval₁_e, _hvstr₁, hvunit₁, hmem₁, hvar₁⟩
                rcases hbeval₀_e with ⟨w₀', w₀'', hbeval₀_e'⟩
                rcases hbeval₁_e with ⟨w₁', w₁'', hbeval₁_e'⟩
                have ht₀_e :
                    terminatesToW e
                      { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm₀ }
                      cfg₀' v₀' :=
                  ⟨fuel₀ - 1, verbose₀, w₀', w₀'', hbeval₀_e'⟩
                have ht₁_e :
                    terminatesToW e
                      { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm₁ }
                      cfg₁' v₁' :=
                  ⟨fuel₁ - 1, verbose₁, w₁', w₁'', hbeval₁_e'⟩
                have hstep_e :=
                  hIH μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀' cfg₁' v₀' v₁'
                    hθ₀ hθ₁ hwf hric₀ hric₁ htagR hagree a₀ a₁ pm₀ pm₁ hwfcfg₀ hwfcfg₁ ht₀_e ht₁_e
                rcases hstep_e with ⟨θ₀', θ₁', hθext₀, hθext₁, hwf', _hwfcf₀', _hwfcf₁', hric₀', hric₁', htagR', hagree_clean_e, _hres_agree_e⟩
                have hctxAfter : ctxAfter ctxᵢ res = ctxAfter ctxᵢ res1 := by
                  simp [ctxAfter, h_mem, h_tag, h_loc, h_ntag]
                have ho₀ : o₀ = Value.unit := by
                  cases hvunit₀
                  rfl
                have ho₁ : o₁ = Value.unit := by
                  cases hvunit₁
                  rfl
                have hric₀'' :
                    runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀' := by
                  simpa [hctxAfter, hmem₀, hvar₀] using hric₀'
                have hric₁'' :
                    runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁' := by
                  simpa [hctxAfter, hmem₁, hvar₁] using hric₁'
                have htagR'' : tagEnvConsistentWithRegime (ctxAfter ctxᵢ res).tagEnv R := by
                  simpa [hctxAfter] using htagR'
                have hagree_clean :
                    agreeOnClean predSat R (ctxAfter ctxᵢ res)
                      cf₀.memory cf₀.varEnv θ₀' cf₁.memory cf₁.varEnv θ₁' := by
                  simpa [hctxAfter, hmem₀, hvar₀, hmem₁, hvar₁] using hagree_clean_e
                refine ⟨θ₀', θ₁', hθext₀, hθext₁, ?_, ?_, ?_, hric₀'', hric₁'', htagR'', hagree_clean, ?_⟩
                · simpa [hctxAfter] using hwf'
                · exact hwfcf₀_final
                · exact hwfcf₁_final
                intro hclean
                cases hclean with
                | inl hpoison =>
                    have hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
                      simp [h_ret_etyp]
                    have hEq : o₀ = o₁ := by
                      simp [ho₀, ho₁]
                    exact agreeValueUnder.clean_eq_nonref hpoison hnotref hEq
                | inr hguard =>
                    rcases hguard with ⟨k, htag, hreg⟩
                    have hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
                      simp [h_ret_etyp]
                    have hEq : o₀ = o₁ := by
                      simp [ho₀, ho₁]
                    exact agreeValueUnder.withPred_true_eq k htag hreg hnotref hEq
        | printInt e =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr, typecheckPrintInt] at htc
            | succ fuel' =>
                have htc' : typecheckPrintInt ctxᵢ e (Nat.succ fuel') = .ok res := by
                  simpa [typecheck, typecheckExpr] using htc
                obtain ⟨res1, htc1, h_mem, h_tag, h_loc, h_ntag, h_ret_etyp⟩ :=
                  typecheckPrintInt_structure ctxᵢ e (Nat.succ fuel') res htc'
                have htc1' : typecheck ctxᵢ e fuel' = .ok res1 := by
                  simpa [typecheck, Nat.succ_sub_one] using htc1
                have hIH := IH (m := fuel') (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
                  e ctxᵢ res1 htc1' R
                intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hagree a₀ a₁ pm₀ pm₁ hwfcfg₀ hwfcfg₁ ht₀ ht₁
                -- Derive wfConfig for final configs using preservation lemma
                have hwfcf₀_final : wfConfig cf₀ := wfConfig_preservedW _ _ _ _ ht₀ hwfcfg₀
                have hwfcf₁_final : wfConfig cf₁ := wfConfig_preservedW _ _ _ _ ht₁ hwfcfg₁
                rcases ht₀ with ⟨fuel₀, verbose₀, w₀₀, w₀₁, hbeval₀⟩
                have hstruct₀ :=
                  bevalPrintInt_structure e fuel₀ verbose₀
                    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm₀ }
                    cf₀ o₀ ⟨w₀₀, w₀₁, hbeval₀⟩
                rcases hstruct₀ with ⟨cfg₀', v₀', hbeval₀_e, _hvint₀, hvunit₀, hmem₀, hvar₀⟩
                rcases ht₁ with ⟨fuel₁, verbose₁, w₁₀, w₁₁, hbeval₁⟩
                have hstruct₁ :=
                  bevalPrintInt_structure e fuel₁ verbose₁
                    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm₁ }
                    cf₁ o₁ ⟨w₁₀, w₁₁, hbeval₁⟩
                rcases hstruct₁ with ⟨cfg₁', v₁', hbeval₁_e, _hvint₁, hvunit₁, hmem₁, hvar₁⟩
                rcases hbeval₀_e with ⟨w₀', w₀'', hbeval₀_e'⟩
                rcases hbeval₁_e with ⟨w₁', w₁'', hbeval₁_e'⟩
                have ht₀_e :
                    terminatesToW e
                      { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm₀ }
                      cfg₀' v₀' :=
                  ⟨fuel₀ - 1, verbose₀, w₀', w₀'', hbeval₀_e'⟩
                have ht₁_e :
                    terminatesToW e
                      { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm₁ }
                      cfg₁' v₁' :=
                  ⟨fuel₁ - 1, verbose₁, w₁', w₁'', hbeval₁_e'⟩
                have hstep_e :=
                  hIH μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀' cfg₁' v₀' v₁'
                    hθ₀ hθ₁ hwf hric₀ hric₁ htagR hagree a₀ a₁ pm₀ pm₁ hwfcfg₀ hwfcfg₁ ht₀_e ht₁_e
                rcases hstep_e with ⟨θ₀', θ₁', hθext₀, hθext₁, hwf', _hwfcf₀', _hwfcf₁', hric₀', hric₁', htagR', hagree_clean_e, _hres_agree_e⟩
                have hctxAfter : ctxAfter ctxᵢ res = ctxAfter ctxᵢ res1 := by
                  simp [ctxAfter, h_mem, h_tag, h_loc, h_ntag]
                have ho₀ : o₀ = Value.unit := by
                  cases hvunit₀
                  rfl
                have ho₁ : o₁ = Value.unit := by
                  cases hvunit₁
                  rfl
                have hric₀'' :
                    runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀' := by
                  simpa [hctxAfter, hmem₀, hvar₀] using hric₀'
                have hric₁'' :
                    runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁' := by
                  simpa [hctxAfter, hmem₁, hvar₁] using hric₁'
                have htagR'' : tagEnvConsistentWithRegime (ctxAfter ctxᵢ res).tagEnv R := by
                  simpa [hctxAfter] using htagR'
                have hagree_clean :
                    agreeOnClean predSat R (ctxAfter ctxᵢ res)
                      cf₀.memory cf₀.varEnv θ₀' cf₁.memory cf₁.varEnv θ₁' := by
                  simpa [hctxAfter, hmem₀, hvar₀, hmem₁, hvar₁] using hagree_clean_e
                refine ⟨θ₀', θ₁', hθext₀, hθext₁, ?_, ?_, ?_, hric₀'', hric₁'', htagR'', hagree_clean, ?_⟩
                · simpa [hctxAfter] using hwf'
                · exact hwfcf₀_final
                · exact hwfcf₁_final
                intro hclean
                cases hclean with
                | inl hpoison =>
                    have hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
                      simp [h_ret_etyp]
                    have hEq : o₀ = o₁ := by
                      simp [ho₀, ho₁]
                    exact agreeValueUnder.clean_eq_nonref hpoison hnotref hEq
                | inr hguard =>
                    rcases hguard with ⟨k, htag, hreg⟩
                    have hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
                      simp [h_ret_etyp]
                    have hEq : o₀ = o₁ := by
                      simp [ho₀, ho₁]
                    exact agreeValueUnder.withPred_true_eq k htag hreg hnotref hEq
        | externVal ty b sp =>
            intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ _hθ₀ _hθ₁ _hwf _hric₀ _hric₁ _htagR _hagree a₀ _a₁ pm₀ _pm₁ _hwfcfg₀ _hwfcfg₁ ht₀ _ht₁
            have hfalse :
                False :=
              terminatesTo_extern_false
                (e := Expr.externVal ty b sp)
                (c₀ := { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm₀ })
                (c₁ := cf₀)
                (o := o₀)
                (by simp [isExternExpr])
                ht₀
            exact False.elim hfalse
        | externFn name ty ret effs =>
            intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ _hθ₀ _hθ₁ _hwf _hric₀ _hric₁ _htagR _hagree a₀ _a₁ pm₀ _pm₁ _hwfcfg₀ _hwfcfg₁ ht₀ _ht₁
            have hfalse :
                False :=
              terminatesTo_extern_false
                (e := Expr.externFn name ty ret effs)
                (c₀ := { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm₀ })
                (c₁ := cf₀)
                (o := o₀)
                (by simp [isExternExpr])
                ht₀
            exact False.elim hfalse
        | externPfn name ty ret =>
            intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ _hθ₀ _hθ₁ _hwf _hric₀ _hric₁ _htagR _hagree a₀ _a₁ pm₀ _pm₁ _hwfcfg₀ _hwfcfg₁ ht₀ _ht₁
            have hfalse :
                False :=
              terminatesTo_extern_false
                (e := Expr.externPfn name ty ret)
                (c₀ := { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm₀ })
                (c₁ := cf₀)
                (o := o₀)
                (by simp [isExternExpr])
                ht₀
            exact False.elim hfalse

-- Wrapper: derive the original step spec (terminatesTo) from the world-indexed one.
theorem TypeSystemEnforcesFaultRobustness_step
  (e : Expr) (ctxᵢ : TypeContext) (predSat : PredSat) :
  TypeSystemEnforcesFaultRobustness_step_spec e ctxᵢ predSat := by
  unfold TypeSystemEnforcesFaultRobustness_step_spec
  intro fuel res htc R
  have hW : StepFRW ctxᵢ R e res predSat :=
    TypeSystemEnforcesFaultRobustness_stepW e ctxᵢ predSat fuel res htc R
  exact StepFR_of_StepFRW hW

end TypeSystemEnforcesFaultRobustness_step_proof

theorem TypeSystemEnforcesFaultRobustness (e : Expr) (s : InputSpec) (obs : ObservableSpec) :
  TypeSystemEnforcesFaultRobustness_spec e s obs := by
  apply TypeSystemEnforcesFaultRobustness_impl
  exact TypeSystemEnforcesFaultRobustness_step
