-- Fault-Robustness proofs (skeletons)

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanPoison.BigStep
import Mathlib.Data.List.Forall2

import LeanProofs.FaultRobustness
import LeanProofs.IOHelpers

open List
open scoped MemoryTypeEnv

-- Result agreement for clean (or de-poisoned) outputs.
-- This captures the chaining requirement: clean results must agree across runs.
def resultAgreesIfClean (predSat : PredSat) (R : Regime) (μ₀ μ₁ : Memory)
  (θ₀ θ₁ : RealizationMap) (qt : QTyp) (o₀ o₁ : Value) : Prop :=
  qtypCleanUnder R qt →
    agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt o₀ o₁

-- Post-context derived from typing result.
-- This is how the step theorem accounts for context evolution (new locs/vars, tags).
def ctxAfter (ctx : TypeContext) (res : TypeResult) : TypeContext :=
  { ctx with memEnv := res.memEnv', tagEnv := res.tagEnv', nextLoc := res.nextLoc', nextTag := res.nextTag' }

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
      runtimeInstantiatesCtx ctx μ₀ ρ₀ θ₀ → runtimeInstantiatesCtx ctx μ₁ ρ₁ θ₁ →
      tagEnvConsistentWithRegime ctx.tagEnv R →
      agreeOnClean predSat R ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ →
      ∀ (a₀ a₁ : Address) (pm : Bool),
        terminatesTo e { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ →
        terminatesTo e { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ →
        ∃ (θ₀' θ₁' : RealizationMap),
          wfExtendsMap θ₀ θ₀' ∧ wfExtendsMap θ₁ θ₁' ∧
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
  rintro his _hos ctx hctx _hpc _hte predSat _hps ⟨fuel, res, htc, hobs⟩
  rcases hobs with ⟨hobs_ret, hobs_mem⟩
  have hstep' := hstep e ctx predSat
  have hstep' := hstep' fuel res htc
  rintro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ a₀ a₁ pm R cf₀ cf₁ o₀ o₁
  rintro hR hθ₀ hθ₁ hics₀ hics₁ hric₀ hric₁ hcrs₀ hcrs₁ hagree htrusted ht₀ ht₁
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
      hθ₀ hθ₁ hric₀ hric₁ htagR hagree_clean
      a₀ a₁ pm ht₀ ht₁
  rcases hstepFR with ⟨θ₀', θ₁', hθ₀ext, hθ₁ext, hagree_clean', hret_agree⟩
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

-- World-indexed termination (IO equality-friendly).
private def terminatesToW (e : Expr) (c₀ c₁ : Config) (out : Value) : Prop :=
  ∃ (fuel : Nat) (verbose : Bool) (w₀ w₁ : Void IO.RealWorld),
    LeanPoison.beval fuel c₀ e verbose w₀ = EST.Out.ok (.success c₁ out) w₁

-- Step theorem variant that uses world-indexed termination premises.
private def StepFRW
  (ctx : TypeContext)
  (R : Regime)
  (e : Expr)
  (res : TypeResult)
  (predSat : PredSat) : Prop :=
    ∀ (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (θ₀ θ₁ : RealizationMap)
      (cf₀ cf₁ : Config) (o₀ o₁ : Value),
      wfRealizationMap θ₀ → wfRealizationMap θ₁ →
      runtimeInstantiatesCtx ctx μ₀ ρ₀ θ₀ → runtimeInstantiatesCtx ctx μ₁ ρ₁ θ₁ →
      tagEnvConsistentWithRegime ctx.tagEnv R →
      agreeOnClean predSat R ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ →
      ∀ (a₀ a₁ : Address) (pm₀ pm₁ : Bool),
        terminatesToW e { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm₀ } cf₀ o₀ →
        terminatesToW e { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm₁ } cf₁ o₁ →
        ∃ (θ₀' θ₁' : RealizationMap),
          wfExtendsMap θ₀ θ₀' ∧ wfExtendsMap θ₁ θ₁' ∧
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
    hθ₀ hθ₁ hric₀ hric₁ htagR hagree a₀ a₁ pm ht₀ ht₁
  have ht₀w := terminatesToW_of_terminatesTo ht₀
  have ht₁w := terminatesToW_of_terminatesTo ht₁
  rcases hstep μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁
      hθ₀ hθ₁ hric₀ hric₁ htagR hagree a₀ a₁ pm pm ht₀w ht₁w with
    ⟨θ₀', θ₁', hθ₀ext, hθ₁ext, _hric₀', _hric₁', _htagR', hagree', hret⟩
  exact ⟨θ₀', θ₁', hθ₀ext, hθ₁ext, hagree', hret⟩

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
              cases h_cond : (etyp != ETyp.int) with
              | true =>
                  simp [h_cond, throw] at h_typecheck
              | false =>
                  simp [h_cond, pure, Except.pure] at h_typecheck
                  refine ⟨result1, h_tc1, ?_⟩
                  -- Result preserves environments/indices; only qualType changes to unit.
                  have h_res :
                      { qualType := { etyp := ETyp.unit, poison := joinPoison ctx.pc poison, pred := Predicate.noPred },
                        memEnv' := result1.memEnv', tagEnv' := result1.tagEnv', nextLoc' := result1.nextLoc',
                        nextTag' := result1.nextTag' } = res := by
                    simpa using h_typecheck
                  rw [← h_res]
                  simp
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
              cases h_cond : (etyp != ETyp.string) with
              | true =>
                  simp [h_cond, throw] at h_typecheck
              | false =>
                  simp [h_cond, pure, Except.pure] at h_typecheck
                  refine ⟨result1, h_tc1, ?_⟩
                  have h_res :
                      { qualType := { etyp := ETyp.unit, poison := joinPoison ctx.pc poison, pred := Predicate.noPred },
                        memEnv' := result1.memEnv', tagEnv' := result1.tagEnv', nextLoc' := result1.nextLoc',
                        nextTag' := result1.nextTag' } = res := by
                    simpa using h_typecheck
                  rw [← h_res]
                  simp
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
    valueHasETyp (θ := {}) v1 ETyp.int ∧
    valueHasETyp (θ := {}) v ETyp.unit ∧
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
          simp [EST.bind] at h_eq
          split at h_eq
          · next p_result p_state =>
            injection h_eq with h_eq_result h_eq_state
            injection h_eq_result with h_eq_cfg h_eq_val
            subst h_eq_cfg h_eq_val
            -- Construct existential for h_beval1
            have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config' (Value.num v₁)) w₁' :=
              ⟨w₀, h_state1, h_beval1⟩
            simp only [Nat.add_sub_cancel]
            exact ⟨config', Value.num v₁, h_beval1_ex, valueHasETyp.num _, valueHasETyp.unit, rfl, rfl⟩
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
    valueHasETyp (θ := {}) v1 ETyp.string ∧
    valueHasETyp (θ := {}) v ETyp.unit ∧
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
          simp [EST.bind] at h_eq
          split at h_eq
          · next p_result p_state =>
            injection h_eq with h_eq_result h_eq_state
            injection h_eq_result with h_eq_cfg h_eq_val
            subst h_eq_cfg h_eq_val
            -- Construct existential for h_beval1
            have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config' (Value.str v₁)) w₁' :=
              ⟨w₀, h_state1, h_beval1⟩
            simp only [Nat.add_sub_cancel]
            exact ⟨config', Value.str v₁, h_beval1_ex, valueHasETyp.str _, valueHasETyp.unit, rfl, rfl⟩
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

private lemma stepFR_literal
  (ctx : TypeContext) (predSat : PredSat) (R : Regime)
  (e : Expr) (res : TypeResult) (v : Value)
  (hval : Expr.toValue? e = some v)
  (hpoison : res.qualType.poison = false)
  (hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls)
  (hctxAfter : ctxAfter ctx res = ctx) :
  StepFRW ctx R e res predSat := by
  intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hric₀ hric₁ htagR hagree a₀ a₁ pm₀ pm₁ ht₀ ht₁
  have hterm₀ := terminatesTo_literal_inv e v hval μ₀ ρ₀ a₀ pm₀ cf₀ o₀ ht₀
  have hterm₁ := terminatesTo_literal_inv e v hval μ₁ ρ₁ a₁ pm₁ cf₁ o₁ ht₁
  rcases hterm₀ with ⟨hcf₀, ho₀⟩
  rcases hterm₁ with ⟨hcf₁, ho₁⟩
  subst hcf₀
  subst hcf₁
  refine ⟨θ₀, θ₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro l a hlookup
      exact hlookup
    · intro hwf
      exact hwf
  · refine ⟨?_, ?_⟩
    · intro l a hlookup
      exact hlookup
    · intro hwf
      exact hwf
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
  intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hric₀ hric₁ htagR hagree a₀ a₁ pm₀ pm₁ ht₀ ht₁
  have hterm₀ := terminatesTo_var_inv name μ₀ ρ₀ a₀ pm₀ cf₀ o₀ ht₀
  have hterm₁ := terminatesTo_var_inv name μ₁ ρ₁ a₁ pm₁ cf₁ o₁ ht₁
  rcases hterm₀ with ⟨v₀, _hlookup₀, hcf₀, _ho₀⟩
  rcases hterm₁ with ⟨v₁, _hlookup₁, hcf₁, _ho₁⟩
  subst hcf₀
  subst hcf₁
  refine ⟨θ₀, θ₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro l a hlookup'
      exact hlookup'
    · intro hwf
      exact hwf
  · refine ⟨?_, ?_⟩
    · intro l a hlookup'
      exact hlookup'
    · intro hwf
      exact hwf
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
                intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hric₀ hric₁ htagR hagree a₀ a₁ pm₀ pm₁ ht₀ ht₁
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
                    hθ₀ hθ₁ hric₀ hric₁ htagR hagree a₀ a₁ pm₀ pm₁ ht₀_e1 ht₁_e1
                rcases hstep_e1 with
                  ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hric₀1, hric₁1, htagR1, hagree_clean1, hres_agree1⟩
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
                have hstep_e2 :=
                  hIH2 cfg₀1.memory cfg₁1.memory cfg₀1.varEnv cfg₁1.varEnv θ₀1 θ₁1
                    cfg₀2 cfg₁2 v₀2 v₁2
                    hθ₀1wf hθ₁1wf hric₀1' hric₁1' htagR_ctx' hagree_clean1'
                    cfg₀1.nextAddr cfg₁1.nextAddr cfg₀1.pureMode cfg₁1.pureMode ht₀_e2 ht₁_e2
                rcases hstep_e2 with
                  ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, hric₀2, hric₁2, htagR2, hagree_clean2, hres_agree2⟩
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
                refine ⟨θ₀2, θ₁2, hθext₀, hθext₁, hric₀'', hric₁'', htagR'', hagree_clean, ?_⟩
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
                intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hric₀ hric₁ htagR hagree a₀ a₁ pm₀ pm₁ ht₀ ht₁
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
                    hθ₀ hθ₁ hric₀ hric₁ htagR hagree a₀ a₁ pm₀ pm₁ ht₀_e ht₁_e
                rcases hstep_e with ⟨θ₀', θ₁', hθext₀, hθext₁, hric₀', hric₁', htagR', hagree_clean_e, hres_agree_e⟩
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
                refine ⟨θ₀', θ₁', hθext₀, hθext₁, hric₀'', hric₁'', htagR'', hagree_clean, ?_⟩
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
            sorry
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
                intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hric₀ hric₁ htagR hagree a₀ a₁ pm₀ pm₁ ht₀ ht₁
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
                    hθ₀ hθ₁ hric₀ hric₁ htagR hagree a₀ a₁ pm₀ pm₁ ht₀_e1 ht₁_e1
                rcases hstep_e1 with
                  ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hric₀1, hric₁1, htagR1, hagree_clean1, hres_agree1⟩
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
                have hstep_e2 :=
                  hIH2 cfg₀1.memory cfg₁1.memory cfg₀1.varEnv cfg₁1.varEnv θ₀1 θ₁1
                    cf₀ cf₁ o₀ o₁
                    hθ₀1wf hθ₁1wf hric₀1' hric₁1' htagR_ctx' hagree_clean1'
                    cfg₀1.nextAddr cfg₁1.nextAddr cfg₀1.pureMode cfg₁1.pureMode ht₀_e2 ht₁_e2
                rcases hstep_e2 with
                  ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, hric₀2, hric₁2, htagR2, hagree_clean2, hres_agree2⟩
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
                refine ⟨θ₀2, θ₁2, hθext₀, hθext₁, hric₀'', hric₁'', htagR'', hagree_clean, ?_⟩
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
        | vlet name e1 e2 =>
            sorry
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
                intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hric₀ hric₁ htagR hagree a₀ a₁ pm₀ pm₁ ht₀ ht₁
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
                    hθ₀ hθ₁ hric₀ hric₁ htagR hagree a₀ a₁ pm₀ pm₁ ht₀_e ht₁_e
                rcases hstep_e with ⟨θ₀', θ₁', hθext₀, hθext₁, hric₀', hric₁', htagR', hagree_clean_e, _hres_agree_e⟩
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
                refine ⟨θ₀', θ₁', hθext₀, hθext₁, hric₀'', hric₁'', htagR'', hagree_clean, ?_⟩
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
                intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hric₀ hric₁ htagR hagree a₀ a₁ pm₀ pm₁ ht₀ ht₁
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
                    hθ₀ hθ₁ hric₀ hric₁ htagR hagree a₀ a₁ pm₀ pm₁ ht₀_e ht₁_e
                rcases hstep_e with ⟨θ₀', θ₁', hθext₀, hθext₁, hric₀', hric₁', htagR', hagree_clean_e, _hres_agree_e⟩
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
                refine ⟨θ₀', θ₁', hθext₀, hθext₁, hric₀'', hric₁'', htagR'', hagree_clean, ?_⟩
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
            intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ _hθ₀ _hθ₁ _hric₀ _hric₁ _htagR _hagree a₀ _a₁ pm₀ _pm₁ ht₀ _ht₁
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
            intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ _hθ₀ _hθ₁ _hric₀ _hric₁ _htagR _hagree a₀ _a₁ pm₀ _pm₁ ht₀ _ht₁
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
            intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ _hθ₀ _hθ₁ _hric₀ _hric₁ _htagR _hagree a₀ _a₁ pm₀ _pm₁ ht₀ _ht₁
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
