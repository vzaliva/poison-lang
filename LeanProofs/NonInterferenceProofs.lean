-- Non-Interference properties for the poison language

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanPoison.BigStep
import Mathlib.Data.List.Forall2

import LeanProofs.NonInterference
import LeanProofs.IOHelpers

open List

section NonInterferenceSpec_step_spec

-- `i` and `o` subscript indexes correspond to input and outputs
-- `0` and `1` subscript indexes correspond to two runs of the program
def NonInterferenceSpec_step
  (e : Expr)
  (sᵢ sₒ : InputSpec)
  (ctxᵢ _ctxₒ : TypeContext)
  (retType : QTyp)
  (isRetObservable : Bool)
  (predSat : PredSat) : Prop :=
    ∀ (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (θ₀ θ₁ : RealizationMap) (Rᵢ : Regime)
      (cf₀ cf₁ : Config) (o₀ o₁ : Value),
      wfRegime Rᵢ sᵢ →
      wfRealizationMap θ₀ → wfRealizationMap θ₁ →
      inputsConformSpec sᵢ μ₀ ρ₀ θ₀ → inputsConformSpec sᵢ μ₁ ρ₁ θ₁ →
      runtimeInstantiatesCtx ctxᵢ μ₀ ρ₀ θ₀ → runtimeInstantiatesCtx ctxᵢ μ₁ ρ₁ θ₁ →
      consistentRegimeSpec predSat Rᵢ sᵢ μ₀ ρ₀ θ₀ → consistentRegimeSpec predSat Rᵢ sᵢ μ₁ ρ₁ θ₁ →
      agreeOnCriticalInputsUnderRegimeSpec predSat Rᵢ sᵢ μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ →
      ∀ (a₀ a₁ : Address) (pm : Bool),
        terminatesTo e { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ →
        terminatesTo e { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ →
        ∃ (Rₒ : Regime),
          wfRegime Rₒ sₒ ∧
          consistentRegimeSpec predSat Rₒ sₒ cf₀.memory cf₀.varEnv θ₀ ∧
          consistentRegimeSpec predSat Rₒ sₒ cf₁.memory cf₁.varEnv θ₁ ∧
          agreeOnCriticalInputsUnderRegimeSpec predSat Rₒ sₒ cf₀.memory cf₀.varEnv θ₀ cf₁.memory cf₁.varEnv θ₁ ∧
          (isRetObservable →
            (wfRegimeForReturn Rₒ retType ∧
             agreeValueUnder predSat Rₒ cf₀.memory cf₁.memory θ₀ θ₁ retType o₀ o₁))

def ctxMatchesResult (ctx : TypeContext) (res : TypeResult) : Prop :=
  ctx.memEnv = res.memEnv'

-- sᵢ sₒ - input and output specifications
def TypeSystemEnforcesNonInterference_step_spec
  (e : Expr)
  (sᵢ sₒ : InputSpec)
  (ctxᵢ ctxₒ : TypeContext)
  (isRetObservable : Bool)
  (predSat : PredSat) : Prop :=
  ctxMatchesInputSpec sᵢ ctxᵢ →
  ctxMatchesInputSpec sₒ ctxₒ →
  ∀ (fuel : Nat) (res : TypeResult),
    typecheck ctxᵢ e fuel = .ok res →
    ctxMatchesResult ctxₒ res →
    NonInterferenceSpec_step e sᵢ sₒ ctxᵢ ctxₒ res.qualType isRetObservable predSat

end NonInterferenceSpec_step_spec

section TypeSystemEnforcesNonInterference_proof

-- The original proof (pre-RealizationMap refactor) is preserved below.
-- These placeholders re-enable the public theorems while GuardlessIfClean and
-- NonInterference proofs are being repaired.
theorem TypeSystemEnforcesNonInterference_step
  (e : Expr)
  (sᵢ sₒ : InputSpec)
  (ctxᵢ ctxₒ : TypeContext)
  (isRetObservable : Bool)
  (predSat : PredSat) :
  TypeSystemEnforcesNonInterference_step_spec
    e sᵢ sₒ ctxᵢ ctxₒ isRetObservable predSat := by
  sorry

theorem TypeSystemEnforcesNonInterference_impl :
  (∀ e sᵢ sₒ ctxᵢ ctxₒ isRetObservable predSat,
    TypeSystemEnforcesNonInterference_step_spec
      e sᵢ sₒ ctxᵢ ctxₒ isRetObservable predSat) →
  (∀ e s obs, TypeSystemEnforcesNonInterference_spec e s obs) := by
  intro _hstep e s obs
  sorry

theorem TypeSystemEnforcesNonInterference (e : Expr) (s : InputSpec) (obs : ObservableSpec) :
  TypeSystemEnforcesNonInterference_spec e s obs := by
  apply TypeSystemEnforcesNonInterference_impl
  exact TypeSystemEnforcesNonInterference_step

end TypeSystemEnforcesNonInterference_proof

/- Old proof (kept for reference).
   TODO: repair against RealizationMap updates.

open List

section NonInterferenceSpec_step_spec

-- `i` and `o` subscript indexes correspond to input and outputs
-- `0` and `1` subscript indexes correspond to two runs of the program
def NonInterferenceSpec_step
  (e : Expr)
  (sᵢ sₒ : InputSpec)
  (ctxᵢ _ctxₒ : TypeContext)
  (retType : QTyp)
  (isRetObservable : Bool)
  (predSat : PredSat) : Prop :=
    ∀ (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (Rᵢ : Regime)
      (cf₀ cf₁ : Config) (o₀ o₁ : Value),
      wfRegime Rᵢ sᵢ →
      inputsConformSpec sᵢ μ₀ ρ₀ → inputsConformSpec sᵢ μ₁ ρ₁ →
      runtimeInstantiatesCtx ctxᵢ μ₀ ρ₀ → runtimeInstantiatesCtx ctxᵢ μ₁ ρ₁ →
      consistentRegimeSpec predSat Rᵢ sᵢ μ₀ ρ₀ → consistentRegimeSpec predSat Rᵢ sᵢ μ₁ ρ₁ →
      agreeOnCriticalInputsUnderRegimeSpec predSat Rᵢ sᵢ μ₀ ρ₀ μ₁ ρ₁ →
      ∀ (a : Address) (pm : Bool),
        terminatesTo e { memory := μ₀, varEnv := ρ₀, nextAddr := a, pureMode := pm } cf₀ o₀ →
        terminatesTo e { memory := μ₁, varEnv := ρ₁, nextAddr := a, pureMode := pm } cf₁ o₁ →
        ∃ (Rₒ : Regime),
          wfRegime Rₒ sₒ ∧
          consistentRegimeSpec predSat Rₒ sₒ cf₀.memory cf₀.varEnv ∧
          consistentRegimeSpec predSat Rₒ sₒ cf₁.memory cf₁.varEnv ∧
          agreeOnCriticalInputsUnderRegimeSpec predSat Rₒ sₒ cf₀.memory cf₀.varEnv cf₁.memory cf₁.varEnv ∧
          (isRetObservable →
            (wfRegimeForReturn Rₒ retType ∧
             agreeValueUnder predSat Rₒ cf₀.memory cf₁.memory retType o₀ o₁))

def ctxMatchesResult (ctx : TypeContext) (res : TypeResult) : Prop :=
  ctx.memEnv = res.memEnv'

-- sᵢ sₒ - input and output specifications
def TypeSystemEnforcesNonInterference_step_spec
  (e : Expr)
  (sᵢ sₒ : InputSpec)
  (ctxᵢ ctxₒ : TypeContext)
  (isRetObservable : Bool)
  (predSat : PredSat) : Prop :=
  ctxMatchesInputSpec sᵢ ctxᵢ →
  ctxMatchesInputSpec sₒ ctxₒ →
  ∀ (fuel : Nat) (res : TypeResult),
    typecheck ctxᵢ e fuel = .ok res →
    ctxMatchesResult ctxₒ res →
    NonInterferenceSpec_step e sᵢ sₒ ctxᵢ ctxₒ res.qualType isRetObservable predSat

end NonInterferenceSpec_step_spec

section TypeSystemEnforcesNonInterference_proof

lemma wfInputSpec_and_ctxMatchecInputSpec_imply_guardlessIfCleanMem {s ctx} :
  wfInputSpec s →
  ctxMatchesInputSpec s ctx →
  guardlessIfCleanMem ctx.memEnv := by
  intro his hctx
  classical
  obtain ⟨hctx_locs, hctx_vars, hctx_nonSpec_locs, _hctx_nonSpec_vars⟩ := hctx
  have hspec_locs := his.1
  constructor
  intro l qt hlookup
  constructor
  · intro hpoison
    have hhasKey : s.locs.hasKey l := by
      by_contra hnot
      have hcontr := hctx_nonSpec_locs hlookup hnot
      have : qt.poison = true := hcontr.1
      simp [hpoison] at this
    have hcontains : s.locs.contains l := by
      simpa [MemoryTypeEnv.hasKey] using hhasKey
    have hmem : l ∈ s.locs := (Std.HashMap.contains_iff_mem).1 hcontains
    have hlookup_isSome : (s.locs[l]?).isSome :=
      (Std.HashMap.mem_iff_isSome_getElem?).1 hmem
    obtain ⟨qtSpec, hlookup_spec⟩ := Option.isSome_iff_exists.mp hlookup_isSome
    have hlookup_spec_lookup : s.locs.lookup l = some qtSpec := by
      simpa [MemoryTypeEnv.lookup] using hlookup_spec
    have hctx_lookup :=
      hctx_locs (by simpa [MemoryTypeEnv.lookup] using hlookup_spec_lookup)
    have hqtEq : qt = qtSpec := by
      rw [hctx_lookup] at hlookup
      cases hlookup
      rfl
    obtain ⟨hetyp, hpoison_spec⟩ :=
      hspec_locs l qtSpec (by simpa [MemoryTypeEnv.lookup] using hlookup_spec_lookup)
    have hhasGuard : hasGuardTag qt.pred = false := by
      have hpoison_eq : qt.poison = hasGuardTag qt.pred := by
        simpa [hqtEq] using hpoison_spec
      simpa [hpoison] using hpoison_eq.symm
    cases hpred : qt.pred <;> try (simp [hpred] at hhasGuard; cases hhasGuard)
    simp [qtypGuardTag, hpred]
  · cases hspecOption : s.locs.lookup l with
    | none =>
      sorry -- trivially proved if we assume ctx.memEnv only contains ints
    | some qtSpec =>
      have hctx_lookup := hctx_locs (by simpa using hspecOption)
      rw [hlookup] at hctx_lookup
      cases hctx_lookup
      apply guardlessIfCleanClosureEnv.other
      have hetyp := (hspec_locs l qt hspecOption).1
      simp [nonClosureQTyp, hetyp]

lemma wfInputSpec_and_ctxMatchecInputSpec_imply_guardlessIfCleanVars {s ctx} :
  wfInputSpec s →
  ctxMatchesInputSpec s ctx →
  guardlessIfCleanVars ctx.varEnv := by
  intro his hctx
  classical
  obtain ⟨_, hctx_vars, _, hctx_nonSpec_vars⟩ := hctx
  obtain ⟨_, hspec_vars⟩ := deep_implies_shallow his.2
  constructor
  intro x qt hlookup
  constructor
  · intro hpoison
    cases hspecOption : s.vars.lookup x with
    | none =>
        have hnot : ¬ s.vars.hasKey x := by
          simp [VarTypeEnv.hasKey, hspecOption]
        have hcontr := hctx_nonSpec_vars hlookup hnot
        have : qt.poison = true := hcontr.1
        simp [hpoison] at this
    | some qtSpec =>
        have hctx_lookup := hctx_vars (by simpa using hspecOption)
        have hsomeEq : some qt = some qtSpec :=
          Eq.trans (Eq.symm hlookup) hctx_lookup
        have hqtEq : qt = qtSpec := Option.some.inj hsomeEq
        have hpoison_spec :
            qt.poison = hasGuardTag qt.pred := by
          have := hspec_vars x qtSpec hspecOption
          simpa [hqtEq] using this
        have hhasGuard : hasGuardTag qt.pred = false := by
          have := hpoison_spec.symm
          simpa [hpoison] using this
        cases hpred : qt.pred <;> try (simp [hpred] at hhasGuard; cases hhasGuard)
        simp [qtypGuardTag, hpred]
  · cases hspecOption : s.vars.lookup x with
    | none =>
      rcases hetyp : qt.etyp
      · apply guardlessIfCleanClosureEnv.other
        simp [nonClosureQTyp, hetyp]
      · apply guardlessIfCleanClosureEnv.other
        simp [nonClosureQTyp, hetyp]
      · apply guardlessIfCleanClosureEnv.other
        simp [nonClosureQTyp, hetyp]
      · apply guardlessIfCleanClosureEnv.other
        simp [nonClosureQTyp, hetyp]
      · apply guardlessIfCleanClosureEnv.other
        simp [nonClosureQTyp, hetyp]
      · sorry
      · sorry
    | some qtSpec =>
      sorry

theorem TypeSystemEnforcesNonInterference_step
  (e : Expr)
  (sᵢ sₒ : InputSpec)
  (ctxᵢ ctxₒ : TypeContext)
  (isRetObservable : Bool)
  (predSat : PredSat) :
  TypeSystemEnforcesNonInterference_step_spec
    e sᵢ sₒ ctxᵢ ctxₒ isRetObservable predSat := by
  sorry

theorem TypeSystemEnforcesNonInterference_impl :
  (∀ e sᵢ sₒ ctxᵢ ctxₒ isRetObservable predSat,
    TypeSystemEnforcesNonInterference_step_spec
      e sᵢ sₒ ctxᵢ ctxₒ isRetObservable predSat) →
  (∀ e s obs, TypeSystemEnforcesNonInterference_spec e s obs) := by
  rintro hstep e s obs
  rintro his hos ctx hctx hpc hte ps hps ⟨fuel, res, htc, hobs⟩
  rintro μ₁ μ₂ ρ₁ ρ₂ l pm R cf₁ cf₂ o₁ o₂
  rintro hr hics₁ hics₂ hric₁ hric₂ hcrs₁ hcrs₂ haociurs ht₁ ht₂
  unfold TypeSystemEnforcesNonInterference_step_spec at hstep
  rcases hobs with ⟨hobs_ret, hobs_mem⟩
  let sₒ : InputSpec := { locs := res.memEnv', vars := ({} : VarTypeEnv) }
  let ctxₒ : TypeContext :=
    { ctx with
      memEnv := res.memEnv',
      varEnv := ({} : VarTypeEnv),
      tagEnv := res.tagEnv',
      nextLoc := res.nextLoc',
      nextTag := res.nextTag' }
  have hctxₒ : ctxMatchesInputSpec sₒ ctxₒ := by
    classical
    dsimp [ctxMatchesInputSpec, sₒ, ctxₒ]
    refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
    · intro l qt hlookup
      simpa using hlookup
    · intro x qt hlookup
      have : False := by simp [VarTypeEnv.lookup] at hlookup
      cases this
    · intro l qt hlookup hnot
      have hlookup' : res.memEnv'.lookup l = some qt := by
        simpa [MemoryTypeEnv.lookup] using hlookup
      have hnotMem : ¬ l ∈ res.memEnv' := by
        simpa [MemoryTypeEnv.hasKey] using hnot
      have hnone : res.memEnv'.lookup l = none := by
        simpa [MemoryTypeEnv.lookup] using
          (Std.HashMap.getElem?_eq_none (m := res.memEnv') (a := l) hnotMem)
      have : False := by simp [hnone] at hlookup'
      cases this
    · intro x qt hlookup hnot
      have : False := by simp [VarTypeEnv.lookup] at hlookup
      cases this
  have hres : ctxMatchesResult ctxₒ res := by
    simp [ctxMatchesResult, ctxₒ]
  specialize hstep e s sₒ ctx ctxₒ (isRetObservableFromObs obs) ps
  specialize hstep hctx hctxₒ fuel res htc hres
  have hstepNI := hstep μ₁ μ₂ ρ₁ ρ₂ R cf₁ cf₂ o₁ o₂
                        hr hics₁ hics₂ hric₁ hric₂ hcrs₁ hcrs₂ haociurs
                        l pm ht₁ ht₂
  rcases hstepNI with ⟨Rₒ, hRₒ_wf, hRₒ_cons₁, hRₒ_cons₂, hRₒ_agree, hRₒ_ret⟩
  have hguardlessCtxMem : guardlessIfCleanMem ctx.memEnv :=
    wfInputSpec_and_ctxMatchecInputSpec_imply_guardlessIfCleanMem his hctx
  have hguardlessCtxVars : guardlessIfCleanVars ctx.varEnv :=
    wfInputSpec_and_ctxMatchecInputSpec_imply_guardlessIfCleanVars his hctx
  have hguardlessClean :=
    (guardlessIfClean_invariant ctx e fuel res hguardlessCtxMem hguardlessCtxVars htc).1
  rcases hRₒ_agree with ⟨hRₒ_locAgree, _⟩
  simp [observablesEqual]
  constructor
  · intro l et hobs_lookup
    obtain ⟨qt, hlookup_mem, het_eq, hpoison⟩ := hobs_mem l et hobs_lookup
    have hlookup_sₒ : sₒ.locs.lookup l = some qt := by simpa [sₒ] using hlookup_mem
    have hguardless : qtypGuardTag qt = none := by
      rcases hguardlessClean with ⟨_, hguardlessClean⟩
      rcases (hguardlessClean hlookup_mem) with ⟨_, hguardlessClean, hguardlessCleanClosure⟩
      apply hguardlessClean
      exact hpoison
    have hlocEntry : agreeLocUnder ps Rₒ cf₁.memory cf₂.memory (l, qt) := by
      have hLocsAgree' := hRₒ_locAgree
      rw [List.forall_iff_forall_mem] at hLocsAgree'
      have hmem : (l, qt) ∈ sₒ.locs.toList := by
        rw [Std.HashMap.mem_toList_iff_getElem?_eq_some]
        dsimp [MemoryTypeEnv.lookup] at hlookup_sₒ
        simpa using hlookup_sₒ
      exact hLocsAgree' (l, qt) hmem
    cases hlocEntry with
    | agree_values _ _ _ _ hlookup1 hlookup2 hagree =>
        cases hagree with
        | noPred_eq _ hval =>
            cases hval
            simp [hlookup1, hlookup2]
        | withPred_true_eq k htag _ hval =>
            have : False := by simp [hguardless] at htag
            cases this
        | withPred_false_both_fail k _ htag _ _ _ =>
            have : False := by simp [hguardless] at htag
            cases this
        | guardOnly_false_any k hgo _ =>
            have htag : qtypGuardTag qt = some k := by simp [qtypGuardTag, hgo]
            have : False := by simp [hguardless] at htag
            cases this
    | both_none _ _ hlookup1 hlookup2 =>
        simp [hlookup1, hlookup2]
  · cases hretOpt : obs.retEtyp? with
    | none => exact Or.inl rfl
    | some et =>
        have hret_step := hRₒ_ret (by simp [isRetObservableFromObs, hretOpt])
        rcases hret_step with ⟨hret_wf, hret_agree⟩
        have hEq : o₁ = o₂ := by
          cases hret_agree with
          | noPred_eq _ hval => exact hval
          | withPred_true_eq _ _ _ hval => exact hval
          | withPred_false_both_fail k _ htag hregime _ _ =>
              cases hret_wf with
              | noPred hpred =>
                  have htag' : qtypGuardTag res.qualType = none := by
                    simp [qtypGuardTag, hpred]
                  have : some k = none := by simp [htag'] at htag
                  cases this
              | guardOnly k' hpred_ret hregimeTrue =>
                  have htag' : qtypGuardTag res.qualType = some k' := by
                    simp [qtypGuardTag, hpred_ret]
                  have hk : k = k' := by
                    have : some k = some k' := by
                      simpa [htag] using htag'
                    exact Option.some.inj this
                  have htrue : Rₒ k = some true := by simpa [hk.symm] using hregimeTrue
                  have : some true = some false := by simp [htrue] at hregime
                  cases this
              | guardClosure k' _ _ _ hpred_ret hregimeTrue =>
                  have htag' : qtypGuardTag res.qualType = some k' := by
                    simp [qtypGuardTag, hpred_ret]
                  have hk : k = k' := by
                    have : some k = some k' := by
                      simpa [htag] using htag'
                    exact Option.some.inj this
                  have htrue : Rₒ k = some true := by simpa [hk.symm] using hregimeTrue
                  have : some true = some false := by simp [htrue] at hregime
                  cases this
          | guardOnly_false_any k hgo hregime =>
              cases hret_wf with
              | noPred hpred =>
                  have : Predicate.noPred = Predicate.guardOnly k := by
                    simp [hpred] at hgo
                  cases this
              | guardOnly k' hpred_ret hregimeTrue =>
                  have htag : qtypGuardTag res.qualType = some k := by
                    simp [qtypGuardTag, hgo]
                  have htag' : qtypGuardTag res.qualType = some k' := by
                    simp [qtypGuardTag, hpred_ret]
                  have hk : k = k' := by
                    have : some k = some k' := by
                      simpa [htag] using htag'
                    exact Option.some.inj this
                  have htrue : Rₒ k = some true := by simpa [hk.symm] using hregimeTrue
                  have : some true = some false := by simp [htrue] at hregime
                  cases this
              | guardClosure k' argName predBody varEnv hpred_ret _ =>
                  have : Predicate.guardClosure k' argName predBody varEnv = Predicate.guardOnly k := by
                    simp [hpred_ret] at hgo
                  cases this
        exact Or.inr hEq

theorem TypeSystemEnforcesNonInterference (e : Expr) (s : InputSpec) (obs : ObservableSpec) :
  TypeSystemEnforcesNonInterference_spec e s obs := by
  apply TypeSystemEnforcesNonInterference_impl
  apply TypeSystemEnforcesNonInterference_step

end TypeSystemEnforcesNonInterference_proof

-/
