-- Non-Interference properties for the poison language

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanPoison.BigStep
import Mathlib.Data.List.Forall2

import LeanProofs.NonInterference
import LeanProofs.IOHelpers

open List
open scoped MemoryTypeEnv

section NonInterferenceSpec_step_spec

-- `i` and `o` subscript indexes correspond to input and outputs
-- `0` and `1` subscript indexes correspond to two runs of the program
def NonInterferenceSpec_step
  (e : Expr)
  (sᵢ sₒ : InputSpec)
  (ctxᵢ : TypeContext)
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
        ∃ (θ₀' θ₁' : RealizationMap) (Rₒ : Regime),
          wfRealizationMap θ₀' ∧ wfRealizationMap θ₁' ∧
          wfExtendsMap θ₀ θ₀' ∧ wfExtendsMap θ₁ θ₁' ∧
          wfRegime Rₒ sₒ ∧
          consistentRegimeSpec predSat Rₒ sₒ cf₀.memory cf₀.varEnv θ₀' ∧
          consistentRegimeSpec predSat Rₒ sₒ cf₁.memory cf₁.varEnv θ₁' ∧
          agreeOnCriticalInputsUnderRegimeSpec predSat Rₒ sₒ
            cf₀.memory cf₀.varEnv θ₀' cf₁.memory cf₁.varEnv θ₁' ∧
          (isRetObservable →
            (wfRegimeForReturn Rₒ retType ∧
             agreeValueUnder predSat Rₒ cf₀.memory cf₁.memory θ₀' θ₁' retType o₀ o₁))

-- sᵢ sₒ - input and output specifications
-- sₒ is constrained to match the typing result (locs = res.memEnv')
def TypeSystemEnforcesNonInterference_step_spec
  (e : Expr)
  (sᵢ sₒ : InputSpec)
  (ctxᵢ : TypeContext)
  (isRetObservable : Bool)
  (predSat : PredSat) : Prop :=
  ctxMatchesInputSpec sᵢ ctxᵢ →
  ∀ (fuel : Nat) (res : TypeResult),
    typecheck ctxᵢ e fuel = .ok res →
    sₒ.locs ⊆ res.memEnv' →
    NonInterferenceSpec_step e sᵢ sₒ ctxᵢ res.qualType isRetObservable predSat

end NonInterferenceSpec_step_spec

section TypeSystemEnforcesNonInterference_proof

theorem TypeSystemEnforcesNonInterference_step
  (e : Expr)
  (sᵢ sₒ : InputSpec)
  (ctxᵢ : TypeContext)
  (isRetObservable : Bool)
  (predSat : PredSat) :
  TypeSystemEnforcesNonInterference_step_spec
    e sᵢ sₒ ctxᵢ isRetObservable predSat := by
  sorry

section TypeSystemEnforcesNonInterference_impl_sketch

private def outputSpec (res : TypeResult) : InputSpec :=
  { locs := res.memEnv', vars := ({} : VarTypeEnv) }

private lemma wfInputSpec_and_ctxMatchecInputSpec_imply_guardlessIfCleanMem {s ctx} :
  wfInputSpec s →
  ctxMatchesInputSpec s ctx →
  guardlessIfCleanMem ctx.memEnv := by
  intro his hctx
  classical
  obtain ⟨hctx_locs, _hctx_vars, hctx_nonSpec_locs, _hctx_nonSpec_vars⟩ := hctx
  have hspec_locs := his.1
  refine guardlessIfCleanMem.intro _ ?_
  intro l qt hlookup
  refine guardlessIfCleanQTypDeep.intro _ ?_ ?_
  · intro hpoison
    have hhasKey : s.locs.hasKey l := by
      by_contra hnot
      have hcontr := hctx_nonSpec_locs hlookup hnot
      have : qt.poison = true := hcontr.1
      simp [hpoison] at this
    have hcontains : s.locs.contains l = true := by
      simpa [MemoryTypeEnv.hasKey] using hhasKey
    have hmem : l ∈ s.locs := (Std.ExtTreeMap.contains_iff_mem).1 hcontains
    have hlookup_isSome : (s.locs[l]?).isSome = true :=
      (Std.ExtTreeMap.mem_iff_isSome_getElem?).1 hmem
    obtain ⟨qtSpec, hlookup_spec⟩ := Option.isSome_iff_exists.mp hlookup_isSome
    have hlookup_spec_lookup : s.locs.lookup l = some qtSpec := by
      simpa [MemoryTypeEnv.lookup] using hlookup_spec
    have hctx_lookup :=
      hctx_locs (by simpa [MemoryTypeEnv.lookup] using hlookup_spec_lookup)
    have hqtEq : qt = qtSpec := by
      rw [hctx_lookup] at hlookup
      cases hlookup
      rfl
    obtain ⟨_hetyp, hpoison_spec⟩ :=
      hspec_locs l qtSpec (by simpa [MemoryTypeEnv.lookup] using hlookup_spec_lookup)
    have hhasGuard : hasGuardTag qt.pred = false := by
      have hpoison_eq : qt.poison = hasGuardTag qt.pred := by
        simpa [hqtEq] using hpoison_spec
      simpa [hpoison] using hpoison_eq.symm
    cases hpred : qt.pred <;> try (simp [hpred] at hhasGuard; cases hhasGuard)
    simp [qtypGuardTag, hpred]
  · cases hspecOption : s.locs.lookup l with
    | none =>
        -- as in old proof; needs stronger assumptions on ctx.memEnv contents
        sorry
    | some qtSpec =>
        have hctx_lookup := hctx_locs (by simpa using hspecOption)
        rw [hlookup] at hctx_lookup
        cases hctx_lookup
        apply guardlessIfCleanClosureEnv.other
        have hetyp := (hspec_locs l qt hspecOption).1
        simp [nonClosureQTyp, hetyp]

private lemma guardlessClosure_of_nonSpecVar {s : InputSpec} {ctx : TypeContext} {x qt} :
  ctxMatchesInputSpec s ctx →
  ctx.varEnv.lookup x = some qt →
  ¬ s.vars.hasKey x →
  guardlessIfCleanClosureEnv qt := by
  -- TODO: port from old proof using ctxMatchesInputSpec non-spec invariants.
  sorry

private lemma guardlessClosure_of_specVar {s : InputSpec} {x qt} :
  wfInputSpecVarsDeep s.vars →
  s.vars.lookup x = some qt →
  guardlessIfCleanClosureEnv qt := by
  -- TODO: port from old proof using deepVarEnvProperty on input specs.
  sorry

private lemma wfInputSpec_and_ctxMatchecInputSpec_imply_guardlessIfCleanVars {s ctx} :
  wfInputSpec s →
  ctxMatchesInputSpec s ctx →
  guardlessIfCleanVars ctx.varEnv := by
  intro his hctx
  classical
  have hctx_all := hctx
  obtain ⟨_, hctx_vars, _, hctx_nonSpec_vars⟩ := hctx
  obtain ⟨_, hspec_vars⟩ := deep_implies_shallow his.2
  refine guardlessIfCleanVars.intro _ ?_
  intro x qt hlookup
  refine guardlessIfCleanQTypDeep.intro _ ?_ ?_
  · intro hpoison
    cases hspecOption : s.vars.lookup x with
    | none =>
        have hnot : ¬ s.vars.hasKey x := by
          intro hhasKey
          have hcontains : s.vars.contains x = true := by
            simpa [VarTypeEnv.hasKey] using hhasKey
          have hmem : x ∈ s.vars := (Std.ExtTreeMap.contains_iff_mem).1 hcontains
          have hsome : (s.vars[x]?).isSome = true :=
            (Std.ExtTreeMap.mem_iff_isSome_getElem?).1 hmem
          have hnone : s.vars[x]? = none := by
            simpa [VarTypeEnv.lookup] using hspecOption
          simp [hnone] at hsome
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
        have hnot : ¬ s.vars.hasKey x := by
          intro hhasKey
          have hcontains : s.vars.contains x = true := by
            simpa [VarTypeEnv.hasKey] using hhasKey
          have hmem : x ∈ s.vars := (Std.ExtTreeMap.contains_iff_mem).1 hcontains
          have hsome : (s.vars[x]?).isSome = true :=
            (Std.ExtTreeMap.mem_iff_isSome_getElem?).1 hmem
          have hnone : s.vars[x]? = none := by
            simpa [VarTypeEnv.lookup] using hspecOption
          simp [hnone] at hsome
        exact guardlessClosure_of_nonSpecVar hctx_all hlookup hnot
    | some qtSpec =>
        have hctx_lookup := hctx_vars (by simpa using hspecOption)
        have hsomeEq : some qt = some qtSpec :=
          Eq.trans (Eq.symm hlookup) hctx_lookup
        have hqtEq : qt = qtSpec := Option.some.inj hsomeEq
        subst hqtEq
        exact guardlessClosure_of_specVar his.2 hspecOption

private lemma ret_eq_of_agreeValueUnder_nonref
  {predSat : PredSat} {R : Regime} {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap}
  {qt : QTyp} {o₀ o₁ : Value} :
  (¬ ∃ t ls, qt.etyp = ETyp.ref t ls) →
  wfRegimeForReturn R qt →
  agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ →
  o₀ = o₁ := by
  intro hnotref hret_wf hret_agree
  cases hret_agree with
  | noPred_eq _ _ hval => exact hval
  | noPred_ref hetyp _ _ _ _ _ _ =>
      exfalso
      exact hnotref ⟨_, _, hetyp⟩
  | withPred_true_eq _ _ _ hval => exact hval
  | withPred_false_both_fail k _ htag hregime _ _ =>
      cases hret_wf with
      | noPred hpred =>
          have htag' : qtypGuardTag qt = none := by
            simp [qtypGuardTag, hpred]
          have : some k = none := by
            calc
              some k = qtypGuardTag qt := by
                symm
                exact htag
              _ = none := by
                exact htag'
          cases this
      | guardOnly k' hpred_ret hregimeTrue =>
          have htag' : qtypGuardTag qt = some k' := by
            simp [qtypGuardTag, hpred_ret]
          have hk : k = k' := by
            have : some k = some k' := by
              calc
                some k = qtypGuardTag qt := by
                  symm
                  exact htag
                _ = some k' := by
                  exact htag'
            exact Option.some.inj this
          have htrue : R k = some true := by
            cases hk
            exact hregimeTrue
          have : some true = some false := by
            calc
              some true = R k := by
                symm
                exact htrue
              _ = some false := by
                exact hregime
          cases this
      | guardClosure k' arg_name pred_body var_env hpred_ret hregimeTrue =>
          have htag' : qtypGuardTag qt = some k' := by
            simp [qtypGuardTag, hpred_ret]
          have hk : k = k' := by
            have : some k = some k' := by
              calc
                some k = qtypGuardTag qt := by
                  symm
                  exact htag
                _ = some k' := by
                  exact htag'
            exact Option.some.inj this
          have htrue : R k = some true := by
            cases hk
            exact hregimeTrue
          have : some true = some false := by
            calc
              some true = R k := by
                symm
                exact htrue
              _ = some false := by
                exact hregime
          cases this
  | guardOnly_false_any k hgo hregime =>
      cases hret_wf with
      | noPred hpred =>
          have : Predicate.noPred = Predicate.guardOnly k := by
            calc
              Predicate.noPred = qt.pred := by
                symm
                exact hpred
              _ = Predicate.guardOnly k := by
                exact hgo
          cases this
      | guardOnly k' hpred_ret hregimeTrue =>
          have htag : qtypGuardTag qt = some k := by
            simp [qtypGuardTag, hgo]
          have htag' : qtypGuardTag qt = some k' := by
            simp [qtypGuardTag, hpred_ret]
          have hk : k = k' := by
            have : some k = some k' := by
              calc
                some k = qtypGuardTag qt := by
                  symm
                  exact htag
                _ = some k' := by
                  exact htag'
            exact Option.some.inj this
          have htrue : R k = some true := by
            cases hk
            exact hregimeTrue
          have : some true = some false := by
            calc
              some true = R k := by
                symm
                exact htrue
              _ = some false := by
                exact hregime
          cases this
      | guardClosure k' arg_name pred_body var_env hpred_ret _ =>
          have : Predicate.guardClosure k' arg_name pred_body var_env = Predicate.guardOnly k := by
            calc
              Predicate.guardClosure k' arg_name pred_body var_env = qt.pred := by
                symm
                exact hpred_ret
              _ = Predicate.guardOnly k := by
                exact hgo
          cases this

private lemma outputSpec_locs_subset (res : TypeResult) :
  (outputSpec res).locs ⊆ res.memEnv' := by
  intro l qt hlookup
  simpa [outputSpec] using hlookup

private lemma mem_guardless_from_typecheck
  {s : InputSpec} {ctx : TypeContext} {e : Expr} {fuel : Nat} {res : TypeResult} :
  wfInputSpec s →
  ctxMatchesInputSpec s ctx →
  typecheck ctx e fuel = .ok res →
  ∀ {l qt}, res.memEnv'.lookup l = some qt → guardlessIfCleanQTyp qt := by
  intro his hctx htc l qt hlookup
  have hguardlessCtxMem : guardlessIfCleanMem ctx.memEnv :=
    wfInputSpec_and_ctxMatchecInputSpec_imply_guardlessIfCleanMem his hctx
  have hguardlessCtxVars : guardlessIfCleanVars ctx.varEnv :=
    wfInputSpec_and_ctxMatchecInputSpec_imply_guardlessIfCleanVars his hctx
  have hguardlessClean :=
    (guardlessIfClean_invariant ctx e fuel res hguardlessCtxMem hguardlessCtxVars htc).1
  cases hguardlessClean with
  | intro _ hmem =>
      have hqtDeep := hmem hlookup
      exact guardlessIfCleanQTypDeep.guardless hqtDeep

private lemma output_mem_guardless
  {s : InputSpec} {ctx : TypeContext} {e : Expr} {fuel : Nat} {res : TypeResult}
  {l : Loc} {qt : QTyp} :
  wfInputSpec s →
  ctxMatchesInputSpec s ctx →
  typecheck ctx e fuel = .ok res →
  res.memEnv'.lookup l = some qt →
  qt.poison = false →
  qtypGuardTag qt = none := by
  intro his hctx htc hlookup hpoison
  have hguardless := mem_guardless_from_typecheck (s := s) (ctx := ctx) (e := e)
    (fuel := fuel) (res := res) his hctx htc hlookup
  exact hguardless hpoison

theorem TypeSystemEnforcesNonInterference_impl :
  (∀ e sᵢ sₒ ctxᵢ isRetObservable predSat,
    TypeSystemEnforcesNonInterference_step_spec
      e sᵢ sₒ ctxᵢ isRetObservable predSat) →
  (∀ e s obs, TypeSystemEnforcesNonInterference_spec e s obs) := by
  intro hstep e s obs
  rintro his _hos ctx hctx _hpc _hte predSat _hps ⟨fuel, res, htc, hobs⟩
  rcases hobs with ⟨hobs_ret, hobs_mem⟩
  let sₒ : InputSpec := outputSpec res
  have hsubset : sₒ.locs ⊆ res.memEnv' := outputSpec_locs_subset res
  have hstep' := hstep e s sₒ ctx (isRetObservableFromObs obs) predSat
  have hstep' := hstep' hctx fuel res htc hsubset
  rintro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ a₀ a₁ pm R cf₀ cf₁ o₀ o₁
  rintro hR hθ₀ hθ₁ hics₀ hics₁ hric₀ hric₁ hcrs₀ hcrs₁ hagree ht₀ ht₁
  have hstepNI :=
    hstep' μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ R cf₀ cf₁ o₀ o₁
      hR hθ₀ hθ₁ hics₀ hics₁ hric₀ hric₁ hcrs₀ hcrs₁ hagree
      a₀ a₁ pm ht₀ ht₁
  rcases hstepNI with
    ⟨θ₀', θ₁', Rₒ, _hθ₀', _hθ₁', _hθ₀ext, _hθ₁ext, _hRₒ_wf,
      _hRₒ_cons₀, _hRₒ_cons₁, hRₒ_agree, hRₒ_ret⟩
  rcases hRₒ_agree with ⟨hRₒ_locAgree, _⟩
  simp [observablesEqual]
  constructor
  · intro l et hobs_lookup
    obtain ⟨qt, hlookup_mem, _het_eq, hpoison⟩ := hobs_mem l et hobs_lookup
    have hlookup_sₒ : sₒ.locs.lookup l = some qt := by
      simpa [sₒ, outputSpec] using hlookup_mem
    have _hguardless : qtypGuardTag qt = none :=
      output_mem_guardless (s := s) (ctx := ctx) (e := e) (fuel := fuel) (res := res)
        his hctx htc hlookup_mem hpoison
    have hlocEntry : agreeLocUnder predSat Rₒ cf₀.memory cf₁.memory θ₀' θ₁' (l, qt) := by
      have hLocsAgree' := hRₒ_locAgree
      rw [List.forall_iff_forall_mem] at hLocsAgree'
      have hmem : (l, qt) ∈ sₒ.locs.toList := by
        rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some]
        dsimp [MemoryTypeEnv.lookup] at hlookup_sₒ
        simpa using hlookup_sₒ
      exact hLocsAgree' (l, qt) hmem
    cases hlocEntry with
    | agree_values _l' _qt' a₀' a₁' n₀ n₁ _hreal₀ _hreal₁ hlookup₀ hlookup₁ hagree =>
        -- Ported from old proof: reduce to equality of stored ints under guardless agreement.
        have hvalEq : n₀ = n₁ := by
          cases hagree with
          | noPred_eq _ _ hval =>
              cases hval
              rfl
          | noPred_ref _ _ _ _ hv1 _ _ _ =>
              cases hv1
          | withPred_true_eq _ _ _ hval =>
              cases hval
              rfl
          | withPred_false_both_fail k _ htag _ _ _ =>
              have : False := by
                have htag' : some k = none := by
                  calc
                    some k = qtypGuardTag qt := by
                      symm
                      exact htag
                    _ = none := by
                      exact _hguardless
                cases htag'
              cases this
          | guardOnly_false_any k hgo _ =>
              have htag : qtypGuardTag qt = some k := by
                simp [qtypGuardTag, hgo]
              have : False := by
                have htag' : some k = none := by
                  calc
                    some k = qtypGuardTag qt := by
                      symm
                      exact htag
                    _ = none := by
                      exact _hguardless
                cases htag'
              cases this
        have hmemEq : cf₀.memory.lookup a₀' = cf₁.memory.lookup a₁' := by
          simp [hlookup₀, hlookup₁, hvalEq]
        refine ⟨a₀', ?_⟩
        refine And.intro ?_ ?_
        · -- TODO: relate θ₀ to θ₀' for observable locations.
          sorry
        · refine ⟨a₁', ?_⟩
          refine And.intro ?_ hmemEq
          -- TODO: relate θ₁ to θ₁' for observable locations.
          sorry
    | both_unrealized _l' _qt' _hnone₀ _hnone₁ =>
        -- TODO: for observable locations, rule out unrealized cases.
        sorry
  · cases hretOpt : obs.retEtyp? with
    | none =>
        -- sameRet = True
        simp
    | some et =>
        -- Use return agreement from the step proof.
        have hret_step := hRₒ_ret (by simp [isRetObservableFromObs, hretOpt])
        -- TODO: split on ref vs non-ref using hobs_ret and hret_step.
        -- The ref case should use θ₀'/θ₁' and wfExtendsMap to witness the same logical loc set.
        -- The non-ref case should reduce to equality.
        rcases hret_step with ⟨hret_wf, hret_agree⟩
        cases et with
        | ref t ls =>
            -- TODO: adapt to ref observability via θ₀'/θ₁' and wfExtendsMap.
            sorry
        | int =>
            have hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
              rcases hobs_ret _ hretOpt with ⟨het, _⟩
              simp [het]
            exact ret_eq_of_agreeValueUnder_nonref hnotref hret_wf hret_agree
        | bool =>
            have hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
              rcases hobs_ret _ hretOpt with ⟨het, _⟩
              simp [het]
            exact ret_eq_of_agreeValueUnder_nonref hnotref hret_wf hret_agree
        | unit =>
            have hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
              rcases hobs_ret _ hretOpt with ⟨het, _⟩
              simp [het]
            exact ret_eq_of_agreeValueUnder_nonref hnotref hret_wf hret_agree
        | string =>
            have hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
              rcases hobs_ret _ hretOpt with ⟨het, _⟩
              simp [het]
            exact ret_eq_of_agreeValueUnder_nonref hnotref hret_wf hret_agree
        | arrow st₁ st₂ p tcls =>
            have hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
              rcases hobs_ret _ hretOpt with ⟨het, _⟩
              simp [het]
            exact ret_eq_of_agreeValueUnder_nonref hnotref hret_wf hret_agree
        | parrow st₁ st₂ p tcls =>
            have hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
              rcases hobs_ret _ hretOpt with ⟨het, _⟩
              simp [het]
            exact ret_eq_of_agreeValueUnder_nonref hnotref hret_wf hret_agree

end TypeSystemEnforcesNonInterference_impl_sketch


theorem TypeSystemEnforcesNonInterference (e : Expr) (s : InputSpec) (obs : ObservableSpec) :
  TypeSystemEnforcesNonInterference_spec e s obs := by
  apply TypeSystemEnforcesNonInterference_impl
  exact TypeSystemEnforcesNonInterference_step

end TypeSystemEnforcesNonInterference_proof
