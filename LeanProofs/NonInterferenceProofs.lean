-- Non-Interference properties for the poison language

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanPoison.BigStep
import Mathlib.Data.List.Forall2

import LeanProofs.NonInterference

open List
open scoped MemoryTypeEnv

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
          fullyRealizes sₒ θ₀' ∧ fullyRealizes sₒ θ₁' ∧
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

section TypeSystemEnforcesNonInterference_impl_proof

private def outputSpec (res : TypeResult) : InputSpec :=
  { locs := res.memEnv', vars := ({} : VarTypeEnv) }

private lemma ret_eq_of_agreeValueUnder_nonref
  {predSat : PredSat} {R : Regime} {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap}
  {qt : QTyp} {o₀ o₁ : Value} :
  (¬ ∃ t ls, qt.etyp = ETyp.ref t ls) →
  wfRegimeForReturn R qt →
  agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ →
  o₀ = o₁ := by
  intro hnotref hret_wf hret_agree
  cases hret_agree with
  | clean_eq_nonref _ _ hval => exact hval
  | poisoned_noPred_eq_nonref _ _ _ hval => exact hval
  | clean_ref _ hetyp _ _ _ _ _ _ =>
      exfalso
      exact hnotref ⟨_, _, hetyp⟩
  | poisoned_noPred_ref _ _ hetyp _ _ _ _ _ _ =>
      exfalso
      exact hnotref ⟨_, _, hetyp⟩
  | withPred_true_eq _ _ _ _ hval => exact hval
  | withPred_true_ref _ _ _ hetyp _ _ _ _ _ _ =>
      exfalso
      exact hnotref ⟨_, _, hetyp⟩
  | withPred_false_poisoned_fail k _ htag hregime _ _ _ =>
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
  | guardOnly_false_poisoned_any k hgo hregime _ =>
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
    ⟨θ₀', θ₁', Rₒ, _hθ₀', _hθ₁', _hθ₀ext, _hθ₁ext, hfull₀, hfull₁, _hRₒ_wf,
      _hRₒ_cons₀, _hRₒ_cons₁, hRₒ_agree, hRₒ_ret⟩
  rcases hRₒ_agree with ⟨hRₒ_locAgree, _⟩
  refine ⟨θ₀', θ₁', _hθ₀ext, _hθ₁ext, ?_⟩
  simp [observablesEqual]
  constructor
  · intro l et hobs_lookup
    obtain ⟨qt, hlookup_mem, _het_eq, hpoison⟩ := hobs_mem l et hobs_lookup
    have hlookup_sₒ : sₒ.locs.lookup l = some qt := by
      simpa [sₒ, outputSpec] using hlookup_mem
    have hlocEntry : agreeLocUnder predSat Rₒ cf₀.memory cf₁.memory θ₀' θ₁' (l, qt) := by
      have hLocsAgree' := hRₒ_locAgree
      rw [List.forall_iff_forall_mem] at hLocsAgree'
      have hmem : (l, qt) ∈ sₒ.locs.toList := by
        rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some]
        dsimp [MemoryTypeEnv.lookup] at hlookup_sₒ
        simpa using hlookup_sₒ
      exact hLocsAgree' (l, qt) hmem
    cases hlocEntry with
    | agree_values _l' _qt' a₀' a₁' n₀ n₁ hreal₀ hreal₁ hlookup₀ hlookup₁ hagree =>
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
              have hcontra : False := by
                have hpoison'' : false = true := by
                  calc
                    false = qt.poison := by
                      symm
                      exact hpoison
                    _ = true := by
                      exact hpoison'
                cases hpoison''
              exact (False.elim hcontra)
          | guardOnly_false_poisoned_any _ _ _ hpoison' =>
              have hcontra : False := by
                have hpoison'' : false = true := by
                  calc
                    false = qt.poison := by
                      symm
                      exact hpoison
                    _ = true := by
                      exact hpoison'
                cases hpoison''
              exact (False.elim hcontra)
        have hmemEq : cf₀.memory.lookup a₀' = cf₁.memory.lookup a₁' := by
          simp [hlookup₀, hlookup₁, hvalEq]
        refine ⟨a₀', ?_⟩
        refine And.intro hreal₀ ?_
        refine ⟨a₁', ?_⟩
        exact And.intro hreal₁ hmemEq
    | both_unrealized _l' _qt' hnone₀ _hnone₁ =>
        have hlookup_some : sₒ.locs[l]? = some qt := by
          simpa [MemoryTypeEnv.lookup] using hlookup_sₒ
        have hlookup_isSome : (sₒ.locs[l]?).isSome = true := by
          simp [hlookup_some]
        have hmem : l ∈ sₒ.locs :=
          (Std.ExtTreeMap.mem_iff_isSome_getElem?).2 hlookup_isSome
        have hcontains : sₒ.locs.contains l = true :=
          (Std.ExtTreeMap.contains_iff_mem).2 hmem
        have hhasKey : sₒ.locs.hasKey l := by
          simpa [MemoryTypeEnv.hasKey] using hcontains
        have hreal := hfull₀ l hhasKey
        have : False := by
          apply hreal
          simpa using hnone₀
        exact (False.elim this)
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
            rcases hobs_ret _ hretOpt with ⟨hret_et, hret_poison⟩
            cases hret_agree with
            | clean_ref hpoison hetyp hlookup1 hin1 hv1 hlookup2 hin2 hv2 =>
                rename_i t' ls' l₁ l₂ a₁ a₂
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
            | poisoned_noPred_ref hpoison _ _ _ _ _ _ _ _ =>
                have hcontra : False := by
                  have hpoison' : false = true := by
                    calc
                      false = res.qualType.poison := by
                        symm
                        exact hret_poison
                      _ = true := by
                        exact hpoison
                  cases hpoison'
                exact (False.elim hcontra)
            | withPred_true_ref _ htag hregime hetyp hlookup1 hin1 hv1 hlookup2 hin2 hv2 =>
                rename_i t' ls' l₁ l₂ a₁ a₂
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
                exact (False.elim this)
            | poisoned_noPred_eq_nonref _ _ hnotref _ =>
                have : False := by
                  apply hnotref
                  exact ⟨t, ls, hret_et⟩
                exact (False.elim this)
            | withPred_true_eq _ _ _ hnotref _ =>
                have : False := by
                  apply hnotref
                  exact ⟨t, ls, hret_et⟩
                exact (False.elim this)
            | withPred_false_poisoned_fail _ _ _ _ hpoison' _ _ =>
                have hcontra : False := by
                  have hpoison'' : false = true := by
                    calc
                      false = res.qualType.poison := by
                        symm
                        exact hret_poison
                      _ = true := by
                        exact hpoison'
                  cases hpoison''
                exact (False.elim hcontra)
            | guardOnly_false_poisoned_any _ _ _ hpoison' =>
                have hcontra : False := by
                  have hpoison'' : false = true := by
                    calc
                      false = res.qualType.poison := by
                        symm
                        exact hret_poison
                      _ = true := by
                        exact hpoison'
                  cases hpoison''
                exact (False.elim hcontra)
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

end TypeSystemEnforcesNonInterference_impl_proof

section TypeSystemEnforcesNonInterference_step_proof

theorem TypeSystemEnforcesNonInterference_step
  (e : Expr)
  (sᵢ sₒ : InputSpec)
  (ctxᵢ : TypeContext)
  (isRetObservable : Bool)
  (predSat : PredSat) :
  TypeSystemEnforcesNonInterference_step_spec
    e sᵢ sₒ ctxᵢ isRetObservable predSat := by
  sorry

end TypeSystemEnforcesNonInterference_step_proof

-- Top-level theorem
theorem TypeSystemEnforcesNonInterference (e : Expr) (s : InputSpec) (obs : ObservableSpec) :
  TypeSystemEnforcesNonInterference_spec e s obs := by
  apply TypeSystemEnforcesNonInterference_impl
  exact TypeSystemEnforcesNonInterference_step
