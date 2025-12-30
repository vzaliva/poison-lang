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
  have hstepFR :=
    (hstep' R) μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁
      hθ₀ hθ₁ hric₀ hric₁ hagree_clean
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

private lemma terminatesTo_num_inv (n : Int)
  (μ : Memory) (ρ : VarEnv) (a : Address) (pm : Bool) (cf : Config) (o : Value) :
  terminatesTo (Expr.num n) { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o →
  cf = { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } ∧ o = Value.num n := by
  intro ht
  rcases ht with ⟨fuel, verbose, hbeval⟩
  have h_eval_world := LeanProofs.evalAtDefault_eq hbeval
  cases fuel with
  | zero =>
      simp [LeanPoison.beval] at h_eval_world
      cases h_eval_world
  | succ fuel =>
      simp [LeanPoison.beval] at h_eval_world
      injection h_eval_world with hcfg hval
      cases hcfg
      cases hval
      constructor <;> rfl

private lemma terminatesTo_bool_inv (b : Bool)
  (μ : Memory) (ρ : VarEnv) (a : Address) (pm : Bool) (cf : Config) (o : Value) :
  terminatesTo (Expr.bool b) { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o →
  cf = { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } ∧ o = Value.bool b := by
  intro ht
  rcases ht with ⟨fuel, verbose, hbeval⟩
  have h_eval_world := LeanProofs.evalAtDefault_eq hbeval
  cases fuel with
  | zero =>
      simp [LeanPoison.beval] at h_eval_world
      cases h_eval_world
  | succ fuel =>
      simp [LeanPoison.beval] at h_eval_world
      injection h_eval_world with hcfg hval
      cases hcfg
      cases hval
      constructor <;> rfl

private lemma terminatesTo_unit_inv
  (μ : Memory) (ρ : VarEnv) (a : Address) (pm : Bool) (cf : Config) (o : Value) :
  terminatesTo Expr.unit { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o →
  cf = { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } ∧ o = Value.unit := by
  intro ht
  rcases ht with ⟨fuel, verbose, hbeval⟩
  have h_eval_world := LeanProofs.evalAtDefault_eq hbeval
  cases fuel with
  | zero =>
      simp [LeanPoison.beval] at h_eval_world
      cases h_eval_world
  | succ fuel =>
      simp [LeanPoison.beval] at h_eval_world
      injection h_eval_world with hcfg hval
      cases hcfg
      cases hval
      constructor <;> rfl

private lemma terminatesTo_str_inv (s : String)
  (μ : Memory) (ρ : VarEnv) (a : Address) (pm : Bool) (cf : Config) (o : Value) :
  terminatesTo (Expr.str s) { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o →
  cf = { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } ∧ o = Value.str s := by
  intro ht
  rcases ht with ⟨fuel, verbose, hbeval⟩
  have h_eval_world := LeanProofs.evalAtDefault_eq hbeval
  cases fuel with
  | zero =>
      simp [LeanPoison.beval] at h_eval_world
      cases h_eval_world
  | succ fuel =>
      simp [LeanPoison.beval] at h_eval_world
      injection h_eval_world with hcfg hval
      cases hcfg
      cases hval
      constructor <;> rfl

private lemma terminatesTo_literal_inv
  (e : Expr) (v : Value)
  (hval : Expr.toValue? e = some v)
  (μ : Memory) (ρ : VarEnv) (a : Address) (pm : Bool) (cf : Config) (o : Value) :
  terminatesTo e { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o →
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
  terminatesTo (Expr.var x) { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o →
  ∃ v, ρ.lookup x = some v ∧
    cf = { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } ∧
    o = v := by
  intro ht
  rcases ht with ⟨fuel, verbose, hbeval⟩
  have h_eval_world := LeanProofs.evalAtDefault_eq hbeval
  cases fuel with
  | zero =>
      simp [LeanPoison.beval] at h_eval_world
      cases h_eval_world
  | succ fuel =>
      simp [LeanPoison.beval] at h_eval_world
      cases hlookup : ρ.lookup x with
      | none =>
          simp [hlookup] at h_eval_world
          cases h_eval_world
      | some v' =>
          simp [hlookup] at h_eval_world
          injection h_eval_world with hcfg hval
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

private lemma stepFR_literal
  (ctx : TypeContext) (predSat : PredSat) (R : Regime)
  (e : Expr) (res : TypeResult) (v : Value)
  (hval : Expr.toValue? e = some v)
  (hpoison : res.qualType.poison = false)
  (hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls)
  (hctxAfter : ctxAfter ctx res = ctx) :
  StepFR ctx R e res predSat := by
  intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hric₀ hric₁ hagree a₀ a₁ pm ht₀ ht₁
  have hterm₀ := terminatesTo_literal_inv e v hval μ₀ ρ₀ a₀ pm cf₀ o₀ ht₀
  have hterm₁ := terminatesTo_literal_inv e v hval μ₁ ρ₁ a₁ pm cf₁ o₁ ht₁
  rcases hterm₀ with ⟨hcf₀, ho₀⟩
  rcases hterm₁ with ⟨hcf₁, ho₁⟩
  subst hcf₀
  subst hcf₁
  refine ⟨θ₀, θ₁, ?_, ?_, ?_, ?_⟩
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
  · simpa [hctxAfter] using hagree
  · intro _hclean
    have hval' : o₀ = o₁ := by
      simp [ho₀, ho₁]
    exact agreeValueUnder.clean_eq_nonref hpoison hnotref hval'

theorem TypeSystemEnforcesFaultRobustness_step
  (e : Expr) (ctxᵢ : TypeContext) (predSat : PredSat) :
  TypeSystemEnforcesFaultRobustness_step_spec e ctxᵢ predSat := by
  unfold TypeSystemEnforcesFaultRobustness_step_spec
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ n IH =>
    intro res htc R
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
            -- Variable case proof skeleton (full proof requires case analysis
            -- on predicates and tag environment).
            intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hric₀ hric₁ hagree a₀ a₁ pm ht₀ ht₁
            have hterm₀ := terminatesTo_var_inv name μ₀ ρ₀ a₀ pm cf₀ o₀ ht₀
            have hterm₁ := terminatesTo_var_inv name μ₁ ρ₁ a₁ pm cf₁ o₁ ht₁
            rcases hterm₀ with ⟨v₀, _hlookup₀, hcf₀, _ho₀⟩
            rcases hterm₁ with ⟨v₁, _hlookup₁, hcf₁, _ho₁⟩
            subst hcf₀
            subst hcf₁
            refine ⟨θ₀, θ₁, ?_, ?_, ?_, ?_⟩
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
              simpa [ctxAfter, hmem, htag, hnextLoc, hnextTag] using hagree
            · -- Result agreement for clean outputs (requires predicate/tagEnv analysis).
              -- TODO: finish variable case.
              sorry
        | op e1 op e2 =>
            sorry
        | unaryop op e =>
            sorry
        | ite e1 e2 e3 =>
            sorry
        | newRef e =>
            sorry
        | assign e1 e2 =>
            sorry
        | deref e =>
            sorry
        | seq e1 e2 =>
            sorry
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
            sorry
        | printInt e =>
            sorry
        | externVal ty b sp =>
            sorry
        | externFn name ty ret effs =>
            sorry
        | externPfn name ty ret =>
            sorry

end TypeSystemEnforcesFaultRobustness_step_proof

theorem TypeSystemEnforcesFaultRobustness (e : Expr) (s : InputSpec) (obs : ObservableSpec) :
  TypeSystemEnforcesFaultRobustness_spec e s obs := by
  apply TypeSystemEnforcesFaultRobustness_impl
  exact TypeSystemEnforcesFaultRobustness_step
