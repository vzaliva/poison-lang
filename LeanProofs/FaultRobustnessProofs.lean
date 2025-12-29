-- Fault-Robustness proofs (skeletons)

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanPoison.BigStep
import Mathlib.Data.List.Forall2

import LeanProofs.FaultRobustness

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

-- Bridge lemma: top-level agreement premises imply the step-level invariant.
-- This is the key link from spec-driven premises to the context-driven StepFR.
private lemma agreeOnCriticalAndTrusted_implies_agreeOnClean
  (predSat : PredSat) (R : Regime) (s : InputSpec) (ctx : TypeContext)
  (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (θ₀ θ₁ : RealizationMap) :
  ctxMatchesInputSpec s ctx →
  agreeOnCriticalInputsUnderRegimeSpec predSat R s μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ →
  agreeOnTrustedInputs predSat R s ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ →
  agreeOnClean predSat R ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ := by
  sorry

theorem TypeSystemEnforcesFaultRobustness_impl :
  (∀ e ctxᵢ predSat,
    TypeSystemEnforcesFaultRobustness_step_spec e ctxᵢ predSat) →
  (∀ e s obs, TypeSystemEnforcesFaultRobustness_spec e s obs) := by
  sorry

end TypeSystemEnforcesFaultRobustness_impl_proof

section TypeSystemEnforcesFaultRobustness_step_proof

theorem TypeSystemEnforcesFaultRobustness_step
  (e : Expr) (ctxᵢ : TypeContext) (predSat : PredSat) :
  TypeSystemEnforcesFaultRobustness_step_spec e ctxᵢ predSat := by
  sorry

end TypeSystemEnforcesFaultRobustness_step_proof

theorem TypeSystemEnforcesFaultRobustness (e : Expr) (s : InputSpec) (obs : ObservableSpec) :
  TypeSystemEnforcesFaultRobustness_spec e s obs := by
  apply TypeSystemEnforcesFaultRobustness_impl
  exact TypeSystemEnforcesFaultRobustness_step
